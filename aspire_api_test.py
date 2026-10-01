#!/usr/bin/env python3
"""
aspire_api_test.py - exercise every object in the Aspire Lua API through the
Aspire MCP server, driven by the MCP Inspector CLI (npx) via subprocess.

What it does
------------
1. Discovery: calls the server's `search_lua_api` / `get_lua_api` tools through
   `npx @modelcontextprotocol/inspector@latest --cli` and builds a full manifest of
   every class (constructors, methods, static methods, properties, enums,
   metamethods) and global function, with parameter and return types.
   The manifest is cached to api_manifest.json (use --refresh to rebuild).
2. Test generation: for every signature it fabricates arguments from the
   declared parameter types, works out a Lua expression that yields an instance
   of each class (constructor, global factory, property or getter chain), and
   emits a small Lua snippet that calls the member inside pcall and checks
   each returned value against the declared return type.
3. Execution: snippets are batched into single-line chunks and sent through
   `run_lua_script` (a small harness is registered once with
   `define_lua_library`). A chunk that fails to compile or aborts is re-run one
   test at a time so one bad member cannot hide the others.
4. Report: results.json, results.csv and report.md in the output folder, a
   console summary, and exit code 1 if anything FAILed.

Statuses
--------
PASS   called without error and every return value has the declared type
FAIL   raised an error, returned the wrong type, or a documented member is missing
WARN   returned nil where the docs do not say nil is possible
SKIP   not called: unsafe (files, dialogs, job mutation, ownership transfer),
       or no way to build an argument / instance. Unsafe members still get an
       existence check where possible, so a missing member is still a FAIL.
ERROR  the harness itself could not report (chunk crashed, timeout, ...)

Safety
------
By default nothing that saves/opens/closes/imports/exports files, shows a
dialog, touches the clipboard, calculates toolpaths or mutates objects that
belong to the open job is *called*. Value objects the test creates itself
(Point2D, Contour, ...) are exercised fully. --include-unsafe lifts this;
only use it on a scratch job you can throw away.
Many members need an open job. With --new-job the script creates a scratch
job (only when no job is open), seeds it with a rectangle, and force-closes
it without saving at the end.

Windows note: npx is a .cmd shim, so every call goes through cmd.exe, which
limits a command line to 8191 characters and breaks on newlines and some
quote/metachar combinations. The generated Lua is therefore single-line, uses
no double quotes and no '%', and chunks are kept under --max-cmd characters.

Examples
--------
  python aspire_api_test.py                              # uses Claude Desktop config, server "aspire"
  python aspire_api_test.py --server aspire --new-job
  python aspire_api_test.py --only Point2D,Contour,Box2D --dump-lua lua_out
  python aspire_api_test.py --target C:/path/to/AspireMcp.exe --stdio
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import csv
import datetime as dt
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any

HARNESS_NAME = "mcpapitest_h"
RESULT_TAG = "@@R"

# --------------------------------------------------------------------------
# Lua harness (registered once with define_lua_library). Must stay free of
# double quotes, '%' and '--' comments; it is joined into one line.
# --------------------------------------------------------------------------
HARNESS_LUA = r"""
local H = {}
H.S = {}
H.D = {}
H.K = {}
function H.k(v) H.K[#H.K + 1] = v return v end
local function clean(s) s = tostring(s) s = s:gsub('[\t\r\n]', ' ') return s:sub(1, 400) end
function H.emit(id, st, d) print('@@R\t' .. id .. '\t' .. st .. '\t' .. clean(d or '')) end
function H.pack(...) return { n = select('#', ...), ... } end
function H.cname(v)
  if type(v) ~= 'userdata' then return type(v) end
  local ok, cn = pcall(function() return v.LuaClassName end)
  if ok and type(cn) == 'string' and cn ~= '' then return cn end
  local ok2, s = pcall(tostring, v)
  if ok2 and type(s) == 'string' then
    local p = s:find(':', 1, true)
    if p and p > 1 and p < 40 then return s:sub(1, p - 1) end
  end
  return 'userdata'
end
local PRIM = { number = true, string = true, boolean = true, table = true, ['function'] = true }
function H.isa(v, t)
  if PRIM[t] then return type(v) == t end
  if t == 'nil' then return v == nil end
  if t == 'any' then return true end
  if type(v) ~= 'userdata' then return false end
  local cn = H.cname(v)
  if cn == t or (H.D[t] and H.D[t][cn]) then return true end
  local sig = H.S[t]
  if not sig then return true end
  for i = 1, #sig do
    local key = sig[i]
    local ok, m = pcall(function() return v[key] end)
    if not ok or m == nil then return false end
  end
  return true
end
function H.inst(id, f)
  local ok, o = pcall(f)
  if not ok then H.emit(id, 'SKIP', 'could not obtain instance: ' .. tostring(o)) return nil end
  if o == nil then H.emit(id, 'SKIP', 'instance expression returned nil (open job / data needed?)') return nil end
  return o
end
function H.run(id, f, rets, nilok)
  local r = H.pack(pcall(f))
  if not r[1] then H.emit(id, 'FAIL', 'error: ' .. tostring(r[2])) return end
  local n = r.n - 1
  if #rets == 0 then H.emit(id, 'PASS', 'no declared return; got ' .. n .. ' value(s)') return end
  local got = {}
  for i = 1, #rets do
    local want, v = rets[i], r[i + 1]
    if v == nil then
      if i == 1 and not nilok and want ~= 'nil' then H.emit(id, 'WARN', 'returned nil, expected ' .. want) return end
      got[#got + 1] = 'nil'
    elseif not H.isa(v, want) then
      H.emit(id, 'FAIL', 'return ' .. i .. ': expected ' .. want .. ', got ' .. H.cname(v)) return
    else
      got[#got + 1] = H.cname(v)
    end
  end
  H.emit(id, 'PASS', table.concat(got, ', '))
end
function H.has(id, f, what, why)
  local ok, v = pcall(f)
  if ok and v ~= nil then H.emit(id, 'SKIP', why .. '; ' .. what .. ' exists')
  else H.emit(id, 'FAIL', 'documented ' .. what .. ' not found' .. (ok and '' or (': ' .. tostring(v)))) end
end
function H.rw(id, o, key)
  local ok, v = pcall(function() return o[key] end)
  if not ok then H.emit(id, 'FAIL', 'read failed: ' .. tostring(v)) return end
  local ok2, e = pcall(function() o[key] = v end)
  if not ok2 then H.emit(id, 'FAIL', 'write failed: ' .. tostring(e)) return end
  local ok3, v2 = pcall(function() return o[key] end)
  if ok3 and (type(v) == 'userdata' or v2 == v) then H.emit(id, 'PASS', 'wrote back ' .. H.cname(v))
  else H.emit(id, 'FAIL', 'value changed after write-back: ' .. tostring(v) .. ' -> ' .. tostring(v2)) end
end
return H
"""

# --------------------------------------------------------------------------
# Heuristics
# --------------------------------------------------------------------------
TYPE_ALIASES = {
    "int": "number", "integer": "number", "double": "number", "float": "number",
    "bool": "boolean", "str": "string", "void": "nil", "none": "nil",
    "userdata": "any", "object": "any", "value": "any", "*": "any",
}
PRIMITIVES = {"number", "string", "boolean", "table", "function", "nil", "any"}

# Words that make a member unsafe to call anywhere (files, UI, app state).
ALWAYS_UNSAFE_WORDS = {
    "Save", "Open", "Close", "Import", "Export", "Show", "Display", "Dialog",
    "Message", "Write", "Undo", "Redo", "Clipboard", "Capture", "Execute",
    "Exit", "Quit", "Browse", "Print", "Load", "Launch", "Thumbnail", "Demo",
    "Calculate", "Recalculate", "Simulate", "Simulation", "Nest", "Post",
}
# Extra words that make a *global function* unsafe.
GLOBAL_UNSAFE_WORDS = {"Job"}
# First words that mean "this changes the object" - skipped on objects that
# belong to the open job (value objects created by the test are fine).
MUTATING_FIRST_WORDS = {
    "Delete", "Remove", "Clear", "Set", "Add", "Insert", "Append", "Create",
    "Move", "Copy", "Group", "Un", "Ungroup", "Switch", "Transform", "Update",
    "Apply", "Invalidate", "Increment", "Modified", "Rename", "Lock", "Unlock",
    "Hide", "Merge", "Split", "Reverse", "Smash", "Offset", "Select",
    "Deselect", "Unselect", "Refresh", "Activate", "Make", "Mark", "Reset",
    "Replace", "Join", "Weld", "Explode", "Paste", "Cut", "Toggle", "Enable",
    "Disable", "Put", "Flip", "Mirror", "Scale", "Rotate", "Translate",
    "Align", "Sort", "Swap", "Do", "Process", "Run", "Start", "Stop", "Begin",
    "End", "Commit", "Recalc", "Regenerate", "Rebuild", "Attach", "Detach",
    "Link", "Unlink", "Push", "Pop", "Assign", "Reorder", "Bake", "Convert",
}
# Methods allowed to *produce* instances from job-bound parents.
PRODUCER_METHOD_RE = re.compile(r"^(Get|Find|Clone|Create\w*Copy|As[A-Z]|To[A-Z])")
# Classes that are exercised only by existence checks unless --include-unsafe.
UNSAFE_CLASSES = {
    "Debug", "FeatureManager", "FileDialog", "HTML_Dialog", "ProgressBar",
    "ToolpathSaver", "PostProcessor", "Nester", "SimulationManager",
    "DicedPanelManager", "DirectoryReader", "mcp",
}
# Classes whose instances belong to the application/job rather than the test.
BOUND_CLASS_RE = re.compile(
    r"(Manager|Job|Database|Registry|Dialog|Bar|Saver|Nester|Reader|PostProcessor|"
    r"Debug|Layer|Sheet|Selection|Toolpath$|ToolpathNode|ToolpathList|Assembly|Level|"
    r"Component|Relief|DocumentVariable)"
)
FILE_PARAM_RE = re.compile(r"(path|file|folder|dir|filename|pathname)", re.I)

# Preferred instance expressions (used only if every identifier in them exists).
OVERRIDES = {
    "Point2D": "Point2D(3,4)",
    "Point3D": "Point3D(3,4,5)",
    "Vector2D": "Vector2D(1,1)",
    "Vector3D": "Vector3D(0,0,1)",
    "Box2D": "Box2D(Point2D(0,0),Point2D(10,10))",
    "Box3D": "Box3D(Point3D(0,0,0),Point3D(10,10,10))",
    "Contour": "CreateRectangle(0,0,10,10,0.01)",
    "ContourGroup": "ArrayGrid(CreateRectangle(0,0,10,10,0.01),1,2,20,20)",
    "Matrix2D": "IdentityMatrix2D()",
    "Matrix3D": "IdentityMatrix3D()",
    "CadContour": "CreateCadContour(CreateRectangle(0,0,10,10,0.01))",
    "CadPolyline": "CreateCadPolyline(CreateRectangle(0,0,10,10,0.01))",
    "CadObjectGroup": "CreateCadGroup(ArrayGrid(CreateRectangle(0,0,10,10,0.01),1,2,20,20))",
    "VectricJob": "VectricJob()",
}
# Second/third argument of the same type gets a different value.
ALTERNATES = {
    "Point2D": ["Point2D(13,9)", "Point2D(7,15)"],
    "Point3D": ["Point3D(13,9,2)", "Point3D(7,15,4)"],
    "Vector2D": ["Vector2D(0,1)", "Vector2D(1,0)"],
    "Vector3D": ["Vector3D(1,0,0)", "Vector3D(0,1,0)"],
}
IDENT_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\s*[\(\.:]")


def camel_words(name: str) -> list[str]:
    return re.findall(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+", name.lstrip("_"))


def norm_type(t: Any) -> str:
    if not t:
        return "nil"
    t = str(t).strip()
    if "|" in t or " or " in t:
        return "any"
    return TYPE_ALIASES.get(t.lower(), t)


def lua_str(s: str) -> str:
    return "'" + s.replace("\\", "\\\\").replace("'", "\\'") + "'"


def number_for(pname: str) -> str:
    n = (pname or "").lower()
    if any(k in n for k in ("index", "idx")) or n in ("pos", "i", "n_index"):
        return "0"
    if "tol" in n:
        return "0.01"
    if "angle" in n or n.endswith("deg"):
        return "45"
    if any(k in n for k in ("param", "fraction", "ratio")) or n == "t":
        return "0.5"
    if any(k in n for k in ("count", "rows", "cols", "num", "number")):
        return "2"
    if any(k in n for k in ("radius", "width", "height", "length", "size", "dist", "diameter",
                             "thickness", "depth", "len")) or n in ("w", "h", "r", "d"):
        return "5"
    return "1"


def string_for(pname: str) -> str:
    n = (pname or "").lower()
    if n in ("view",):
        return "'active'"
    if n in ("camera",):
        return "'plan'"
    if "section" in n:
        return "'mcp_api_test'"
    return "'mcp_api_test'"


def table_for(pname: str) -> str:
    n = (pname or "").lower()
    if "point" in n or "pts" in n:
        return "{Point2D(0,0),Point2D(10,0),Point2D(10,10)}"
    return "{}"


# --------------------------------------------------------------------------
# Inspector CLI wrapper
# --------------------------------------------------------------------------
class InspectorError(RuntimeError):
    pass


class Inspector:
    def __init__(self, args: argparse.Namespace):
        self.args = args
        npx = shutil.which(args.npx) or args.npx
        if args.inspector_cmd:
            self.prefix = args.inspector_cmd.split()
        else:
            self.prefix = [npx, "-y", args.inspector_pkg, "--cli"]
        if args.target:
            self.target = list(args.target)
        else:
            self.target = []
            if args.config:
                self.target += ["--config", args.config]
            if args.server:
                self.target += ["--server", args.server]
        # Inspector 2.x gives up connecting after 30s by default; Aspire can take
        # longer to answer initialize (busy, modal dialog, still starting).
        self.opts = []
        if args.connect_timeout > 0:
            self.opts += ["--connect-timeout", str(int(args.connect_timeout * 1000))]
        self.calls = 0

    def base_cmd(self, method: str) -> list[str]:
        cmd = list(self.prefix)
        if self.args.target:
            cmd += self.target  # a raw command goes first, options follow
        else:
            cmd += self.target
        cmd += self.opts
        cmd += ["--method", method]
        return cmd

    def cmd_len(self, cmd: list[str]) -> int:
        return len(subprocess.list2cmdline(cmd))

    def _run(self, cmd: list[str], timeout: float) -> Any:
        self.calls += 1
        if self.args.verbose:
            shown = subprocess.list2cmdline(cmd)
            print(f"    $ {shown[:300]}{'...' if len(shown) > 300 else ''}", file=sys.stderr)
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                                  errors="replace", timeout=timeout)
        except subprocess.TimeoutExpired:
            raise InspectorError(f"timed out after {timeout}s")
        except FileNotFoundError as e:
            raise InspectorError(f"could not start inspector ({e}); is Node/npx on PATH?")
        out = (proc.stdout or "").strip()
        data = _parse_json(out)
        if data is None:
            msg = (proc.stderr or "").strip()[-1500:] or out[-1500:]
            raise InspectorError(f"inspector exit {proc.returncode}: {msg}")
        return data

    def list_tools(self) -> list[dict]:
        data = self._run(self.base_cmd("tools/list"), self.args.timeout)
        return data.get("tools", [])

    def call_tool(self, tool: str, timeout: float | None = None, **tool_args: str) -> tuple[str, bool]:
        cmd = self.tool_cmd(tool, **tool_args)
        data = self._run(cmd, timeout or self.args.timeout)
        text = "\n".join(c.get("text", "") for c in data.get("content", []) if c.get("type") == "text")
        return text, bool(data.get("isError"))

    def tool_cmd(self, tool: str, **tool_args: str) -> list[str]:
        cmd = self.base_cmd("tools/call") + ["--tool-name", tool]
        for k, v in tool_args.items():
            cmd += ["--tool-arg", f"{k}={v}"]
        return cmd


def _parse_json(text: str) -> Any:
    if not text:
        return None
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass
    start = text.find("{")
    end = text.rfind("}")
    if start != -1 and end > start:
        try:
            return json.loads(text[start:end + 1])
        except json.JSONDecodeError:
            return None
    return None


# --------------------------------------------------------------------------
# Discovery
# --------------------------------------------------------------------------
def discover(insp: Inspector, args: argparse.Namespace) -> dict:
    print("Discovering the Lua API ...")
    pointers: list[str] = []
    try:
        text, err = insp.call_tool("search_lua_api", kind='["class","function"]')
        data = json.loads(text)
        if err or data.get("truncated"):
            raise ValueError("search truncated or failed")
        pointers = [m["pointer"] for m in data["matches"] if m.get("kind") in ("class", "function")]
        print(f"  search_lua_api listed {len(pointers)} classes/functions")
    except Exception as e:  # fall back to walking the pointers
        print(f"  search_lua_api listing failed ({e}); walking /classes/N and /functions/N")
        pointers = _walk_pointers(insp)

    manifest = {"generated": dt.datetime.now().isoformat(timespec="seconds"),
                "classes": {}, "functions": {}}

    def fetch(ptr: str):
        text, err = insp.call_tool("get_lua_api", pointer=ptr)
        if err:
            raise InspectorError(text)
        return ptr, json.loads(text)

    with cf.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = [pool.submit(fetch, p) for p in pointers]
        for i, fut in enumerate(cf.as_completed(futs), 1):
            try:
                ptr, entry = fut.result()
            except Exception as e:
                print(f"  ! fetch failed: {e}")
                continue
            entry["pointer"] = ptr
            bucket = "classes" if ptr.startswith("/classes/") else "functions"
            manifest[bucket][entry["name"]] = entry
            if i % 20 == 0 or i == len(futs):
                print(f"  fetched {i}/{len(futs)}")
    return manifest


def _walk_pointers(insp: Inspector) -> list[str]:
    ptrs = []
    for kind in ("classes", "functions"):
        i = 0
        while True:
            try:
                text, err = insp.call_tool("get_lua_api", pointer=f"/{kind}/{i}")
                json.loads(text)
                if err:
                    break
            except Exception:
                break
            ptrs.append(f"/{kind}/{i}")
            i += 1
    return ptrs


# --------------------------------------------------------------------------
# Model helpers
# --------------------------------------------------------------------------
@dataclass
class Producer:
    expr: str
    bound: bool          # belongs to the app/job, so do not mutate it
    via: str             # how it was obtained (for the report)


@dataclass
class Test:
    id: str
    cls: str             # class name or "(global)"
    member: str
    kind: str            # ctor, method, static, prop-read, prop-write, meta, enum, function, class
    signature: str
    code: str = ""       # Lua snippet; empty => resolved in Python
    types: set = field(default_factory=set)
    status: str = ""
    detail: str = ""


class Api:
    def __init__(self, manifest: dict):
        self.classes: dict[str, dict] = manifest["classes"]
        self.functions: dict[str, dict] = manifest["functions"]
        self.children: dict[str, list[str]] = {}
        for name, c in self.classes.items():
            parent = c.get("inherits")
            if parent:
                self.children.setdefault(parent, []).append(name)

    def exists(self, ident: str) -> bool:
        return ident in self.classes or ident in self.functions

    def ancestors(self, cls: str) -> list[str]:
        out, seen = [], set()
        cur = self.classes.get(cls, {}).get("inherits")
        while cur and cur not in seen:
            out.append(cur)
            seen.add(cur)
            cur = self.classes.get(cur, {}).get("inherits")
        return out

    def descendants(self, cls: str) -> list[str]:
        out, stack = [], list(self.children.get(cls, []))
        while stack:
            c = stack.pop(0)
            out.append(c)
            stack.extend(self.children.get(c, []))
        return out

    def all_methods(self, cls: str) -> list[dict]:
        methods = list(self.classes.get(cls, {}).get("methods", []))
        for a in self.ancestors(cls):
            methods += self.classes.get(a, {}).get("methods", [])
        return methods

    def all_props(self, cls: str) -> list[dict]:
        props = list(self.classes.get(cls, {}).get("properties", []))
        for a in self.ancestors(cls):
            props += self.classes.get(a, {}).get("properties", [])
        return props

    def duck_sig(self, cls: str) -> list[str]:
        for c in [cls] + self.ancestors(cls):
            names = [m["name"] for m in self.classes.get(c, {}).get("methods", [])
                     if not m.get("metamethod") and not m.get("static")]
            if names:
                return names[:5]
        return []


def is_value_class(name: str) -> bool:
    return not BOUND_CLASS_RE.search(name)


def override_ok(api: Api, expr: str) -> bool:
    return all(api.exists(i) for i in IDENT_RE.findall(expr))


# --------------------------------------------------------------------------
# Instance producers
# --------------------------------------------------------------------------
class Builder:
    def __init__(self, api: Api, include_unsafe: bool):
        self.api = api
        self.unsafe_ok = include_unsafe
        self.prod: dict[str, Producer] = {}
        self._solve()

    # -- argument fabrication ------------------------------------------------
    def arg_expr(self, ptype: str, pname: str) -> tuple[str, bool] | None:
        t = norm_type(ptype)
        if t == "number":
            return number_for(pname), False
        if t == "string":
            return string_for(pname), False
        if t == "boolean":
            return "false", False
        if t == "table":
            return table_for(pname), False
        if t == "function":
            return "function() end", False
        if t in ("nil", "any"):
            return "nil", False
        p = self.prod.get(t)
        if p:
            return p.expr, p.bound
        return None

    def args_for(self, params: list[dict]) -> tuple[list[str], bool] | None:
        out, bound, seen = [], False, {}
        for p in params:
            t = norm_type(p.get("type"))
            n = seen.get(t, 0)
            seen[t] = n + 1
            if n and t in ALTERNATES:  # avoid degenerate calls like Box2D(p, p)
                out.append(ALTERNATES[t][(n - 1) % len(ALTERNATES[t])])
                continue
            r = self.arg_expr(p.get("type"), p.get("name", ""))
            if r is None:
                return None
            out.append(r[0])
            bound = bound or r[1]
        return out, bound

    # -- fixpoint search -----------------------------------------------------
    def _solve(self):
        api = self.api
        for cls, expr in OVERRIDES.items():
            if cls in api.classes and override_ok(api, expr):
                self.prod[cls] = Producer(expr, not is_value_class(cls), "override")

        for _ in range(8):
            before = len(self.prod)
            # constructors
            for name, c in api.classes.items():
                if name in self.prod or name in UNSAFE_CLASSES and not self.unsafe_ok:
                    continue
                for sig in sorted(c.get("constructors", []), key=lambda s: len(s.get("parameters", []))):
                    a = self.args_for(sig.get("parameters", []))
                    if a is not None:
                        self.prod[name] = Producer(f"{name}({','.join(a[0])})",
                                                   not is_value_class(name) or a[1], "constructor")
                        break
            # global functions
            for fname, f in api.functions.items():
                if global_unsafe_reason(fname, f):
                    continue
                for sig in f.get("signatures", []):
                    rets = sig.get("returns", [])
                    if not rets:
                        continue
                    t = norm_type(rets[0].get("type"))
                    if t in PRIMITIVES or t in self.prod or t not in api.classes:
                        continue
                    a = self.args_for(sig.get("parameters", []))
                    if a is not None:
                        self.prod[t] = Producer(f"{fname}({','.join(a[0])})", a[1], f"global {fname}")
            # properties and getter methods of what we can already build
            for owner, p in list(self.prod.items()):
                if len(p.expr) > 250:
                    continue
                for prop in api.all_props(owner):
                    t = norm_type(prop.get("type"))
                    if t in self.prod or t not in api.classes or prop.get("static"):
                        continue
                    self.prod[t] = Producer(f"H.k({p.expr}).{prop['name']}", p.bound, f"{owner}.{prop['name']}")
                for m in api.all_methods(owner):
                    if m.get("metamethod") or m.get("static") or not PRODUCER_METHOD_RE.match(m["name"]):
                        continue
                    if member_unsafe_words(m["name"]):
                        continue
                    for sig in m.get("signatures", []):
                        rets = sig.get("returns", [])
                        if not rets:
                            continue
                        t = norm_type(rets[0].get("type"))
                        if t in self.prod or t not in api.classes:
                            continue
                        if takes_ownership(sig) or has_file_param(sig):
                            continue
                        a = self.args_for(sig.get("parameters", []))
                        if a is not None:
                            self.prod[t] = Producer(f"H.k({p.expr}):{m['name']}({','.join(a[0])})",
                                                    p.bound or a[1], f"{owner}:{m['name']}")
            # abstract bases: use any buildable descendant
            for name in api.classes:
                if name in self.prod:
                    continue
                for d in api.descendants(name):
                    if d in self.prod:
                        dp = self.prod[d]
                        self.prod[name] = Producer(dp.expr, dp.bound, f"subclass {d}")
                        break
            if len(self.prod) == before:
                break


# --------------------------------------------------------------------------
# Safety rules
# --------------------------------------------------------------------------
def member_unsafe_words(name: str) -> str | None:
    words = set(camel_words(name))
    hit = words & ALWAYS_UNSAFE_WORDS
    return f"unsafe ({'/'.join(sorted(hit))})" if hit else None


def has_file_param(sig: dict) -> bool:
    return any(norm_type(p.get("type")) == "string" and FILE_PARAM_RE.search(p.get("name", ""))
               for p in sig.get("parameters", []))


def takes_ownership(sig: dict) -> bool:
    return any("ownership" in (p.get("doc") or "").lower() for p in sig.get("parameters", []))


def notes_side_effect(entry: dict) -> bool:
    return any(n.get("kind") == "side_effect" for n in entry.get("notes", []) or [])


def global_unsafe_reason(name: str, entry: dict) -> str | None:
    words = camel_words(name)
    hit = set(words) & (ALWAYS_UNSAFE_WORDS | GLOBAL_UNSAFE_WORDS)
    if hit:
        return f"unsafe ({'/'.join(sorted(hit))})"
    if words and words[0] in {"Select", "Delete", "Remove", "Clear", "Set", "Move", "Group", "Ungroup", "Allow"}:
        return f"changes application state ({words[0]})"
    if notes_side_effect(entry):
        return "documented side effect"
    return None


def method_unsafe_reason(name: str, entry: dict, sig: dict, bound: bool) -> str | None:
    r = member_unsafe_words(name)
    if r:
        return r
    if notes_side_effect(entry):
        return "documented side effect"
    if has_file_param(sig):
        return "takes a file path"
    if takes_ownership(sig):
        return "takes ownership of an argument (crash risk)"
    words = camel_words(name)
    if bound and words and words[0] in MUTATING_FIRST_WORDS:
        return f"would change the open job ({words[0]})"
    return None


# --------------------------------------------------------------------------
# Test generation
# --------------------------------------------------------------------------
META_OPS = {
    "__add": "o + {0}", "__sub": "o - {0}", "__mul": "o * {0}", "__div": "o / {0}",
    "__pow": "o ^ {0}", "__eq": "o == {0}", "__lt": "o < {0}", "__le": "o <= {0}",
    "__concat": "o .. {0}", "__unm": "-o", "__len": "#o",
}


def sig_text(params: list[dict], rets: list[dict]) -> str:
    p = ", ".join(f"{x.get('name', '?')}: {x.get('type', '?')}" for x in params)
    r = ", ".join(str(x.get("type")) for x in rets) or "()"
    return f"({p}) -> {r}"


def nil_ok(rets: list[dict], extra_doc: str = "") -> bool:
    text = " ".join((r.get("doc") or "") for r in rets) + " " + (extra_doc or "")
    return bool(re.search(r"\bnil\b|\bempty\b|\bor none\b", text, re.I))


def rets_lua(rets: list[dict]) -> tuple[str, set]:
    types = [norm_type(r.get("type")) for r in rets]
    return "{" + ",".join(lua_str(t) for t in types) + "}", {t for t in types if t not in PRIMITIVES}


def build_tests(api: Api, b: Builder, only: set | None, include_unsafe: bool,
                test_writes: bool, job_open: bool = True) -> list[Test]:
    tests: list[Test] = []
    NO_JOB = "needs an open job (none open; use --new-job)"

    def add(t: Test):
        # Calling into job-bound objects with no job open can crash the host,
        # so those are never sent. VectricJob() and .Exists are always safe.
        if (not job_open and t.code and t.kind not in ("class", "enum")
                and getattr(t, "_bound", False)
                and not (t.cls == "VectricJob" and t.member in ("(constructor)", "Exists"))):
            t.code, t.status, t.detail = "", "SKIP", NO_JOB
        tests.append(t)

    # ---- global functions ----
    if not only or "(global)" in only or any(o in api.functions for o in only):
        for fname, f in sorted(api.functions.items()):
            if only and "(global)" not in only and fname not in only:
                continue
            for i, sig in enumerate(f.get("signatures", []), 1):
                params, rets = sig.get("parameters", []), sig.get("returns", [])
                tid = f"{fname}#{i}"
                t = Test(tid, "(global)", fname, "function", sig_text(params, rets))
                why = None if include_unsafe else global_unsafe_reason(fname, f)
                if why:
                    t.code = f"H.has({lua_str(tid)}, function() return {fname} end, 'function', {lua_str(why)})"
                    add(t)
                    continue
                a = b.args_for(params)
                if a is None:
                    t.status, t.detail = "SKIP", "cannot build an argument: " + missing_types(b, params)
                    add(t)
                    continue
                rl, types = rets_lua(rets)
                t.types = types
                t._bound = a[1]
                t.code = (f"H.run({lua_str(tid)}, function() return {fname}({','.join(a[0])}) end, "
                          f"{rl}, {str(nil_ok(rets, f.get('doc', ''))).lower()})")
                add(t)

    # ---- classes ----
    for cname, c in sorted(api.classes.items()):
        if only and cname not in only:
            continue
        unsafe_class = cname in UNSAFE_CLASSES and not include_unsafe
        inst = b.prod.get(cname)

        # class existence
        add(Test(f"{cname}", cname, "(class)", "class", "",
                 code=f"H.run({lua_str(cname)}, function() return {cname} end, {{'any'}}, false)"))

        if unsafe_class:
            t = Test(f"{cname}.*", cname, "*", "class", "",
                     status="SKIP", detail="class exercised by existence check only (unsafe class)")
            add(t)
            continue

        # constructors
        for i, sig in enumerate(c.get("constructors", []), 1):
            params, rets = sig.get("parameters", []), sig.get("returns", [{"type": cname}])
            tid = f"{cname}.new#{i}"
            t = Test(tid, cname, "(constructor)", "ctor", sig_text(params, rets))
            a = b.args_for(params)
            t._bound = (not is_value_class(cname)) or bool(a and a[1])
            if a is None:
                t.status, t.detail = "SKIP", "cannot build an argument: " + missing_types(b, params)
            else:
                rl, t.types = rets_lua(rets or [{"type": cname}])
                t.code = f"H.run({lua_str(tid)}, function() return {cname}({','.join(a[0])}) end, {rl}, false)"
            add(t)

        # methods (own only; inherited ones are tested on their base class)
        for m in c.get("methods", []):
            mname = m["name"]
            for i, sig in enumerate(m.get("signatures", []), 1):
                params, rets = sig.get("parameters", []), sig.get("returns", [])
                static = bool(m.get("static"))
                meta = bool(m.get("metamethod"))
                sep = "." if static else ":"
                tid = f"{cname}{sep}{mname}#{i}"
                kind = "meta" if meta else ("static" if static else "method")
                t = Test(tid, cname, mname, kind, sig_text(params, rets))
                t._bound = bool(inst and inst.bound) or (static and not is_value_class(cname))
                if m.get("deprecated") or sig.get("deprecated"):
                    t.detail = "deprecated. "
                bound = inst.bound if inst else False
                why = None if include_unsafe else method_unsafe_reason(mname, m, sig, bound or static)
                a = b.args_for(params)
                rl, t.types = rets_lua(rets)
                nok = str(nil_ok(rets, m.get("doc", ""))).lower()

                if static:
                    if why:
                        t.code = f"H.has({lua_str(tid)}, function() return {cname}.{mname} end, 'static method', {lua_str(why)})"
                    elif a is None:
                        t.status, t.detail = "SKIP", t.detail + "cannot build an argument: " + missing_types(b, params)
                    else:
                        t.code = f"H.run({lua_str(tid)}, function() return {cname}.{mname}({','.join(a[0])}) end, {rl}, {nok})"
                    add(t)
                    continue

                if not inst:
                    t.status, t.detail = "SKIP", t.detail + "no way to obtain an instance of " + cname
                    add(t)
                    continue
                pre = f"do local o = H.inst({lua_str(tid)}, function() return {inst.expr} end) if o then "
                post = " end end"
                if why:
                    if meta:
                        t.status, t.detail = "SKIP", why
                        add(t)
                        continue
                    t.code = pre + f"H.has({lua_str(tid)}, function() return o.{mname} end, 'method', {lua_str(why)})" + post
                    add(t)
                    continue
                if a is None:
                    t.status, t.detail = "SKIP", t.detail + "cannot build an argument: " + missing_types(b, params)
                    add(t)
                    continue
                if meta:
                    if mname in ("tostring", "__tostring"):
                        call = "tostring(o)"
                    elif mname == "__call":
                        call = f"o({','.join(a[0])})"
                    elif mname in META_OPS:
                        if META_OPS[mname].count("{0}") and not a[0]:
                            a = (["o"], False)
                        call = META_OPS[mname].format(*(a[0] or ["o"]))
                    else:
                        t.status, t.detail = "SKIP", f"metamethod {mname} not exercised"
                        add(t)
                        continue
                    if mname in ("__eq", "__lt", "__le") and not rets:
                        rl = "{'boolean'}"
                    t.code = pre + f"H.run({lua_str(tid)}, function() return {call} end, {rl}, {nok})" + post
                else:
                    t.code = pre + f"H.run({lua_str(tid)}, function() return o:{mname}({','.join(a[0])}) end, {rl}, {nok})" + post
                add(t)

        # properties
        for p in c.get("properties", []):
            pname, ptype = p["name"], norm_type(p.get("type"))
            access = p.get("access", "read")
            static = bool(p.get("static"))
            rl, types = rets_lua([{"type": ptype}])
            nok = str(nil_ok([], p.get("doc", ""))).lower()
            if "read" in access:
                tid = f"{cname}.{pname}"
                t = Test(tid, cname, pname, "prop-read", f": {p.get('type')} ({access})", types=types)
                t._bound = bool(inst and inst.bound) or (static and not is_value_class(cname))
                if p.get("deprecated"):
                    t.detail = "deprecated. "
                if static:
                    t.code = f"H.run({lua_str(tid)}, function() return {cname}.{pname} end, {rl}, {nok})"
                elif inst:
                    t.code = (f"do local o = H.inst({lua_str(tid)}, function() return {inst.expr} end) if o then "
                              f"H.run({lua_str(tid)}, function() return o.{pname} end, {rl}, {nok}) end end")
                else:
                    t.status, t.detail = "SKIP", "no way to obtain an instance of " + cname
                add(t)
            if test_writes and "write" in access and not static:
                tid = f"{cname}.{pname}=set"
                t = Test(tid, cname, pname, "prop-write", f": {p.get('type')} ({access})")
                t._bound = bool(inst and inst.bound)
                if not inst:
                    t.status, t.detail = "SKIP", "no way to obtain an instance of " + cname
                elif inst.bound and not include_unsafe:
                    t.status, t.detail = "SKIP", "instance belongs to the open job; write-back not attempted"
                elif "read" not in access:
                    t.status, t.detail = "SKIP", "write-only property"
                else:
                    t.code = (f"do local o = H.inst({lua_str(tid)}, function() return {inst.expr} end) if o then "
                              f"H.rw({lua_str(tid)}, o, {lua_str(pname)}) end end")
                add(t)

        # enums
        for e in c.get("enums", []) or []:
            for v in e.get("values", []):
                vname = v["name"] if isinstance(v, dict) else str(v)
                tid = f"{cname}.{vname}"
                add(Test(tid, cname, vname, "enum", f"{e.get('name')} value",
                         code=f"H.run({lua_str(tid)}, function() return {cname}.{vname} end, {{'number'}}, false)"))
    return tests


def missing_types(b: Builder, params: list[dict]) -> str:
    miss = [norm_type(p.get("type")) for p in params if b.arg_expr(p.get("type"), p.get("name", "")) is None]
    return ", ".join(sorted(set(miss))) or "?"


# --------------------------------------------------------------------------
# Execution
# --------------------------------------------------------------------------
def one_line(lua: str) -> str:
    lines = [ln.strip() for ln in lua.strip().splitlines()]
    s = " ".join(ln for ln in lines if ln)
    bad = [ch for ch in ('"', "%") if ch in s]
    if bad or "--" in s:
        raise ValueError(f"generated Lua contains characters unsafe for cmd.exe: {bad or '--'}")
    return s


def preamble(api: Api, types: set) -> str:
    parts = []
    for t in sorted(types):
        sig = api.duck_sig(t)
        if sig:
            parts.append(f"{t}={{{','.join(lua_str(s) for s in sig)}}}")
    desc = []
    for t in sorted(types):
        d = api.descendants(t)
        if d:
            desc.append(f"{t}={{{','.join(f'{x}=true' for x in d)}}}")
    return (f"local H = require({lua_str(HARNESS_NAME)}) H.S = {{{','.join(parts)}}} "
            f"H.D = {{{','.join(desc)}}} ")


def make_chunks(api: Api, insp: Inspector, tests: list[Test], max_cmd: int) -> list[list[Test]]:
    base = insp.cmd_len(insp.tool_cmd("run_lua_script", script="x")) + 40
    budget = max_cmd - base
    chunks, cur, cur_types, cur_len = [], [], set(), 0
    for t in tests:
        new_types = cur_types | t.types
        est = len(preamble(api, new_types)) + cur_len + len(t.code) + 60
        if cur and est > budget:
            chunks.append(cur)
            cur, cur_types, cur_len = [], set(), 0
            new_types = set(t.types)
        cur.append(t)
        cur_types = new_types
        cur_len += len(t.code) + 1
    if cur:
        chunks.append(cur)
    return chunks


def chunk_script(api: Api, chunk: list[Test]) -> str:
    types = set().union(*(t.types for t in chunk)) if chunk else set()
    body = " ".join(t.code for t in chunk)
    return one_line(preamble(api, types) + body + " H.emit('__chunk', 'DONE', '')")


def parse_results(text: str) -> dict[str, tuple[str, str]]:
    res = {}
    for line in text.splitlines():
        if line.startswith(RESULT_TAG + "\t"):
            parts = line.split("\t", 3)
            if len(parts) >= 3:
                res[parts[1]] = (parts[2], parts[3] if len(parts) > 3 else "")
    return res


def run_chunk(api: Api, insp: Inspector, chunk: list[Test], dump_dir: Path | None, idx: str,
              max_cmd: int) -> None:
    script = chunk_script(api, chunk)
    if dump_dir:
        (dump_dir / f"chunk_{idx}.lua").write_text(script, encoding="utf-8")
    if insp.cmd_len(insp.tool_cmd("run_lua_script", script=script)) > max_cmd and len(chunk) > 1:
        mid = len(chunk) // 2
        run_chunk(api, insp, chunk[:mid], dump_dir, idx + "a", max_cmd)
        run_chunk(api, insp, chunk[mid:], dump_dir, idx + "b", max_cmd)
        return
    try:
        text, err = insp.call_tool("run_lua_script", timeout=insp.args.lua_timeout, script=script)
    except InspectorError as e:
        text, err = f"inspector error: {e}", True
    got = parse_results(text)
    missing = [t for t in chunk if t.id not in got]
    for t in chunk:
        if t.id in got:
            st, d = got[t.id]
            t.status, t.detail = st, (t.detail + d).strip()
    if missing:
        if len(chunk) > 1:
            # isolate the offender(s): re-run each missing test on its own
            for j, t in enumerate(missing):
                run_chunk(api, insp, [t], dump_dir, f"{idx}_{j}", max_cmd)
        else:
            t = chunk[0]
            t.status = "ERROR"
            t.detail = (t.detail + " " + _first_error(text)).strip()


def _first_error(text: str) -> str:
    lines = [ln for ln in text.splitlines() if ln.strip() and not ln.startswith(RESULT_TAG)]
    return " | ".join(lines[:3])[:400] or "no result reported"


# --------------------------------------------------------------------------
# Job setup
# --------------------------------------------------------------------------
def job_exists(insp: Inspector) -> bool | None:
    try:
        text, _ = insp.call_tool("run_lua_script", script="return VectricJob().Exists")
        return "=> true" in text
    except InspectorError:
        return None


def create_scratch_job(insp: Inspector) -> bool:
    script = one_line("""
        local ok = CreateNewJob('mcp_api_test', Box2D(Point2D(0,0), Point2D(200,200)), 20, true, true)
        if ok then
          local layer = VectricJob().LayerManager:GetActiveLayer()
          layer:AddObject(CreateCadContour(CreateRectangle(20,20,60,40,0.01)), true)
          layer:AddObject(CreateCadContour(CreateCircle(120,120,30,0.01,0)), true)
        end
        return ok
    """)
    text, _ = insp.call_tool("run_lua_script", script=script)
    return "=> true" in text


def close_scratch_job(insp: Inspector) -> None:
    insp.call_tool("run_lua_script", script="return ForceCloseCurrentJob(true)")


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------
STATUSES = ["PASS", "FAIL", "WARN", "SKIP", "ERROR"]


def write_reports(out: Path, tests: list[Test], meta: dict) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    counts = {s: sum(1 for t in tests if t.status == s) for s in STATUSES}
    rows = [{k: v for k, v in asdict(t).items() if k not in ("code", "types")} for t in tests]
    (out / "results.json").write_text(json.dumps({"meta": meta, "counts": counts, "results": rows},
                                                 indent=2), encoding="utf-8")
    with open(out / "results.csv", "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["id", "cls", "member", "kind", "signature", "status", "detail"])
        w.writeheader()
        w.writerows(rows)

    by_cls: dict[str, dict[str, int]] = {}
    for t in tests:
        by_cls.setdefault(t.cls, {s: 0 for s in STATUSES})[t.status] = by_cls.get(t.cls, {}).get(t.status, 0) + 1
    md = [f"# Aspire Lua API test report", "",
          f"- Run: {meta['started']} ({meta['seconds']:.0f}s, {meta['inspector_calls']} inspector calls)",
          f"- Server: {meta['server']}",
          f"- Job open during tests: {meta['job']}",
          f"- Unsafe members called: {meta['include_unsafe']}", "",
          "| " + " | ".join(STATUSES) + " | Total |", "|" + "---|" * (len(STATUSES) + 1),
          "| " + " | ".join(str(counts[s]) for s in STATUSES) + f" | {len(tests)} |", ""]
    for status in ("FAIL", "ERROR", "WARN"):
        bad = [t for t in tests if t.status == status]
        if bad:
            md += [f"## {status} ({len(bad)})", "", "| Test | Signature | Detail |", "|---|---|---|"]
            md += [f"| `{t.id}` | `{t.signature}` | {t.detail.replace('|', '/')} |" for t in bad]
            md.append("")
    md += ["## By class", "", "| Class | " + " | ".join(STATUSES) + " |", "|---|" + "---|" * len(STATUSES)]
    for cls in sorted(by_cls):
        md.append(f"| {cls} | " + " | ".join(str(by_cls[cls].get(s, 0)) for s in STATUSES) + " |")
    (out / "report.md").write_text("\n".join(md) + "\n", encoding="utf-8")
    return counts


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def bridge_busy_hint() -> str:
    """McpBridge keeps its pipe connection open for its whole lifetime and, when
    Aspire reports the pipe busy, waits up to 390s rather than failing. A connect
    timeout therefore usually means another client (Claude Desktop's own bridge)
    already holds the pipe."""
    hint = ("Hint: McpBridge waits silently while Aspire's pipe is busy. If Claude Desktop "
            "(or another MCP client) is connected to Aspire, quit it fully (tray icon too) "
            "or disable its Aspire server, then retry. Also check Aspire is open with no "
            "dialog showing.")
    if os.name != "nt":
        return hint
    try:
        out = subprocess.run(["tasklist", "/FI", "IMAGENAME eq McpBridge.exe", "/FO", "CSV", "/NH"],
                             capture_output=True, text=True, timeout=10).stdout
    except (OSError, subprocess.SubprocessError):
        return hint
    pids = [line.split('","')[1] for line in out.splitlines() if line.startswith('"McpBridge.exe"')]
    if pids:
        hint += f"\n      McpBridge.exe already running (PID {', '.join(pids)}) - likely holding the pipe."
    return hint


def default_config() -> str | None:
    appdata = os.environ.get("APPDATA")
    candidates = []
    if appdata:
        candidates.append(Path(appdata) / "Claude" / "claude_desktop_config.json")
    candidates += [Path.home() / "Library/Application Support/Claude/claude_desktop_config.json",
                   Path.home() / ".config/Claude/claude_desktop_config.json"]
    for c in candidates:
        if c.exists():
            return str(c)
    return None


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_argument_group("server connection")
    g.add_argument("--config", default=None, help="MCP config file (default: Claude Desktop config if found)")
    g.add_argument("--server", default="aspire", help="server name inside --config (default: aspire)")
    g.add_argument("--target", nargs=argparse.REMAINDER,
                   help="launch the server with this command instead of --config/--server (must be last)")
    g.add_argument("--npx", default="npx")
    g.add_argument("--inspector-pkg", default="@modelcontextprotocol/inspector@latest")
    g.add_argument("--inspector-cmd", default=None,
                   help="full inspector command prefix, e.g. 'node C:/.../cli.js' (bypasses npx/cmd.exe)")
    g.add_argument("--timeout", type=float, default=120, help="seconds per discovery call")
    g.add_argument("--connect-timeout", type=float, default=120,
                   help="seconds the inspector waits to connect/initialize (0 = don't pass; "
                        "needed for inspector < 2.x, which lacks --connect-timeout)")
    g.add_argument("--lua-timeout", type=float, default=420, help="seconds per run_lua_script call")
    t = ap.add_argument_group("test selection")
    t.add_argument("--only", default=None, help="comma list of classes/functions; '(global)' = all globals")
    t.add_argument("--include-unsafe", action="store_true", help="also call file/UI/job-mutating members")
    t.add_argument("--no-writes", action="store_true", help="skip property write-back tests")
    t.add_argument("--new-job", action="store_true",
                   help="create a scratch job if none is open, force-close it (unsaved) afterwards")
    o = ap.add_argument_group("output")
    o.add_argument("--manifest", default="api_manifest.json", help="manifest cache file")
    o.add_argument("--refresh", action="store_true", help="rebuild the manifest cache")
    o.add_argument("--out", default=None, help="output folder (default: api_test_<timestamp>)")
    o.add_argument("--dump-lua", default=None, help="folder to write each generated Lua chunk to")
    o.add_argument("--plan-only", action="store_true", help="generate tests and Lua, do not run them")
    o.add_argument("--max-cmd", type=int, default=7800 if os.name == "nt" else 60000,
                   help="max command-line length per inspector call")
    o.add_argument("--jobs", type=int, default=4, help="parallel discovery calls")
    o.add_argument("--keep-harness", action="store_true", help="leave the Lua harness library registered")
    o.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args(argv)

    if not args.target and not args.config:
        args.config = default_config()
        if not args.config:
            ap.error("no --config found; pass --config PATH (with --server) or --target CMD ...")
    started = dt.datetime.now()
    t0 = time.time()
    insp = Inspector(args)
    server_desc = " ".join(args.target) if args.target else f"{args.server} ({args.config})"
    print(f"Server: {server_desc}")

    # ---- preflight ----
    try:
        tools = {tl["name"]: tl for tl in insp.list_tools()}
    except InspectorError as e:
        print(f"Could not list tools: {e}")
        if "timed out" in str(e).lower():
            print(bridge_busy_hint())
        return 2
    need = {"run_lua_script", "get_lua_api", "search_lua_api", "define_lua_library"}
    if need - tools.keys():
        print(f"Server is missing tools: {sorted(need - tools.keys())} (has {sorted(tools)})")
        return 2
    print(f"  tools: {', '.join(sorted(tools))}")

    # ---- manifest ----
    mpath = Path(args.manifest)
    if mpath.exists() and not args.refresh:
        manifest = json.loads(mpath.read_text(encoding="utf-8"))
        print(f"Using cached manifest {mpath} ({manifest.get('generated')}); --refresh to rebuild")
    else:
        manifest = discover(insp, args)
        mpath.write_text(json.dumps(manifest, indent=1), encoding="utf-8")
        print(f"  saved {mpath}")
    api = Api(manifest)
    print(f"  {len(api.classes)} classes, {len(api.functions)} global functions")

    # ---- harness + job (before planning: what is safe depends on the job) ----
    created_job = False
    exists = False
    if not args.plan_only:
        text, err = insp.call_tool("define_lua_library", name=HARNESS_NAME, source=one_line(HARNESS_LUA))
        if err:
            print(f"Could not register the Lua harness: {text}")
            return 2
        exists = bool(job_exists(insp))
        if not exists and args.new_job:
            print("No job open - creating scratch job 'mcp_api_test' ...")
            created_job = create_scratch_job(insp)
            exists = created_job
            print("  created" if created_job else "  could not create a job; job-bound tests will SKIP")
        elif not exists:
            print("No job is open: members that need one will SKIP (use --new-job for a scratch job).")

    # ---- plan ----
    only = {s.strip() for s in args.only.split(",")} if args.only else None
    builder = Builder(api, args.include_unsafe)
    tests = build_tests(api, builder, only, args.include_unsafe, not args.no_writes,
                        job_open=exists or args.plan_only)
    runnable = [x for x in tests if x.code]
    print(f"  {len(tests)} tests planned, {len(runnable)} to run in Aspire, "
          f"{len(tests) - len(runnable)} resolved without calling")
    out = Path(args.out or f"api_test_{started:%Y%m%d_%H%M%S}")
    out.mkdir(parents=True, exist_ok=True)
    (out / "instance_producers.json").write_text(
        json.dumps({k: asdict(v) for k, v in sorted(builder.prod.items())}, indent=1), encoding="utf-8")
    dump = Path(args.dump_lua) if args.dump_lua else None
    if dump:
        dump.mkdir(parents=True, exist_ok=True)
        (dump / f"{HARNESS_NAME}.lua").write_text(HARNESS_LUA, encoding="utf-8")

    chunks = make_chunks(api, insp, runnable, args.max_cmd)
    if args.plan_only:
        for i, ch in enumerate(chunks):
            s = chunk_script(api, ch)
            if dump:
                (dump / f"chunk_{i:04d}.lua").write_text(s, encoding="utf-8")
        for x in runnable:
            x.status, x.detail = "SKIP", "plan only"
        counts = write_reports(out, tests, {"started": started.isoformat(timespec="seconds"),
                                            "seconds": time.time() - t0, "inspector_calls": insp.calls,
                                            "server": server_desc, "job": "n/a",
                                            "include_unsafe": args.include_unsafe})
        print(f"Plan written to {out} ({len(chunks)} chunks)")
        return 0

    # ---- run ----
    try:
        for i, ch in enumerate(chunks, 1):
            run_chunk(api, insp, ch, dump, f"{i:04d}", args.max_cmd)
            done = sum(1 for x in runnable if x.status)
            fails = sum(1 for x in runnable if x.status in ("FAIL", "ERROR"))
            print(f"  chunk {i}/{len(chunks)}: {done}/{len(runnable)} done, {fails} failing", flush=True)
    except KeyboardInterrupt:
        print("Interrupted - writing partial report")
    finally:
        if created_job:
            try:
                close_scratch_job(insp)
                print("Closed scratch job (not saved).")
            except InspectorError as e:
                print(f"Could not close scratch job: {e}")
        if not args.keep_harness:
            try:
                insp.call_tool("remove_lua_library", name=HARNESS_NAME)
            except InspectorError:
                pass

    for x in tests:
        if not x.status:
            x.status, x.detail = "ERROR", "not run"
    meta = {"started": started.isoformat(timespec="seconds"), "seconds": time.time() - t0,
            "inspector_calls": insp.calls, "server": server_desc, "job": bool(exists),
            "include_unsafe": args.include_unsafe}
    counts = write_reports(out, tests, meta)
    print("\n" + "  ".join(f"{s}: {counts[s]}" for s in STATUSES) + f"  (total {len(tests)})")
    for x in tests:
        if x.status in ("FAIL", "ERROR"):
            print(f"  {x.status:5} {x.id:45} {x.detail[:110]}")
    print(f"\nReports: {out / 'report.md'}, results.json, results.csv")
    return 1 if counts["FAIL"] or counts["ERROR"] else 0


if __name__ == "__main__":
    sys.exit(main())