"""Convert NNG4's lean4game levels into plain Lean exercise files.

usage: python3 -I extract.py <nng4-checkout> <out-repo>

Each core world becomes NngLocal/Worlds/Wnn_<World>.lean. A level's solution is
dropped and replaced by `sorry`; its narration, tactic docs and hints survive as
comments. Support modules (MyNat definitions, game tactics) are copied with the
`Game.` prefix renamed to `NngLocal.`.
"""
import os
import pathlib
import re
import sys

SRC = pathlib.Path(sys.argv[1])
OUT = pathlib.Path(sys.argv[2])
WORLDS = ["Tutorial", "Addition", "Multiplication", "Power", "Implication",
          "AdvAddition", "LessOrEqual", "AdvMultiplication", "Algorithm"]
# Imported by Game.Metadata; the game's tactic layer every level sees.
METADATA_TACTICS = ["FromMathlib", "Induction", "Cases", "Rfl", "Rw", "Use", "Ne", "SimpAdd"]
# Not ported: GameApi/Doc need the game server; Xyzzy is an axiom-backed
# `sorry` that `lake build` would not report.
DROP_IMPORTS = {"GameApi", "Game.Metadata", "Game.Doc.Definitions", "Game.Doc.Tactics",
                "Game.Tactic.Xyzzy", "ImportGraph"}
# Imports a level module, so it cannot be a support module; inlined instead.
INLINE_MODULES = {"Game.MyNat.DecidableEq"}


def scan_toplevel(text):
    """Split into chunks starting at column-0 lines outside strings/comments."""
    starts, i, n = [], 0, len(text)
    depth, in_str, line_start = 0, False, True
    while i < n:
        c = text[i]
        if line_start and depth == 0 and not in_str and c not in " \t\n\"" and not text.startswith("--", i):
            starts.append(i)
        line_start = False
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
        elif depth > 0:
            if text.startswith("/-", i):
                depth += 1; i += 2; continue
            if text.startswith("-/", i):
                depth -= 1; i += 2; continue
        else:
            if text.startswith("/-", i):
                depth += 1; i += 2; continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j < 0 else j
                continue
            if c == '"':
                in_str = True
            elif c == "'" and i + 2 < n and text[i + 2] == "'":
                i += 3; continue  # char literal like '"'
        if c == "\n":
            line_start = True
        i += 1
    starts.append(n)
    chunks, carry = [], ""
    for a, b in zip(starts, starts[1:]):
        piece = text[a:b]
        if piece.startswith("/--"):
            carry += piece  # a doc comment belongs to the command after it
        else:
            chunks.append(carry + piece); carry = ""
    return chunks + ([carry] if carry else [])


def read_string(s, i):
    """s[i] == '"'; return (unescaped contents, index after closing quote)."""
    out, i = [], i + 1
    while s[i] != '"':
        if s[i] == "\\":
            nxt = s[i + 1]
            out.append({"n": "\n", "t": "\t", '"': '"', "\\": "\\"}.get(nxt, "\\" + nxt))
            i += 2
        else:
            out.append(s[i]); i += 1
    return "".join(out), i + 1


def first_string(chunk):
    i = chunk.find('"')
    return read_string(chunk, i)[0] if i >= 0 else ""


def find_assign(s):
    """Index of the first top-level `:=` outside strings/comments."""
    i, depth, in_str = 0, 0, False
    while i < len(s):
        if in_str:
            if s[i] == "\\": i += 2; continue
            if s[i] == '"': in_str = False
        elif s.startswith("/-", i): depth += 1; i += 2; continue
        elif depth and s.startswith("-/", i): depth -= 1; i += 2; continue
        elif depth == 0:
            if s[i] == '"': in_str = True
            elif s.startswith(":=", i): return i
        i += 1
    raise ValueError("no := in statement")


SOLUTIONS = os.environ.get("NNG_SOLUTIONS") == "1"


def solution_body(proof):
    """Upstream's reference proof with game-engine commands removed.

    Oracle mode only: compiling these against the extraction checks that the
    statements and ported tactics behave as upstream's.
    """
    body = proof[proof.index("by") + 2:]
    out, i = [], 0
    for m in re.finditer(r'\bHint\b\s*((?:\([^)]*\)\s*)*)"', body):
        if m.start() < i: continue
        out.append(body[i:m.start()])
        i = read_string(body, m.end() - 1)[1]
    out.append(body[i:])
    lines, skip_indent = [], None
    for line in "".join(out).splitlines():
        indent = len(line) - len(line.lstrip())
        if skip_indent is not None:
            if not line.strip() or indent > skip_indent: continue
            skip_indent = None
        if line.strip() == "Branch":
            skip_indent = indent; continue
        if line.strip():
            lines.append(line.replace("xyzzy", "sorry"))
    return lines


def hints(proof):
    found = []
    for m in re.finditer(r'\bHint\b\s*((?:\([^)]*\)\s*)*)"', proof):
        text, _ = read_string(proof, m.end() - 1)
        found.append(("hidden" in m.group(1), text.strip()))
    return found


def safe_comment(text):
    # Keep narration from terminating or nesting the enclosing comment.
    return text.replace("-/", "-⁠/").replace("/-", "/⁠-")


def doc_of(chunk):
    m = re.match(r"/--(.*?)-/\s*", chunk, re.S)
    return (m.group(1).strip(), chunk[m.end():]) if m else (None, chunk)


def collect_docs(paths, keyword):
    docs = {}
    for p in paths:
        for chunk in scan_toplevel(p.read_text()):
            doc, body = doc_of(chunk)
            m = re.match(rf"{keyword}\s+([^\s\"]+)", body)
            if m and doc:
                docs.setdefault(m.group(1).split(".")[-1], doc)
    return docs


def world_levels(world):
    imports = re.findall(r"^import (Game\.Levels\.\S+)", (SRC / f"Game/Levels/{world}.lean").read_text(), re.M)
    return [SRC / (imp.replace(".", "/") + ".lean") for imp in imports]


def strip_namespace(code):
    return re.sub(r"^(namespace MyNat|end MyNat|open MyNat)\s*$\n?", "", code, flags=re.M)


def convert_level(path, tactic_docs, theorem_docs):
    meta = {"new_tactics": [], "new_theorems": [], "disabled": [], "code": [], "imports": []}
    pending_prefix, pending_doc = "", None
    for chunk in scan_toplevel(path.read_text()):
        doc, body = doc_of(chunk)
        head = body.split(None, 1)[0] if body.strip() else ""
        if head == "import":
            meta["imports"] += re.findall(r"^import (\S+)", body, re.M)
        elif head == "Level":
            meta["level"] = int(body.split()[1])
        elif head == "Title":
            meta["title"] = first_string(body)
        elif head == "Introduction":
            meta["intro"] = first_string(body)
        elif head == "Conclusion":
            meta["conclusion"] = first_string(body)
        elif head in ("NewTactic", "NewHiddenTactic"):
            if head == "NewTactic":
                meta["new_tactics"] += body.split()[1:]
        elif head in ("NewTheorem", "NewHiddenTheorem"):
            meta["new_theorems"] += [t.split(".")[-1] for t in body.split()[1:]]
        elif head in ("DisabledTheorem", "DisabledTactic"):
            meta["disabled"] += [t.split(".")[-1] for t in body.split()[1:]]
        elif head == "set_option" and body.rstrip().endswith(" in"):
            pending_prefix = body.rstrip() + "\n"
        elif head == "Statement":
            meta["statement"] = (doc, pending_prefix, body)
            pending_prefix = ""
        elif head in ("World", "TheoremTab", "TacticDoc", "TheoremDoc", "DefinitionDoc",
                      "NewDefinition", "namespace", "end", "open", ""):
            pass
        elif body.startswith("/-"):
            pass  # commented-out upstream code or narration
        elif head in ("attribute", "instance", "macro", "theorem", "lemma", "def"):
            meta["code"].append(("statement" in meta, doc, body.rstrip()))
        else:
            raise ValueError(f"{path}: unhandled top-level command {head!r}")

    doc, prefix, body = meta["statement"]
    assign = find_assign(body)
    header = body[len("Statement"):assign].strip()
    proof = body[assign:]
    m = re.match(r"([A-Za-z_][\w'.]*)\b(?!\s*:=)", header)
    name = m.group(1) if m and not header.startswith(":") else None
    signature = header[m.end():].strip() if name else header

    lines = [f"/-! ## Level {meta['level']} · {meta['title']}"]
    if meta.get("intro"):
        lines += ["", safe_comment(meta["intro"].strip())]
    for tac in meta["new_tactics"]:
        lines += ["", f"### Tactic `{tac}`", "", safe_comment(tactic_docs.get(tac, "(no upstream doc)"))]
    if meta["new_theorems"]:
        lines += ["", "### New theorems", ""]
        for thm in meta["new_theorems"]:
            d = theorem_docs.get(thm)
            lines.append(f"* `{thm}`" + (f" — {safe_comment(' '.join(d.split()))}" if d else ""))
    if meta["disabled"]:
        lines += ["", "**Not allowed in this level:** " + ", ".join(f"`{d}`" for d in meta["disabled"])]
    lines += ["-/", ""]

    def emit_code(after):
        out = []
        for is_after, code_doc, code in meta["code"]:
            if is_after == after:
                out += ([f"/-- {code_doc} -/"] if code_doc else []) + [strip_namespace(code), ""]
        return out

    lines += emit_code(False)

    kw = "theorem " + name if name else "example"
    if doc:
        lines.append(f"/-- {doc} -/" if name else f"/- {doc} -/")
    sig_sep = "" if signature.startswith(":") else " "
    lines.append(f"{prefix}{kw}{sig_sep}{signature} := by")
    for hidden, text in hints(proof):
        tag = "Hint (hidden)" if hidden else "Hint"
        hint_lines = text.splitlines() or [""]
        lines.append(f"  -- {tag}: {hint_lines[0]}")
        lines += [f"  --   {l}".rstrip() for l in hint_lines[1:]]
    lines += (solution_body(proof) if SOLUTIONS else ["  sorry"]) + [""] + emit_code(True)
    if meta.get("conclusion"):
        lines += ["", "/-! **Conclusion.** " + safe_comment(meta["conclusion"].strip()) + " -/"]
    return lines + [""], meta["imports"]


def module_path(mod, root):
    return root / (mod.replace(".", "/") + ".lean")


def rename(text):
    return re.sub(r"\bGame\.", "NngLocal.", text)


def main():
    level_files = [lf for w in WORLDS for lf in world_levels(w)]
    tactic_docs = collect_docs(level_files + sorted((SRC / "Game/Tactic").glob("*.lean")), "TacticDoc")
    theorem_docs = collect_docs(level_files, "TheoremDoc")

    support = set()
    worlds_dir = OUT / "NngLocal/Worlds"
    worlds_dir.mkdir(parents=True, exist_ok=True)
    world_modules, total = [], 0
    for idx, world in enumerate(WORLDS, 1):
        stem = f"W{idx:02d}_{world}"
        wtext = (SRC / f"Game/Levels/{world}.lean").read_text()
        wtitle = wintro = ""
        for chunk in scan_toplevel(wtext):
            if chunk.startswith("Title"): wtitle = first_string(chunk)
            if chunk.startswith("Introduction"): wintro = first_string(chunk)
        body, imports, inlined = [], set(), set()
        for lf in world_levels(world):
            lines, imps = convert_level(lf, tactic_docs, theorem_docs)
            for imp in imps:
                if imp in INLINE_MODULES and imp not in inlined:
                    inlined.add(imp)
                    src = module_path(imp, SRC).read_text()
                    for sub in re.findall(r"^import (\S+)", src, re.M):
                        if not sub.startswith("Game.Levels"): imports.add(sub)
                    code = strip_namespace(re.sub(r"^import .*\n", "", src, flags=re.M)).strip()
                    body += [f"/-! Upstream support module `{imp}`, inlined here because it",
                             "depends on the previous level. -/", "", code, ""]
                elif not imp.startswith("Game.Levels") and imp not in DROP_IMPORTS:
                    imports.add(imp)
            body += lines
            total += 1
        imports |= {f"Game.Tactic.{t}" for t in METADATA_TACTICS} | {"Game.MyNat.Definition"}
        support |= imports
        prev = [f"import NngLocal.Worlds.{world_modules[-1]}"] if world_modules else []
        header = prev + [f"import {rename(i)}" for i in sorted(imports)] + [
            "", f"/-! # {wtitle or world}", "", safe_comment(wintro.strip()), "",
            f"Extracted from NNG4 `Game/Levels/{world}`. Replace each `sorry` with a proof.", "-/", "",
            "namespace MyNat", ""]
        (worlds_dir / f"{stem}.lean").write_text("\n".join(header + body + ["end MyNat", ""]))
        world_modules.append(stem)

    # Transitive closure of support modules, copied verbatim apart from the rename.
    todo, seen = list(support), set()
    while todo:
        mod = todo.pop()
        if mod in seen or not mod.startswith("Game."): continue
        seen.add(mod)
        src = module_path(mod, SRC).read_text()
        for sub in re.findall(r"^(?:public )?import (?:all )?(\S+)", src, re.M):
            if sub.startswith("Game.Levels"):
                raise ValueError(f"{mod} imports a level; add it to INLINE_MODULES")
            todo.append(sub)
        dest = module_path(rename(mod), OUT)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(rename(src))

    (OUT / "NngLocal.lean").write_text(f"import NngLocal.Worlds.{world_modules[-1]}\n")
    print(f"{total} levels; support modules: {', '.join(sorted(seen))}")


main()
