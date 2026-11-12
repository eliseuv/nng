"""Show which levels are solved.

usage: python3 -I tools/progress.py

A level is unsolved while its section (from one `## Level` heading to the next)
still contains a `sorry` outside comments. Reads the world files only; it does
not run Lean, so a proof that fails to compile still counts as solved.
"""
import pathlib
import re

WORLDS = pathlib.Path(__file__).resolve().parent.parent / "NngLocal" / "Worlds"
LEVEL_HEADING = re.compile(r"^/-! ## Level (\d+) · (.*)$", re.M)


def strip_comments(text):
    """Remove (nested) block comments and line comments, keeping newlines."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else ""); i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def levels(path):
    """Yield (heading, unsolved) per level; headings are matched on raw text
    because they live inside block comments."""
    text = path.read_text()
    marks = list(LEVEL_HEADING.finditer(text))
    for k, m in enumerate(marks):
        end = marks[k + 1].start() if k + 1 < len(marks) else len(text)
        # Start after the heading line: the heading's own comment is still open.
        body = text[m.end():end]
        # The heading opens a block comment that closes before the code.
        close = body.find("-/")
        code = strip_comments(body[close + 2:]) if close >= 0 else ""
        yield f"{m.group(1)} · {m.group(2)}", bool(re.search(r"\bsorry\b", code))


def main():
    total = solved = 0
    for path in sorted(WORLDS.glob("W*.lean")):
        results = list(levels(path))
        done = sum(not unsolved for _, unsolved in results)
        total += len(results); solved += done
        print(f"{path.stem}  {done}/{len(results)}")
        for heading, unsolved in results:
            print(f"  [{' ' if unsolved else 'x'}] {heading}")
    print(f"\ntotal {solved}/{total}")


main()
