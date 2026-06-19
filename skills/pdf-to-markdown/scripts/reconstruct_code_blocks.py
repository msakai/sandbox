#!/usr/bin/env python3
"""
Hybrid code-block reconstruction for PDF -> Markdown conversion.

The problem: docling collapses each fenced code block to (nearly) one line but
keeps correct token spacing; `pdftotext -layout` keeps the original line breaks
and indentation but corrupts spacing (letterspacing, alignment padding).

This script matches each docling code block to its region in the layout text by
*whitespace-stripped substring matching*, then rebuilds the block using docling's
characters/spacing with the layout's line breaks and relative indentation.

Usage:
    pdftotext -layout INPUT.pdf LAYOUT.txt
    reconstruct_code_blocks.py DOCLING.md LAYOUT.txt -o OUT.md [--clean]

- Reads fenced ``` blocks from DOCLING.md in document order.
- Blocks that cannot be matched (typically multi-column figures, or glyph
  mismatches between the two extractors) are LEFT UNCHANGED and reported on
  stderr so you can fix them by hand.
- --clean additionally applies BNF spacing tidy-ups (brackets / postfix * +).

This is a best-effort helper, not a magic wand: always eyeball the result and
handle the reported UNMATCHED blocks manually.
"""
import sys
import re
import argparse


def nonws(s):
    return ''.join(ch for ch in s if not ch.isspace())


def build_layout_index(layout):
    """Concatenation of all non-whitespace chars of `layout`, plus a list mapping
    each such char back to its offset in `layout`."""
    chars, positions = [], []
    for i, ch in enumerate(layout):
        if not ch.isspace():
            chars.append(ch)
            positions.append(i)
    return ''.join(chars), positions


def line_bounds(layout):
    """(start, end) offsets per line (end exclusive, newline not included)."""
    bounds, start = [], 0
    for i, ch in enumerate(layout):
        if ch == '\n':
            bounds.append((start, i))
            start = i + 1
    bounds.append((start, len(layout)))
    return bounds


def find_line(bounds, pos):
    lo, hi = 0, len(bounds) - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if bounds[mid][1] < pos:
            lo = mid + 1
        else:
            hi = mid
    return lo


def indent_of(line):
    return len(line) - len(line.lstrip(' '))


def reconstruct_block(content, layout, lstripped, lpos, bounds, cursor):
    """Return (rebuilt_lines, new_cursor) or (None, cursor) if unmatched."""
    d_stripped = nonws(content)
    if not d_stripped:
        return None, cursor
    s = lstripped.find(d_stripped, cursor)
    if s < 0:                       # order may drift; retry from the top
        s = lstripped.find(d_stripped)
        if s < 0:
            return None, cursor
    e = s + len(d_stripped)         # exclusive, in stripped space
    first = find_line(bounds, lpos[s])
    last = find_line(bounds, lpos[e - 1])
    region = [layout[bounds[i][0]:bounds[i][1]] for i in range(first, last + 1)]
    if d_stripped not in nonws(''.join(region)):
        return None, cursor

    counts = [len(nonws(l)) for l in region]
    nonempty = [indent_of(l) for l in region if l.strip()]
    base = min(nonempty) if nonempty else 0

    flat = ' '.join(content.split('\n'))   # layout is the authority on breaks
    out, di, N = [], 0, len(flat)
    for li, c in enumerate(counts):
        if c == 0:
            out.append('')                 # keep blank lines inside the block
            continue
        while di < N and flat[di] == ' ':  # drop space at a break boundary
            di += 1
        seg, consumed = [], 0
        while di < N and consumed < c:
            ch = flat[di]
            seg.append(ch)
            if not ch.isspace():
                consumed += 1
            di += 1
        indent = ' ' * max(0, indent_of(region[li]) - base)
        out.append((indent + ''.join(seg)).rstrip())
    return out, e


CLEAN_RULES = [
    (re.compile(r'([(⟨])\s+'), r'\1'),                 # "( " / "⟨ " -> "("/"⟨"
    (re.compile(r'\s+([)⟩])'), r'\1'),                 # " )" / " ⟩" -> ")"/"⟩"
    (re.compile(r'([)⟩])\s+([*+∗])'), r'\1\2'),   # ") ∗" -> ")∗"
    (re.compile(r'(?<=\S)  +(?=\S)'), ' '),                 # collapse inner runs
]


def clean_line(line):
    for rx, rep in CLEAN_RULES:
        line = rx.sub(rep, line)
    return line


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('docling', help='docling-converted Markdown')
    ap.add_argument('layout', help='output of `pdftotext -layout`')
    ap.add_argument('-o', '--output', help='write here (default: stdout)')
    ap.add_argument('--clean', action='store_true', help='also tidy BNF spacing')
    args = ap.parse_args()

    doc = open(args.docling, encoding='utf-8').read().split('\n')
    layout = open(args.layout, encoding='utf-8').read()
    lstripped, lpos = build_layout_index(layout)
    bounds = line_bounds(layout)

    out, cursor, matched, unmatched, i = [], 0, 0, 0, 0
    while i < len(doc):
        if doc[i].startswith('```'):
            j = i + 1
            while j < len(doc) and not doc[j].startswith('```'):
                j += 1
            content = '\n'.join(doc[i + 1:j])
            rebuilt, cursor = reconstruct_block(
                content, layout, lstripped, lpos, bounds, cursor)
            out.append(doc[i])                       # opening fence
            if rebuilt is None:
                out.extend(doc[i + 1:j])
                unmatched += 1
                preview = content.replace('\n', ' ')[:80]
                sys.stderr.write(f'UNMATCHED block @ line {i + 1}: {preview}\n')
            else:
                out.extend([clean_line(l) for l in rebuilt] if args.clean else rebuilt)
                matched += 1
            if j < len(doc):
                out.append(doc[j])                   # closing fence
            i = j + 1
        else:
            out.append(doc[i])
            i += 1

    text = '\n'.join(out)
    if args.output:
        open(args.output, 'w', encoding='utf-8').write(text)
    else:
        sys.stdout.write(text)
    sys.stderr.write(f'\nDone: {matched} matched, {unmatched} unmatched.\n')


if __name__ == '__main__':
    main()
