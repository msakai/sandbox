---
name: pdf-to-markdown
description: >-
  Convert technical PDFs (specs, reference manuals, papers with BNF grammars,
  code/S-expressions, inference rules, multi-column figures) into clean Markdown.
  Use when asked to turn a PDF into .md, clean up docling/pdftotext output, fix
  mangled code blocks, extract embedded figures, rebuild a garbled table of
  contents, or fix heading hierarchy from a converted PDF.
---

# PDF → Markdown conversion

No single tool gets a technical PDF right. Combine them, each for its strength,
and script the mechanical parts. **Read `reference.md` in this skill for the full
playbook**; this file is the quick workflow.

## Tools (check availability first)
- `uvx docling FILE.pdf` — prose reflow, headings, tables; rasterizes vector figures.
  *But* collapses code blocks to one line and embeds images as base64.
- `pdftotext -layout FILE.pdf OUT.txt` — preserves line breaks & indentation.
  *But* adds letterspacing spaces and reads columns row-wise.
- `pdftotext FILE.pdf OUT.txt` — logical reading order (use to check column order).
- `pdfimages -list FILE.pdf` — is there any real raster image? (vector figs show none)
- `pdftoppm -r 200 -x X -y Y -W W -H H -png FILE.pdf out` — render a page/region to PNG.
- Python — for scripted transforms.

## Workflow
1. **Baseline:** start from docling Markdown (keep the original as `*_docling.md`
   for diffing). Generate `pdftotext -layout` too.
2. **Code blocks (the key step):** run
   `scripts/reconstruct_code_blocks.py DOCLING.md LAYOUT.txt -o OUT.md --clean`.
   It matches each docling block to the layout region (whitespace-stripped) and
   restores layout line breaks with docling spacing. ~85–90% match automatically;
   it reports UNMATCHED blocks on stderr — fix those by hand (usually multi-column
   figures or glyph mismatches). See reference.md §2–§4.
3. **Images:** `pdfimages -list` first. Extract docling's base64 data-URIs to a
   sibling `<doc>_images/` dir. Triage: real figures → keep; decorative chapter-
   title graphics ("CHAPTER 4") → heading text. Irreducible math (inference rules,
   multi-case definitions docling marks `<!-- formula-not-decoded -->`) → crop a
   PNG with `pdftoppm`. Reference.md §5.
4. **Headings:** reassign one-level-`##` output to a real tree (`#` title, `##`
   parts/front-matter, `###` chapters/appendices, `####`/`#####` sections; auto-
   derive from `N.M.K` numbering). Demote false headings (captions, Definition/
   Remark labels, title-page metadata). Reference.md §7.
5. **Structure repair:** relocate chapter/appendix titles & figures docling floated
   to the wrong place; rejoin sentences split by an inserted figure; reconstruct
   fragmented numbered lists. Reference.md §6.
6. **TOC / List of Figures:** rewrite from the clean `pdftotext -layout` of the
   contents pages into a nested list / table. Reference.md §8.
7. **Global cleanups:** split ligatures (`fl ag`→`flag`), HTML entities
   (`&gt;`→`>`), letterspaced hyphens (`declare -datatype`). Reference.md §3.
8. **Validate:** balanced code fences; zero remaining `formula-not-decoded`; every
   `![](…)` resolves; sane heading outline. Reference.md §9.

## Notes
- `pdftoppm -f N` (PDF page) often ≠ document page N (front-matter offset);
  calibrate by reading a rendered page header. Output is zero-padded (`out-088.png`).
- Cross-check exact notation against a source repo (e.g. an older TeX edition) when
  available; the target-version PDF stays authoritative for version-specific text.
- Prefer scripts (anchor/line-range based) over many fragile literal edits for
  large or repetitive regions.
