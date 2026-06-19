# Converting Technical PDFs to Markdown — Techniques & Lessons

A practical playbook distilled from converting *The SMT-LIB Standard v2.7* (a
112-page reference manual full of BNF grammars, S-expression code, inference
rules, multi-column figures, and a garbled table of contents) from PDF to clean
Markdown. Use this when asked to do a similar conversion.

The core problem: **no single tool gets everything right.** The winning move is
to combine tools, each for what it does best, and to script the mechanical parts.

---

## 1. Tools and what each is good/bad at

| Tool | Good for | Fails at |
|------|----------|----------|
| **docling** (`uvx docling file.pdf`) | Prose paragraph reflow, heading detection, table structure, rasterizing vector figures | Collapses every code block to ONE line; adds spaces inside `⟨…⟩`; embeds images as base64 data URIs; misorders/mislabels figures & chapter titles; fragments numbered lists |
| **`pdftotext -layout`** (poppler) | Preserves line breaks & indentation (code, grammar, tables); good for reconstructing structure | Inserts spurious spaces from monospace/letterspaced fonts (`#x0`→`# x0`); reads multi-column layouts **row-wise**, interleaving columns |
| **plain `pdftotext`** | Logical reading order; reveals true column/grid reading order | Loses code line structure |
| **`pdfimages -list`** | Detect whether the PDF has real raster images | — (vector figures show nothing) |
| **`pdftoppm -r DPI -x -y -W -H -png`** | Render a page (or a cropped region) to PNG for math that can't be represented as text | Crop coords are trial-and-error |

Also have: Python (for scripted transforms), and — if available — the document's
**source (e.g., a TeX repo of an earlier version)** for cross-checking exact
notation and structure.

**Recommended baseline:** start from the docling Markdown for prose/headings, then
fix code blocks, images, headings, and structure as below. Keep the original
docling output around as `*_docling.md` for diffing.

---

## 2. The key technique: hybrid code-block reconstruction

docling preserves **correct token spacing** but loses line breaks.
`pdftotext -layout` preserves **correct line breaks** but corrupts spacing.
Combine them: take docling's characters/spacing, re-insert layout's line breaks.

Algorithm (per code block, both lists are in document order):

1. Build a whitespace-stripped char stream of the entire `-layout` text, keeping a
   map from each stripped char back to its original offset.
2. For each docling code block, strip its whitespace too and **find that string as
   a substring** of the layout stream (advance a cursor so blocks match in order).
3. The matched span maps back to a contiguous region of layout lines → that region
   has the **correct line breaks and indentation**.
4. Reconstruct: walk docling's (correctly-spaced) characters and insert a newline
   wherever the layout region had one (align by non-whitespace count). Dedent the
   block by its common minimum indent; keep relative indentation.

Why it works: the whitespace-stripped content is identical in both, so matching is
robust to all the spacing differences. ~85–90% of blocks match cleanly this way.

**Blocks that fail to match** are the interesting ones — usually multi-column
layouts or heavy math where the two tools disagree on glyphs/order. Handle those
manually (see §4, §6).

### Spacing cleanup rules (apply to reconstructed code)
- Remove space after `(` and `⟨`; remove space before `)` and `⟩`.
- Remove space between `⟩`/`)` and a following postfix `∗`/`+` (BNF repetition).
- Collapse 2+ *internal* spaces to one (kills alignment padding) — never touch
  leading indentation.
- Unescape docling's `\_ \* \# \& \< \> \$ \` …` and HTML entities (`&gt; &lt; &amp;`)
  inside code.

Result: `⟨ spec_constant ⟩ ::= … ( ⟨ s_expr ⟩ ∗ )` → `⟨spec_constant⟩ ::= … (⟨s_expr⟩∗)`.

---

## 3. Letterspacing & hyphen artifacts

Typewriter/monospace fonts make BOTH extractors insert spaces *within* tokens:

- `#x0` → `# x0`, `|sym|` → `| sym |`, `:keyword` → `: keyword`. The §2 bracket
  rules + a `#`/`:`/`|` cleanup handle most; prefer docling's version for short
  example lines (docling usually keeps these tight).
- **Hyphenated identifiers split**: `declare-datatype` → `declare -datatype`,
  `const-array` → `const - array`, `:left-assoc` → `:left -assoc`.
- **Ambiguity that no single rule solves**: `(- Int Int)` (the minus *function* —
  space required) vs `const-array` (hyphenated name — no space).

Strategy:
- Apply a **curated allow-list** of known command/keyword names for de-hyphenation
  (`declare-*`, `define-*`, `check-sat`, `get-*`, `set-*`, `:left-assoc`,
  `:right-assoc`, `:produce-*`, `const-array`, …): replace `word -word`/`word- word`
  → `word-word` only for those.
- Then **scan for residuals** with `grep -nE '[A-Za-z] -[A-Za-z]'` inside code
  blocks and fix case-by-case.
- For genuinely ambiguous cases, **check the PDF prose** — the same identifier is
  usually typeset correctly somewhere in running text (`pdftotext -f P -l P`).

### Split ligatures
`fl`/`fi` ligatures often break: `flag`→`fl ag`, `first`→`fi rst`, `flat`→`fl at`.
Find with `grep -oE '[A-Za-z] f[il] [a-z]+'`, fix the unambiguous ones globally.

---

## 4. Multi-column layouts (the silent trap)

When a figure is laid out in two columns (a script "over two columns", a legend, a
two-column abstract syntax):
- `pdftotext -layout` keeps both columns on the same physical line (interleaved).
- docling may read column-by-column, or interleave differently.
- These are exactly the blocks where whitespace-stripped matching **fails**.

Reconstruct **manually** by reading each column top-to-bottom in the figure's
intended order (often: entire left column, then entire right column). Render the
page with `pdftoppm` to see the true layout if unsure.

---

## 5. Images

1. Run `pdfimages -list` first. If empty, the "figures" are vector graphics that
   docling has rasterized into **base64 data URIs** — extract those to files:
   decode each `data:image/png;base64,…`, write `*.png` into a sibling
   `<doc>_images/` directory, and replace the embed with `![alt](path)`.
2. **Triage** each extracted image:
   - Genuine diagrams/figures → keep as image files.
   - **Decorative chapter-title graphics** ("CHAPTER 4", "APPENDIX B") → convert to
     heading *text* (they're redundant with the following title). Delete the image.
3. **Math that Markdown can't represent** (inference-rule fractions, multi-case
   denotational definitions, anything docling marks `<!-- formula-not-decoded -->`)
   → render the PDF region to an image:
   ```
   pdftoppm -f P -l P -r 200 -x X -y Y -W W -H H -png file.pdf out
   ```
   `-x/-y/-W/-H` are device pixels at the chosen DPI (200 is a good default; an
   8.5×11in page → 1700×2200 px). Iterate: render, view the PNG, adjust the crop.
   Keep the heading/caption as text; crop just the equation block.
   - Before imaging, check it isn't actually decodable — e.g. a BNF "grammar"
     docling flagged as a formula is better rendered as a text code block.

### Gotchas
- **Page-number offset**: `pdftoppm -f N` (PDF page) often ≠ document page N
  (front matter). Render once and read the running header to calibrate.
- **`pdftoppm` output filename** zero-pads: `-f 88` → `out-088.png`.
- Render a full page first to find a feature's Y, then crop tight.

---

## 6. Structure repair (docling reordering)

docling floats title pages and figures to the wrong place. Common repairs:
- **Chapter/appendix titles land mid-content** (e.g. a chapter title dropped into
  the middle of a changelog; an appendix title placed *after* its first
  subsections). Relocate them to the front of their section.
- **Figures placed at page tops** get inserted mid-paragraph or mid-definition.
  Move the figure out and **rejoin the split sentence** (the two halves are usually
  adjacent in the source text, e.g. "…the SMT-LIB logic" + "language is a family…").
- **Numbered lists/definitions fragmented** into code blocks + stray lines (e.g.
  `Definition 1` split into `1.`, `2. … ar(s) =`, `0 is a sort;`, a stray `∗`).
  Reconstruct the clean list from `pdftotext`.
- Drop stray combining characters left by failed glyph decoding (e.g. a lone `̸`).

---

## 7. Heading hierarchy

docling often emits everything at one level (`##`). Reassign by logical depth:

| Level | Use |
|-------|-----|
| `#` | document title |
| `##` | Parts; front matter (Preface, Acknowledgments, Contents, List of Figures) |
| `###` | Chapters; Appendices; Bibliography; Index |
| `####` | Sections `N.M`; appendix subsections |
| `#####` | Subsections `N.M.K`; named sub-blocks |
| `######` | deepest named blocks |

- **Auto-derive** numbered headings from the dotted number (`N.M.K` → count dots).
- **Map named headings explicitly** (chapter titles, appendix subsections).
- **Demote false headings** docling invented: title-page metadata (`Release:`,
  `Copyright …`), figure/table captions, `Definition`/`Remark` labels, glossary-
  style item labels (`:flag support: required`). Turn them into bold text or
  normal prose.

Do bulk level changes with a script (regex on heading lines + an explicit
name→level map); do relocations/merges with targeted edits.

---

## 8. TOC and reference tables

A dot-leader Table of Contents becomes table chaos through any extractor. Don't
patch it — **rewrite it**:
1. `pdftotext -layout` the contents pages → clean section list + page numbers.
2. Emit a nested Markdown list (`- **Part** — page`, indented by depth).

Same for *List of Figures* → a clean `| Figure | Title | Page |` table.

---

## 9. Workflow & verification

- **Script the mechanical parts.** For repeated/large transforms, write a Python
  script that operates on line content or anchor strings, rather than many fragile
  literal edits. Use whitespace-stripped matching and line-range replacement.
- **Cross-check with source** if available (e.g. an older TeX edition): confirms
  exact notation (`pdec` vs `fdec`, `::=` vs `:=`) and intended structure. But the
  target-version PDF is authoritative for version-specific content.
- **Final validation checklist:**
  - `grep -c '^```'` is even (balanced fences).
  - zero remaining `<!-- formula-not-decoded -->` (or all intentionally imaged).
  - every `![](…)` path resolves to a file on disk.
  - no leftover scaffolding markers (`%%%…%%%`, `NOT MATCHED`, stray combining chars).
  - heading outline (`grep -nE '^#{1,6} '`) reads as a sensible tree.
- **Environment note:** zsh `noclobber` makes `cat > file` fail if the file exists;
  use `cat >|` or `rm` first when regenerating helper scripts.

---

## 10. Quick order of operations

1. `pdfimages -list`; generate `pdftotext -layout` and (optionally) plain text.
2. Extract embedded images → files; triage decorative vs real.
3. Reconstruct code blocks via the §2 hybrid; apply §3 spacing/hyphen/ligature fixes.
4. Manually fix the blocks that failed to match (§4 multi-column, §6 fragments).
5. Image the irreducible math (§5).
6. Fix heading hierarchy (§7) and demote false headings.
7. Rewrite TOC / List of Figures (§8).
8. Repair structural reordering (§6); fix HTML entities & ligatures globally.
9. Run the §9 validation checklist; clean up temp files.
