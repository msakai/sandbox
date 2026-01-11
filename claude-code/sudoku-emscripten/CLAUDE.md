# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a single-page Sudoku solver application built with vanilla HTML, CSS, and JavaScript. The entire application is contained in `sudoku.html` with no external dependencies or build process.

## Development

**Running the application:**
```bash
open sudoku.html
```

The app runs entirely in the browser - no server or build step required.

## Coding Guidelines

**Language:** All text content, comments, and user-facing messages should be written in English unless explicitly instructed otherwise.

## Architecture

**Single-file structure:** All HTML, CSS, and JavaScript are in `sudoku.html`

**Key components:**

- **Grid management** (lines 189-239):
  - `initGrid()`: Dynamically generates 81 input elements for the 9x9 grid
  - `getGrid()`: Converts DOM state to a 9x9 array representation
  - `setGrid()`: Updates DOM from array representation

- **Solver algorithm** (lines 242-292):
  - `isValid()`: Validates number placement against Sudoku rules (row, column, 3x3 block)
  - `solve()`: Recursive backtracking algorithm that tries numbers 1-9 in empty cells

- **Visual feedback:**
  - `.initial` class: User's original input (gray background)
  - `.solved` class: Auto-generated solution (green background)
  - 3x3 block boundaries use CSS nth-child selectors (lines 74-82)

**State management:**
- `initialCells` Set tracks which cells were user-provided vs auto-solved
- No framework - direct DOM manipulation

**Algorithm:** Classic backtracking with constraint checking. Tries numbers sequentially, recurses on valid placements, backtracks on conflicts.
