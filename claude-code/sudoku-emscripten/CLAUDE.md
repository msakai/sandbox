# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a single-page Sudoku solver application built with vanilla HTML, CSS, and JavaScript. The main application is contained in `sudoku.html`, which uses `minisat.js` (a SAT solver compiled to JavaScript via Emscripten) to solve puzzles.

## Development

**Running the application:**
```bash
open sudoku.html
```

The app runs entirely in the browser - no server or build step required.

## Coding Guidelines

**Language:** All text content, comments, and user-facing messages should be written in English unless explicitly instructed otherwise.

## Architecture

**File structure:**
- `sudoku.html`: Main application with HTML, CSS, and JavaScript
- `minisat.js`: MiniSat SAT solver compiled to JavaScript via Emscripten

**Key components in sudoku.html:**

- **Grid management:**
  - `initGrid()`: Dynamically generates 81 input elements for the 9x9 grid
  - `getGrid()`: Converts DOM state to a 9x9 array representation
  - `setGrid()`: Updates DOM from array representation

- **Solver integration:**
  - `gridToString()`: Converts 9x9 array to 81-character string (digits for filled cells, `.` for empty)
  - `stringToGrid()`: Converts 81-character string back to 9x9 array
  - `solveSudoku()`: Calls MiniSat solver via `Module.cwrap('sudoku_c', 'string', ['string'])`

- **Visual feedback:**
  - `.initial` class: User's original input (gray background)
  - `.solved` class: Auto-generated solution (green background)
  - 3x3 block boundaries use CSS nth-child selectors

**State management:**
- `initialCells` Set tracks which cells were user-provided vs auto-solved
- No framework - direct DOM manipulation

**Solver:** Uses MiniSat SAT solver. The Sudoku puzzle is encoded as a SAT problem and solved using the MiniSat algorithm compiled to JavaScript via Emscripten.
