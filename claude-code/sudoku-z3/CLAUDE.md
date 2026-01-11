# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a browser-based Sudoku solver application using the Z3 theorem prover. The application is built with Vite and vanilla JavaScript.

## Development

**Setup:**
```bash
npm install
mkdir -p public
cp node_modules/z3-solver/build/z3-built.js public/
cp node_modules/z3-solver/build/z3-built.wasm public/
```

**Running the application:**
```bash
npm run dev
```

Open http://localhost:5173/ in your browser.

**Production build:**
```bash
npm run build
npm run preview
```

## Coding Guidelines

**Language:** All text content, comments, and user-facing messages should be written in English unless explicitly instructed otherwise.

## Architecture

**File structure:**
- `index.html`: Main HTML with UI and z3-built.js loader
- `src/main.js`: UI and grid management logic
- `src/solver.js`: Z3-based Sudoku solver
- `public/z3-built.js`: Z3 WASM loader (copied from node_modules)
- `public/z3-built.wasm`: Z3 WASM binary (~33MB)
- `vite.config.js`: Vite config with COOP/COEP headers and global polyfill

**Legacy files (for reference):**
- `sudoku.html`: Original MiniSat-based implementation
- `minisat.js`: MiniSat SAT solver compiled via Emscripten

**Key components in src/main.js:**

- **Grid management:**
  - `initGrid()`: Dynamically generates 81 input elements for the 9x9 grid
  - `getGrid()`: Converts DOM state to a 9x9 array representation
  - `setGrid()`: Updates DOM from array representation

- **Visual feedback:**
  - `.initial` class: User's original input (gray background)
  - `.solved` class: Auto-generated solution (green background)
  - 3x3 block boundaries use CSS nth-child selectors

**Key components in src/solver.js:**

- `initZ3()`: Initializes the Z3 solver (async, called on page load)
- `solveSudoku(grid)`: Solves the puzzle using Z3 constraints (async)

**Z3 Constraint Encoding:**
- Each cell is an `Int` variable constrained to 1-9
- `Distinct()` constraints for each row, column, and 3x3 block
- Initial values are fixed with equality constraints
- `solver.check()` returns 'sat' if solvable, then `solver.model()` extracts values

**State management:**
- `initialCells` Set tracks which cells were user-provided vs auto-solved
- No framework - direct DOM manipulation

## Technical Notes

**SharedArrayBuffer requirement:**
Z3-solver uses WebAssembly threads which require `SharedArrayBuffer`. This needs special HTTP headers:
- `Cross-Origin-Opener-Policy: same-origin`
- `Cross-Origin-Embedder-Policy: require-corp`

These are configured in `vite.config.js`.

**Z3 initialization:**
The `z3-built.js` must be loaded via a script tag before ES modules, as it sets up `window.initZ3` required by z3-solver's browser build.
