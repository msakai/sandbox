# Sudoku Solver (Z3)

A browser-based Sudoku solver using the Z3 theorem prover.

## Requirements

- Node.js >= 16

## Setup

```bash
npm install
```

After installation, copy the Z3 WASM files to the public directory:

```bash
mkdir -p public
cp node_modules/z3-solver/build/z3-built.js public/
cp node_modules/z3-solver/build/z3-built.wasm public/
```

## Usage

### Development

```bash
npm run dev
```

Open http://localhost:5173/ in your browser.

### Production Build

```bash
npm run build
npm run preview
```

## File Structure

```
sudoku-z3/
├── index.html          # Main HTML with UI and z3-built.js loader
├── package.json        # Dependencies (z3-solver, vite)
├── vite.config.js      # Vite config with COOP/COEP headers
├── public/
│   ├── z3-built.js     # Z3 WASM loader (copied from node_modules)
│   └── z3-built.wasm   # Z3 WASM binary (~33MB)
└── src/
    ├── main.js         # UI and grid management
    └── solver.js       # Sudoku solver using Z3
```

## How It Works

The Sudoku puzzle is encoded as a constraint satisfaction problem and solved using Z3:

- Each cell is an integer variable constrained to values 1-9
- Each row must have distinct values
- Each column must have distinct values
- Each 3x3 block must have distinct values
- Initial values are fixed as additional constraints

## Notes

- Z3-solver requires `SharedArrayBuffer`, which needs special HTTP headers (COOP/COEP). Vite is configured to serve these headers automatically.
- The `z3-built.js` must be loaded via a script tag before the module imports, as it sets up `window.initZ3` required by z3-solver.
