import { init } from 'z3-solver';

let ctx = null;
let isInitialized = false;

export async function initZ3() {
  if (isInitialized) return;

  const { Context } = await init();
  ctx = new Context('main');
  isInitialized = true;
}

export function isZ3Ready() {
  return isInitialized;
}

export async function solveSudoku(grid) {
  if (!ctx) {
    throw new Error('Z3 is not initialized. Call initZ3() first.');
  }

  const { Solver, Int, And, Distinct } = ctx;
  const solver = new Solver();

  // Create 9x9 integer variables
  const cells = [];
  for (let i = 0; i < 9; i++) {
    cells[i] = [];
    for (let j = 0; j < 9; j++) {
      cells[i][j] = Int.const(`cell_${i}_${j}`);
    }
  }

  // Constraint: each cell is between 1 and 9
  for (let i = 0; i < 9; i++) {
    for (let j = 0; j < 9; j++) {
      solver.add(And(cells[i][j].ge(1), cells[i][j].le(9)));
    }
  }

  // Constraint: each row has distinct values
  for (let i = 0; i < 9; i++) {
    solver.add(Distinct(...cells[i]));
  }

  // Constraint: each column has distinct values
  for (let j = 0; j < 9; j++) {
    const col = cells.map(row => row[j]);
    solver.add(Distinct(...col));
  }

  // Constraint: each 3x3 block has distinct values
  for (let bi = 0; bi < 3; bi++) {
    for (let bj = 0; bj < 3; bj++) {
      const block = [];
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          block.push(cells[bi * 3 + i][bj * 3 + j]);
        }
      }
      solver.add(Distinct(...block));
    }
  }

  // Constraint: initial values from the puzzle
  for (let i = 0; i < 9; i++) {
    for (let j = 0; j < 9; j++) {
      if (grid[i][j] !== 0) {
        solver.add(cells[i][j].eq(grid[i][j]));
      }
    }
  }

  // Solve
  const result = await solver.check();

  if (result === 'sat') {
    const model = solver.model();
    const solution = [];

    for (let i = 0; i < 9; i++) {
      solution[i] = [];
      for (let j = 0; j < 9; j++) {
        const value = model.eval(cells[i][j]);
        solution[i][j] = Number(value.toString());
      }
    }

    return solution;
  }

  return null; // No solution found
}
