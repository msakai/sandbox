import { initZ3, isZ3Ready, solveSudoku } from './solver.js';

let initialCells = new Set();

// DOM elements
const grid = document.getElementById('grid');
const solveBtn = document.getElementById('solveBtn');
const clearBtn = document.getElementById('clearBtn');
const exampleBtn = document.getElementById('exampleBtn');
const messageEl = document.getElementById('message');

// Initialize grid
function initGrid() {
  grid.innerHTML = '';

  for (let i = 0; i < 81; i++) {
    const input = document.createElement('input');
    input.type = 'text';
    input.className = 'cell';
    input.maxLength = 1;
    input.id = `cell-${i}`;

    input.addEventListener('input', (e) => {
      const value = e.target.value;
      if (value && !/^[1-9]$/.test(value)) {
        e.target.value = '';
      }
      e.target.classList.remove('solved');
    });

    grid.appendChild(input);
  }
}

// Get current state from grid
function getGrid() {
  const gridData = [];
  for (let i = 0; i < 9; i++) {
    gridData[i] = [];
    for (let j = 0; j < 9; j++) {
      const cell = document.getElementById(`cell-${i * 9 + j}`);
      const value = cell.value;
      gridData[i][j] = value ? parseInt(value) : 0;
    }
  }
  return gridData;
}

// Set values to grid
function setGrid(gridData, markSolved = false) {
  for (let i = 0; i < 9; i++) {
    for (let j = 0; j < 9; j++) {
      const cell = document.getElementById(`cell-${i * 9 + j}`);
      const value = gridData[i][j];
      cell.value = value || '';

      if (value && markSolved && !initialCells.has(i * 9 + j)) {
        cell.classList.add('solved');
      }
    }
  }
}

// Show message
function showMessage(text, type = '') {
  messageEl.textContent = text;
  messageEl.className = 'message' + (type ? ` ${type}` : '');
}

// Show loading message with spinner
function showLoading(text) {
  messageEl.innerHTML = `<span class="spinner"></span>${text}`;
  messageEl.className = 'message loading';
}

// Set buttons enabled/disabled
function setButtonsEnabled(enabled) {
  solveBtn.disabled = !enabled || !isZ3Ready();
  clearBtn.disabled = !enabled;
  exampleBtn.disabled = !enabled;
}

// Solve Sudoku using Z3
async function handleSolve() {
  showMessage('');

  // Record initial cells
  initialCells.clear();
  for (let i = 0; i < 81; i++) {
    const cell = document.getElementById(`cell-${i}`);
    if (cell.value) {
      initialCells.add(i);
      cell.classList.add('initial');
    }
  }

  const gridData = getGrid();

  setButtonsEnabled(false);
  showLoading('Solving...');

  try {
    const solution = await solveSudoku(gridData);

    if (solution) {
      setGrid(solution, true);
      showMessage('Solved!', 'success');
    } else {
      showMessage('No solution found. Please check your input.', 'error');
    }
  } catch (error) {
    console.error('Solver error:', error);
    showMessage('An error occurred while solving.', 'error');
  } finally {
    setButtonsEnabled(true);
  }
}

// Clear grid
function handleClear() {
  showMessage('');
  initialCells.clear();

  for (let i = 0; i < 81; i++) {
    const cell = document.getElementById(`cell-${i}`);
    cell.value = '';
    cell.classList.remove('initial', 'solved');
  }
}

// Load example
function handleLoadExample() {
  handleClear();

  // Simple Sudoku puzzle
  const example = [
    [5, 3, 0, 0, 7, 0, 0, 0, 0],
    [6, 0, 0, 1, 9, 5, 0, 0, 0],
    [0, 9, 8, 0, 0, 0, 0, 6, 0],
    [8, 0, 0, 0, 6, 0, 0, 0, 3],
    [4, 0, 0, 8, 0, 3, 0, 0, 1],
    [7, 0, 0, 0, 2, 0, 0, 0, 6],
    [0, 6, 0, 0, 0, 0, 2, 8, 0],
    [0, 0, 0, 4, 1, 9, 0, 0, 5],
    [0, 0, 0, 0, 8, 0, 0, 7, 9]
  ];

  setGrid(example);
}

// Initialize Z3 on page load
async function initApp() {
  initGrid();

  // Add event listeners
  solveBtn.addEventListener('click', handleSolve);
  clearBtn.addEventListener('click', handleClear);
  exampleBtn.addEventListener('click', handleLoadExample);

  // Initialize Z3
  showLoading('Initializing Z3 solver...');
  setButtonsEnabled(false);

  try {
    await initZ3();
    showMessage('Ready to solve!', 'success');
    solveBtn.disabled = false;
  } catch (error) {
    console.error('Z3 initialization error:', error);
    showMessage('Failed to initialize Z3 solver. Please refresh the page.', 'error');
  } finally {
    clearBtn.disabled = false;
    exampleBtn.disabled = false;
  }
}

// Start the app
initApp();
