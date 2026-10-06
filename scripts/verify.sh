#!/bin/sh
set -eu
cd "$(dirname "$0")/.."

# Build one module at a time; each Lean process uses at most two threads.
export LEAN_NUM_THREADS=2
for module in TicTacToe.Basic TicTacToe.Game TicTacToe.DSL TicTacToe.Tactics TicTacToe.Examples TicTacToe Main; do
  lake --wfail build "+$module:c.o"
done
lake --wfail build +TicTacToeTests
lake --wfail build
lake exe tictactoe
