# TicTacToe

![CI](https://github.com/alok/TicTacToe/actions/workflows/ci.yml/badge.svg)

Tic-tac-toe positions, move scripts, and placement proofs in Lean 4.
This is an example of **syntax oriented programming**, a variant of language
oriented programming: give the domain its own readable syntax, then translate
that syntax into ordinary Lean values and checked proofs.

The design is inspired by [lean4-maze](https://github.com/dwrensha/lean4-maze).

## Quick start

Install [Lean through elan](https://lean-lang.org/install/); `lean-toolchain`
pins Lean 4.34.1. The library has no external dependencies.

```sh
lake build            # library, checked examples, tests, and demo executable
lake exe tictactoe    # print a board and its status
```

## Positions look like boards

```lean
import TicTacToe
open TicTacToe

example : WonBy .X (board!
  X | O | _
  _ | X | _
  O | _ | X) := by decide
```

`board!` requires exactly three rows of three cells. `X` and `O` are marks;
`_` is an empty square. It describes a position directly, including positions
that could not arise under alternating turns.

## Scripts look like moves

```lean
import TicTacToe
open TicTacToe

def rowWin : Board := moves!
  X 0 0  O 1 1
  X 0 1  O 2 2
  X 0 2

example : WonBy .X rowWin := by decide

example : rowWin = (board!
  X | X | X
  _ | O | _
  _ | _ | O) := rfl
```

Each move gives a player, row, and column; coordinates start at zero.
The elaborator applies `Board.move` to the empty board and rejects out-of-bounds
or occupied cells at the offending move. Its result is an ordinary board value.
`decide` constructs a proof that Lean's kernel checks; `rfl` checks that both
syntaxes denote the same board.

## Proofs read as placements

```lean
import TicTacToe
open TicTacToe

example : CanLeadToStatus initialBoard (.Win .X) := by
  place X 0 0
  place O 1 1
  place X 0 1
  place O 2 2
  place X 0 2
  finish_game
```

Each `place` step supplies a proof that the placement succeeds. `finish_game`
checks the resulting status. This proves that the displayed sequence reaches
an X win. A forced winning strategy would additionally need to account for
all possible opponent replies.

See [Examples.lean](TicTacToe/Examples.lean) for a complete draw as both a
script and a placement proof.

## Guarantees and boundaries

- `board!` constructs nine cells; `mkBoard` checks the size of a raw array.
- `moves!` and `place` check bounds and occupancy using the same operation.
- The classifier checks all three rows, three columns, and two diagonals.
- Placement scripts and proofs allow repeated players and moves after a win.
  They do not enforce X moving first, alternating turns, or ending a game.
- `Board` is an abbreviation for `Array Square`; its type does not enforce size
  or legal game history. `setSquare` can also clear a cell with `.empty`.
- Arbitrary literals can give both players winning lines. The classifier
  reports X's win first in that case.

This focus complements [Theoric's domain-driven tic-tac-toe article](https://theoric.com/blog/domain_driven_development/):
its example carries a game's rules through API and database boundaries;
this library explores how positions and proofs can be expressed in the
domain's own syntax inside Lean. It does not provide a server or persistence layer.

## Development

[TicTacToeTests.lean](TicTacToeTests.lean) checks every winning line for both
players, a true draw, coordinate round trips, size validation, rejected moves,
syntax equivalence, and failed proof steps. `lake build` includes these tests
and the examples by default. For a build that schedules one module at a time:

```sh
./scripts/verify.sh
```

See [CHANGELOG.md](CHANGELOG.md) for changes.
