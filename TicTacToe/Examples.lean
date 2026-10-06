import TicTacToe.DSL
import TicTacToe.Tactics

namespace TicTacToe.Examples

/-! # Syntax oriented programming

Positions look like boards, placement scripts look like moves, and
reachability proofs read as a sequence of placements.
-/

def rowWin : Board := moves!
  X 0 0  O 1 1
  X 0 1  O 2 2
  X 0 2

example : rowWin = (board!
  X | X | X
  _ | O | _
  _ | _ | O) := rfl

example : WonBy .X rowWin := by decide

example : CanLeadToStatus initialBoard (.Win .X) := by
  place X 0 0
  place O 1 1
  place X 0 1
  place O 2 2
  place X 0 2
  finish_game

def drawnBoard : Board := moves!
  X 0 0  O 0 1  X 0 2
  O 1 1  X 1 0  O 1 2
  X 2 1  O 2 0  X 2 2

example : drawnBoard = (board!
  X | O | X
  X | O | O
  O | X | X) := rfl

example : getGameStatus drawnBoard = .Draw := by decide

example : CanLeadToStatus initialBoard .Draw := by
  place X 0 0
  place O 0 1
  place X 0 2
  place O 1 1
  place X 1 0
  place O 1 2
  place X 2 1
  place O 2 0
  place X 2 2
  finish_game

end TicTacToe.Examples
