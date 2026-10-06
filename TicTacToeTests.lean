import TicTacToe
import TicTacToe.Examples

open TicTacToe

namespace TicTacToeTests

-- Coordinates cover every square and reject either out-of-bounds axis.
example : ∀ i : Fin 9, (fromIdx i.val).bind (fun (r, c) => toIdx r c) = some i.val := by
  decide

example : ∀ r c : Fin 3, (toIdx r.val c.val).bind fromIdx = some (r.val, c.val) := by
  decide

example : toIdx 3 0 = none ∧ toIdx 0 3 = none ∧ fromIdx 9 = none := by decide
example : initialBoard.size = boardSize := by decide
example : mkBoard #[] = none := by decide
example : mkBoard (Array.replicate 10 .empty) = none := by decide
example : mkBoard initialBoard = some initialBoard := by decide
example : getGameStatus initialBoard = .Ongoing := by decide
example : getGameStatus (#[] : Board) = .Ongoing := by decide
example : isBoardFull (#[] : Board) = false := by decide
example : isBoardFull (Array.replicate 10 (.occupied .X)) = false := by decide

-- The eight lines are explicit fixtures, independent of the classifier.
private def winningPositions : List Board := [
  (board! X | X | X  _ | _ | _  _ | _ | _),
  (board! _ | _ | _  X | X | X  _ | _ | _),
  (board! _ | _ | _  _ | _ | _  X | X | X),
  (board! X | _ | _  X | _ | _  X | _ | _),
  (board! _ | X | _  _ | X | _  _ | X | _),
  (board! _ | _ | X  _ | _ | X  _ | _ | X),
  (board! X | _ | _  _ | X | _  _ | _ | X),
  (board! _ | _ | X  _ | X | _  X | _ | _)]

example : winningPositions.all (fun b => getGameStatus b == .Win .X) = true := by decide

private def replaceXWithO (b : Board) : Board :=
  (b.toList.map fun s => match s with
    | .empty => .empty
    | .occupied _ => .occupied .O).toArray

example : winningPositions.all (fun b => getGameStatus (replaceXWithO b) == .Win .O) = true := by
  decide

example : getGameStatus Examples.drawnBoard = .Draw := by decide
example : checkPlayerWin Examples.drawnBoard .X = false ∧
    checkPlayerWin Examples.drawnBoard .O = false := by decide

example : getGameStatus (board! X | X | X  O | O | O  _ | _ | _) = .Win .X := by
  decide

-- Low-level placement and literal elaboration agree.
example : initialBoard.move .X 0 0 = some (moves! X 0 0) := by decide
example : Board.move (moves! X 0 0) .O 0 0 = none := by decide
example : initialBoard.move .X 3 0 = none ∧ initialBoard.move .O 0 3 = none := by decide
example : Board.move #[] .X 0 0 = none := by decide
example : Board.move (moves! X 0 0) .X 0 0 = none := by decide
example : setSquare (moves! X 0 0) 0 0 .empty = some initialBoard := by decide
example : getSquare (moves! O 2 1) 2 1 = some (.occupied .O) := by decide

-- Preserve the placement DSL's contract: repeated players and post-win
-- placements are allowed. Turn rules belong to a separate game model.
example : (moves! O 0 0 O 0 1) = (board! O | O | _  _ | _ | _  _ | _ | _) := rfl
example : (moves! X 0 0 X 0 1 X 0 2 O 2 2) =
    (board! X | X | X  _ | _ | _  _ | _ | O) := rfl

-- The board borders and column headings align with the labeled rows.
#guard ppBoard Examples.rowWin ==
  "      0   1   2\n    ┌───┬───┬───┐\n  0 │ X │ X │ X │\n    ├───┼───┼───┤\n  1 │   │ O │   │\n    ├───┼───┼───┤\n  2 │   │   │ O │\n    └───┴───┴───┘"

/-- error: move (3,0) is out of bounds -/
#guard_msgs in
#check (moves! X 3 0)

/-- error: move (0,3) is out of bounds -/
#guard_msgs in
#check (moves! O 0 3)

/-- error: square (1,1) is already occupied -/
#guard_msgs in
#check (moves! X 1 1 O 1 1)

/-- error: square (2,2) is already occupied -/
#guard_msgs in
#check (moves! O 2 2 X 2 2)

-- Invalid proof steps fail without changing the proof state.
example : CanLeadToStatus initialBoard .Ongoing := by
  fail_if_success place X 3 0
  fail_if_success place O 0 3
  place X 0 0
  fail_if_success place X 0 0
  fail_if_success place O 0 0
  finish_game

example : CanLeadToStatus initialBoard (.Win .O) := by
  fail_if_success finish_game
  place O 0 0
  place O 1 1
  place O 2 2
  finish_game

end TicTacToeTests
