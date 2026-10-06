import TicTacToe.Game

namespace TicTacToe

/-! # Placement proofs

The tactics build a witness that a sequence of in-bounds placements on empty
squares reaches a requested status. They use the same `Board.move` operation
as `moves!`. Reachability allows either player at each step; it does not assert
a winning strategy against an opponent or enforce alternating turns.
-/

/-- A placement succeeds and produces `nextBoard`. -/
def IsValidMove (board : Board) (p : Player) (row col : Nat) (nextBoard : Board) : Prop :=
  board.move p row col = some nextBoard

instance (board : Board) (p : Player) (row col : Nat) (nextBoard : Board) :
    Decidable (IsValidMove board p row col nextBoard) :=
  inferInstanceAs (Decidable (board.move p row col = some nextBoard))

/-- Some sequence of valid placements reaches `targetStatus` from `board`. -/
inductive CanLeadToStatus : Board → GameStatus → Prop where
  | IsFinalStatus {board : Board} (targetStatus : GameStatus) :
      getGameStatus board = targetStatus → CanLeadToStatus board targetStatus
  | ViaMove {board : Board} (player : Player) (row col : Nat)
      (nextBoard : Board) (targetStatus : GameStatus) :
      IsValidMove board player row col nextBoard →
      CanLeadToStatus nextBoard targetStatus → CanLeadToStatus board targetStatus

/-- A win for `p` is reachable through placements. This is an existence claim
about a sequence, not a claim that `p` can force a win against all replies. -/
abbrev Winnable (board : Board) (p : Player) : Prop :=
  CanLeadToStatus board (.Win p)

/-- Compute the next position while leaving its validity as a proof obligation.
The fixed fallback keeps goals from duplicating the previous board at each
step; `valid` rules out a failed placement, so that fallback is never used. -/
theorem CanLeadToStatus.place {board : Board} {targetStatus : GameStatus}
    (p : Player) (row col : Nat)
    (valid : IsValidMove board p row col ((board.move p row col).getD initialBoard))
    (rest : CanLeadToStatus ((board.move p row col).getD initialBoard) targetStatus) :
    CanLeadToStatus board targetStatus :=
  .ViaMove p row col _ targetStatus valid rest

/-- Place X at a literal row and column, proving that the cell is available. -/
macro "place " "X " row:num col:num : tactic =>
  `(tactic| first
    | refine TicTacToe.CanLeadToStatus.place TicTacToe.Player.X $row $col ?_ ?_
      · decide
    | fail "cannot place X: coordinate is out of bounds or occupied")

/-- Place O at a literal row and column, proving that the cell is available. -/
macro "place " "O " row:num col:num : tactic =>
  `(tactic| first
    | refine TicTacToe.CanLeadToStatus.place TicTacToe.Player.O $row $col ?_ ?_
      · decide
    | fail "cannot place O: coordinate is out of bounds or occupied")

/-- Finish a reachability proof by checking the current board's status. -/
macro "finish_game" : tactic =>
  `(tactic| exact TicTacToe.CanLeadToStatus.IsFinalStatus _ (by decide))

end TicTacToe
