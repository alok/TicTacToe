import TicTacToe.Game

open Lean Elab Term

namespace TicTacToe

/-! # Move-script syntax

`moves! X 0 0 O 1 1` places marks in order, starting from `initialBoard`.
Coordinates are literal, zero-based row and column numbers. Bounds and
occupancy are checked during elaboration using `Board.move`.

Like the underlying placement operation, scripts allow repeated players
and placements after a win. They describe positions, not complete game rules.
-/

declare_syntax_cat tttMove
syntax "X" num num : tttMove
syntax "O" num num : tttMove

/-- Construct a board from one or more placements, rejecting invalid cells
at the offending move's source location. -/
syntax (name := movesSyntax) "moves! " tttMove+ : term

private def applyMove (board : Board) (player : Player) (row col : Nat)
    (stx : Syntax) : TermElabM Board := do
  if (toIdx row col).isNone then
    throwErrorAt stx "move ({row},{col}) is out of bounds"
  match board.move player row col with
  | some next => pure next
  | none => throwErrorAt stx "square ({row},{col}) is already occupied"

elab_rules : term
  | `(moves! $ms:tttMove*) => do
    let mut board := initialBoard
    for m in ms do
      match m with
      | `(tttMove| X $r:num $c:num) =>
        board ← applyMove board .X r.getNat c.getNat m
      | `(tttMove| O $r:num $c:num) =>
        board ← applyMove board .O r.getNat c.getNat m
      | _ => throwErrorAt m "unsupported move syntax"
    let cells ← board.mapM fun square =>
      match square with
      | .empty => `(Square.empty)
      | .occupied .X => `(Square.occupied Player.X)
      | .occupied .O => `(Square.occupied Player.O)
    elabTerm (← `((#[$cells,*] : TicTacToe.Board))) none

end TicTacToe
