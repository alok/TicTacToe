import Lean.Elab
import Lean.Elab.Term
import Lean.Meta
import Lean.Parser

namespace TicTacToe

/-- Represents a player in Tic Tac Toe. -/
inductive Player | X | O deriving Repr, BEq, Inhabited

instance : ToString Player where
  toString
    | .X => "X"
    | .O => "O"

/-- Represents a single square on the Tic Tac Toe board. -/
inductive Square
  | empty
  | occupied (player : Player)
  deriving Repr, BEq, Inhabited

instance : ToString Square where
  toString
    | .empty       => " "
    | .occupied p  => toString p

@[simp] def boardSize : Nat := 9

/-- Convert a 2-d coordinate to the underlying array index. Returns `none` if out of bounds. -/
@[simp] def toIdx (row col : Nat) : Option Nat :=
  if _h₁ : row < 3 then
    if _h₂ : col < 3 then
      some (row * 3 + col)
    else none
  else none

/-- Convert an array index back to a 2-d coordinate. Returns `none` if the index is out of range. -/
@[simp] def fromIdx (idx : Nat) : Option (Nat × Nat) :=
  if _h : idx < boardSize then
    some (idx / 3, idx % 3)
  else none

/-- The board is a flat `Array` of exactly nine `Square`s. -/
abbrev Board := Array Square

/-- Smart-constructor ensuring the array has exactly nine elements. -/
@[inline] def mkBoard (squares : Array Square) : Option Board :=
  if _h : squares.size = boardSize then some squares else none

/-- The empty board. -/
def initialBoard : Board :=
  Array.replicate boardSize Square.empty

@[simp] def getSquare (b : Board) (row col : Nat) : Option Square := do
  let idx ← toIdx row col
  b[idx]?

/-- Set a square on the board. Fails if the coordinate is out of bounds or already occupied. -/
@[simp] def setSquare (b : Board) (row col : Nat) (s : Square) : Option Board :=
  match toIdx row col with
  | none      => none
  | some idx  =>
    match b[idx]? with
    | none          => none
    | some current  =>
      if current == Square.empty || s == Square.empty then
        some (b.setIfInBounds idx s)
      else none

/-- Render `b` nicely in a UTF-8 box-drawing style **with row/column indices**. -/
def ppBoard (b : Board) : String :=
  let get (r c : Nat) : String :=
    -- Safely fetch the square, defaulting to empty (this should never trigger in-bounds)
    toString <| b.getD ((toIdx r c).getD 0) Square.empty

  -- Pretty print a single cell with surrounding spaces for uniform width.
  let cell (r c : Nat) : String := s!" {get r c} "

  -- A full row prefixed with the row index.
  let row (r : Nat) : String :=
    s!"  {r} │{cell r 0}│{cell r 1}│{cell r 2}│"

  let header := "    0   1   2\n"
  let top    := "  ┌───┬───┬───┐\n"
  let sep    := "  ├───┼───┼───┤\n"
  let bottom := "  └───┴───┴───┘"
  header ++ top ++ row 0 ++ "\n" ++ sep ++ row 1 ++ "\n" ++ sep ++ row 2 ++ "\n" ++ bottom

instance : Repr Board where
  reprPrec b _ := ppBoard b

instance : ToString Board where
  toString := ppBoard

/-- Attempt to place `p` at `(row,col)` on `b`. -/
@[simp] def Board.move (b : Board) (p : Player) (row col : Nat) : Option Board :=
  setSquare b row col (.occupied p)

/-- The possible outcomes of a finished game. -/
inductive GameStatus
  | Win (p : Player)
  | Draw
  | Ongoing
  deriving Repr, BEq

def gameStatusToString : GameStatus → String
| .Win p   => s!"Win {p}"
| .Draw    => "Draw"
| .Ongoing => "Ongoing"

instance : ToString GameStatus where
  toString := gameStatusToString

/-- `checkPlayerWin b p` is `true` iff `p` has a three-in-a-row on `b`. -/
@[simp] def checkPlayerWin (b : Board) (p : Player) : Bool :=
  let s := Square.occupied p
  let row? r := [0,1,2].all fun c => getSquare b r c == some s
  let col? c := [0,1,2].all fun r => getSquare b r c == some s
  let diag1 := (getSquare b 0 0 == some s) && (getSquare b 1 1 == some s) && (getSquare b 2 2 == some s)
  let diag2 := (getSquare b 0 2 == some s) && (getSquare b 1 1 == some s) && (getSquare b 2 0 == some s)
  row? 0 || row? 1 || row? 2 || col? 0 || col? 1 || col? 2 || diag1 || diag2

@[simp] def isBoardFull (b : Board) : Bool :=
  b.all fun sq => sq != Square.empty

@[simp] def getGameStatus (b : Board) : GameStatus :=
  if checkPlayerWin b Player.X then GameStatus.Win Player.X
  else if checkPlayerWin b Player.O then GameStatus.Win Player.O
  else if isBoardFull b then GameStatus.Draw
  else GameStatus.Ongoing

/-!
### Domain-specific board literal `board!`
We allow writing a board directly using e.g.
```
board!
  X | O | _
  _ | X | _
  O | _ | X
```
-/

/-! Syntax category for a cell. -/
declare_syntax_cat tttCell
syntax "X" : tttCell
syntax "O" : tttCell
syntax "_" : tttCell

/-! Syntax category for a single row. -/
declare_syntax_cat tttRow
syntax (name := tttRowRule) tttCell "|" tttCell "|" tttCell : tttRow

/-! The full board consists of three rows written one after another. -/
declare_syntax_cat tttBoardSyntax
syntax tttRow tttRow tttRow : tttBoardSyntax

/-- Internal helper: elaborate a single cell. -/
private def elabTttCell (stx : Lean.Syntax) : Lean.Elab.Term.TermElabM Square :=
  match stx with
  | `(tttCell| X) => pure (.occupied .X)
  | `(tttCell| O) => pure (.occupied .O)
  | `(tttCell| _) => pure .empty
  | _             => Lean.throwError s!"unsupported cell syntax {stx}"

/-- The term elaborator turning `board!` syntax into a `TicTacToe.Board` value. -/
elab "board! " b:tttBoardSyntax : term => do
  let mut squares : Array Square := #[]
  unless b.raw.getNumArgs = 3 do
    Lean.throwError s!"Expected 3 rows, got {b.raw.getNumArgs}"
  for rowIdx in [:3] do
    let row := b.raw.getArg rowIdx
    unless row.isOfKind `TicTacToe.tttRowRule do
      Lean.throwError s!"malformed tttRow"
    -- row := cell | cell | cell  (5 args with separators)
    let cells := #[row.getArg 0, row.getArg 2, row.getArg 4]
    for cell in cells do
      squares := squares.push (← elabTttCell cell)
  unless squares.size = boardSize do
    Lean.throwError s!"internal error: expected 9 squares, got {squares.size}"
  -- build an array literal expression `#[...]` corresponding to squares
  let squareTerms ← squares.mapM fun sq =>
    match sq with
    | .empty => `(Square.empty)
    | .occupied .X => `(Square.occupied Player.X)
    | .occupied .O => `(Square.occupied Player.O)
  let arrSyntax ← `(#[$squareTerms,*])
  let boardTy ← `(TicTacToe.Board)
  Lean.Elab.Term.elabTerm arrSyntax (some (← Lean.Elab.Term.elabType boardTy))

-- Example usage of the custom syntax:
#eval board!
  X | O | _
  _ | X | _
  O | _ | X

#eval getGameStatus (board!
  X | X | X
  O | O | _
  _ | _ | _)

#eval initialBoard

/-!
### Logical predicate expressing that a board is a win for a given player.
-/

def WonBy (p : Player) (b : Board) : Prop :=
  getGameStatus b = (.Win p)

--lemma decidableWonBy (p : Player) (b : Board) : Decidable (WonBy p b) :=
--  inferInstance

end TicTacToe
