import Lean

namespace TicTacToe

/-- Represents a player in Tic Tac Toe. -/
inductive Player | X | O deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString Player where
  toString
    | .X => "X"
    | .O => "O"

/-- Represents a single square on the Tic Tac Toe board. -/
inductive Square
  | empty
  | occupied (player : Player)
  deriving Repr, BEq, DecidableEq, Inhabited

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

/-- A flat array of squares. `initialBoard`, `mkBoard`, and the literals produce
nine-cell boards; the abbreviation itself does not enforce the size. -/
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

/-- Place a mark on an empty square, or clear a square with `.empty`.
Fails for out-of-bounds coordinates, missing cells, or overwriting a mark. -/
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

  let header := "      0   1   2\n"
  let top    := "    ┌───┬───┬───┐\n"
  let sep    := "    ├───┼───┼───┤\n"
  let bottom := "    └───┴───┴───┘"
  header ++ top ++ row 0 ++ "\n" ++ sep ++ row 1 ++ "\n" ++ sep ++ row 2 ++ "\n" ++ bottom

instance : Repr Board where
  reprPrec b _ := ppBoard b

instance : ToString Board where
  toString := ppBoard

/-- Attempt to place `p` at `(row, col)` on `b`.
Checks bounds and occupancy; does not enforce turn order or game status. -/
@[simp] def Board.move (b : Board) (p : Player) (row col : Nat) : Option Board :=
  setSquare b row col (.occupied p)

/-- The possible outcomes of a finished game. -/
inductive GameStatus
  | Win (p : Player)
  | Draw
  | Ongoing
  deriving Repr, BEq, DecidableEq

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
  b.size == boardSize && b.toList.all fun sq => sq != Square.empty

/-- Classify a position. If an arbitrary literal gives both players a winning
line, X takes precedence. This function does not validate a game's history. -/
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

/-- Translate a cell to an ordinary Lean constructor term. -/
private def termOfCell (stx : Lean.TSyntax `tttCell) : Lean.MacroM (Lean.TSyntax `term) :=
  match stx with
  | `(tttCell| X) => `(Square.occupied Player.X)
  | `(tttCell| O) => `(Square.occupied Player.O)
  | `(tttCell| _) => `(Square.empty)
  | _ => Lean.Macro.throwErrorAt stx "unsupported cell syntax"

private def termsOfRow (stx : Lean.TSyntax `tttRow) :
    Lean.MacroM (Array (Lean.TSyntax `term)) := do
  match stx with
  | `(tttRow| $a:tttCell | $b:tttCell | $c:tttCell) =>
    #[a, b, c].mapM termOfCell
  | _ => Lean.Macro.throwErrorAt stx "unsupported row syntax"

/-- A nine-cell position literal. The grammar checks the shape, not whether
the position can occur in a game with alternating turns. -/
macro "board! " b:tttBoardSyntax : term => do
  match b with
  | `(tttBoardSyntax| $a:tttRow $b:tttRow $c:tttRow) =>
    let cells := (← termsOfRow a) ++ (← termsOfRow b) ++ (← termsOfRow c)
    `((#[$cells,*] : TicTacToe.Board))
  | _ => Lean.Macro.throwErrorAt b "unsupported board syntax"

/-!
### Logical predicate expressing that a board is a win for a given player.
-/

/-- The status classifier reports a win for `p` on this position. -/
def WonBy (p : Player) (b : Board) : Prop :=
  getGameStatus b = (.Win p)

instance (p : Player) (b : Board) : Decidable (WonBy p b) :=
  inferInstanceAs (Decidable (getGameStatus b = .Win p))

end TicTacToe
