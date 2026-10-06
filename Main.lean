import TicTacToe

open TicTacToe

/-- Entry point printing a demo board built with the `moves!` DSL. -/
def main : IO Unit := do
  let demo := moves!
    X 0 0 O 1 1 X 0 1 O 2 2 X 0 2
  IO.println "Demo board:"
  IO.println (ppBoard demo)
  IO.println s!"Status: {getGameStatus demo}"
