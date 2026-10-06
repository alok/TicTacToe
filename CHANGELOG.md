# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]
### Changed

- Complete the local `moves!` work and use `Board.move` for its checks.
- Add decidable equality and a `WonBy` instance so documented proofs work.
- Translate `board!` through typed syntax patterns instead of raw tree offsets.
- Complete placement reachability proofs with `place` and `finish_game` tactics.
- Move demonstrations into checked examples and correct the draw sequence.
- Check all winning lines, syntax equivalence, invalid moves, and proof failures
  in the default build; add a sequential verification script.
- Require nine cells when checking whether a board is full.
- Align the printed borders and column headings with the labeled rows.
- Pin Lean 4.34.1 and document the syntax's guarantees and game-rule boundaries.

### Added
- Initial TicTacToe Lean library files (`TicTacToe.lean`, `TicTacToe/Basic.lean`).
- `Main.lean` executable.
- Lake build configuration (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`).
- Basic GitHub Actions CI workflow to build the project.

## [0.1.0] - 2025-05-09:19:37
### Added
- Initial project setup.
- Added MIT License.
- Basic README.md.
- Basic CHANGELOG.md.
- Ignored editor backup files in .gitignore.

## [0.2.0] - 2025-05-09:18:17
### Added
- Core game logic (`Player`, `Square`, `Board`, `getGameStatus`, etc.) in `TicTacToe/Game.lean`.
- `board!` term DSL to define `Board` literals directly in `TicTacToe/Game.lean`.
- `moves!` term DSL to define `Board` by a sequence of moves in `TicTacToe/DSL.lean`.
- `WonBy` predicate in `TicTacToe/Game.lean`.
- Example `#eval` statements in `Game.lean` and `DSL.lean` for inline testing.
- Updated `Main.lean` to use the new DSLs.
- Updated `README.md` with new DSL examples and marked TODOs as complete.

### Fixed
- Various linter errors and compilation issues during DSL development.
- Deprecation warnings for `Array.get!` and `Array.mkArray`.

### Changed
- Refactored initial `Main.lean` code into library modules.
- Restructured `TicTacToe.lean` to import new modules.

### Improved
- Enhanced `ppBoard` pretty printer to include row and column indices and uniform spacing for clearer, aligned output. (2025-05-09:??:??)
