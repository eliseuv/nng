# Notice

The level statements, narration, hints and tactic documentation in `NngLocal/Worlds/`, and the support modules in `NngLocal/MyNat/` and `NngLocal/Tactic/`, come from the Natural Number Game (NNG4), https://github.com/leanprover-community/NNG4, commit `57b3591` (2026-11-09). NNG4 is by Kevin Buzzard, Jon Eugster and contributors, and is licensed under the Apache License 2.0 (see `LICENSE`).

Changes from upstream:

- `tools/extract.py` converts the nine core worlds (Tutorial through Algorithm, 79 levels) from the lean4game DSL into plain Lean: each level's solution is replaced by `sorry`; its introduction, hints, conclusion and the docs of tactics it introduces are kept as comments.
- Support modules are copied unchanged apart from renaming the `Game.` module prefix to `NngLocal.`. `Game.MyNat.DecidableEq` is inlined into the Algorithm world because it depends on one of that world's levels.
- Not carried over: the game server (`GameApi`), the documentation modules, the non-core `Old*`/`WIP*` worlds, and the `xyzzy` tactic, which proves anything through an axiom that `lake build` would not report.
