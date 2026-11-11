# Natural Number Game, locally

The levels of the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4), extracted from [NNG4](https://github.com/leanprover-community/NNG4) into plain Lean files and solved in an editor instead of the browser. Each level is a theorem ending in `sorry`, with the original narration, tactic docs and hints kept as comments. See `NOTICE.md` for provenance and what changed from upstream.

## Branches

- `start` (default) — the unplayed game: every level still ends in `sorry`. Begin here.
- `main` — the maintainer's own playthrough, with levels being solved over time. It contains spoilers.

To play from scratch, either click **Use this template** on GitHub to get your own copy (leave "Include all branches" unticked so `main` stays out), or clone it:

```sh
git clone https://github.com/eliseuv/nng.git
cd nng
git switch -c my-playthrough   # keep your solutions on your own branch
```

## Setup

The Lean compiler is pinned by `lean-toolchain` and fetched by [elan](https://github.com/leanprover/elan) on first use. Mathlib comes in as a dependency, so the first build downloads about 1 GB of prebuilt Mathlib files and needs about 8 GB of disk.

### With Nix

The flake provides `elan`, `git` and `curl`:

```sh
nix develop          # or let direnv load it via .envrc
lake exe cache get   # prebuilt Mathlib oleans for the pinned compiler; skip it and Mathlib compiles from source
lake build           # one "declaration uses `sorry`" warning per unsolved level
```

### Without Nix

Install elan following the [Lean installation guide](https://lean-lang.org/install/). Then, from the repository root:

```sh
lake exe cache get
lake build
```

`git` and `curl` must be on `PATH`.

## Playing

Open `NngLocal/Worlds/W01_Tutorial.lean` in an editor with a Lean language server, such as the Lean 4 VS Code extension or lean.nvim. With Nix, start the editor from inside the dev shell. Replace each `sorry` with a proof. The infoview shows the goal as you type, and a level is solved when its `sorry` warning disappears.

Work through the worlds in numeric order. Each one imports the previous, and later levels use theorems proved in earlier ones. Hints marked `(hidden)` are the ones the game shows only on request.

The tactics are the game's, not core Lean's: `rw` does not close goals with `rfl` afterwards, and `+`, `*` and `^` are opaque, specified only by the axioms the levels introduce.

## Re-extracting

`tools/extract.py <nng4-checkout> .` regenerates `NngLocal/` from an NNG4 checkout. With `NNG_SOLUTIONS=1` it keeps upstream's reference proofs instead of `sorry`; building that output in a scratch directory checks the extraction against upstream (only the Fermat's Last Theorem level should remain unproved).

## Licence

NNG4 is Apache-2.0 (`LICENSE`); the extracted levels and ported tactics keep that licence.
