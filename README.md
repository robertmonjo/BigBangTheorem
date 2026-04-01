# BigBangTheorem

Lean supplementary material for the article on the Big Bang closedness theorem.

## Contents

Fast analytic route:

- `BigBangTheorem/BigBangTheorem_Strong.lean`:
  analytic core of the strong version, based on Lipschitz control of the slice-volume function.

- `BigBangTheorem/BigBangTheorem_Weak.lean`:
  analytic core of the weak version, based on finite accumulated expansion.

Theorem-level formalized route:

- `BigBangTheorem/BigBangTheorem_FullFramework.lean`:
  abstract structures matching the theorem-level hypotheses used in the article
  (`dynamical manifold`, `regularity`, `maximal regularity`, and the compactness criterion).

- `BigBangTheorem/BigBangTheorem_FullStrong.lean`:
  full strong theorem stated and proved from the framework above.

- `BigBangTheorem/BigBangTheorem_FullWeak.lean`:
  full weak theorem stated and proved from the same framework, together with the implication
  from maximal regularity to regularity.

- `BigBangTheorem.lean`:
  root module importing both the fast files and the theorem-level files.

## Requirements

- `elan`
- `lake`
- Lean toolchain `leanprover/lean4:v4.29.0-rc8`

The required Lean version is specified in the file `lean-toolchain`.

## Build

Clone the repository and run:

```bash
lake build
```

At the first build, `lake` will download the pinned version of `mathlib4`.

## Expected outcome

If the build succeeds, both the fast analytic files and the theorem-level formalized files are checked by Lean and the project compiles without errors.

## Notes

This repository contains two complementary formal routes for the strong and weak versions of the theorem discussed in the article:

- a lightweight route for the analytic lemmas used in the proof;
- a theorem-level route where the hypotheses and the final strong/weak closedness theorems are formalized end-to-end from an abstract spacetime package matching the article.
