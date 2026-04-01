# BigBangTheorem

Lean supplementary material for the article on the Big Bang closedness theorem.

## Contents

- `BigBangTheorem/BigBangTheorem_Strong.lean`:
  analytic core of the strong version, based on Lipschitz control of the slice-volume function.

- `BigBangTheorem/BigBangTheorem_Weak.lean`:
  analytic core of the weak version, based on finite accumulated expansion.

- `BigBangTheorem.lean`:
  root module importing the strong and weak files.

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

If the build succeeds, the supplementary Lean files are checked by Lean and the project compiles without errors.

## Notes

This repository contains the supplementary formal material corresponding to the strong and weak versions of the theorem discussed in the article. The files isolate the analytic estimates used in the proof and the abstract compactness implication derived from finite volume together with homogeneity.
