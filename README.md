# BigBangTheorem

Lean supplementary material for the article on the Big Bang closedness theorem.

## Contents

Fast analytic route:

- `BigBangTheorem/BigBangTheorem_Strong.lean`:
  analytic core of the strong version, based on Lipschitz control of the slice-volume function.

- `BigBangTheorem/BigBangTheorem_Weak.lean`:
  analytic core of the weak version, based on finite accumulated expansion.

- `BigBangTheorem/BigBangTheorem_VolumeVariation.lean`:
  the first variation of the slice volume. Section `VolumeVariation` holds the analytic
  lemmas: the derivative of a square-root density, and Lipschitz control of a function
  obtained either from a bound on its derivative or from an integral representation of it.
  Section `FirstVariation` packages the hypotheses of the corresponding proposition of the
  article in a structure `SliceVolume` and derives its full statement from them: the
  Lipschitz estimate with the rate limit as constant (`abs_sub_le`, `lipschitzWith`),
  differentiability outside a null set with the derivative bounded by the rate limit
  (`ae_differentiableAt`, `ae_abs_deriv_le`), and the first variation formula itself
  (`hasDerivAt`, for a continuous rate).

  The geometric input is the field `first_variation`, namely the identity
  `V t - V s = ∫ τ in s..t, rate τ` with `rate τ` the integrated expansion of the slice at
  time `τ`. That identity comes from the Lorentzian geometry of the foliation, which is not
  formalized here; everything else in the proposition is derived from it inside Lean.

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

## Verification

The package was checked on a Linux host with the pinned toolchain and `mathlib4` revision:

```bash
lake build BigBangTheorem.BigBangTheorem_VolumeVariation
lake build BigBangTheorem
```

Both complete without errors or warnings from the project files. No declaration uses `sorry`,
and no axioms beyond the Lean defaults are introduced: `#print axioms` on the results of the
volume-variation module reports only `propext`, `Classical.choice` and `Quot.sound`.

Run builds outside a synchronised folder such as OneDrive or Dropbox. File locking on `.lake`
inside such folders can make a build fail for reasons unrelated to the Lean sources, so a
failure there is not evidence about the package.

## Notes

This repository contains two complementary formal routes for the strong and weak versions of the theorem discussed in the article:

- a lightweight route for the analytic lemmas used in the proof;
- a theorem-level route where the hypotheses and the final strong/weak closedness theorems are formalized end-to-end from an abstract spacetime package matching the article.
