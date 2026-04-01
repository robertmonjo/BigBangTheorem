import Mathlib.Data.Real.Basic

namespace BigBangTheorem

/--
Abstract spacetime package matching the theorem-level data used in the article.
The Lorentzian and foliation background is represented here by named fields,
so that the strong and weak theorems can be formalized end-to-end as Lean
statements without replacing the faster analytic files.
-/
structure DynamicalManifold where
  V : Real → Real
  tmin : Real
  SlicesHomogeneous : Prop
  SlicesComplete : Prop
  SpatiallyClosed : Prop
  slicesHomogeneous : SlicesHomogeneous
  slicesComplete : SlicesComplete
  nonneg_volume : ∀ t, 0 ≤ V t
  bigBang :
    ∀ ε > 0, ∀ x > tmin, ∃ y, tmin < y ∧ y ≤ x ∧ V y ≤ ε
  finiteVolume_implies_closed :
    SlicesHomogeneous →
      SlicesComplete →
      (∀ x, x > tmin → ∃ B, V x ≤ B) →
      SpatiallyClosed

/--
Weak temporal regularity: between any two slices with `tmin < t0 ≤ t`, the
accumulated expansion provides some finite bound for the change in volume.
-/
structure Regular (M : DynamicalManifold) where
  accumulatedExpansion :
    ∀ {t0 t}, M.tmin < t0 → t0 ≤ t → ∃ I, |M.V t - M.V t0| ≤ I

/--
Strong temporal regularity: the slice-volume function is globally Lipschitz
with a finite rate limit.
-/
structure MaximallyRegular (M : DynamicalManifold) where
  rateLimit : Real
  rateLimit_nonneg : 0 ≤ rateLimit
  lipschitz : ∀ x y, |M.V x - M.V y| ≤ rateLimit * |x - y|

theorem MaximallyRegular.toRegular
    {M : DynamicalManifold} (h : MaximallyRegular M) :
    Regular M := by
  refine ⟨?_⟩
  intro t0 t ht0 hle
  refine ⟨h.rateLimit * |t - t0|, h.lipschitz t t0⟩

end BigBangTheorem
