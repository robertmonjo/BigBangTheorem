import BigBangTheorem.BigBangTheorem_FullFramework
import BigBangTheorem.BigBangTheorem_Weak

namespace BigBangTheorem

/--
Weak analytic step: regularity plus the Big Bang condition yields finite volume
for every slice.
-/
theorem finite_volume_of_big_bang_regular
    (M : DynamicalManifold) (hReg : Regular M) :
    ∀ x, x > M.tmin → ∃ B, M.V x ≤ B := by
  intro x hx
  obtain ⟨t0, ht0_gt, ht0_le, ht0_small⟩ := M.bigBang 1 zero_lt_one x hx
  obtain ⟨I, hI⟩ := hReg.accumulatedExpansion (t0 := t0) (t := x) ht0_gt ht0_le
  refine ⟨1 + I, ?_⟩
  exact
    finite_volume_from_integrable_expansion
      (V := M.V)
      (t := x)
      (t0 := t0)
      (B := 1)
      (I := I)
      M.nonneg_volume
      ht0_small
      hI

/--
Weak version of the Big Bang theorem in the theorem-level formalization.
-/
theorem bigBangTheorem_weak_full
    (M : DynamicalManifold) (hReg : Regular M) :
    M.SpatiallyClosed := by
  apply
    M.finiteVolume_implies_closed
      M.slicesHomogeneous
      M.slicesComplete
  exact finite_volume_of_big_bang_regular M hReg

/--
The strong theorem implies the weak theorem through the abstract implication
`maximally regular => regular`.
-/
theorem bigBangTheorem_strong_via_weak
    (M : DynamicalManifold) (hReg : MaximallyRegular M) :
    M.SpatiallyClosed :=
  bigBangTheorem_weak_full M hReg.toRegular

end BigBangTheorem
