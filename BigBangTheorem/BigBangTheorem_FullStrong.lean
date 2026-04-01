import BigBangTheorem.BigBangTheorem_FullFramework
import BigBangTheorem.BigBangTheorem_Strong

namespace BigBangTheorem

/--
Strong analytic step: maximal regularity gives finite volume for every slice.
-/
theorem finite_volume_of_big_bang_maximallyRegular
    (M : DynamicalManifold) (hReg : MaximallyRegular M) :
    ∀ x, x > M.tmin → ∃ B, M.V x ≤ B := by
  simpa using
    finite_volume_of_big_bang_lipschitz
      (V := M.V)
      (L := hReg.rateLimit)
      (tmin := M.tmin)
      M.nonneg_volume
      hReg.lipschitz
      M.bigBang

/--
Strong version of the Big Bang theorem in the theorem-level formalization.
-/
theorem bigBangTheorem_strong_full
    (M : DynamicalManifold) (hReg : MaximallyRegular M) :
    M.SpatiallyClosed := by
  apply
    M.finiteVolume_implies_closed
      M.slicesHomogeneous
      M.slicesComplete
  exact finite_volume_of_big_bang_maximallyRegular M hReg

end BigBangTheorem
