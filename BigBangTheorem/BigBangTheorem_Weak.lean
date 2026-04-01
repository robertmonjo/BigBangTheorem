import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace BigBangTheorem

section Weak

variable {V : Real → Real}
variable {t t0 B I : Real}

/--
If the volume is small at some nearby time `t0` and the accumulated expansion
between `t0` and `t` gives a finite bound `I` for `|V t - V t0|`, then `V t`
is finite with explicit bound `B + I`.
-/
theorem finite_volume_from_integrable_expansion
    (hNonneg : ∀ x, 0 ≤ V x)
    (hSmall : V t0 ≤ B)
    (hIntegral : |V t - V t0| ≤ I) :
    V t ≤ B + I := by
  have hBabs : |V t0| ≤ B := by
    simpa [abs_of_nonneg (hNonneg t0)] using hSmall
  have htriangle : |V t| ≤ |V t - V t0| + |V t0| := by
    have hdecomp : (V t - V t0) + V t0 = V t := by
      linarith
    calc
      |V t| = |(V t - V t0) + V t0| := by
        simpa [hdecomp]
      _ ≤ |V t - V t0| + |V t0| := abs_add_le _ _
  have hmain : |V t| ≤ B + I := by
    linarith
  simpa [abs_of_nonneg (hNonneg t)] using hmain

/--
Abstract compactness step shared by the strong and weak versions of the theorem.
-/
theorem big_bang_implies_closed_universe
    {ClosedUniverse Homogeneous : Prop}
    (hFiniteVolume : ∀ x, ∃ B, V x ≤ B)
    (hCompactCriterion :
      Homogeneous → (∀ x, ∃ B, V x ≤ B) → ClosedUniverse)
    (hSymmetry : Homogeneous) :
    ClosedUniverse :=
  hCompactCriterion hSymmetry hFiniteVolume

end Weak

end BigBangTheorem
