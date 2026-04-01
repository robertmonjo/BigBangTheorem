import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace BigBangTheorem

section Strong

variable {V : Real → Real}
variable {L t t0 B : Real}

/--
If `V` is Lipschitz with constant `L` and has a known bound `B` at one time `t0`,
then every other time `t` has an explicit finite bound.
-/
theorem volume_bound_from_lipschitz
    (hLip : ∀ x y, |V x - V y| ≤ L * |x - y|)
    (hB : |V t0| ≤ B) :
    |V t| ≤ B + L * |t - t0| := by
  have hdecomp : (V t - V t0) + V t0 = V t := by
    linarith
  have habs : |V t| = |(V t - V t0) + V t0| := by
    exact congrArg abs hdecomp.symm
  have htriangle : |V t| ≤ |V t - V t0| + |V t0| := by
    calc
      |V t| = |(V t - V t0) + V t0| := habs
      _ ≤ |V t - V t0| + |V t0| := abs_add_le _ _
  have hsum : |V t - V t0| + |V t0| ≤ B + L * |t - t0| := by
    have hLip' := hLip t t0
    linarith
  exact le_trans htriangle hsum

/--
If a nonnegative volume function is small at one time `t0`, then Lipschitz control
propagates finiteness to every other time.
-/
theorem finite_volume_from_small_nearby_value
    (hNonneg : ∀ x, 0 ≤ V x)
    (hLip : ∀ x y, |V x - V y| ≤ L * |x - y|)
    (hSmall : V t0 ≤ B) :
    V t ≤ B + L * |t - t0| := by
  have hBabs : |V t0| ≤ B := by
    simpa [abs_of_nonneg (hNonneg t0)] using hSmall
  have hmain :=
    volume_bound_from_lipschitz (V := V) (L := L) (t := t) (t0 := t0) (B := B) hLip hBabs
  have htabs : |V t| = V t := by
    simp [abs_of_nonneg (hNonneg t)]
  simpa [htabs] using hmain

/--
If a nonnegative volume function becomes arbitrarily small near the initial time and is
globally Lipschitz, then every slice has finite volume with an explicit bound.
-/
theorem finite_volume_of_big_bang_lipschitz
    {tmin : Real}
    (hNonneg : ∀ x, 0 ≤ V x)
    (hLip : ∀ x y, |V x - V y| ≤ L * |x - y|)
    (hNearBang : ∀ ε > 0, ∀ x > tmin, ∃ y, tmin < y ∧ y ≤ x ∧ V y ≤ ε) :
    ∀ x, x > tmin → ∃ B, V x ≤ B := by
  intro x hx
  let y0 := Classical.choose (hNearBang 1 zero_lt_one x hx)
  have hy0 : tmin < y0 ∧ y0 ≤ x ∧ V y0 ≤ 1 := Classical.choose_spec (hNearBang 1 zero_lt_one x hx)
  have hsmall : V y0 ≤ 1 := hy0.2.2
  refine ⟨1 + L * |x - y0|, ?_⟩
  exact
    finite_volume_from_small_nearby_value
      (V := V) (L := L) (t := x) (t0 := y0) (B := 1)
      hNonneg hLip hsmall

end Strong

end BigBangTheorem
