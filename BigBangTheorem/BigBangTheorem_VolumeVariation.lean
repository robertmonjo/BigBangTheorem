import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace BigBangTheorem

section VolumeVariation

/--
If a positive density is written as `sqrt (D t)` and `D` satisfies
`(d/dt) D = 2 E D`, then the density satisfies `(d/dt) sqrt(D) = E sqrt(D)`.

This captures the algebraic core of the local calculation
`d/dt (sqrt(det h_t)) = N θ_t sqrt(det h_t)` used in the manuscript.
-/
theorem deriv_sqrt_of_deriv_eq_two_mul
    {D E : ℝ → ℝ} {t : ℝ}
    (hD : DifferentiableAt ℝ D t)
    (hPos : 0 < D t)
    (hDeriv : deriv D t = 2 * E t * D t) :
    deriv (fun s ↦ Real.sqrt (D s)) t = E t * Real.sqrt (D t) := by
  have hne : D t ≠ 0 := ne_of_gt hPos
  have hsqrt_ne : Real.sqrt (D t) ≠ 0 := Real.sqrt_ne_zero'.2 hPos
  have hsqpow : (Real.sqrt (D t)) ^ 2 = D t := by
    nlinarith [Real.sq_sqrt (le_of_lt hPos)]
  calc
    deriv (fun s ↦ Real.sqrt (D s)) t = deriv D t / (2 * Real.sqrt (D t)) := by
      simpa using deriv_sqrt hD hne
    _ = (2 * E t * D t) / (2 * Real.sqrt (D t)) := by rw [hDeriv]
    _ = E t * Real.sqrt (D t) := by
      field_simp [hsqrt_ne]
      rw [hsqpow]

/--
On a compact interval `[a,b]`, a bound on the absolute value of the derivative
within the interval gives the corresponding Lipschitz control of the function.

This is the route used in the first revision of the manuscript, where the
Lipschitz estimate was obtained by bounding `d/dt V`. The current proof instead
takes absolute values in an integral representation; see
`abs_sub_le_of_integral_repr` below.
-/
theorem abs_sub_le_of_abs_derivWithin_le_Icc
    {V F : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b)
    (hV : DifferentiableOn ℝ V (Set.Icc a b))
    (hFormula : ∀ x ∈ Set.Icc a b, derivWithin V (Set.Icc a b) x = F x)
    (hBound : ∀ x ∈ Set.Icc a b, |F x| ≤ C) :
    |V b - V a| ≤ C * |b - a| := by
  have hMain :=
    norm_image_sub_le_of_norm_deriv_le_segment (f := V) (a := a) (b := b) hV
      (by
        intro x hx
        have hx' : x ∈ Set.Icc a b := ⟨hx.1, le_of_lt hx.2⟩
        rw [hFormula x hx', Real.norm_eq_abs]
        exact hBound x hx')
      b ⟨hab, le_rfl⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hMain

/--
Symmetric interval version of `abs_sub_le_of_abs_derivWithin_le_Icc`, and hence
also part of the first-revision route.
-/
theorem abs_sub_le_of_abs_derivWithin_le_uIcc
    {V F : ℝ → ℝ} {s t C : ℝ}
    (hV : DifferentiableOn ℝ V (Set.uIcc s t))
    (hFormula : ∀ x ∈ Set.uIcc s t, derivWithin V (Set.uIcc s t) x = F x)
    (hBound : ∀ x ∈ Set.uIcc s t, |F x| ≤ C) :
    |V t - V s| ≤ C * |t - s| := by
  rcases le_total s t with hst | hts
  · have hSet : Set.uIcc s t = Set.Icc s t := Set.uIcc_of_le hst
    have hV' : DifferentiableOn ℝ V (Set.Icc s t) := by
      simpa [hSet] using hV
    have hFormula' : ∀ x ∈ Set.Icc s t, derivWithin V (Set.Icc s t) x = F x := by
      intro x hx
      simpa [hSet] using hFormula x (by simpa [hSet] using hx)
    have hBound' : ∀ x ∈ Set.Icc s t, |F x| ≤ C := by
      intro x hx
      simpa [hSet] using hBound x (by simpa [hSet] using hx)
    exact abs_sub_le_of_abs_derivWithin_le_Icc hst hV' hFormula' hBound'
  · have hSet : Set.uIcc s t = Set.Icc t s := by
      simp [Set.uIcc, min_eq_right hts, max_eq_left hts]
    have hV' : DifferentiableOn ℝ V (Set.Icc t s) := by
      simpa [hSet] using hV
    have hFormula' : ∀ x ∈ Set.Icc t s, derivWithin V (Set.Icc t s) x = F x := by
      intro x hx
      simpa [hSet] using hFormula x (by simpa [hSet] using hx)
    have hBound' : ∀ x ∈ Set.Icc t s, |F x| ≤ C := by
      intro x hx
      simpa [hSet] using hBound x (by simpa [hSet] using hx)
    have hMain : |V s - V t| ≤ C * |s - t| :=
      abs_sub_le_of_abs_derivWithin_le_Icc hts hV' hFormula' hBound'
    simpa [abs_sub_comm] using hMain

/--
Lipschitz control obtained from an integral representation of the slice-volume
function, rather than from a bound on its derivative.

This mirrors the final step of Proposition 2.21 in its current form: the estimate
is obtained by taking absolute values in the Fubini identity
`V t - V s = ∫ τ in s..t, f τ`, where `f τ` stands for the instantaneous rate
`∫_{Σ_τ} N θ_τ dμ_τ`, whose absolute value is bounded by the rate limit `C` by
maximal regularity. No differentiability of `V` is required.
-/
theorem abs_sub_le_of_integral_repr
    {V f : ℝ → ℝ} {s t C : ℝ}
    (hrepr : V t - V s = ∫ τ in s..t, f τ)
    (hbound : ∀ τ ∈ Set.uIoc s t, |f τ| ≤ C) :
    |V t - V s| ≤ C * |t - s| := by
  rw [hrepr, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
  intro x hx
  rw [Real.norm_eq_abs]
  exact hbound x hx

end VolumeVariation

end BigBangTheorem
