import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Rademacher

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


section FirstVariation

open MeasureTheory intervalIntegral

/--
The data of Proposition 2.21, at the level at which its proof actually operates.

`V` is the slice-volume function and `rate τ` stands for the instantaneous rate
`∫_{Σ_τ} N θ_τ dμ_τ`. The field `rate_bound` is maximal regularity with rate
limit `C`, and `first_variation` is the identity obtained in the manuscript from
the density identity `∂_t dμ_t = N θ_t dμ_t` through Tonelli's and Fubini's
theorems.

The Lorentzian geometry that produces `first_variation` is not formalized here:
it is the geometric input, and everything else in the proposition is derived
from it below.
-/
structure SliceVolume where
  V : ℝ → ℝ
  rate : ℝ → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  rate_bound : ∀ τ, |rate τ| ≤ C
  rate_integrable : ∀ s t : ℝ, IntervalIntegrable rate volume s t
  first_variation : ∀ s t : ℝ, V t - V s = ∫ τ in s..t, rate τ

namespace SliceVolume

variable (S : SliceVolume)

/-- The estimate of Proposition 2.21, with the rate limit as Lipschitz constant. -/
theorem abs_sub_le (s t : ℝ) : |S.V t - S.V s| ≤ S.C * |t - s| :=
  abs_sub_le_of_integral_repr (S.first_variation s t) fun τ _ => S.rate_bound τ

/-- Proposition 2.21: the slice-volume function is Lipschitz. -/
theorem lipschitzWith : LipschitzWith S.C.toNNReal S.V := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ S.C_nonneg]
  exact S.abs_sub_le y x

/-- The slice-volume function is the integral of its rate from any base time. -/
theorem eq_add_integral (t : ℝ) :
    S.V t = S.V 0 + ∫ τ in (0:ℝ)..t, S.rate τ := by
  have h := S.first_variation 0 t
  linarith


/--
The slice-volume function is differentiable almost everywhere, with no
regularity assumption on the instantaneous rate.

This is the content of the manuscript's remark that the slice-volume function is
absolutely continuous: being Lipschitz by `lipschitzWith`, it is in particular
absolutely continuous, and hence differentiable outside a null set. Formally the
step is Rademacher's theorem.
-/
theorem ae_differentiableAt :
    ∀ᵐ t, DifferentiableAt ℝ S.V t :=
  S.lipschitzWith.ae_differentiableAt

/--
Wherever the slice-volume function is differentiable, its derivative is bounded
by the rate limit. Together with `ae_differentiableAt` this gives the estimate
`|dV/dt| ≤ C` almost everywhere, which is the form in which the bound is used.
-/
theorem abs_deriv_le_of_hasDerivAt {t d : ℝ} (h : HasDerivAt S.V d t) :
    |d| ≤ S.C := by
  have hle : ‖d‖ ≤ (S.C.toNNReal : ℝ) := h.le_of_lipschitz S.lipschitzWith
  rwa [Real.norm_eq_abs, Real.coe_toNNReal _ S.C_nonneg] at hle

/-- Almost everywhere, the slice-volume function has a derivative bounded by the rate limit. -/
theorem ae_abs_deriv_le :
    ∀ᵐ t, |deriv S.V t| ≤ S.C := by
  filter_upwards [S.ae_differentiableAt] with t ht
  exact S.abs_deriv_le_of_hasDerivAt ht.hasDerivAt

/--
The first variation formula, for a continuous instantaneous rate: the derivative
of the slice-volume function is the integrated expansion of the slice.
-/
theorem hasDerivAt (hcont : Continuous S.rate) (t : ℝ) :
    HasDerivAt S.V (S.rate t) t := by
  have hfun : (fun u => S.V 0 + ∫ τ in (0:ℝ)..u, S.rate τ) = S.V := by
    funext u
    exact (S.eq_add_integral u).symm
  have h : HasDerivAt (fun u => ∫ τ in (0:ℝ)..u, S.rate τ) (S.rate t) t :=
    integral_hasDerivAt_right (S.rate_integrable 0 t)
      (hcont.stronglyMeasurableAtFilter volume _) hcont.continuousAt
  simpa [hfun] using h.const_add (S.V 0)

end SliceVolume

end FirstVariation

end BigBangTheorem
