module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.DigammaReflection
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.DigammaIntegral

/-! # The Fourier cosine transform of sech

`∫₀^∞ cos(t x) / cosh(x/2) dx = π / cosh(π t)`. With `d = 2`, Gauss's integral for the
digamma function turns the difference `ψ(3/4 + it/2) − ψ(1/4 + it/2)` into the integral of
`e^{−itx} / (2 cosh(x/2))` over the half-line. The real part of that difference is
`π sech(π t)` by `re_digamma_quarter_sub_three_quarters`. No contour integration is used.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set

namespace RiemannMasullo

/-- The half-line kernel `e^{−itx} / (2 cosh(x/2))`. -/
def sechKernel (t x : ℝ) : ℂ :=
  exp (-(I * t * x)) / (2 * (Real.cosh (x / 2) : ℂ))

/-- The difference of two Gauss kernels with `d = 2` is the sech kernel. -/
theorem gauss_sub_eq_sechKernel (t : ℝ) {x : ℝ} (hx : 0 < x) :
    gaussDigammaDifference 2 (2 * (3 / 4 + I * t / 2)) x -
      gaussDigammaDifference 2 (2 * (1 / 4 + I * t / 2)) x = sechKernel t x := by
  set a : ℂ := exp (-(x : ℂ) / 2) with ha
  set E : ℂ := exp (-(I * t * x)) with hE
  have ha0 : a ≠ 0 := exp_ne_zero _
  have e1 : exp (-(2 * (3 / 4 + I * t / 2)) * (x : ℂ)) = a ^ 3 * E := by
    rw [ha, hE, ← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
  have e2 : exp (-(2 * (1 / 4 + I * t / 2)) * (x : ℂ)) = a * E := by
    rw [ha, hE, ← exp_add]; congr 1; ring
  have e3 : exp (-((2 : ℝ) : ℂ) * (x : ℂ)) = a ^ 4 := by
    rw [ha, ← exp_nat_mul]; congr 1; push_cast; ring
  have hcosh : (2 : ℂ) * (Real.cosh (x / 2) : ℂ) = a⁻¹ + a := by
    rw [Real.cosh_eq]; push_cast
    rw [ha, ← exp_neg]; ring_nf
  have ha1 : (1 : ℂ) - a ^ 4 ≠ 0 := by
    have : ‖a‖ < 1 := by
      rw [ha, norm_exp]; simp; linarith
    intro h
    have h4 : a ^ 4 = 1 := by linear_combination -h
    have := congrArg norm h4
    rw [norm_pow, norm_one] at this
    have hn : 0 ≤ ‖a‖ := norm_nonneg _
    nlinarith [pow_lt_one₀ hn ‹‖a‖ < 1› (by norm_num : (4 : ℕ) ≠ 0)]
  have ha2 : (1 : ℂ) + a ^ 2 ≠ 0 := by
    intro h
    apply ha1
    linear_combination (1 - a ^ 2) * h
  unfold gaussDigammaDifference sechKernel
  rw [e1, e2, e3, ← hE, hcosh]
  field_simp
  ring

/-- The sech kernel is integrable on the half-line, with integral `(ψ(3/4+it/2) − ψ(1/4+it/2))/2`. -/
theorem integral_sechKernel (t : ℝ) :
    IntegrableOn (sechKernel t) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), sechKernel t x) =
        (digamma (3 / 4 + I * t / 2) - digamma (1 / 4 + I * t / 2)) / 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hdiv (z : ℂ) : 2 * z / ((2 : ℝ) : ℂ) = z := by push_cast; ring
  obtain ⟨hi1, hv1⟩ := integral_gaussDigammaDifference (w := 2 * (3 / 4 + I * t / 2)) h2
    (by rw [hdiv]; simp)
  obtain ⟨hi2, hv2⟩ := integral_gaussDigammaDifference (w := 2 * (1 / 4 + I * t / 2)) h2
    (by rw [hdiv]; simp)
  have heq : EqOn (fun x ↦ gaussDigammaDifference 2 (2 * (3 / 4 + I * t / 2)) x -
      gaussDigammaDifference 2 (2 * (1 / 4 + I * t / 2)) x) (sechKernel t) (Ioi 0) :=
    fun x hx ↦ gauss_sub_eq_sechKernel t hx
  refine ⟨(hi1.sub hi2).congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hi1 hi2, hv1, hv2, hdiv, hdiv]
  push_cast
  ring

/-- **Fourier cosine transform of sech.** `∫₀^∞ cos(t x) / cosh(x/2) dx = π / cosh(π t)`. -/
theorem integral_cos_div_cosh_half (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), Real.cos (t * x) / Real.cosh (x / 2) = Real.pi / Real.cosh (Real.pi * t) := by
  obtain ⟨hi, hv⟩ := integral_sechKernel t
  have hre (x : ℝ) : (sechKernel t x).re = Real.cos (t * x) / Real.cosh (x / 2) / 2 := by
    unfold sechKernel
    rw [show (2 : ℂ) * (Real.cosh (x / 2) : ℂ) = ((2 * Real.cosh (x / 2) : ℝ) : ℂ) by push_cast; rfl,
      div_ofReal_re, show -(I * t * x) = ((-(t * x) : ℝ) : ℂ) * I by push_cast; ring,
      exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  have hint : (∫ x in Ioi (0 : ℝ), (sechKernel t x).re) = (∫ x in Ioi (0 : ℝ), sechKernel t x).re :=
    integral_re hi
  simp_rw [hre] at hint
  have hd := re_digamma_quarter_sub_three_quarters t
  have hval : (∫ x in Ioi (0 : ℝ), Real.cos (t * x) / Real.cosh (x / 2) / 2) =
      Real.pi / Real.cosh (Real.pi * t) / 2 := by
    rw [hint, hv]
    rw [show (digamma (3 / 4 + I * t / 2) - digamma (1 / 4 + I * t / 2)) / 2 =
      -(digamma (1 / 4 + I * t / 2) - digamma (3 / 4 + I * t / 2)) / 2 by ring]
    rw [div_ofNat_re, neg_re, hd]
    ring
  rw [integral_div] at hval
  linarith

end RiemannMasullo
