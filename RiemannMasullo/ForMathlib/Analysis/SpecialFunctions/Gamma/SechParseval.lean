module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.SechFourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Pairing a cosine transform with sech, and the archimedean supertrace

For integrable `g` with cosine transform `h t = ∫ g u cos(t u) du`,
`∫ h t / cosh(π t) dt = ∫ g u / cosh(u/2) du`. The proof combines Fubini with the kernel
`∫ cos(t u) / cosh(π t) dt = 1 / cosh(u/2)`, which comes from `integral_cos_div_cosh_half`.

With `re_digamma_quarter_sub_three_quarters`, this evaluates the difference of the archimedean
explicit-formula terms of the even and odd sign characters of `ℝ^×`:
`(1/2π) ∫ h t · Re[ψ(1/4+it/2) − ψ(3/4+it/2)] dt = −(1/2) ∫ g u / cosh(u/2) du`.
The difference is `≤ 0` whenever `h ≥ 0`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace RiemannMasullo

/-- `1 + x²/2 ≤ cosh x`. -/
theorem one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have h1 := Real.cosh_sq_sub_sinh_sq (x / 2)
  have hs : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rcases le_total 0 (x / 2) with hx | hx
    · have := Real.self_le_sinh_iff.mpr hx
      nlinarith
    · have := Real.sinh_le_self_iff.mpr hx
      nlinarith
  nlinarith

/-- `t ↦ 1 / cosh(π t)` is integrable on `ℝ`. -/
theorem integrable_inv_cosh_pi_mul : Integrable fun t : ℝ ↦ 1 / Real.cosh (Real.pi * t) := by
  have hmaj : Integrable fun t : ℝ ↦ 2 * (1 + (Real.pi * t) ^ 2)⁻¹ :=
    ((integrable_inv_one_add_sq.comp_mul_left' Real.pi_ne_zero).const_mul 2).congr
      (Filter.Eventually.of_forall fun t ↦ by simp)
  have hcont : Continuous fun t : ℝ ↦ 1 / Real.cosh (Real.pi * t) :=
    continuous_const.div (by fun_prop) fun t ↦ (Real.cosh_pos _).ne'
  refine hmaj.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t ↦ ?_)
  have hc := one_add_sq_div_two_le_cosh (Real.pi * t)
  have hpos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [div_le_iff₀ hpos]
  have : 0 < 1 + (Real.pi * t) ^ 2 := by positivity
  field_simp
  nlinarith

/-- **The sech kernel on the line.** `∫ cos(t u) / cosh(π t) dt = 1 / cosh(u/2)`. -/
theorem integral_cos_mul_div_cosh_pi (u : ℝ) :
    ∫ t : ℝ, Real.cos (t * u) / Real.cosh (Real.pi * t) = 1 / Real.cosh (u / 2) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have heven : (fun t : ℝ ↦ Real.cos (t * u) / Real.cosh (Real.pi * t)) =
      fun t ↦ (fun s : ℝ ↦ Real.cos (s * u) / Real.cosh (Real.pi * s)) |t| := by
    funext t
    rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · simp only [h, neg_mul, Real.cos_neg, mul_neg, Real.cosh_neg]
  rw [heven, integral_comp_abs (f := fun s : ℝ ↦ Real.cos (s * u) / Real.cosh (Real.pi * s))]
  have hscale := integral_comp_mul_left_Ioi
    (fun x : ℝ ↦ Real.cos (u / (2 * Real.pi) * x) / Real.cosh (x / 2)) 0 hpi
  simp only [mul_zero, smul_eq_mul] at hscale
  have hcongr : (fun t : ℝ ↦ Real.cos (u / (2 * Real.pi) * (2 * Real.pi * t)) /
      Real.cosh (2 * Real.pi * t / 2)) = fun t ↦ Real.cos (t * u) / Real.cosh (Real.pi * t) := by
    funext t
    congr 2
    · field_simp
    · ring
  rw [hcongr] at hscale
  rw [hscale, integral_cos_div_cosh_half,
    show Real.pi * (u / (2 * Real.pi)) = u / 2 by field_simp]
  field_simp

/-- **Parseval against sech.** For integrable `g` with cosine transform
`h t = ∫ g u cos(t u) du`, `∫ h t / cosh(π t) dt = ∫ g u / cosh(u/2) du`. -/
theorem integral_cosTransform_div_cosh (g : ℝ → ℝ) (hg : Integrable g) :
    ∫ t : ℝ, (∫ u : ℝ, g u * Real.cos (t * u)) / Real.cosh (Real.pi * t) =
      ∫ u : ℝ, g u / Real.cosh (u / 2) := by
  let F : ℝ → ℝ → ℝ := fun t u ↦ g u * Real.cos (t * u) / Real.cosh (Real.pi * t)
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hdom := integrable_inv_cosh_pi_mul.mul_prod hg.norm
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
    · have hm : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ g z.2) (volume.prod volume) := hg.1.comp_snd
      have hc : Continuous fun z : ℝ × ℝ ↦ Real.cos (z.1 * z.2) / Real.cosh (Real.pi * z.1) :=
        (by fun_prop : Continuous fun z : ℝ × ℝ ↦ Real.cos (z.1 * z.2)).div (by fun_prop)
          fun z ↦ (Real.cosh_pos _).ne'
      refine (hm.mul hc.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun z ↦ ?_)
      obtain ⟨t, u⟩ := z
      simp only [Function.uncurry_apply_pair, F, Pi.mul_apply, mul_div_assoc]
    · obtain ⟨t, u⟩ := z
      have hpos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
      simp only [Function.uncurry_apply_pair, F, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos hpos]
      have hc := Real.abs_cos_le_one (t * u)
      have hg0 := abs_nonneg (g u)
      rw [div_le_iff₀ hpos]
      field_simp
      nlinarith
  have hL : (fun t : ℝ ↦ (∫ u : ℝ, g u * Real.cos (t * u)) / Real.cosh (Real.pi * t)) =
      fun t ↦ ∫ u, F t u := by
    funext t; simp only [F]; rw [integral_div]
  rw [hL, integral_integral_swap hF]
  congr 1; funext u
  simp only [F]
  simp_rw [mul_div_assoc]
  rw [integral_const_mul, integral_cos_mul_div_cosh_pi]
  ring

/-- **The archimedean supertrace.** For integrable `g` with cosine transform `h`, the
difference of the even and odd archimedean terms of the explicit formula is
`(1/2π) ∫ h t · Re[ψ(1/4+it/2) − ψ(3/4+it/2)] dt = −(1/2) ∫ g u / cosh(u/2) du`. -/
theorem archimedean_supertrace (g : ℝ → ℝ) (hg : Integrable g) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∫ u : ℝ, g u * Real.cos (t * u)) *
        (digamma (1 / 4 + I * t / 2) - digamma (3 / 4 + I * t / 2)).re =
      -(1 / 2) * ∫ u : ℝ, g u / Real.cosh (u / 2) := by
  simp_rw [re_digamma_quarter_sub_three_quarters]
  have h (t : ℝ) : (∫ u : ℝ, g u * Real.cos (t * u)) * (-Real.pi / Real.cosh (Real.pi * t)) =
      -Real.pi * ((∫ u : ℝ, g u * Real.cos (t * u)) / Real.cosh (Real.pi * t)) := by ring
  simp_rw [h]
  rw [integral_const_mul, integral_cosTransform_div_cosh g hg]
  field_simp

/-- **Sign of the supertrace.** If the cosine transform of `g` is nonnegative (for instance
`g = φ ∗ φ̃` with `φ` even), the archimedean supertrace is `≤ 0`. -/
theorem archimedean_supertrace_nonpos (g : ℝ → ℝ) (hg : Integrable g)
    (hpos : ∀ t, 0 ≤ ∫ u : ℝ, g u * Real.cos (t * u)) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∫ u : ℝ, g u * Real.cos (t * u)) *
        (digamma (1 / 4 + I * t / 2) - digamma (3 / 4 + I * t / 2)).re ≤ 0 := by
  have h := archimedean_supertrace g hg
  rw [← integral_cosTransform_div_cosh g hg] at h
  rw [h]
  have : 0 ≤ ∫ t : ℝ, (∫ u : ℝ, g u * Real.cos (t * u)) / Real.cosh (Real.pi * t) :=
    integral_nonneg fun t ↦ div_nonneg (hpos t) (Real.cosh_pos _).le
  linarith

end RiemannMasullo
