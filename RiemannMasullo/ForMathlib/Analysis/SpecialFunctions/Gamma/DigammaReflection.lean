module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import RiemannMasullo.External.ZetaLab.Zeta23.GammaFacts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Conjugation and the quarter-shift difference of the digamma function

On the line `Re s = 1/4` the
difference `ψ(s) − ψ(s + 1/2)` has real part `−π sech(π t)`, where `s = 1/4 + it/2`. Up to
the factor `1/2π`, this is the difference between the archimedean terms of the explicit
formula for the even (`Γ_ℝ(s)`) and odd (`Γ_ℝ(s + 1)`) characters of `ℝ^×`.

Conjugation of the digamma function is not reproved: the proof uses `Zeta23.digamma_conj`
from the vendored Zeta23 code (`External/ZetaLab/Zeta23/GammaFacts.lean`), distributed in
teal-sea/zeta-lab under Apache-2.0.
-/

@[expose] public section

open Complex

namespace RiemannMasullo

/-- `cot(π/4 + iy) = (1 − i sinh 2y) / cosh 2y` for real `y`. -/
theorem cot_pi_div_four_add_mul_I (y : ℝ) :
    cot (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I) =
      ((1 / Real.cosh (2 * y) : ℝ) : ℂ) -
        ((Real.sinh (2 * y) / Real.cosh (2 * y) : ℝ) : ℂ) * I := by
  have hc : cos ((Real.pi / 4 : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [← ofReal_cos, Real.cos_pi_div_four]
  have hs : sin ((Real.pi / 4 : ℝ) : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [← ofReal_sin, Real.sin_pi_div_four]
  rw [cot_eq_cos_div_sin, cos_add_mul_I, sin_add_mul_I, hc, hs, ← ofReal_cosh, ← ofReal_sinh,
    Real.cosh_two_mul, Real.sinh_two_mul]
  have h1 := Real.cosh_sq_sub_sinh_sq y
  have hpos : 0 < Real.cosh y := Real.cosh_pos y
  have hC : (0 : ℝ) < Real.cosh y ^ 2 + Real.sinh y ^ 2 := by positivity
  have hr : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hden : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (Real.cosh y : ℂ) +
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (Real.sinh y : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg re h
    simp at this
    nlinarith
  rw [div_eq_iff hden]
  apply Complex.ext
  · simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im, mul_im,
      sub_im]
    field_simp
    linear_combination (Real.sqrt 2 * Real.cosh y) * h1
  · simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im, mul_im,
      sub_im]
    field_simp
    linear_combination (Real.sqrt 2 * Real.sinh y) * h1

/-- On the line `Re s = 1/4`, with `s = 1/4 + it/2`, the real part of `ψ(s) − ψ(s + 1/2)`
is `−π / cosh(π t)`. The proof applies the reflection formula at `s`, whose image `1 − s` is
the conjugate of `s + 1/2`. -/
theorem re_digamma_quarter_sub_three_quarters (t : ℝ) :
    (digamma (1 / 4 + I * t / 2) - digamma (3 / 4 + I * t / 2)).re =
      -Real.pi / Real.cosh (Real.pi * t) := by
  set s : ℂ := 1 / 4 + I * t / 2 with hs_def
  have hs : ∀ n : ℤ, s ≠ n := by
    intro n h
    have h' := congrArg re h
    simp [hs_def] at h'
    have h4 : (4 : ℝ) * n = 1 := by linarith
    have h4' : (4 : ℤ) * n = 1 := by exact_mod_cast h4
    omega
  have hconj : digamma (3 / 4 + I * t / 2) = (starRingEnd ℂ) (digamma (1 - s)) := by
    rw [← Zeta23.digamma_conj]
    congr 1
    apply Complex.ext <;> simp [hs_def, map_ofNat] <;> ring
  have hpis : (Real.pi : ℂ) * s =
      ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * t / 2 : ℝ) : ℂ) * I := by
    rw [hs_def]; push_cast; ring
  rw [hconj, sub_re, conj_re, digamma_one_sub hs, add_re, hpis, cot_pi_div_four_add_mul_I,
    show 2 * (Real.pi * t / 2) = Real.pi * t by ring]
  simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  ring

end RiemannMasullo
