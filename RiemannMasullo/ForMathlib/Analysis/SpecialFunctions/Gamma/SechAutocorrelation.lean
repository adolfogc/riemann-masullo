module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.SechParseval
public import Mathlib.Analysis.Convolution

/-! # The archimedean supertrace on autocorrelations

For integrable real `φ`, the autocorrelation `g u = ∫ φ(v) φ(v − u) dv` (that is `φ ∗ φ̃`,
with `φ̃(u) = φ(−u)`) has cosine transform `C(t)² + S(t)²`, where `C` and `S` are the cosine
and sine transforms of `φ`. So `archimedean_supertrace_nonpos` applies with no further
hypothesis: the even-minus-odd archimedean term is `−(1/2) ∫ g u / cosh(u/2) du ≤ 0`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set

namespace RiemannMasullo

/-- The autocorrelation `u ↦ ∫ φ(v) φ(v − u) dv`, that is `φ ∗ φ̃` with `φ̃(u) = φ(−u)`. -/
def autocorrelation (φ : ℝ → ℝ) (u : ℝ) : ℝ := ∫ v, φ v * φ (v - u)

/-- The integrand of the autocorrelation is integrable on the plane. -/
theorem integrable_autocorrelation_integrand {φ : ℝ → ℝ} (hφ : Integrable φ) :
    Integrable (fun p : ℝ × ℝ ↦ φ p.2 * φ (p.2 - p.1)) (volume.prod volume) := by
  have h := hφ.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (g := fun y ↦ φ (-y))
    hφ.comp_neg (μ := volume) (ν := volume)
  refine h.congr (Filter.Eventually.of_forall fun p ↦ ?_)
  simp [neg_sub]

theorem integrable_autocorrelation {φ : ℝ → ℝ} (hφ : Integrable φ) :
    Integrable (autocorrelation φ) :=
  (integrable_autocorrelation_integrand hφ).integral_prod_left

private theorem integrable_mul_cos {φ : ℝ → ℝ} (hφ : Integrable φ) (t : ℝ) :
    Integrable fun v ↦ φ v * Real.cos (t * v) :=
  hφ.mul_bdd (by fun_prop : Continuous fun v ↦ Real.cos (t * v)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v ↦ by simpa using Real.abs_cos_le_one (t * v))

private theorem integrable_mul_sin {φ : ℝ → ℝ} (hφ : Integrable φ) (t : ℝ) :
    Integrable fun v ↦ φ v * Real.sin (t * v) :=
  hφ.mul_bdd (by fun_prop : Continuous fun v ↦ Real.sin (t * v)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v ↦ by simpa using Real.abs_sin_le_one (t * v))

/-- **The cosine transform of an autocorrelation is a sum of two squares.** -/
theorem cosTransform_autocorrelation {φ : ℝ → ℝ} (hφ : Integrable φ) (t : ℝ) :
    ∫ u, autocorrelation φ u * Real.cos (t * u) =
      (∫ v, φ v * Real.cos (t * v)) ^ 2 + (∫ v, φ v * Real.sin (t * v)) ^ 2 := by
  set C := ∫ v, φ v * Real.cos (t * v)
  set S := ∫ v, φ v * Real.sin (t * v)
  have hP := integrable_autocorrelation_integrand hφ
  have hF : Integrable (Function.uncurry fun u v ↦ φ v * φ (v - u) * Real.cos (t * u))
      (volume.prod volume) := by
    refine hP.norm.mono' ?_ (Filter.Eventually.of_forall fun p ↦ ?_)
    · exact (hP.1.mul (by fun_prop : Continuous fun p : ℝ × ℝ ↦
        Real.cos (t * p.1)).aestronglyMeasurable).congr
        (Filter.Eventually.of_forall fun p ↦ by obtain ⟨u, v⟩ := p; rfl)
    · obtain ⟨u, v⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      have hc : ‖Real.cos (t * u)‖ ≤ 1 := by simpa using Real.abs_cos_le_one (t * u)
      have h0 := mul_nonneg (norm_nonneg (φ v)) (norm_nonneg (φ (v - u)))
      nlinarith
  have hinner (v : ℝ) : ∫ u, φ (v - u) * Real.cos (t * u) =
      Real.cos (t * v) * C + Real.sin (t * v) * S := by
    have := integral_sub_left_eq_self (fun w ↦ φ w * Real.cos (t * (v - w))) volume v
    simp only [sub_sub_cancel] at this
    rw [this]
    have hexp (w : ℝ) : φ w * Real.cos (t * (v - w)) =
        Real.cos (t * v) * (φ w * Real.cos (t * w)) +
          Real.sin (t * v) * (φ w * Real.sin (t * w)) := by
      rw [mul_sub, Real.cos_sub]; ring
    simp_rw [hexp]
    rw [integral_add ((integrable_mul_cos hφ t).const_mul _) ((integrable_mul_sin hφ t).const_mul _),
      integral_const_mul, integral_const_mul]
  calc ∫ u, autocorrelation φ u * Real.cos (t * u)
      = ∫ u, ∫ v, φ v * φ (v - u) * Real.cos (t * u) := by
        congr 1; funext u; rw [autocorrelation, integral_mul_const]
    _ = ∫ v, ∫ u, φ v * φ (v - u) * Real.cos (t * u) := integral_integral_swap hF
    _ = ∫ v, φ v * (Real.cos (t * v) * C + Real.sin (t * v) * S) := by
        congr 1; funext v
        simp_rw [mul_assoc]
        rw [integral_const_mul, hinner]
    _ = C ^ 2 + S ^ 2 := by
        have hexp (v : ℝ) : φ v * (Real.cos (t * v) * C + Real.sin (t * v) * S) =
            C * (φ v * Real.cos (t * v)) + S * (φ v * Real.sin (t * v)) := by ring
        simp_rw [hexp]
        rw [integral_add ((integrable_mul_cos hφ t).const_mul _)
          ((integrable_mul_sin hφ t).const_mul _), integral_const_mul, integral_const_mul]
        ring

/-- **The archimedean supertrace is nonpositive on autocorrelations.** For every integrable
real `φ`, with `g = φ ∗ φ̃`, the even-minus-odd archimedean term equals
`−(1/2) ∫ g u / cosh(u/2) du` and is `≤ 0`. -/
theorem archimedean_supertrace_autocorrelation {φ : ℝ → ℝ} (hφ : Integrable φ) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∫ u : ℝ, autocorrelation φ u * Real.cos (t * u)) *
        (digamma (1 / 4 + I * t / 2) - digamma (3 / 4 + I * t / 2)).re =
      -(1 / 2) * ∫ u : ℝ, autocorrelation φ u / Real.cosh (u / 2) ∧
    (1 / (2 * Real.pi)) * ∫ t : ℝ, (∫ u : ℝ, autocorrelation φ u * Real.cos (t * u)) *
        (digamma (1 / 4 + I * t / 2) - digamma (3 / 4 + I * t / 2)).re ≤ 0 :=
  ⟨archimedean_supertrace _ (integrable_autocorrelation hφ),
    archimedean_supertrace_nonpos _ (integrable_autocorrelation hφ) fun t ↦ by
      rw [cosTransform_autocorrelation hφ]; positivity⟩

end RiemannMasullo
