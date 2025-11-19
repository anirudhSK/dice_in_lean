import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

-- Axiomatize the two properties of the standard normal CDF used in the paper.
variable (Phi : ℝ → ℝ)

noncomputable def Phi_int (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, Real.exp (-t^2 / 2)

-- First, prove the integrand is positive
lemma exp_neg_sq_pos (t : ℝ) : 0 < Real.exp (-t^2 / 2) := by
  apply Real.exp_pos

axiom Phi_strictMono : StrictMono Phi
axiom Phi_zero : Phi 0 = (1 : ℝ) / 2

/-- The pairwise comparison probability for two independent normals
    A ~ N(μ₁, σ₁^2), B ~ N(μ₂, σ₂^2) (σ₁, σ₂ > 0). -/
noncomputable def Pgauss (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ :=
  Phi ((μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2))

/-- Helper: from Φ(x) > Φ(0) and StrictMono Φ deduce x > 0. -/
theorem arg_pos_of_Phi_gt_zero {x : ℝ}
  (h : Phi x > Phi 0) (hmono : StrictMono Phi) : x > 0 := by
    by_contra hneg
    -- hneg : ¬ (x > 0), equivalently x ≤ 0
    have hx : x ≤ 0 := le_of_not_gt hneg
    have hphi_le : Phi x ≤ Phi 0 := hmono.monotone hx
    linarith

/-- The core scalar lemma used by the paper:
    if Pgauss μ₁ μ₂ σ₁ σ₂ > 1/2 then μ₁ > μ₂ (assuming σ₁,σ₂ > 0). -/
theorem mean_gt_of_prob_gt_half
  {μ₁ μ₂ σ₁ σ₂ : ℝ}
  (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
  (h : Pgauss Phi μ₁ μ₂ σ₁ σ₂ > 1 / 2) :
  μ₁ > μ₂ := by
  -- unfold the definition and apply monotonicity of Phi
  unfold Pgauss at h
  have denom_pos : 0 < Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) := by
    have h1 : 0 < σ₁ * σ₁ := mul_pos hσ₁ hσ₁
    have h2 : 0 < σ₂ * σ₂ := mul_pos hσ₂ hσ₂
    have hsum : 0 < σ₁ * σ₁ + σ₂ * σ₂ := add_pos h1 h2
    have hsum_pow : 0 < σ₁ ^ 2 + σ₂ ^ 2 := by
      simpa [pow_two] using hsum
    exact (Real.sqrt_pos).mpr hsum_pow
  have hard : μ₁ > μ₂ := by
    -- from h : Phi ((μ₁ - μ₂) / denom) > 1/2 and Phi 0 = 1/2 we get Phi (...) > Phi 0
    have hphi : Phi ((μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) > Phi 0 := by
      rw [← Phi_zero] at h
      exact h
    -- strict monotonicity gives the argument > 0
    have h_inter : (μ₁ - μ₂) / √(σ₁ ^ 2 + σ₂ ^ 2) > 0 := by
      exact arg_pos_of_Phi_gt_zero (Phi := Phi) (hmono := Phi_strictMono Phi)
                                   (x := (μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) (h := hphi)
    -- multiply both sides by denom > 0 to get μ₁ - μ₂ > 0
    have mulpos := mul_pos h_inter denom_pos
    have denom_ne : Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) ≠ 0 := ne_of_gt denom_pos
    have : ((μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) * Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) = μ₁ - μ₂ := by
      field_simp [denom_ne]
    rw [this] at mulpos
    -- add μ₂ to both sides to turn μ₁ - μ₂ > 0 into μ₁ > μ₂
    simpa [sub_add_cancel] using add_lt_add_right mulpos μ₂
  exact hard

/-- Main proposition (Appendix A):
    for independent normal random variables X ~ N(μ1, σ1^2), Y ~ N(μ2, σ2^2),
    Z ~ N(μ3, σ3^2) with positive σ's,
    the preference relation defined by P(X>Y) > 1/2 is transitive. -/
theorem gauss_transitivity
  {μ₁ μ₂ μ₃ σ₁ σ₂ σ₃ : ℝ}
  (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hσ₃ : 0 < σ₃)
  (h12 : Pgauss Phi μ₁ μ₂ σ₁ σ₂ > 1 / 2)
  (h23 : Pgauss Phi μ₂ μ₃ σ₂ σ₃ > 1 / 2) :
  Pgauss Phi μ₁ μ₃ σ₁ σ₃ > 1/2 := by
  have μ₁_gt_μ₂ := mean_gt_of_prob_gt_half Phi hσ₁ hσ₂ h12
  have μ₂_gt_μ₃ := mean_gt_of_prob_gt_half Phi hσ₂ hσ₃ h23
  -- means are reals, so transitivity gives μ₁ > μ₃
  have μ₁_gt_μ₃ : μ₁ > μ₃ := by linarith [μ₁_gt_μ₂, μ₂_gt_μ₃]
  -- convert back to probability statement
  have denom_pos : 0 < Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : σ₁ ^ 2 + σ₃ ^ 2 > 0 := by
      have h1 := pow_pos hσ₁ 2
      have h3 := pow_pos hσ₃ 2
      linarith
    exact this
  have argpos : (μ₁ - μ₃) / Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2) > 0 := by
        -- μ₁ > μ₃  ⟹  μ₁ - μ₃ > 0
    have diff_pos : μ₁ - μ₃ > 0 := sub_pos.mpr μ₁_gt_μ₃
    -- divide two positive numbers
    exact div_pos diff_pos denom_pos
  -- apply monotonicity of Phi to get the final result
  have phi_monotonic := Phi_strictMono Phi
  have hphi : Phi ((μ₁ - μ₃) / Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2)) > Phi 0 := by
    exact phi_monotonic (a := 0)
                        (b := ((μ₁ - μ₃) / Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2)))
                        argpos
  simp [Phi_zero] at hphi
  simpa [Pgauss] using hphi
