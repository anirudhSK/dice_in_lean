import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

def hello := "world123"
#eval IO.println s!"DiceInLean: {hello}"

/-- Simple alias for demonstration: treat Float as Real here. -/
abbrev Realf := Float

theorem real_eq_self (r : Realf) : r = r := rfl

theorem real_eq_self_mathlib (r : Real) : r = r := rfl

theorem real_le_antisymm {x y : Real} (hxy : x ≤ y) (hyx : y ≤ x) : x = y :=
  le_antisymm hxy hyx

theorem real_le_antisymm_interactive {x y : Real} (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  apply le_antisymm
  · exact hxy
  · exact hyx

-- Axiomatize the two properties of the standard normal CDF used in the paper.
variable (Phi : ℝ → ℝ)

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
  (h : Pgauss Phi μ₁ μ₂ σ₁ σ₂ > 1/2) :
  μ₁ > μ₂ := by sorry
