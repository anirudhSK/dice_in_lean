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
    A ~ N(μA, σA^2), B ~ N(μB, σB^2) (σA, σB > 0). -/
noncomputable def Pgauss (μA μB σA σB : ℝ) : ℝ :=
  Phi ((μA - μB) / Real.sqrt (σA ^ 2 + σB ^ 2))
