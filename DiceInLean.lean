import Mathlib.Data.Real.Basic

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
