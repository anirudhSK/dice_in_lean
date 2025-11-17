import Mathlib.Data.Real.Basic

def hello := "world123"
#eval IO.println s!"DiceInLean: {hello}"

/-- Simple alias for demonstration: treat Float as Real here. -/
abbrev Realf := Float

theorem real_eq_self (r : Realf) : r = r := rfl
