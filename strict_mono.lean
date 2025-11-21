import Mathlib.Data.Real.Basic

example : StrictMono (fun x : ℝ => x) :=
by
  intro x y hxy
  exact hxy
