import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable def gaussian (x : ℝ) : ℝ :=
  Real.exp (-x^2 / 2)

noncomputable def Phi (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, gaussian t

lemma int_diff (x y : ℝ) : Phi x - Phi y = ∫ t in x..y, gaussian t := by sorry
