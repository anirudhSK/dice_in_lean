import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (- x^2 / 2)

open MeasureTheory
theorem gaussian_integrableOn : IntegrableOn gaussian (Set.univ : Set ℝ) volume := by sorry
