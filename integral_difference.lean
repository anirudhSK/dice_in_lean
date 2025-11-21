import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Real
noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (-x^2 / 2)
noncomputable def Phi (x : ℝ) : ℝ := ∫ t in Set.Iic x, gaussian t

lemma int_diff_Iic (x y : ℝ) : (∫ t in Set.Iic y, gaussian t) - ∫ t in Set.Iic x, gaussian t  = ∫ t in x..y, gaussian t := by
  have hf_total : MeasureTheory.IntegrableOn gaussian (Set.univ : Set ℝ) MeasureTheory.volume := by sorry

  have hx : MeasureTheory.IntegrableOn gaussian (Set.Iic x) MeasureTheory.volume :=
    MeasureTheory.IntegrableOn.mono_set hf_total (Set.subset_univ (Set.Iic x))
  have hy : MeasureTheory.IntegrableOn gaussian (Set.Iic y) MeasureTheory.volume :=
    MeasureTheory.IntegrableOn.mono_set hf_total (Set.subset_univ (Set.Iic y))
  have h_interval :
    (∫ t in Set.Iic y, gaussian t) - ∫ t in Set.Iic x, gaussian t = ∫ t in x..y, gaussian t :=
    intervalIntegral.integral_Iic_sub_Iic hx hy
  exact h_interval

-- Step 2: Define a convenient lemma using Phi
lemma int_diff (x y : ℝ) :
    Phi y - Phi x = ∫ t in x..y, gaussian t := by
  unfold Phi
  exact (int_diff_Iic x y)
