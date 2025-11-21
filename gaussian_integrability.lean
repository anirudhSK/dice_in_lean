import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (- x^2 / 2)

open MeasureTheory
theorem gaussian_integrableOn : IntegrableOn gaussian (Set.univ : Set ℝ) volume := by
  have hb : 0 < (1 / 2 : ℝ) := by norm_num
  -- integrable on (0, ∞)
  have h_int : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) (Set.Ioi 0) volume:= by
     exact (integrableOn_Ioi_exp_neg_mul_sq_iff).mpr hb
  -- this gives integrability on the set Ioi 0; but our function is even, so we can extend to all ℝ
  -- integrable on (-∞, 0) by change of variable x ↦ -x
  have h_neg : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) (Set.Iio 0) := by sorry

    -- integrable on {0} trivially
  have h0 : IntegrableOn (fun x => Real.exp (-(1/2) * x^2)) {0} volume := sorry

  -- combine all three parts
  have h_union : Set.Iio 0 ∪ {0} ∪ Set.Ioi 0 = Set.univ := by sorry
  sorry
