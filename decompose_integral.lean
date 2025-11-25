import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-- Standard Gaussian function used in examples. -/
noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (-(x^2 : ℝ))

/-- Decomposition of the real line into three disjoint pieces. -/
lemma real_univ_split : (Set.univ : Set ℝ) = Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ) := by
  ext x
  simp

theorem integral_split_three :
∫ x, gaussian x = (∫ x in Set.Iio (0 : ℝ), gaussian x) + (∫ x in ({0} : Set ℝ), gaussian x) + (∫ x in Set.Ioi (0 : ℝ), gaussian x) := by
  have hsplit : (Set.univ : Set ℝ) = Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ) := real_univ_split
  calc
    ∫ x, gaussian x
       = ∫ x in (Set.univ : Set ℝ), gaussian x := by
          simp
    _ = ∫ x in Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ), gaussian x := by
          simp
    _ = ∫ x in Set.Iio (0 : ℝ) ∪ (({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ)), gaussian x := by
          rw [Set.union_assoc]
    _ = ∫ x in Set.Iio (0 : ℝ), gaussian x + ∫ x in ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ), gaussian x := by
          have h_disj : Disjoint (Set.Iio (0 : ℝ)) (({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ)) := by sorry
          have ht : MeasurableSet (({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ)) := by sorry
          have h_integrable1 : MeasureTheory.IntegrableOn gaussian (Set.Iio (0 : ℝ)) MeasureTheory.volume := by sorry
          have h_integrable2 : MeasureTheory.IntegrableOn gaussian (({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ)) MeasureTheory.volume := by sorry
          convert MeasureTheory.setIntegral_union h_disj ht h_integrable1 h_integrable2
          have : ∫ x in Set.Iio 0, gaussian x = ∫ x in Set.Iio 0, gaussian x ∂MeasureTheory.volume := by rfl
          rw [<- this]
          have : ∫ x in ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ), gaussian x = ∫ x in ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ), gaussian x ∂MeasureTheory.volume := by rfl
          rw [<- this]
          simp


    _ = ∫ x in Set.Iio (0 : ℝ), gaussian x + (∫ x in ({0} : Set ℝ), gaussian x + ∫ x in Set.Ioi (0 : ℝ), gaussian x) := by sorry
    _ = (∫ x in Set.Iio (0 : ℝ), gaussian x) + (∫ x in ({0} : Set ℝ), gaussian x) + (∫ x in Set.Ioi (0 : ℝ), gaussian x) := by sorry
