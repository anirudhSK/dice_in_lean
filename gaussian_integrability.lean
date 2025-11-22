import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (- x^2 / 2)

open MeasureTheory

def neg_map : ℝ → ℝ := fun x => -x

lemma neg_map_measurable_embedding : MeasurableEmbedding neg_map := by sorry

lemma neg_map_measure_preserving : MeasurePreserving neg_map volume volume := by sorry

lemma helper1 :
  (fun x ↦ Real.exp (-(1 / 2) * x ^ 2)) ∘ neg_map
    = fun x ↦ Real.exp (-(1 / 2) * x ^ 2) := by
  funext x
  simp [neg_map]

lemma helper2 :
  neg_map ⁻¹' Set.Iio 0 = Set.Ioi 0 := by
  ext x
  simp [neg_map, Set.Iio, Set.Ioi]

theorem gaussian_integrableOn : IntegrableOn gaussian (Set.univ : Set ℝ) volume := by
  have hb : 0 < (1 / 2 : ℝ) := by norm_num
  -- integrable on (0, ∞)
  have h_int : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) (Set.Ioi 0) volume:= by
    exact (integrableOn_Ioi_exp_neg_mul_sq_iff).mpr hb
  -- this gives integrability on the set Ioi 0; but our function is even, so we can extend to all ℝ
  -- integrable on (-∞, 0) by change of variable x ↦ -x
  have h_neg : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) (Set.Iio 0) volume := by
    have h_comp : IntegrableOn ((fun x => Real.exp (-(1 / 2) * x ^ 2)) ∘ neg_map) (neg_map ⁻¹' Set.Iio 0) volume := by
      rw [helper1, helper2]
      exact h_int
    exact (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
           neg_map_measure_preserving
           neg_map_measurable_embedding).mp h_comp

    -- integrable on {0} trivially
  have h0 : IntegrableOn (fun x => Real.exp (-(1/2) * x^2)) {0} volume := by
    apply integrableOn_singleton
    · dsimp only
      simp
    · simpa using measure_singleton

  have h_union : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) (Set.Iio 0 ∪ {0}) volume := by
    exact IntegrableOn.union h_neg h0

  have h_union2 : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) (Set.Iio 0 ∪ {0} ∪ Set.Ioi 0) volume := by
    exact IntegrableOn.union h_union h_int

  have univ_set_union : Set.Iio 0 ∪ {0} ∪ Set.Ioi 0 = Set.univ := by
    ext x; by_cases hx : x < 0 <;> by_cases hzero : x = 0 <;> by_cases hpos : 0 < x <;> simp [hx, hzero, hpos, lt_of_le_of_ne]

  have h_univ : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) Set.univ volume := by
    simpa [univ_set_union] using h_union2

  have hfun : (fun x ↦ Real.exp (-(1 / 2) * x ^ 2)) = (fun x ↦ Real.exp (-x ^ 2 / 2)) := by
    funext x
    simp [div_eq_mul_inv, mul_comm]

  unfold gaussian
  rw [<- hfun]
  exact h_univ
