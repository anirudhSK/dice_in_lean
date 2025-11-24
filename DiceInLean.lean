import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable def gaussian (x : ℝ) : ℝ :=  Real.exp (-x^2 / 2)

noncomputable def Phi (x : ℝ) : ℝ := ∫ t in Set.Iic x, gaussian t
axiom Phi_zero : Phi 0 = (1 : ℝ) / 2

-----------------
---Gaussian integrability proof
-----------------
open MeasureTheory

def neg_map : ℝ → ℝ := fun x => -x

lemma neg_map_measurable_embedding : MeasurableEmbedding neg_map := by sorry

lemma neg_map_measure_preserving : MeasurePreserving neg_map volume volume := by
  have h_meas : Measurable neg_map := by
    exact neg_map_measurable_embedding.measurable
  have h_map  : Measure.map neg_map volume = volume := by sorry
  exact MeasureTheory.MeasurePreserving.mk h_meas h_map

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
    have h_comp : IntegrableOn ((fun x => Real.exp (-(1 / 2) * x ^ 2)) ∘ neg_map)
                               (neg_map ⁻¹' Set.Iio 0) volume := by
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

  have h_union2 : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2))
                               (Set.Iio 0 ∪ {0} ∪ Set.Ioi 0) volume := by
    exact IntegrableOn.union h_union h_int

  have univ_set_union : Set.Iio 0 ∪ {0} ∪ Set.Ioi 0 = Set.univ := by
    ext x; by_cases hx : x < 0 <;> by_cases hzero : x = 0 <;>
    by_cases hpos : 0 < x <;> simp [hzero]

  have h_univ : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) Set.univ volume := by
    simpa [univ_set_union] using h_union2

  have hfun : (fun x ↦ Real.exp (-(1 / 2) * x ^ 2)) = (fun x ↦ Real.exp (-x ^ 2 / 2)) := by
    funext x
    simp [div_eq_mul_inv, mul_comm]

  unfold gaussian
  rw [<- hfun]
  exact h_univ
--------------------------------

lemma int_diff_Iic (x y : ℝ) : (∫ t in Set.Iic y, gaussian t) - ∫ t in Set.Iic x, gaussian t  =
                                ∫ t in x..y, gaussian t := by
  have hf_total : MeasureTheory.IntegrableOn gaussian (Set.univ : Set ℝ) MeasureTheory.volume := by
    exact gaussian_integrableOn
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

lemma Phi_strictMono : StrictMono Phi := by
  unfold StrictMono
  intros x y hxy
  rw [<- sub_pos]
  rw [int_diff x y]
  have hcont : Continuous gaussian := by
    have h_inner : Continuous fun (t : ℝ)  => -(t ^ 2) / 2 := by
      exact ((continuous_id.pow 2).neg).div_const 2
    exact Real.continuous_exp.comp h_inner
  have hpos : ∀ t ∈ Set.Ioc x y, 0 <= gaussian t := by
    intros t ht
    unfold gaussian
    exact le_of_lt (Real.exp_pos _)
  have hex : ∃ c ∈ Set.Icc x y, 0 < gaussian c := by
    use x
    constructor
    · exact Set.left_mem_Icc.mpr (le_of_lt hxy)
    · unfold gaussian
      exact Real.exp_pos _
  exact intervalIntegral.integral_pos hxy hcont.continuousOn hpos hex


/-- The pairwise comparison probability for two independent normals
    A ~ N(μ₁, σ₁^2), B ~ N(μ₂, σ₂^2) (σ₁, σ₂ > 0). -/
noncomputable def Pgauss (Phi : ℝ -> ℝ) (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ :=
  Phi ((μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2))

/-- Helper: from Φ(x) > Φ(0) and StrictMono Φ deduce x > 0. -/
theorem arg_pos_of_Phi_gt_zero {x : ℝ}
  (h : Phi x > Phi 0) (hmono : StrictMono Phi) : x > 0 := by
    by_contra hneg
    -- hneg : ¬ (x > 0), equivalently x ≤ 0
    have hx : x ≤ 0 := le_of_not_gt hneg
    have hphi_le : Phi x ≤ Phi 0 := hmono.monotone hx
    linarith

/-- The core scalar lemma used by the paper:
    if Pgauss μ₁ μ₂ σ₁ σ₂ > 1/2 then μ₁ > μ₂ (assuming σ₁,σ₂ > 0). -/
theorem mean_gt_of_prob_gt_half
  {μ₁ μ₂ σ₁ σ₂ : ℝ}
  (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
  (h : Pgauss Phi μ₁ μ₂ σ₁ σ₂ > 1 / 2) :
  μ₁ > μ₂ := by
  -- unfold the definition and apply monotonicity of Phi
  unfold Pgauss at h
  have denom_pos : 0 < Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) := by
    have h1 : 0 < σ₁ * σ₁ := mul_pos hσ₁ hσ₁
    have h2 : 0 < σ₂ * σ₂ := mul_pos hσ₂ hσ₂
    have hsum : 0 < σ₁ * σ₁ + σ₂ * σ₂ := add_pos h1 h2
    have hsum_pow : 0 < σ₁ ^ 2 + σ₂ ^ 2 := by
      simpa [pow_two] using hsum
    exact (Real.sqrt_pos).mpr hsum_pow
  have hard : μ₁ > μ₂ := by
    -- from h : Phi ((μ₁ - μ₂) / denom) > 1/2 and Phi 0 = 1/2 we get Phi (...) > Phi 0
    have hphi : Phi ((μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) > Phi 0 := by
      rw [← Phi_zero] at h
      exact h
    -- strict monotonicity gives the argument > 0
    have h_inter : (μ₁ - μ₂) / √(σ₁ ^ 2 + σ₂ ^ 2) > 0 := by
      exact arg_pos_of_Phi_gt_zero (hmono := Phi_strictMono)
                                   (x := (μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) (h := hphi)
    -- multiply both sides by denom > 0 to get μ₁ - μ₂ > 0
    have mulpos := mul_pos h_inter denom_pos
    have denom_ne : Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) ≠ 0 := ne_of_gt denom_pos
    have : ((μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) * Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) = μ₁ - μ₂ := by
      field_simp [denom_ne]
    rw [this] at mulpos
    -- add μ₂ to both sides to turn μ₁ - μ₂ > 0 into μ₁ > μ₂
    simpa [sub_add_cancel] using add_lt_add_right mulpos μ₂
  exact hard

/-- Main proposition (Appendix A):
    for independent normal random variables X ~ N(μ1, σ1^2), Y ~ N(μ2, σ2^2),
    Z ~ N(μ3, σ3^2) with positive σ's,
    the preference relation defined by P(X>Y) > 1/2 is transitive. -/
theorem gauss_transitivity
  {μ₁ μ₂ μ₃ σ₁ σ₂ σ₃ : ℝ}
  (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hσ₃ : 0 < σ₃)
  (h12 : Pgauss Phi μ₁ μ₂ σ₁ σ₂ > 1 / 2)
  (h23 : Pgauss Phi μ₂ μ₃ σ₂ σ₃ > 1 / 2) :
  Pgauss Phi μ₁ μ₃ σ₁ σ₃ > 1/2 := by
  have μ₁_gt_μ₂ := mean_gt_of_prob_gt_half hσ₁ hσ₂ h12
  have μ₂_gt_μ₃ := mean_gt_of_prob_gt_half hσ₂ hσ₃ h23
  -- means are reals, so transitivity gives μ₁ > μ₃
  have μ₁_gt_μ₃ : μ₁ > μ₃ := by linarith [μ₁_gt_μ₂, μ₂_gt_μ₃]
  -- convert back to probability statement
  have denom_pos : 0 < Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : σ₁ ^ 2 + σ₃ ^ 2 > 0 := by
      have h1 := pow_pos hσ₁ 2
      have h3 := pow_pos hσ₃ 2
      linarith
    exact this
  have argpos : (μ₁ - μ₃) / Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2) > 0 := by
        -- μ₁ > μ₃  ⟹  μ₁ - μ₃ > 0
    have diff_pos : μ₁ - μ₃ > 0 := sub_pos.mpr μ₁_gt_μ₃
    -- divide two positive numbers
    exact div_pos diff_pos denom_pos
  -- apply monotonicity of Phi to get the final result
  have phi_monotonic := Phi_strictMono
  have hphi : Phi ((μ₁ - μ₃) / Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2)) > Phi 0 := by
    exact phi_monotonic (a := 0)
                        (b := ((μ₁ - μ₃) / Real.sqrt (σ₁ ^ 2 + σ₃ ^ 2)))
                        argpos
  simp [Phi_zero] at hphi
  simpa [Pgauss] using hphi
