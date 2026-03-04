import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable def gaussian (x : ℝ) : ℝ := (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-x^2 / 2)

noncomputable def Phi (x : ℝ) : ℝ := ∫ t in Set.Iic x, gaussian t

open MeasureTheory

-----------------
---Gaussian integrability proof
-----------------
def neg_map : ℝ → ℝ := fun x => -x

lemma neg_map_measurable_embedding : MeasurableEmbedding neg_map := by
  have h_inj : Function.Injective neg_map := by
    intro x y hxy
    simp [neg_map] at hxy
    linarith
  have h_meas : Measurable neg_map := by
    apply measurable_neg
  have h_preimage : ∀ t, MeasurableSet t → MeasurableSet (neg_map '' t) := by
    intro t ht
    simpa [neg_map] using (measurable_neg ht)
  exact MeasurableEmbedding.mk h_inj h_meas h_preimage

lemma neg_map_measure_preserving : MeasurePreserving neg_map volume volume := by
  have h_meas : Measurable neg_map := by
    apply measurable_neg
  have h_map  : Measure.map neg_map volume = volume :=
    Measure.map_neg_eq_self (μ := volume)
  exact MeasureTheory.MeasurePreserving.mk h_meas h_map

lemma helper1 :
  (fun x ↦ (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2)) ∘ neg_map
    = fun x ↦ (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2) := by
  funext x
  simp [neg_map]

lemma helper2 :
  neg_map ⁻¹' Set.Iio 0 = Set.Ioi 0 := by
  ext x
  simp [neg_map, Set.Iio, Set.Ioi]

theorem gaussian_integrableOn : IntegrableOn gaussian (Set.univ : Set ℝ) volume := by
  have hb : 0 < (1 / 2 : ℝ) := by norm_num
  -- integrable on (0, ∞)
  have h_int : IntegrableOn (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2))
               (Set.Ioi 0) volume:= by
    have h_exp : IntegrableOn (fun x => Real.exp (-(1 / 2) * x ^ 2)) (Set.Ioi 0) volume :=
      (integrableOn_Ioi_exp_neg_mul_sq_iff).mpr hb
    -- multiply by the constant
    exact h_exp.const_mul (1 / Real.sqrt (2 * Real.pi))
  -- this gives integrability on the set Ioi 0; but our function is even, so we can extend to all ℝ
  -- integrable on (-∞, 0) by change of variable x ↦ -x
  have h_neg : IntegrableOn (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2))
               (Set.Iio 0) volume := by
    have h_comp : IntegrableOn
                  ((fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2)) ∘neg_map)
                  (neg_map ⁻¹' Set.Iio 0) volume := by
      rw [helper1, helper2]
      exact h_int
    exact (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
           neg_map_measure_preserving
           neg_map_measurable_embedding).mp h_comp

    -- integrable on {0} trivially
  have h0 : IntegrableOn (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1/2) * x^2))
                         {0} volume := by
    apply integrableOn_singleton
    · dsimp only
      simp
      simp only [ENNReal.mul_eq_top, not_or]
      constructor
      · -- ¬(‖(√π)⁻¹‖ₑ = ⊤ ∧ ‖√2‖ₑ⁻¹ ≠ 0)
        simp
      · -- ¬(‖(√π)⁻¹‖ₑ ≠ 0 ∧ ‖√2‖ₑ⁻¹ = ⊤)
        simp
    · simp

  have h_union : IntegrableOn
                 (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2))
                 (Set.Iio 0 ∪ {0}) volume := by
    exact IntegrableOn.union h_neg h0

  have h_union2 : IntegrableOn
                  (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2))
                  (Set.Iio 0 ∪ {0} ∪ Set.Ioi 0) volume := by
    exact IntegrableOn.union h_union h_int

  have univ_set_union : Set.Iio 0 ∪ {0} ∪ Set.Ioi 0 = Set.univ := by
    ext x; by_cases hx : x < 0 <;> by_cases hzero : x = 0 <;>
    by_cases hpos : 0 < x <;> simp [hzero]

  have h_univ : IntegrableOn (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2))
                Set.univ volume := by
    simpa [univ_set_union] using h_union2

  unfold gaussian
    -- Prove the functions are equal
  have : (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-x ^ 2 / 2)) =
         (fun x => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 2) * x ^ 2)) := by
    ext x
    congr 1
    ring
  rw [this]
  exact h_univ
-------------------------end of gaussian integrability proof-------------------------

-------- Prove that Phi(0) = 1/2 --------
lemma gaussian_even (x : ℝ) : gaussian (-x) = gaussian x := by
  unfold gaussian
  have : (-x)^2 = x^2 := by ring
  simp [this]

lemma integral_gaussian_total : ∫ x : ℝ, gaussian x = 1 := by
  simp only [gaussian]
  have h := integral_gaussian (1/2)
  -- Go from Integral k * x  to k * Integral x
  rw [integral_const_mul]
  -- prove that  ∫ (x : ℝ), Real.exp (-(1 / 2) * x ^ 2) = ∫ (a : ℝ), Real.exp (-a ^ 2 / 2)
  have h_func : (fun x => Real.exp (-(1 / 2) * x ^ 2)) = (fun a => Real.exp (-a ^ 2 / 2)) := by
    funext x
    congr 1
    ring
  rw [h_func] at h
  rw [h]
  -- simplify the constants
  field_simp

lemma integral_left_eq_integral_right :
  (∫ t in Set.Iic (0 : ℝ), (gaussian t : ℝ))
    = (∫ t in Set.Ici (0 : ℝ), (gaussian t : ℝ)) := by
    -- Preimage relation
    have h_pre : neg_map ⁻¹' Set.Iic 0 = Set.Ici 0 := by
      ext x; simp [neg_map, Set.Iic, Set.Ici]

    -- Step 1: Transform the integral using measure-preserving property
    -- ∫_{(-∞,0]} f = ∫_{[0,∞)} f∘neg_map
    have h_transform : (∫ t in Set.Iic 0, gaussian t) =
                        ∫ t in Set.Ici 0, (gaussian ∘ neg_map) t := by
      -- First, use measure preserving to rewrite LHS with mapped measure
      have step1 : (∫ t in Set.Iic 0, gaussian t) =
                   ∫ t in Set.Iic 0, gaussian t ∂(Measure.map neg_map volume) := by
          rw [neg_map_measure_preserving.map_eq]

      -- Prepare integrability condition
      have h_integrable : AEStronglyMeasurable gaussian (Measure.map neg_map volume) := by
        rw [neg_map_measure_preserving.map_eq]
        have h' : Integrable gaussian volume := by
         simpa [IntegrableOn] using gaussian_integrableOn
        exact h'.aestronglyMeasurable

      -- Prepare measurability condition
      have h_aemeas : AEMeasurable neg_map volume := by
        exact neg_map_measurable_embedding.measurable.aemeasurable

      -- Apply setIntegral_map
      have step2 : ∫ t in Set.Iic 0, gaussian t ∂(Measure.map neg_map volume) =
                   ∫ t in neg_map ⁻¹' Set.Iic 0, (gaussian ∘ neg_map) t := by
        rw [MeasureTheory.setIntegral_map measurableSet_Iic h_integrable h_aemeas]
        rfl

      -- Use preimage relation
      have step3 : ∫ t in neg_map ⁻¹' Set.Iic 0, (gaussian ∘ neg_map) t =
               ∫ t in Set.Ici 0, (gaussian ∘ neg_map) t := by rw [h_pre]

      -- Chain them together
      rw [step1, step2, step3]

    -- Step 2: Simplify gaussian ∘ neg_map to just gaussian using evenness
    rw [h_transform]
    congr 1
    ext t
    simp only [Function.comp, neg_map]
    exact gaussian_even t

lemma integral_left_half :
  (∫ t in Set.Iic (0 : ℝ), gaussian t) = 1/2 := by
   have h_split :
    ∫ x : ℝ, gaussian x =
    (∫ t in Set.Iic (0 : ℝ), gaussian t) + (∫ t in Set.Ici (0 : ℝ), gaussian t) := by
      have h_univ : ∫ x : ℝ, gaussian x = ∫ x in Set.univ, gaussian x := by simp
      rw [h_univ]
      have univ_split : Set.univ = Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ) := by
        ext x
        simp
      rw [univ_split]
      have hst : AEDisjoint volume (Set.Iic (0 : ℝ)) (Set.Ici (0 : ℝ)) := by
        simp [AEDisjoint, Set.Iic, Set.Ici]
        have null_inter : ({ x : ℝ | x ≤ 0 } ∩ { x : ℝ | 0 ≤ x }) = {0} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_setOf, Set.mem_singleton_iff, le_antisymm_iff]
        rw [null_inter]
        simp

      have ht : NullMeasurableSet  (Set.Ici (0 : ℝ)) :=
        ⟨Set.Ici (0 : ℝ), measurableSet_Ici, by simp⟩

      have hfs : IntegrableOn gaussian (Set.Iic (0 : ℝ)) volume := by
        have h' : Integrable gaussian volume := by
          simpa [IntegrableOn] using gaussian_integrableOn
        exact (Integrable.integrableOn h' (s := Set.Iic 0)  (μ := volume))


      have hft : IntegrableOn gaussian (Set.Ici (0 : ℝ)) volume := by
        have h' : Integrable gaussian volume := by
          simpa [IntegrableOn] using gaussian_integrableOn
        exact (Integrable.integrableOn h' (s := Set.Ici 0)  (μ := volume))

      rw [MeasureTheory.integral_union_ae hst ht hfs hft]
   rw [<- integral_left_eq_integral_right] at h_split
   have h2 : (∫ t in Set.Iic 0, gaussian t) + (∫ t in Set.Iic 0, gaussian t)
          = 2 * ∫ t in Set.Iic 0, gaussian t := by ring
   rw [h2] at h_split
   rw [mul_comm] at h_split
   rw [integral_gaussian_total] at h_split
   have : (∫ t in Set.Iic 0, gaussian t) = 1 / 2 := by
     field_simp at h_split
     linarith
   exact this

lemma Phi_zero : Phi 0 = (1 : ℝ) / 2 := by
  unfold Phi
  simpa using integral_left_half
-------- End of Phi(0) = 1/2 proof --------

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
    -- exp is continuous, compose with the inner function
    have h_exp : Continuous fun (t : ℝ) => Real.exp (-t ^ 2 / 2) := by
      exact Real.continuous_exp.comp h_inner
    -- multiply by the constant (1 / √(2π))
    have h_const : Continuous fun (t : ℝ) => (1 / Real.sqrt (2 * Real.pi)) := by
      exact continuous_const
    exact Continuous.mul h_const h_exp
  have hpos : ∀ t ∈ Set.Ioc x y, 0 <= gaussian t := by
    intros t ht
    unfold gaussian
    apply mul_nonneg
    · apply div_nonneg
      · exact zero_le_one
      · simp
    · exact le_of_lt (Real.exp_pos _)
  have hex : ∃ c ∈ Set.Icc x y, 0 < gaussian c := by
    use x
    constructor
    · exact Set.left_mem_Icc.mpr (le_of_lt hxy)
    · unfold gaussian
      apply mul_pos
      --prove that 1/√(2π) > 0
      · apply div_pos
        · exact zero_lt_one
        · simp [Real.pi_pos]
      · exact Real.exp_pos _
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
    if Pgauss μ₁ μ₂ σ₁ σ₂ > p then μ₁ - μ₂ > c * (Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) (assuming σ₁,σ₂ > 0). -/
theorem mean_gt_of_prob_gt_half
  {p : ℝ}
  {c : ℝ} (hc : Phi c = p)
  {μ₁ μ₂ σ₁ σ₂ : ℝ}
  (hp1 : (1/2 : ℝ) < p) (hp2 : p < 1)
  (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
  (h : Pgauss Phi μ₁ μ₂ σ₁ σ₂ > p) :
  μ₁ - μ₂ > c * (Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) := by
  -- unfold the definition and apply monotonicity of Phi
  unfold Pgauss at h
  have denom_pos : 0 < Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) := by
    have h1 : 0 < σ₁ * σ₁ := mul_pos hσ₁ hσ₁
    have h2 : 0 < σ₂ * σ₂ := mul_pos hσ₂ hσ₂
    have hsum : 0 < σ₁ * σ₁ + σ₂ * σ₂ := add_pos h1 h2
    have hsum_pow : 0 < σ₁ ^ 2 + σ₂ ^ 2 := by
      simpa [pow_two] using hsum
    exact (Real.sqrt_pos).mpr hsum_pow
  have hard : μ₁ - μ₂ > c * (Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) := by
    -- from h : Phi ((μ₁ - μ₂) / denom) > p and Phi c = p we get Phi (...) > Phi 0
    have hphi : Phi ((μ₁ - μ₂) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) > Phi c := by
      rw [← hc] at h
      exact h
    -- strict monotonicity gives the argument > 0
    have h_inter : (μ₁ - μ₂) / √(σ₁ ^ 2 + σ₂ ^ 2) > Phi c := by
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
    the preference relation defined by P(X>Y) > p is transitive. -/
theorem gauss_transitivity
  {p : ℝ} (hp1 : (1/2 : ℝ) < p) (hp2 : p < 1)
  {c : ℝ} (hc : Phi c = p) -- TODO: need to move this into proof.
  {μ₁ μ₂ μ₃ σ₁ σ₂ σ₃ : ℝ}
  (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hσ₃ : 0 < σ₃)
  (h12 : Pgauss Phi μ₁ μ₂ σ₁ σ₂ > p)
  (h23 : Pgauss Phi μ₂ μ₃ σ₂ σ₃ > p) :
  Pgauss Phi μ₁ μ₃ σ₁ σ₃ > p := by
  have μ₁_gt_μ₂ := mean_gt_of_prob_gt_half hc hp1 hp2 hσ₁ hσ₂ h12
  have μ₂_gt_μ₃ := mean_gt_of_prob_gt_half hc hp1 hp2 hσ₂ hσ₃ h23
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

#print axioms gauss_transitivity
