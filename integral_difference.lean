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

lemma int_diff (x y : ℝ) : Phi y - Phi x = ∫ t in x..y, gaussian t := by
  -- Step 1: state that Phi is the limit of finite integrals
  have hPhi_x : Filter.Tendsto (λ R => ∫ t in -R..x, gaussian t) Filter.atTop (nhds (Phi x)) := sorry
  have hPhi_y : Filter.Tendsto (λ R => ∫ t in -R..y, gaussian t) Filter.atTop (nhds (Phi y)) := sorry

  have hdiff : Filter.Tendsto (λ R => (∫ t in -R..y, gaussian t - ∫ t in -R..x, gaussian t))
               Filter.atTop
               (nhds (Phi y - Phi x)) := sorry

  -- Step 2: for any finite R ≥ max(-x,-y), split the integral over adjacent intervals
  have hsplit : ∀ R, R ≥ max (-x) (-y) ->∫ t in -R..y, gaussian t - ∫ t in -R..x, gaussian t = ∫ t in x..y, gaussian t := sorry

  -- Step 3: take the limit R → ∞
  -- for R large enough, the difference is constant, so the limit equals ∫ x..y

  -- pick R large enough
  have hR : (max (-x) (-y)) ≥ max (-x) (-y) := le_refl _

  -- use hsplit to replace the difference of integrals with ∫ x..y
  have hconst : (λ R => ∫ t in -R..y, gaussian t - ∫ t in -R..x, gaussian t) (max (-x) (-y)) = ∫ t in x..y, gaussian t :=
  hsplit _ hR

  have heventually : Filter.Eventually (λ R => (λ R => ∫ t in -R..y, gaussian t - ∫ t in -R..x, gaussian t) R = ∫ t in x..y, gaussian t) Filter.atTop := sorry

  have heq : Filter.EventuallyEq Filter.atTop
                                 (λ R => ∫ t in -R..y, gaussian t - ∫ t in -R..x, gaussian t)
                                 (λ _ => ∫ t in x..y, gaussian t) := sorry

  have hlimit : Filter.Tendsto (λ R => ∫ t in -R..y, gaussian t - ∫ t in -R..x, gaussian t)
                Filter.atTop (nhds (∫ t in x..y, gaussian t)) :=
    Filter.EventuallyEq.tendsto heq
  unfold Phi
👉#search infty.
