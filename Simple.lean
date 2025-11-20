import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Basic
import Mathlib.Order.Filter

open scoped Real Topology Interval
open MeasureTheory

noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (-x^2 / 2)

noncomputable def Phi (x : ℝ) : ℝ := ∫ t in Set.Iic x, gaussian t

theorem deriv_Phi (x : ℝ) : deriv Phi x = gaussian x := by
  have h_cont : Continuous gaussian := by sorry
  have h_meas : Measurable gaussian := by sorry
  have h_int_univ : Integrable gaussian := by sorry
  have h_finite_deriv : ∀ a, HasDerivAt (fun y => ∫ t in a..y, gaussian t) (gaussian x) x := by sorry
  have h_deriv : HasDerivAt Phi (gaussian x) x := by
    have h_lim : Tendsto (fun a => ∫ t in a..x, gaussian t) atBot (𝓝 (∫ t in (−∞ : ℝ)..x, gaussian t)) :=
  simpa [Phi] using h_deriv.deriv
