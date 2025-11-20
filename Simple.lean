import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Real Topology Interval
open MeasureTheory

noncomputable def gaussian (x : ℝ) : ℝ :=
  Real.exp (-x^2 / 2)

noncomputable def Phi (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, gaussian t

theorem deriv_Phi (x : ℝ) : deriv Phi x = gaussian x := by
  -- continuity of gaussian
  have h_cont : Continuous gaussian := by sorry

  -- measurability of gaussian
  have h_meas : Measurable gaussian := by sorry

  -- integrability on ℝ
  have h_int_univ : Integrable gaussian := by sorry

  -- integrability on Iic x
  have h_int_Iic : IntegrableOn gaussian (Set.Iic x) := by sorry

  -- the FTC: hasDerivAt for the integral with variable upper limit
  have h_deriv :
      HasDerivAt (fun y => ∫ t in Set.Iic y, gaussian t) (gaussian x) x := by
    -- apply the appropriate FTC lemma from IntervalIntegral.FundThmCalculus
    have hFTC :=
      MeasureTheory.hasDerivAt_integral_Iic_of_tendsto_ae
        (f := gaussian)
        (x := x)

  simpa [Phi] using h_deriv.deriv
