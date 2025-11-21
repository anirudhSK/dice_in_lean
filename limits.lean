import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Real

example : Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
  Filter.tendsto_id
