/-
EOI.lean
Economic Order Interval (EOI) heuristic verification
Lean 4 skeleton version
Author: Ieva Daukantas et al.
2025 November 30
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace EOI
noncomputable section

/-- Parameters of the model.
`s.setupCost` = fixed cost per order `s`,
`s.holdingCost` = holding cost rate `h` per unit per period,
`s.demands` = list of period demands `(d₁, …, dₙ)`. -/
structure Problem where
  setupCost   : ℝ
  holdingCost : ℝ
  demands     : List ℝ

/-- Length of the planning horizon `n` (number of periods). -/
def horizon (P : Problem) : ℕ :=
  P.demands.length

/-- Average demand per period
  \bar d = (1/n) * Σ d_t, or 0 if the horizon is empty. -/
def avgDemand (P : Problem) : ℝ :=
  if h : P.demands ≠ [] then
    (P.demands.foldl (· + ·) 0) / (P.demands.length : ℝ)
  else 0

/-- Continuous Economic Order Interval (EOI) formula
  τ* = sqrt( 2 s / (h * \bar d) ). -/
def eoi (P : Problem) : ℝ :=
  Real.sqrt (2 * P.setupCost / (P.holdingCost * avgDemand P))

/-- A simple correctness predicate: an interval `τ` (in periods) is
within the horizon and within `ε` (tolerance) of the EOI heuristic value. -/
def satisfiesEOI (P : Problem) (interval ε : ℝ) : Prop :=
  0 < interval ∧ interval ≤ (P.demands.length : ℝ) ∧ abs (interval - eoi P) ≤ ε


/-- Example instance -/
def exampleProblem : Problem :=
  { setupCost := 500,
    holdingCost := 2,
    demands := [100, 200, 150, 250] }


theorem example_demands_length_coe : (exampleProblem.demands.length : ℝ) = 4 := by
  dsimp [exampleProblem]

theorem example_satisfiesEOI : satisfiesEOI exampleProblem (eoi exampleProblem) 0.001 := by
  dsimp [satisfiesEOI]
  -- compute and rewrite `eoi exampleProblem` to a simpler numeric sqrt
  have heoi : eoi exampleProblem = Real.sqrt ((20 : ℝ) / 7) := by
    dsimp [eoi, avgDemand, exampleProblem]
    norm_num
  rw [heoi]
  -- finish the three conjuncts by numeric checking
  have h_pos : 0 < Real.sqrt ((20 : ℝ) / 7 : ℝ) := by norm_num

  have h_le : Real.sqrt ((20 : ℝ) / 7) ≤ (4 : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    simp
    norm_num
  simp
  norm_num
  dsimp [exampleProblem]

  have h_nonneg : 0 ≤ (20 / 7 : ℝ) := by norm_num
  have h_sq : (20 / 7 : ℝ) ≤ (4 : ℝ)^2 := by norm_num

  -- use the fact that sqrt(x) / sqrt(y) = sqrt(x / y) for positive reals
  have h_noneg_7 : 0 ≤ (7 : ℝ) := by norm_num
  have h_pos_7 : 0 < (7 : ℝ) := by norm_num
  have h_noneg_20 : 0 ≤ (20 : ℝ) := by norm_num

  have h_sqrt_div : Real.sqrt (20 : ℝ) / Real.sqrt 7 = Real.sqrt (20 / 7) := by
    have h7_pos : 0 < (7 : ℝ) := by norm_num
    rw [← Real.sqrt_div h_noneg_20]
  rw [h_sqrt_div]
  norm_cast

end --EOI
