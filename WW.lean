/-
WW.lean
Formalization of the Wagner–Whitin dynamic lot-sizing recursion.
Lean 4 
Author: Ieva Daukantas et al.
2025 November 30
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Wagner_Whitin.EOI     

import Mathlib.Order.Basic
import Mathlib.Tactic
import Init.Data.List.Basic 

open scoped BigOperators

namespace WW
noncomputable section

/-- Parameters of a production-inventory problem. -/
structure Problem where
  setupCost   : ℝ
  holdingCost : ℝ
  demands     : ℕ → ℝ         
  horizon     : ℕ
  nonneg_h    : 0 ≤ holdingCost
  nonneg_d    : ∀ t, 0 ≤ demands t

/-- Total cost of producing in period `i` to cover demands through `j`
    (Wagner–Whitin cost interval f(i,j)). -/
def costInterval (P : Problem) (i j : ℕ) : ℝ :=
  P.setupCost +
    P.holdingCost *
      Finset.sum (Finset.Ico i j) fun t => (↑(t - i + 1) : ℝ) * P.demands t


/-- Helper lemma to Rewrite `((j - i + 1 : ℕ) : ℝ)` as `↑j + (-↑i + 1)` when `i ≤ j`. -/
lemma castSubAddOne_eq (i j : ℕ) (hij : i ≤ j) :
    ((j - i + 1 : ℕ) : ℝ) = (j : ℝ) + (-(i : ℝ) + 1) := by
  -- First: (j - i + 1 : ℕ) = (j - i : ℕ) + 1, then cast
  have h1 : ((j - i + 1 : ℕ) : ℝ) = ((j - i : ℕ) : ℝ) + 1 := by
    simp [Nat.cast_add, Nat.cast_one]
  -- Cast the subtraction (needs `i ≤ j`)
  have hsub : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
    simpa using (Nat.cast_sub hij : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ))
  -- Finish by simple algebra
  calc
    ((j - i + 1 : ℕ) : ℝ)
        = ((j - i : ℕ) : ℝ) + 1 := h1
    _   = ((j : ℝ) - (i : ℝ)) + 1 := by simp [hsub]
    _   = (j : ℝ) + (-(i : ℝ) + 1) := by ring

/-- **Cost convexity lemma:** `f(i,j+1) − f(i,j) = h · (j−i+1) · D_j`. -/
lemma costInterval_convex (P : Problem) (i j : ℕ) (hij : i ≤ j) :
    costInterval P i (j + 1) - costInterval P i j
      = P.holdingCost * ((j - i + 1 : ℕ) : ℝ) * P.demands j := by
  unfold costInterval
  -- Split off the last term of the sum at j
  rw [Finset.sum_Ico_succ_top hij]
  -- The two big sums cancel; tidy up the arithmetic structure
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_assoc]


/-- **Monotonicity:**
     `f(i,j) ≤ f(i,j+1)` under non-negative holding cost and demand. -/
lemma costInterval_monotone
    (P : Problem) {i j : ℕ} (hij : i ≤ j) :
    costInterval P i j ≤ costInterval P i (j + 1) := by
  -- From convexity lemma:
  have diff := costInterval_convex P i j hij
  have h_cast : (↑(j - i + 1) : ℝ) = (↑j - ↑i + 1) := by norm_cast
  -- Rearrange the equality to express f(i,j+1) as f(i,j)+…
  have eq_sub : costInterval P i (j + 1) - P.holdingCost * (↑j - ↑i + 1) * P.demands j
    = costInterval P i j := by
    -- Replace (↑j - ↑i + 1) with ↑(j - i + 1)
    rw [← h_cast]
    -- Substitute diff in reverse (since we want to remove the added term)
    rw [← diff]
    ring

  -- show the added term is nonnegative
  have term_nonneg : 
    0 ≤ P.holdingCost * (↑j - ↑i + 1) * P.demands j := by
    have hh := P.nonneg_h
    have hd := P.nonneg_d j

    have hj' : 0 ≤ (↑j - ↑i + 1) := by
      norm_num

    -- convert the nat inequality to ℝ and use the cast lemma to match the term
    have hjr : 0 ≤ (↑j - ↑i + 1 : ℝ) := by
      have : 0 ≤ ((j - i + 1 : ℕ) : ℝ) := by
        norm_cast
      have hj'' : 0 ≤ (↑j - ↑i + 1) := by
        norm_cast

      linarith

    have term_nonneg : 0 ≤ P.holdingCost * (↑j - ↑i + 1) * P.demands j := by
      have hh := P.nonneg_h
      have hd := P.nonneg_d j
      have hjr : 0 ≤ (↑j - ↑i + 1 : ℝ) := by
        norm_cast

      -- combine the three nonnegativities
      have h := mul_nonneg hh (mul_nonneg hjr hd)
      -- fix associativity: (h * (a * d)) ↔ (h * a * d)
      simpa [mul_assoc] using h


    exact term_nonneg



  -- rewrite to the form `costInterval i (j+1) = costInterval i j + term` and finish
  have eq_add : costInterval P i (j + 1)
    = costInterval P i j + P.holdingCost * (↑j - ↑i + 1) * P.demands j := by
    rw [← eq_sub]; ring
  rw [eq_add]
  -- costInterval P i j ≤ costInterval P i j + term since term ≥ 0
  linarith [term_nonneg]




/-- Dynamic-programming optimal cumulative cost F(j):
    minimal cost to satisfy demand up to period j. -/
def optCost (P : Problem) : ℕ → ℝ
  | 0     => 0
  | j + 1 =>
      -- use Fin (j+1) so each index i has proof i.val < j+1
      let candidates :=
        (List.finRange (j + 1)).map
          (fun (i : Fin (j + 1)) =>
            let k := (i : ℕ)
            optCost P k + costInterval P k (j + 1))
      candidates.foldl min candidates.head!
termination_by j => j
decreasing_by  
  simp



-- Key helper 1: the fold result is ≤ the accumulator.
lemma foldl_min_le_acc {α : Type*} [LinearOrder α] :
    ∀ (xs : List α) (acc : α), xs.foldl min acc ≤ acc
  | [], acc => by simp
  | x :: xs, acc => by
      -- foldl min acc (x :: xs) = foldl min (min acc x) xs
      simpa [List.foldl_cons] using
        (le_trans (foldl_min_le_acc xs (min acc x)) (min_le_left _ _))

-- Key helper 2: monotonicity of foldl in the accumulator.
lemma foldl_min_mono_acc {α : Type*} [LinearOrder α] :
    ∀ (xs : List α) {a b : α}, a ≤ b → xs.foldl min a ≤ xs.foldl min b
  | [], a, b, hab => by simpa
  | x :: xs, a, b, hab => by
      -- min is monotone in each argument
      have hmin : min a x ≤ min b x := by exact min_le_min hab le_rfl
      -- recurse on the tail
      simpa [List.foldl_cons] using
        (foldl_min_mono_acc xs hmin)

lemma foldl_min_le_of_mem {α : Type*} [LinearOrder α] :
    ∀ (acc : α) (xs : List α), ∀ {x}, x ∈ xs → xs.foldl min acc ≤ x := by
  intro acc xs
  induction xs generalizing acc with
  | nil =>
      intro x hx
      cases hx
  | cons y ys ih =>
      intro x hx
      simp only [List.foldl_cons]
      cases hx with
      | head =>
          -- case x = y
          have h₁ := foldl_min_le_acc ys (min acc y)
          have h₂ : min acc y ≤ y := min_le_right _ _
          exact le_trans h₁ h₂
      | tail  =>
          -- case x ∈ ys
          have hmono : ys.foldl min (min acc y) ≤ ys.foldl min acc :=
            foldl_min_mono_acc ys (min_le_left _ _)
          rename_i hmem
          exact le_trans hmono (ih acc hmem)


/-- **Optimality property**:
    By construction, `F(j+1) ≤ F(i) + f(i,j+1)` for all `i ≤ j`. -/
lemma optCost_min_property
    (P : Problem) (j i : ℕ) (hi : i ≤ j) :
    optCost P (j + 1) ≤ optCost P i + costInterval P i (j + 1) := by
  unfold optCost

  set vals :
    List ℝ :=
      (List.finRange (j + 1)).map
        (fun (k : Fin (j + 1)) =>
          optCost P k.val + costInterval P k.val (j + 1)) with hvals


  classical
  let fi : Fin (j + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  have fi_mem : fi ∈ List.finRange (j + 1) := by
    simpa using List.mem_finRange fi

  have target_mem : optCost P i + costInterval P i (j + 1) ∈ vals := by
    refine List.mem_map.mpr ?_
    refine ⟨fi, fi_mem, ?_⟩
    simp [vals, fi]

  -- foldl min ≤ any member
  have base_le_target :
      vals.foldl min vals.head!
        ≤ optCost P i + costInterval P i (j + 1) :=
    foldl_min_le_of_mem _ _ target_mem


    -- rewrite the LHS
  have hLHS :
      (have candidates := vals;
        List.foldl min candidates.head! candidates)
    = vals.foldl min vals.head! := rfl

  -- case on `i` so the RHS `match i with` simplifies to `optCost P i`
  cases i with
  | zero =>
      -- RHS becomes `0 + costInterval P 0 (j+1)` and
      -- `base_le_target`’s RHS is `optCost P 0 + ... = 0 + ...`
      simpa [hLHS, optCost] using base_le_target
  | succ i' =>
      -- RHS becomes exactly the fold for `optCost P (i'+1)` plus the same `costInterval`
      simpa [hLHS, optCost] using base_le_target


end
end WW
