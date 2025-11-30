# Wagner_Whitin_and_EOI
Wagner-Whitin and Economic Order Interval theory verification i Lean 4 and experimental validation in Python 3.

----------------------------------------------------------------------
Verified Wagner–Whitin and EOI Models (Lean 4 + Python 3 Experiments) 
----------------------------------------------------------------------

This repository contains the mechanized formalization of the classical 
Wagner–Whitin (WW) dynamic lot-sizing model and the Economic Order Interval (EOI)
heuristic in Lean 4, together with Python 3 scripts used to evaluate their 
practical behaviour. 

The accompanying paper presents: 
1. The first machine-checked formalization of the WW cost-interval function and optimality recursion. 
2. New mechanized convexity and monotonicity lemmas absent from the classical literature. 
3. A constructive, list-based proof of the dynamic-programming optimality inequality. 
4. Reusable proof infrastructure for folds, minima, and algebraic inequalities. 
5. A Lean 4 mechanization of the EOI heuristic and its feasibility conditions. 
6. Executable experiments illustrating the expected cost optimality and runtime behaviour of WW vs. EOI.


----------------------------------------------------------------------
Repository Structure
----------------------------------------------------------------------
- WW.lean formalization of Wagner-Whitin (WW) theory in Lean 
- EOI.lean formalization of Economic Order Interval (EOI) theory in Lean
- exp_ww_eoi.py experimental validation of WW and EOI in Python3
- README.md

----------------------------------------------------------------------
Dependencies:
----------------------------------------------------------------------
* Lean version 4.25.0-rc2
* Lake version 5.0.0-src+744f980
* Make sure that .toolchain file specifies: leanprover/lean4:v4.25.0-rc2
* Python version 3.8.10
* Make sure to have installed Python's "matplotlib>=3.7" and "tqdm>=4.65"

----------------------------------------------------------------------
WW.lean
----------------------------------------------------------------------
- Formalizes the cost-interval function 'f(i,j)'.
- Implements the dynamic-programming recurrence for optimal cost 'F(j)'.
- Declares and defines proofs of:
  - convexity lemma
  - monotonicity lemma
  - folded-minimum correctness lemma
- Concludes with the formal optimality inequality and recursion theorem.

----------------------------------------------------------------------
'EOI.lean'
----------------------------------------------------------------------
- Formalizes the EOI formula.
- Shows feasibility preservation on the horizons.
- Proves correctness of the analytical structure of EOI as used in the literature.

----------------------------------------------------------------------
'experiments.py'
----------------------------------------------------------------------
Implements executable versions of WW and EOI in Python to test the hypotheses:
- H_1: WW yields lower total cost than EOI.
- H_2: EOI runs faster due to closed-form computation.

The script can:
- generate random demand instances,
- run 1000-instance cost-optimality tests,
- benchmark runtime scaling (n = 10, 100, 1000),
- output plots (PNG) and speed tables (TXT) with timestamps.



