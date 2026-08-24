/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.SUnit
import InverseGalois.Rigidity.RET.Genus.OrdValuation

/-!
# The adic valuation of an `X`-unit

The order of an element at a prime and its adic valuation there carry the same information, the
valuation being the exponential of the negated order.  So a nonzero element has valuation one at a
prime exactly when its order there vanishes, and an `X`-unit, whose order vanishes outside `X`, has
valuation one at every prime outside `X`.

## Main results

* `InverseGalois.CFT.valuation_eq_one_iff_ord_eq_zero`: a nonzero element has adic valuation one at
  a prime exactly when its order there vanishes.
* `InverseGalois.CFT.valuation_eq_one_of_mem_sUnits`: **an `X`-unit has adic valuation one at every
  prime outside `X`.**

## Tags

Dedekind domain, adic valuation, order, S-unit
-/

namespace InverseGalois.CFT

open IsDedekindDomain Rigidity.RET

section Valuation

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- A nonzero element has adic valuation one at a prime exactly when its order there vanishes. -/
theorem valuation_eq_one_iff_ord_eq_zero (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = 1 ↔ ord K v x = 0 := by
  rw [valuation_eq_exp_neg_ord K v hx, ← WithZero.exp_zero (M := ℤ), WithZero.exp_inj, neg_eq_zero]

/-- **An `X`-unit has adic valuation one at every prime outside `X`.** -/
theorem valuation_eq_one_of_mem_sUnits {X : Set (HeightOneSpectrum R)} {u : Kˣ}
    (hu : u ∈ sUnits K X) {v : HeightOneSpectrum R} (hv : v ∉ X) :
    v.valuation K (u : K) = 1 :=
  (valuation_eq_one_iff_ord_eq_zero v (Units.ne_zero u)).mpr (mem_sUnits.mp hu v hv)

end Valuation

end InverseGalois.CFT
