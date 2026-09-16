/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdUltra
import InverseGalois.Rigidity.RET.Genus.OrdValuation

/-!
# Comparing adic valuations through orders

The adic valuation at a height-one prime is the exponential of the negated order there, and the
exponential is strictly monotone, so one nonzero element has smaller valuation than another exactly
when it has larger order.  Statements phrased with the valuation — the filtration of the units of a
completion, for instance — are therefore read off from the additive bookkeeping of orders, which is
where the ultrametric calculus lives.

## Main results

* `InverseGalois.CFT.valuation_lt_iff_ord_lt`: **one nonzero element has smaller adic valuation
  than another exactly when it has larger order.**
* `InverseGalois.CFT.ord_sub_eq_right`: a strictly worse subtrahend fixes the order of a
  difference.

## Tags

adic valuation, order, height-one prime, Dedekind domain
-/

namespace InverseGalois.CFT

open IsDedekindDomain Rigidity.RET

section Compare

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- **One nonzero element has smaller adic valuation than another exactly when it has larger
order.** -/
theorem valuation_lt_iff_ord_lt {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    v.valuation K x < v.valuation K y ↔ ord K v y < ord K v x := by
  rw [valuation_eq_exp_neg_ord K v hx, valuation_eq_exp_neg_ord K v hy, WithZero.exp_lt_exp,
    neg_lt_neg_iff]

/-- A strictly worse subtrahend fixes the order of a difference. -/
theorem ord_sub_eq_right {x y : K} (hy : y ≠ 0) (h : ord K v y < ord K v x) :
    ord K v (x - y) = ord K v y := by
  rw [show x - y = -(y - x) by ring, ord_neg, ord_sub_of_ord_lt hy h]

end Compare

end InverseGalois.CFT
