/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Global.HasseNorm

/-!
# One finite place omitted from the Hasse principle

The Hasse principle for a quadratic extension of the rationals asks a condition at every place, and
reciprocity makes one of them redundant: `exists_sub_sq_of_forall_local` drops the real place.  The
same argument drops any *one* place, the remaining ones being given.  Since the product of the local
symbols over all places is one, a symbol which is known at every place but one is known there too.

The form the Scholz–Reichardt construction at the prime two needs is the one in which the real place
is retained and a single finite place is dropped: a totally real solution has trivial symbol at the
real place, so the condition at the dyadic place comes for free from the conditions at the odd
places.  Retaining the real place is what makes the count work — with two unknown symbols and one
relation nothing follows.

## Main results

* `InverseGalois.CFT.hilbertSymbolAt_eq_one_of_forall_ne`: **a local Hilbert symbol which is one at
  the real place and at every finite place but one is one at that place as well.**
* `InverseGalois.CFT.hilbertSymbol_rat_of_forall_finite_ne`: the rational Hilbert symbol under the
  same hypotheses.
* `InverseGalois.CFT.exists_sub_sq_of_forall_local_ne`: **the Hasse norm theorem for a quadratic
  extension of the rationals with one finite place omitted**, the real place being retained.

## Tags

Hilbert symbol, reciprocity, Hasse principle, Hasse norm theorem, quadratic extension
-/

namespace InverseGalois.CFT

open Local

/-- **A local Hilbert symbol which is one at the real place and at every finite place but one is
one at that place as well.**  The product of the finite symbols is the symbol at the real place,
and all but one factor is one. -/
theorem hilbertSymbolAt_eq_one_of_forall_ne {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (q : Nat.Primes)
    (hreal : hilbertSymbol ((a : ℝ)) ((b : ℝ)) = 1)
    (hloc : ∀ p : Nat.Primes, p ≠ q → hilbertSymbolAt p a b = 1) :
    hilbertSymbolAt q a b = 1 := by
  have h := hilbertProduct_finite_eq_real ha hb
  rwa [hreal, finprod_eq_single (fun p : Nat.Primes => hilbertSymbolAt p a b) q hloc] at h

/-- **One finite place is redundant in the Hasse principle for the Hilbert symbol**, as soon as the
real place is retained. -/
theorem hilbertSymbol_rat_of_forall_finite_ne {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (q : Nat.Primes)
    (hreal : hilbertSymbol ((a : ℝ)) ((b : ℝ)) = 1)
    (hloc : ∀ p : Nat.Primes, p ≠ q → hilbertSymbolAt p a b = 1) :
    hilbertSymbol a b = 1 := by
  refine hilbertSymbol_rat_of_forall_local ha hb hreal fun p => ?_
  rcases eq_or_ne p q with rfl | hpq
  · exact hilbertSymbolAt_eq_one_of_forall_ne ha hb p hreal hloc
  · exact hloc p hpq

/-- **The Hasse norm theorem for a quadratic extension of the rational field with one finite place
omitted.**  A nonzero rational which is a norm from the reals and from `ℚ_p(√b)` at every prime but
one is a norm from `ℚ(√b)`; the condition at the omitted prime is supplied by reciprocity. -/
theorem exists_sub_sq_of_forall_local_ne {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (q : Nat.Primes)
    (hreal : ∃ u v : ℝ, ((a : ℝ)) = u ^ 2 - ((b : ℝ)) * v ^ 2)
    (hloc : ∀ p : Nat.Primes, p ≠ q → ∃ u v : ℚ_[(p : ℕ)],
      ((a : ℚ_[(p : ℕ)])) = u ^ 2 - ((b : ℚ_[(p : ℕ)])) * v ^ 2) :
    ∃ u v : ℚ, a = u ^ 2 - b * v ^ 2 := by
  have hbR : ((b : ℝ)) ≠ 0 := by simpa using hb
  refine (hilbertSymbol_eq_one_iff_exists_sub_sq' hb).1 ?_
  refine hilbertSymbol_rat_of_forall_finite_ne ha hb q
    ((hilbertSymbol_eq_one_iff_exists_sub_sq' hbR).2 hreal) fun p hpq => ?_
  exact (hilbertSymbolAt_eq_one_iff_exists_sub_sq hb).2 (hloc p hpq)

end InverseGalois.CFT
