/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdBound

/-!
# The ultrametric calculus of orders at a prime

The order at a prime is a valuation, so a sum vanishes at least as deeply as its worst summand, and
— the sharp form, the one that does the work — *exactly* as deeply as its worst summand when that
worst summand is strictly worse than the others.  Sums of orders come from products, and the
finitely-many-factor version of that is the other half of the calculus.

These two rules are what turns an algebraic identity between elements of a cover into a count.  A
factorization `∏ᵢ (a - bᵢ) = c` reads as `∑ᵢ ord (a - bᵢ) = ord c`; if every factor is known to
vanish to order at least `m` and the total is `N`, then the factors that vanish deeper than `m` are
constrained by `N - n·m`, and when that slack is small only one factor can use it.  That is how a
root of an equation is told apart from the others by a single place.

## Main results

* `Rigidity.RET.min_ord_le_ord_add` — the order of a sum is at least the smaller of the two orders.
* `Rigidity.RET.ord_add_of_ord_lt` — a strictly worse summand fixes the order of the sum.
* `Rigidity.RET.ord_prod` — the order of a finite product is the sum of the orders.
-/

open IsDedekindDomain

noncomputable section

namespace Rigidity.RET

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {v : HeightOneSpectrum R}

/-- The order of `-1` is zero: it is a unit. -/
theorem ord_neg_one : ord K v (-1 : K) = 0 := by
  have h : ord K v ((-1 : K) * (-1 : K)) = ord K v (-1 : K) + ord K v (-1 : K) :=
    ord_mul v (by norm_num) (by norm_num)
  rw [show ((-1 : K) * (-1 : K)) = 1 by ring, ord_one] at h
  omega

/-- Negation does not change the order. -/
@[simp]
theorem ord_neg (x : K) : ord K v (-x) = ord K v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [show (-x) = (-1 : K) * x by ring, ord_mul v (by norm_num) hx, ord_neg_one, zero_add]

/-- **The order of a sum is at least the smaller of the two orders.** -/
theorem min_ord_le_ord_add {x y : K} (hxy : x + y ≠ 0) :
    min (ord K v x) (ord K v y) ≤ ord K v (x + y) :=
  (ordAtLeast_iff _ hxy).1
    ((ordAtLeast_of_ord_le (min_le_left _ _)).add (ordAtLeast_of_ord_le (min_le_right _ _)))

/-- **The order of a difference is at least the smaller of the two orders.** -/
theorem min_ord_le_ord_sub {x y : K} (hxy : x - y ≠ 0) :
    min (ord K v x) (ord K v y) ≤ ord K v (x - y) := by
  have h := min_ord_le_ord_add (v := v) (x := x) (y := -y) (by rwa [← sub_eq_add_neg])
  rwa [ord_neg, ← sub_eq_add_neg] at h

/-- **A strictly worse summand fixes the order of the sum.** -/
theorem ord_add_of_ord_lt {x y : K} (hx : x ≠ 0) (h : ord K v x < ord K v y) :
    ord K v (x + y) = ord K v x := by
  have hxy : x + y ≠ 0 := by
    rintro hz
    have : y = -x := by linear_combination hz
    rw [this, ord_neg] at h
    exact lt_irrefl _ h
  refine le_antisymm ?_ (le_trans (by omega) (min_ord_le_ord_add (v := v) hxy))
  by_contra hcon
  push_neg at hcon
  have hb : OrdAtLeast K v (ord K v x + 1) x := by
    have h1 : OrdAtLeast K v (ord K v x + 1) (x + y) := ordAtLeast_of_ord_le (by omega)
    have h2 : OrdAtLeast K v (ord K v x + 1) y := ordAtLeast_of_ord_le (by omega)
    simpa using h1.sub h2
  have := (ordAtLeast_iff _ hx).1 hb
  omega

/-- **A strictly worse term fixes the order of a difference.** -/
theorem ord_sub_of_ord_lt {x y : K} (hx : x ≠ 0) (h : ord K v x < ord K v y) :
    ord K v (x - y) = ord K v x := by
  rw [sub_eq_add_neg]
  exact ord_add_of_ord_lt hx (by rwa [ord_neg])

/-- **The order of a finite product is the sum of the orders.** -/
theorem ord_prod {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    ord K v (∏ i ∈ s, f i) = ∑ i ∈ s, ord K v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul v (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end Rigidity.RET
