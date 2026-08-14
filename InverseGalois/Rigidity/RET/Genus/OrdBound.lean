/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdValuation

/-!
# Bounding the order of a function at a single prime

Statements about the order of a function at a prime are awkward to add and multiply as they stand,
because the order of the zero function is not a number.  Bounding the order from below repairs
this: the bound `n ≤ ord x`, read as the multiplicative statement that the adic valuation of `x` is
at most `exp (-n)`, holds vacuously for the zero function, and is stable under sums, differences
and products in the way orders are.

With that calculus in place a derivation can be pushed down towards preserving the functions
regular at a prime.  Suppose a derivation is known to create a pole of order at most `N` out of a
function with no pole, and suppose the coordinate at the prime — a function vanishing to order
exactly one — is differentiated to something with a pole of order at most `N - 1`.  Then a function
with no pole differentiates to something with a pole of order at most `N - 1`: subtract the value
of the function at the prime, which the derivation kills, and what is left is the coordinate times
a function with no pole, whose two Leibniz terms both gain the missing order.  Iterating removes
the pole altogether.

## Main definitions

* `Rigidity.RET.OrdAtLeast` — the order of a function at a prime is at least a given integer.

## Main results

* `Rigidity.RET.ordAtLeast_iff` — for a nonzero function the bound is the inequality of orders.
* `Rigidity.RET.OrdAtLeast.add`, `Rigidity.RET.OrdAtLeast.mul` — the calculus of bounds.
* `Rigidity.RET.ordAtLeast_deriv_of_descent` — a derivation with a bounded pole at a prime, whose
  effect on the coordinate there gains an order at every stage, preserves the functions regular at
  that prime.
-/

open IsDedekindDomain FractionalIdeal WithZero
open scoped nonZeroDivisors

noncomputable section


namespace Rigidity.RET

section OrdBound

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- **The order of a function at a prime is at least `n`.**  Multiplicatively: the adic valuation
is at most `exp (-n)`.  The zero function satisfies every such bound. -/
def OrdAtLeast (n : ℤ) (x : K) : Prop := v.valuation K x ≤ exp (-n)

variable {K v}

@[simp]
theorem ordAtLeast_zero_fun (n : ℤ) : OrdAtLeast K v n (0 : K) := by
  simp [OrdAtLeast]

/-- **For a nonzero function the bound is the inequality of orders.** -/
theorem ordAtLeast_iff (n : ℤ) {x : K} (hx : x ≠ 0) : OrdAtLeast K v n x ↔ n ≤ ord K v x := by
  rw [OrdAtLeast, valuation_eq_exp_neg_ord K v hx, exp_le_exp, neg_le_neg_iff]

/-- **Being regular at a prime is the bound `0`.** -/
theorem ordAtLeast_zero_iff {x : K} : OrdAtLeast K v 0 x ↔ 0 ≤ ord K v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  · exact ordAtLeast_iff 0 hx

theorem ordAtLeast_of_ord_le {n : ℤ} {x : K} (h : n ≤ ord K v x) : OrdAtLeast K v n x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ordAtLeast_zero_fun n
  · exact (ordAtLeast_iff n hx).2 h

/-! ## The calculus of bounds -/

theorem OrdAtLeast.mono {m n : ℤ} (h : m ≤ n) {x : K} (hx : OrdAtLeast K v n x) :
    OrdAtLeast K v m x :=
  hx.trans (exp_le_exp.2 (neg_le_neg h))

theorem OrdAtLeast.add {n : ℤ} {x y : K} (hx : OrdAtLeast K v n x) (hy : OrdAtLeast K v n y) :
    OrdAtLeast K v n (x + y) :=
  le_trans (Valuation.map_add _ _ _) (max_le hx hy)

theorem OrdAtLeast.neg {n : ℤ} {x : K} (hx : OrdAtLeast K v n x) : OrdAtLeast K v n (-x) := by
  rwa [OrdAtLeast, Valuation.map_neg]

theorem OrdAtLeast.sub {n : ℤ} {x y : K} (hx : OrdAtLeast K v n x) (hy : OrdAtLeast K v n y) :
    OrdAtLeast K v n (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem OrdAtLeast.mul {m n : ℤ} {x y : K} (hx : OrdAtLeast K v m x) (hy : OrdAtLeast K v n y) :
    OrdAtLeast K v (m + n) (x * y) := by
  rw [OrdAtLeast, map_mul, neg_add, exp_add]
  exact mul_le_mul' hx hy

/-- **Functions of the domain are regular at every prime.** -/
theorem ordAtLeast_algebraMap (r : R) : OrdAtLeast K v 0 (algebraMap R K r) :=
  ordAtLeast_zero_iff.2 (ord_nonneg v r)

/-! ## Factoring out the coordinate at a prime -/

theorem ne_zero_of_ord_eq_one {t : K} (ht : ord K v t = 1) : t ≠ 0 := by
  rintro rfl
  rw [ord_zero] at ht
  exact one_ne_zero ht.symm

/-- **A function vanishing at a prime is the coordinate there times a regular function.** -/
theorem exists_eq_mul_of_ordAtLeast_one {t : K} (ht : ord K v t = 1) {x : K}
    (hx : OrdAtLeast K v 1 x) : ∃ y : K, OrdAtLeast K v 0 y ∧ x = t * y := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_eq_one ht
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, ordAtLeast_zero_fun 0, by rw [mul_zero]⟩
  refine ⟨x / t, ?_, by field_simp⟩
  have hdiv : ord K v (x / t) = ord K v x - 1 := by rw [ord_div v hx0 ht0, ht]
  refine ordAtLeast_of_ord_le ?_
  have := (ordAtLeast_iff 1 hx0).1 hx
  omega

end OrdBound

/-! ## Removing the pole of a derivation -/

section Descent

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {v : HeightOneSpectrum R}
variable {k : Type*} [Field k] [Algebra k K]

/-- **A derivation whose pole at a prime can always be lowered by one has no pole there.**

The hypotheses are: every function regular at the prime has a value there, in the constants; the
coordinate at the prime is differentiated to something whose pole is one order smaller than the
worst pole the derivation creates; and the derivation creates a pole of order at most `N`. -/
theorem ordAtLeast_deriv_of_descent (δ : Derivation k K K) {t : K} (ht : ord K v t = 1)
    (hres : ∀ z : K, OrdAtLeast K v 0 z → ∃ c : k, OrdAtLeast K v 1 (z - algebraMap k K c))
    (hstep : ∀ N : ℕ, 1 ≤ N → (∀ z : K, OrdAtLeast K v 0 z → OrdAtLeast K v (-(N : ℤ)) (δ z)) →
      OrdAtLeast K v (1 - (N : ℤ)) (δ t))
    (N : ℕ) (hN : ∀ z : K, OrdAtLeast K v 0 z → OrdAtLeast K v (-(N : ℤ)) (δ z)) :
    ∀ z : K, OrdAtLeast K v 0 z → OrdAtLeast K v 0 (δ z) := by
  induction N with
  | zero => simpa using hN
  | succ N ih =>
    refine ih ?_
    have hδt : OrdAtLeast K v (-(N : ℤ)) (δ t) := by
      have h := hstep (N + 1) (by omega) hN
      push_cast at h
      simpa using h
    intro z hz
    obtain ⟨c, hc⟩ := hres z hz
    obtain ⟨z₁, hz₁, hzeq⟩ := exists_eq_mul_of_ordAtLeast_one ht hc
    have hz' : z = algebraMap k K c + t * z₁ := by
      rw [← hzeq]; ring
    have hδ : δ z = δ t * z₁ + t * δ z₁ := by
      rw [hz', map_add, δ.map_algebraMap, zero_add, δ.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hδ]
    refine OrdAtLeast.add ?_ ?_
    · simpa using hδt.mul hz₁
    · have h1 : OrdAtLeast K v 1 t := ordAtLeast_of_ord_le (le_of_eq ht.symm)
      have := h1.mul (hN z₁ hz₁)
      refine this.mono ?_
      omega

end Descent

end Rigidity.RET
