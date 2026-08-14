/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Substituting a fraction into a polynomial, without leaving the base ring

A formula for a root of a family of equations is a fraction: a polynomial `N` divided by a
denominator `d` taken from the coefficient ring.  Substituting such a fraction into a polynomial
`P` of degree `n` and clearing the denominator once and for all produces `scaledComp P N d`, the
polynomial `∑ⱼ Pⱼ dⁿ⁻ʲ Nʲ`, which lives in the coefficient ring and equals `dⁿ · P(N/d)` wherever
the fraction makes sense.

That is what makes an identity proved over the field of fractions usable pointwise: the identity
is a divisibility between polynomials with coefficients in the base ring, and divisibility is
preserved by every evaluation.  In particular a divisibility by a monic `P` may be proved after
passing to the fraction field and then brought back (`Polynomial.map_dvd_map`).

## Main definitions

* `Rigidity.RET.scaledComp` — the denominator-cleared substitution.

## Main results

* `Rigidity.RET.eval₂_scaledComp_of_inv` — the value of the substitution wherever the denominator
  is invertible.
* `Rigidity.RET.isRoot_of_dvd_scaledComp` — a root of a specialization of `P` is carried to a root
  of that specialization by any formula whose substitution `P` divides.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **The substitution of the fraction `N / d` into `P`, with the denominator cleared.** -/
def scaledComp (P N : Polynomial R) (d : R) : Polynomial R :=
  ∑ j ∈ Finset.range (P.natDegree + 1), C (P.coeff j * d ^ (P.natDegree - j)) * N ^ j

theorem eval₂_scaledComp (φ : R →+* S) (u : S) (P N : Polynomial R) (d : R) :
    eval₂ φ u (scaledComp P N d)
      = ∑ j ∈ Finset.range (P.natDegree + 1),
          φ (P.coeff j) * φ d ^ (P.natDegree - j) * eval₂ φ u N ^ j := by
  simp only [scaledComp, eval₂_finset_sum, eval₂_mul, eval₂_C, eval₂_pow, map_mul, map_pow]

/-- **Wherever the denominator is invertible the cleared substitution is the substitution**, scaled
by the `n`-th power of the denominator. -/
theorem eval₂_scaledComp_of_inv (φ : R →+* S) (u e : S) (P N : Polynomial R) {d : R}
    (he : φ d * e = 1) :
    eval₂ φ u (scaledComp P N d)
      = φ d ^ P.natDegree * eval₂ φ (e * eval₂ φ u N) P := by
  rw [eval₂_scaledComp, eval₂_eq_sum_range' φ (Nat.lt_succ_self _) (e * eval₂ φ u N),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow : φ d ^ P.natDegree * e ^ j = φ d ^ (P.natDegree - j) := by
    calc φ d ^ P.natDegree * e ^ j
        = φ d ^ (P.natDegree - j) * (φ d * e) ^ j := by
          rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj']
      _ = φ d ^ (P.natDegree - j) := by rw [he, one_pow, mul_one]
  calc φ (P.coeff j) * φ d ^ (P.natDegree - j) * eval₂ φ u N ^ j
      = φ (P.coeff j) * (φ d ^ P.natDegree * e ^ j) * eval₂ φ u N ^ j := by rw [hpow]
    _ = φ d ^ P.natDegree * (φ (P.coeff j) * (e * eval₂ φ u N) ^ j) := by
        rw [mul_pow]; ring

/-- **A formula carries roots to roots.**  If `P` divides the cleared substitution of `N / d` into
itself, then wherever the denominator is invertible and cancellable, the fraction sends a root of
the specialization of `P` to a root of that specialization. -/
theorem isRoot_of_dvd_scaledComp [NoZeroDivisors S] (φ : R →+* S) {P N : Polynomial R} {d : R}
    (hdvd : P ∣ scaledComp P N d) {u e : S} (he : φ d * e = 1) (hd : φ d ≠ 0)
    (hu : (P.map φ).IsRoot u) : (P.map φ).IsRoot (e * eval₂ φ u N) := by
  obtain ⟨M, hM⟩ := hdvd
  have hzero : eval₂ φ u (scaledComp P N d) = 0 := by
    rw [hM, eval₂_mul, ← eval_map, show (P.map φ).eval u = 0 from hu, zero_mul]
  rw [eval₂_scaledComp_of_inv φ u e P N he] at hzero
  have h2 := (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hd)
  show (P.map φ).eval (e * eval₂ φ u N) = 0
  rw [eval_map]
  exact h2

/-- **Two polynomials congruent modulo `P` take the same value at a root of a specialization
of `P`.** -/
theorem eval₂_eq_of_dvd_sub (φ : R →+* S) {P A B : Polynomial R} (hdvd : P ∣ A - B) {u : S}
    (hu : (P.map φ).IsRoot u) : eval₂ φ u A = eval₂ φ u B := by
  obtain ⟨M, hM⟩ := hdvd
  have h : eval₂ φ u (A - B) = 0 := by
    rw [hM, eval₂_mul, ← eval_map, show (P.map φ).eval u = 0 from hu, zero_mul]
  rw [eval₂_sub, sub_eq_zero] at h
  exact h

/-! ### Reading the cleared substitution over the field of fractions -/

section Field

variable {K : Type*} [Field K]

/-- **The cleared substitution, over a field where the denominator is invertible.** -/
theorem map_scaledComp (ψ : R →+* K) (P N : Polynomial R) {d : R} (hd : ψ d ≠ 0) :
    (scaledComp P N d).map ψ
      = C (ψ d) ^ P.natDegree * (P.map ψ).comp (C (ψ d)⁻¹ * N.map ψ) := by
  have he : (C.comp ψ : R →+* Polynomial K) d * C (ψ d)⁻¹ = 1 := by
    rw [RingHom.comp_apply, ← C_mul, mul_inv_cancel₀ hd, C_1]
  have h := eval₂_scaledComp_of_inv (C.comp ψ : R →+* Polynomial K) X (C (ψ d)⁻¹) P N he
  rw [show ((C.comp ψ : R →+* Polynomial K) d) = C (ψ d) from rfl] at h
  rw [show (scaledComp P N d).map ψ = eval₂ (C.comp ψ : R →+* Polynomial K) X (scaledComp P N d)
    from rfl, h, show eval₂ (C.comp ψ : R →+* Polynomial K) X N = N.map ψ from rfl]
  congr 1
  exact (eval₂_map (f := ψ) (p := P) C _).symm

/-- **A divisibility proved over the field of fractions descends** to the cleared substitution. -/
theorem dvd_scaledComp (ψ : R →+* K) (hψ : Function.Injective ψ) {P N : Polynomial R} {d : R}
    (hP : P.Monic) (hd : ψ d ≠ 0)
    (hdvd : P.map ψ ∣ (P.map ψ).comp (C (ψ d)⁻¹ * N.map ψ)) : P ∣ scaledComp P N d := by
  rw [← Polynomial.map_dvd_map ψ hψ hP, map_scaledComp ψ P N hd]
  exact hdvd.mul_left _

end Field

end Rigidity.RET

end
