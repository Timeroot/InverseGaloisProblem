/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.CyclicKummerModel

/-!
# The exponents of a multi-point Kummer model have no common factor with the degree

A cyclic cover of the line is the splitting field of `Xⁿ - ∏ᵢ (T - tᵢ)^{eᵢ}`, and that polynomial is
irreducible.  Irreducibility already forces the exponents to have no factor in common with `n`: if
a divisor `d > 1` of `n` divided every `eᵢ`, the radicand would be a `d`-th power `cᵈ`, and then
`Xⁿ - cᵈ` would be divisible by the proper factor `X^{n/d} - c`.

The conclusion is what makes a Kummer radicand usable as an independence certificate: the orders of
the radicand at the places lying over the points `tᵢ` are the exponents `eᵢ`, and a family of
integers is coprime to `n` as a whole exactly when no divisor of `n` above `1` divides all of them.

## Main results

* `Rigidity.RET.not_exists_pow_of_irreducible_X_pow_sub_C` — an irreducible `Xⁿ - a` has a radicand
  that is not a `d`-th power for any divisor `d > 1` of `n`.
* `Rigidity.RET.gcd_eq_one_of_irreducible_multiA` — the exponents of an irreducible multi-point
  Kummer polynomial are, together with `n`, of greatest common divisor one.
* `Rigidity.RET.exists_multiKummer_model_gcd` — the multi-point Kummer model of a cyclic cover,
  with that extra clause.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-- **An irreducible `Xⁿ - a` has a radicand that is not a proper power.**  If `a = bᵈ` with `d` a
divisor of `n` bigger than `1`, then `X^{n/d} - b` divides `Xⁿ - a`; it is neither a unit, having
positive degree, nor an associate of `Xⁿ - a`, having smaller degree. -/
theorem not_exists_pow_of_irreducible_X_pow_sub_C {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    {a : F} (hirr : Irreducible (X ^ n - C a)) {d : ℕ} (hd : d ∣ n) (hd1 : 1 < d) :
    ¬∃ b : F, a = b ^ d := by
  rintro ⟨b, rfl⟩
  obtain ⟨m, rfl⟩ := hd
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hn
  have hne : (X ^ m - C b : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hm b
  have hdvd : (X ^ m - C b : F[X]) ∣ X ^ (d * m) - C (b ^ d) := by
    have h1 : (X ^ (d * m) - C (b ^ d) : F[X]) = (X ^ m) ^ d - (C b) ^ d := by
      rw [← pow_mul, mul_comm m d, map_pow]
    rw [h1]
    exact sub_dvd_pow_sub_pow _ _ d
  obtain ⟨c, hc⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hc with hu | hu
  · refine Polynomial.not_isUnit_of_natDegree_pos _ ?_ hu
    rw [natDegree_X_pow_sub_C]
    exact hm
  · have hcne : c ≠ 0 := hu.ne_zero
    have hdeg := congrArg Polynomial.natDegree hc
    rw [natDegree_X_pow_sub_C, natDegree_mul hne hcne, natDegree_X_pow_sub_C,
      Polynomial.natDegree_eq_zero_of_isUnit hu, add_zero] at hdeg
    have hone : d * m = 1 * m := by rw [one_mul]; exact hdeg
    have : d = 1 := Nat.eq_of_mul_eq_mul_right hm hone
    omega

/-- **The exponents of an irreducible multi-point Kummer polynomial are coprime to the degree.** -/
theorem gcd_eq_one_of_irreducible_multiA {r n : ℕ} (hn : 0 < n) {t : Fin r → k} {e : Fin r → ℕ}
    (hirr : Irreducible
      (X ^ n - C (algebraMap (Polynomial k) (RatFunc k) (multiA t e)))) :
    Nat.gcd n (Finset.univ.gcd e) = 1 := by
  set d : ℕ := Nat.gcd n (Finset.univ.gcd e) with hd
  have hdn : d ∣ n := Nat.gcd_dvd_left _ _
  have hde : ∀ i, d ∣ e i := fun i =>
    (Nat.gcd_dvd_right _ _).trans (Finset.gcd_dvd (Finset.mem_univ i))
  by_contra hne
  have hd0 : d ≠ 0 := fun h => by simp [h] at hdn; omega
  have hd1 : 1 < d := by omega
  refine not_exists_pow_of_irreducible_X_pow_sub_C hn hirr hdn hd1
    ⟨algebraMap (Polynomial k) (RatFunc k) (multiA t fun i => e i / d), ?_⟩
  rw [← map_pow]
  congr 1
  simp only [multiA, ← Finset.prod_pow, ← pow_mul]
  exact Finset.prod_congr rfl fun i _ => by rw [Nat.div_mul_cancel (hde i)]

open Module in
/-- **A cover of the line with cyclic deck group is a multi-point Kummer cover whose exponents are
coprime to the degree.** -/
theorem exists_multiKummer_model_gcd (L : LineCover) [IsCyclic L.deck] :
    ∃ (r : ℕ) (t : Fin r → k) (e : Fin r → ℕ),
      Function.Injective t ∧ (∀ i, e i < finrank (RatFunc k) L.M) ∧
      Nat.gcd (finrank (RatFunc k) L.M) (Finset.univ.gcd e) = 1 ∧
      Irreducible (X ^ finrank (RatFunc k) L.M -
          C (algebraMap (Polynomial k) (RatFunc k) (multiA t e))) ∧
      IsSplittingField (RatFunc k) L.M
        (X ^ finrank (RatFunc k) L.M -
          C (algebraMap (Polynomial k) (RatFunc k) (multiA t e))) := by
  obtain ⟨r, t, e, hinj, hlt, hirr, hsplit⟩ := exists_multiKummer_model L
  exact ⟨r, t, e, hinj, hlt, gcd_eq_one_of_irreducible_multiA finrank_pos hirr, hirr, hsplit⟩

end Rigidity.RET
