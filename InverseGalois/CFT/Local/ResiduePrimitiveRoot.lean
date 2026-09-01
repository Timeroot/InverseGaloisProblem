/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.ResidueRootUnity

/-!
# A root of unity above a prescribed power of a primitive root

The multiplicative group of the residues modulo a prime is cyclic, so some natural number has the
property that the exponents for which its power is congruent to one are exactly the multiples of
one less than the prime.  Such a number is a primitive root, and its powers run through all the
nonzero residues.

A complete valued field whose residue characteristic is that prime therefore contains, for every
factorisation of one less than the prime, a primitive root of unity of the second factor whose
residue is the prescribed power of the primitive root.  The root of unity of order one less than
the prime lying above the primitive root is raised to the first factor; that power is congruent to
the same power of the number, and the multiplicative order of that power modulo the prime is
exactly the second factor.

Prescribing the residue is what makes the root of unity usable twice: the same natural number names
a root of unity in a field and in an extension of it, and two roots of unity with the same residue
coincide.

## Main results

* `InverseGalois.CFT.exists_natCast_primitiveRoot`: **a prime has a primitive root.**
* `InverseGalois.CFT.exists_isPrimitiveRoot_valued_sub_natCast_lt_one`: **a complete valued field of
  residue characteristic a prime contains, for every factorisation of one less than that prime, a
  primitive root of unity of the second factor congruent to the first power of a prescribed
  primitive root.**

## Tags

valued field, complete field, residue field, primitive root, root of unity, Teichmüller lift,
class field theory
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### A primitive root modulo a prime -/

/-- **A prime has a primitive root**: a natural number prime to it whose powers congruent to one
are exactly those of exponent a multiple of one less than the prime.  The multiplicative group of
the residues is cyclic, and a generator has that order. -/
theorem exists_natCast_primitiveRoot {q : ℕ} (hq : q.Prime) :
    ∃ b : ℕ, ¬ q ∣ b ∧ ∀ k : ℕ, q ∣ b ^ k - 1 → (q - 1) ∣ k := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units q]
  have hord : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  obtain ⟨b, hbcast⟩ : ∃ b : ℕ, ((b : ℕ) : ZMod q) = ((g : (ZMod q)ˣ) : ZMod q) :=
    ⟨((g : (ZMod q)ˣ) : ZMod q).val, by rw [ZMod.natCast_val, ZMod.cast_id]⟩
  have hb : ¬ q ∣ b := by
    intro hd
    have hz : ((b : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff b q).mpr hd
    rw [hbcast] at hz
    exact g.ne_zero hz
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero q)
  refine ⟨b, hb, fun k hk => ?_⟩
  have hk1 : 1 ≤ b ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
  have hz : ((b ^ k - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ q).mpr hk
  rw [Nat.cast_sub hk1, Nat.cast_pow, Nat.cast_one, sub_eq_zero, hbcast] at hz
  have hgk : g ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hz)
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hgk

/-! ### The root of unity above a power of a primitive root -/

section Lift

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {q e : ℕ}

/-- **A complete valued field of residue characteristic a prime contains, for every factorisation
of one less than that prime, a primitive root of unity of the second factor congruent to the first
power of a prescribed primitive root.**  The primitive root is congruent to a root of unity of
order one less than the prime, whose power by the first factor is congruent to the same power of
the primitive root; the multiplicative order of that power modulo the prime is the second
factor. -/
theorem exists_isPrimitiveRoot_valued_sub_natCast_lt_one (h : HasResidueChar A q e) {b N M : ℕ}
    (hb : ¬ q ∣ b) (hbord : ∀ k : ℕ, q ∣ b ^ k - 1 → (q - 1) ∣ k) (hN : N ≠ 0)
    (hMN : M * N = q - 1) :
    ∃ ζ : A, IsPrimitiveRoot ζ N ∧ Valued.v (ζ - ((b ^ M : ℕ) : A)) < 1 := by
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hMN
    omega
  obtain ⟨ξ, hξpow, hξb⟩ := exists_pow_sub_one_eq_one_valued_sub_natCast_lt_one h hb
  have hpow : (ξ ^ M) ^ N = 1 := by
    rw [← pow_mul, hMN, hξpow]
  have hval : Valued.v (ξ ^ M - ((b ^ M : ℕ) : A)) < 1 := by
    rw [Nat.cast_pow]
    exact valued_sub_pow_lt_one (valued_eq_one_of_pow_eq_one₀ hq10 hξpow).le
      (valued_natCast_le_one b) hξb M
  have hordM : ∀ k : ℕ, q ∣ (b ^ M) ^ k - 1 → N ∣ k := by
    intro k hk
    rw [← pow_mul] at hk
    have hdvd := hbord (M * k) hk
    rw [← hMN] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hM0)).mp hdvd
  exact ⟨ξ ^ M, isPrimitiveRoot_of_valued_sub_natCast_lt_one h hN hpow hval hordM, hval⟩

end Lift

end InverseGalois.CFT
