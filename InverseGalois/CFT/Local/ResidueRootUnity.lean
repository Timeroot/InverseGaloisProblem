/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.CyclotomicRadical

/-!
# Lifting the roots of unity of the residue field

A complete valued field of residue characteristic `q` contains a root of unity of order one less
than `q` above every natural number prime to `q`.  Fermat's little theorem makes the power of
exponent `q - 1` of such a number congruent to one, a factor congruent to one has a root of every
exponent prime to the residue characteristic which is again congruent to one, and dividing the
number by such a root turns the congruence into an equation without moving the residue.

Choosing the number to be a primitive root modulo `q` makes the resulting root of unity primitive
of order `q - 1`, and raising it to the complementary power produces a primitive root of unity of
any prescribed order dividing `q - 1`: powers of a root of unity of order prime to the residue
characteristic stay congruent to the corresponding powers of the number, and the number has the
prescribed multiplicative order modulo `q`.

## Main results

* `InverseGalois.CFT.valued_natCast_lt_one_of_dvd`: a multiple of the residue characteristic has
  valuation less than one.
* `InverseGalois.CFT.exists_pow_sub_one_eq_one_valued_sub_natCast_lt_one`: **a natural number prime
  to the residue characteristic is congruent to a root of unity of order one less than that
  characteristic.**
* `InverseGalois.CFT.exists_isPrimitiveRoot_of_dvd_sub_one`: **a complete valued field of residue
  characteristic `q` contains a primitive root of unity of every order dividing `q - 1`.**

## Tags

valued field, complete field, residue field, root of unity, Fermat's little theorem, primitive
root, Teichmüller lift
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### Multiples of the residue characteristic -/

section Dvd

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {q e : ℕ}

/-- **A multiple of the residue characteristic has valuation less than one.**  The valuation is
that of the residue characteristic times that of the cofactor, and the latter is at most one. -/
theorem valued_natCast_lt_one_of_dvd (h : HasResidueChar A q e) {n : ℕ} (hn : q ∣ n) :
    Valued.v ((n : ℕ) : A) < 1 := by
  obtain ⟨c, rfl⟩ := hn
  rw [Nat.cast_mul, Valuation.map_mul]
  calc Valued.v ((q : ℕ) : A) * Valued.v ((c : ℕ) : A)
      ≤ Valued.v ((q : ℕ) : A) * 1 := mul_le_mul' le_rfl (valued_natCast_le_one c)
    _ = Valued.v ((q : ℕ) : A) := mul_one _
    _ < 1 := valued_residueChar_lt_one h

end Dvd

/-! ### Roots of unity above a natural number -/

section Lift

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {q e : ℕ}

/-- **A natural number prime to the residue characteristic is congruent to a root of unity of order
one less than that characteristic.**  Fermat's little theorem makes the power of exponent `q - 1`
of the number congruent to one, and such a factor is the corresponding power of a factor congruent
to one, because `q - 1` is prime to the residue characteristic; dividing the number by that factor
leaves the residue unchanged. -/
theorem exists_pow_sub_one_eq_one_valued_sub_natCast_lt_one (h : HasResidueChar A q e) {b : ℕ}
    (hb : ¬ q ∣ b) : ∃ ξ : A, ξ ^ (q - 1) = 1 ∧ Valued.v (ξ - (b : A)) < 1 := by
  haveI : Fact q.Prime := ⟨h.prime⟩
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero q)
  have hbv : Valued.v ((b : ℕ) : A) = 1 :=
    valued_natCast_eq_one_of_not_dvd hq (valued_residueChar_lt_one h) hb
  have hbne : ((b : ℕ) : A) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hbv
    exact zero_ne_one hbv
  -- Fermat's little theorem
  have hbz : ((b : ℕ) : ZMod q) ≠ 0 := fun hz => hb ((ZMod.natCast_eq_zero_iff b q).mp hz)
  have hferm : ((b : ℕ) : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hbz
  have hb1 : 1 ≤ b ^ (q - 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
  have hdvd : q ∣ b ^ (q - 1) - 1 := by
    refine (ZMod.natCast_eq_zero_iff _ q).mp ?_
    rw [Nat.cast_sub hb1, Nat.cast_pow, Nat.cast_one, hferm, sub_self]
  obtain ⟨c, hc⟩ := hdvd
  have hnat : b ^ (q - 1) = q * c + 1 := by omega
  have hu1 : Valued.v (((b : ℕ) : A) ^ (q - 1) - 1) < 1 := by
    have hcast : ((b : ℕ) : A) ^ (q - 1) - 1 = ((q * c : ℕ) : A) := by
      have hh := congrArg (fun m : ℕ => (m : A)) hnat
      push_cast at hh ⊢
      rw [hh]
      ring
    rw [hcast]
    exact valued_natCast_lt_one_of_dvd h ⟨c, rfl⟩
  -- correct the power of exponent `q - 1` by a factor congruent to one
  have hbpow : ((b : ℕ) : A) ^ (q - 1) ≠ 0 := pow_ne_zero _ hbne
  have hUmem : Units.mk0 (((b : ℕ) : A) ^ (q - 1)) hbpow ∈ unitFiltration A 0 := by
    rw [mem_unitFiltration]
    simpa using le_exp_neg_one_of_lt_one hu1
  have hnd : ¬ q ∣ (q - 1) := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨y, hymem, hypow⟩ := exists_mem_unitFiltration_zero_pow_eq h hq10 hnd hUmem
  have hy1 : Valued.v ((y : A) - 1) < 1 :=
    lt_one_of_le_exp_neg (by omega) (mem_unitFiltration.mp hymem)
  have hyv : Valued.v ((y : A)) = 1 := valued_eq_one_of_sub_one_lt_one hy1
  have hy0 : ((y : Aˣ) : A) ≠ 0 := y.ne_zero
  have hyq : ((y : A)) ^ (q - 1) = ((b : ℕ) : A) ^ (q - 1) := by
    rw [← Units.val_pow_eq_pow_val, hypow, Units.val_mk0]
  refine ⟨((b : ℕ) : A) / (y : A), ?_, ?_⟩
  · rw [div_pow, hyq, div_self hbpow]
  · have hsplit : ((b : ℕ) : A) / (y : A) - ((b : ℕ) : A)
        = (((b : ℕ) : A) * (1 - (y : A))) / (y : A) := by
      field_simp
    rw [hsplit, map_div₀, hyv, div_one, Valuation.map_mul, hbv, one_mul,
      show (1 : A) - (y : A) = -(((y : A)) - 1) by ring, Valuation.map_neg]
    exact hy1

/-- **A complete valued field of residue characteristic `q` contains a primitive root of unity of
every order dividing `q - 1`.**  A primitive root modulo `q` is congruent to a root of unity of
order `q - 1`, and the power of that root of unity by the complementary factor is congruent to the
same power of the primitive root, whose multiplicative order modulo `q` is the prescribed one. -/
theorem exists_isPrimitiveRoot_of_dvd_sub_one (h : HasResidueChar A q e) {N : ℕ} (hN : N ≠ 0)
    (hNq : N ∣ q - 1) : ∃ ξ : A, IsPrimitiveRoot ξ N := by
  haveI : Fact q.Prime := ⟨h.prime⟩
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  obtain ⟨M, hM⟩ := hNq
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hM
    omega
  -- a primitive root modulo the residue characteristic
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
  have hbord : ∀ k : ℕ, q ∣ b ^ k - 1 → (q - 1) ∣ k := by
    intro k hk
    have hk1 : 1 ≤ b ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
    have hz : ((b ^ k - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ q).mpr hk
    rw [Nat.cast_sub hk1, Nat.cast_pow, Nat.cast_one, sub_eq_zero, hbcast] at hz
    have hgk : g ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hz)
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hgk
  obtain ⟨ξ, hξpow, hξb⟩ := exists_pow_sub_one_eq_one_valued_sub_natCast_lt_one h hb
  have hpow : (ξ ^ M) ^ N = 1 := by
    rw [← pow_mul, mul_comm M N, ← hM, hξpow]
  have hval : Valued.v (ξ ^ M - ((b ^ M : ℕ) : A)) < 1 := by
    rw [Nat.cast_pow]
    exact valued_sub_pow_lt_one (valued_eq_one_of_pow_eq_one₀ hq10 hξpow).le
      (valued_natCast_le_one b) hξb M
  have hordM : ∀ k : ℕ, q ∣ (b ^ M) ^ k - 1 → N ∣ k := by
    intro k hk
    rw [← pow_mul] at hk
    have hdvd := hbord (M * k) hk
    rw [hM, mul_comm N M] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hM0)).mp hdvd
  exact ⟨ξ ^ M, isPrimitiveRoot_of_valued_sub_natCast_lt_one h hN hpow hval hordM⟩

end Lift

end InverseGalois.CFT
