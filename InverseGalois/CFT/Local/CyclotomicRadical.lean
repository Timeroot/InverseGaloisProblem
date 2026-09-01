/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicResidue
import InverseGalois.CFT.Local.CyclotomicUniformiser
import InverseGalois.CFT.Local.PrimeResidue
import InverseGalois.CFT.Local.UnitPowRoot

/-!
# A radical of the opposite of the residue characteristic, and its Galois action

Over a complete valued field of residue characteristic an odd prime, adjoining a primitive root of
unity of that order produces an element whose power of exponent one less than the prime is the
opposite of the prime.  The difference of the root and one already has that power up to a factor
congruent to one, and a factor congruent to one has a root of every exponent prime to the residue
characteristic which is again congruent to one, so multiplying the difference by such a root
corrects the factor away.  The correcting factor being congruent to one, the radical so produced is
congruent to the difference of the root and one.

Such a radical carries the Teichmüller character.  An automorphism preserving the valuation fixes
the opposite of the prime, so it multiplies the radical by a root of unity of order dividing one
less than the prime, and that root of unity is congruent to the exponent to which the automorphism
raises the root of unity: the correcting factor contributes nothing because it is congruent to one,
and the difference of the root and one contributes the partial geometric sum, which is congruent to
the number of its terms.  A root of unity of order prime to the residue characteristic is determined
by its residue, so the multiplier is the Teichmüller lift of the exponent.

Raising the radical to a power descends it to any divisor of one less than the prime: the power of
exponent that divisor is again a radical, of the same opposite of the prime, and the automorphism
multiplies it by the corresponding power of the Teichmüller lift, which is congruent to the same
power of the exponent.  When that power of the exponent is congruent to one modulo the prime, the
multiplier is a root of unity of order prime to the residue characteristic congruent to one, hence
trivial, and the automorphism fixes the descended radical outright.

## Main results

* `InverseGalois.CFT.exists_pow_eq_neg_natCast`: **a primitive root of unity of odd prime order,
  minus one, becomes a radical of the opposite of that prime after multiplication by a factor
  congruent to one.**
* `InverseGalois.CFT.pow_aut_div_eq_one`: an automorphism multiplies such a radical by a root of
  unity of order dividing one less than the prime.
* `InverseGalois.CFT.valued_aut_div_sub_natCast_lt_one`: **the multiplier is congruent to the
  exponent to which the automorphism raises the root of unity.**
* `InverseGalois.CFT.aut_eq_mul_of_pow_eq_one`: **an automorphism multiplies such a radical by the
  root of unity of order dividing one less than the prime whose residue is that exponent.**
* `InverseGalois.CFT.isPrimitiveRoot_of_valued_sub_natCast_lt_one`: **a root of unity congruent to a
  natural number of that multiplicative order modulo the residue characteristic is primitive.**
* `InverseGalois.CFT.eq_one_of_valued_sub_natCast_lt_one`: **a root of unity of order prime to the
  residue characteristic congruent to a natural number congruent to one is one.**
* `InverseGalois.CFT.eq_one_of_dvd_pow_sub_one`: the Teichmüller multiplier is trivial when its
  exponent is.
* `InverseGalois.CFT.exists_pow_eq_neg_natCast_aut`: **a radical of the opposite of the prime of any
  exponent dividing one less than the prime, together with the root of unity by which a given
  automorphism multiplies it.**
* `InverseGalois.CFT.exists_pow_eq_neg_natCast_forall_aut`: **one such radical serves every
  automorphism at once.**

## Tags

valued field, complete field, root of unity, radical, Teichmüller character, residue
characteristic, ramification
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### The radical -/

section Radical

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {q e : ℕ} {ζ : A}

/-- **A primitive root of unity of odd prime order, minus one, becomes a radical of the opposite of
that prime after multiplication by a factor congruent to one.**  The power of exponent one less than
the prime of the difference of the root and one is the opposite of the prime times a factor
congruent to one, and such a factor is the corresponding power of a factor congruent to one, because
one less than the prime is prime to the residue characteristic. -/
theorem exists_pow_eq_neg_natCast (h : HasResidueChar A q e) (hodd : Odd q)
    (hζ : IsPrimitiveRoot ζ q) :
    ∃ μ : A, μ ^ (q - 1) = -((q : ℕ) : A) ∧ Valued.v (μ / (ζ - 1) - 1) < 1 := by
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  have hep : 0 < e := h.pos
  have hqv : Valued.v ((q : ℕ) : A) < 1 := by
    rw [h.val_p]
    simpa using WithZero.exp_lt_exp.mpr (show -(e : ℤ) < 0 by omega)
  have hζne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hq1)
  obtain ⟨u, hu1, hupow⟩ := exists_pow_sub_one_eq_neg_natCast_mul hq hodd hζ hqv
  have huv : Valued.v u = 1 := valued_eq_one_of_sub_one_lt_one hu1
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz, map_zero] at huv
    exact zero_ne_one huv
  have hUmem : (Units.mk0 u hu0)⁻¹ ∈ unitFiltration A 0 := by
    refine Subgroup.inv_mem _ ?_
    rw [mem_unitFiltration]
    simpa using le_exp_neg_one_of_lt_one hu1
  have hnd : ¬ q ∣ (q - 1) := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨y, hymem, hypow⟩ := exists_mem_unitFiltration_zero_pow_eq h hq10 hnd hUmem
  have hyval : ((y : A)) ^ (q - 1) = u⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, hypow, Units.val_inv_eq_inv_val, Units.val_mk0]
  refine ⟨(ζ - 1) * (y : A), ?_, ?_⟩
  · rw [mul_pow, hupow, hyval, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  · rw [mul_comm, mul_div_assoc, div_self hζne, mul_one]
    exact lt_one_of_le_exp_neg (by omega) (mem_unitFiltration.mp hymem)

end Radical

/-! ### The Galois action on the radical -/

section Action

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {q e : ℕ} {ζ μ : A} {σ : A ≃+* A}

/-- An automorphism multiplies a radical of the opposite of the residue characteristic by a root of
unity of order dividing one less than the residue characteristic: the automorphism fixes the
opposite of the prime, which is the power of the radical. -/
theorem pow_aut_div_eq_one (h : HasResidueChar A q e) (hμ : μ ^ (q - 1) = -((q : ℕ) : A)) :
    (σ μ / μ) ^ (q - 1) = 1 := by
  have hqne : ((q : ℕ) : A) ≠ 0 := h.natCast_ne_zero h.prime.ne_zero
  have hnum : (σ μ) ^ (q - 1) = -((q : ℕ) : A) := by
    rw [← map_pow, hμ, map_neg, map_natCast]
  rw [div_pow, hnum, hμ, div_self (neg_ne_zero.mpr hqne)]

/-- **An automorphism multiplies a radical of the opposite of the residue characteristic by an
element congruent to the exponent to which it raises the root of unity.**  The radical is the
difference of the root and one times a factor congruent to one; the factor contributes a quotient
congruent to one because the automorphism preserves the valuation, and the difference contributes
the partial geometric sum of the root with as many terms as the exponent, which is congruent to the
exponent. -/
theorem valued_aut_div_sub_natCast_lt_one (h : HasResidueChar A q e) (hζ : IsPrimitiveRoot ζ q)
    (hσv : ∀ x : A, Valued.v (σ x) = Valued.v x) {a : ℕ} (hσζ : σ ζ = ζ ^ a)
    (hμζ : Valued.v (μ / (ζ - 1) - 1) < 1) : Valued.v (σ μ / μ - (a : A)) < 1 := by
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hep : 0 < e := h.pos
  have hqv : Valued.v ((q : ℕ) : A) < 1 := by
    rw [h.val_p]
    simpa using WithZero.exp_lt_exp.mpr (show -(e : ℤ) < 0 by omega)
  have hζ1 : Valued.v (ζ - 1) < 1 := valued_sub_one_lt_one hq hζ hqv
  have hζv : Valued.v ζ = 1 := valued_eq_one_of_pow_eq_one₀ hq.ne_zero hζ.pow_eq_one
  have hζne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hq1)
  set w := μ / (ζ - 1) with hwdef
  have hwv : Valued.v w = 1 := valued_eq_one_of_sub_one_lt_one hμζ
  have hw0 : w ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hwv
    exact zero_ne_one hwv
  have hwμ : μ = (ζ - 1) * w := by
    rw [hwdef, mul_div_cancel₀ _ hζne]
  -- the correcting factor contributes a quotient congruent to one
  have hqw : Valued.v (σ w / w) = 1 := by
    rw [map_div₀, hσv, hwv, div_one]
  have hσw : Valued.v (σ w / w - 1) < 1 := by
    have hone : σ w / w - 1 = (σ w - w) / w := by
      field_simp
    have hdiff : Valued.v (σ w - w) < 1 := by
      have hsw : σ w - w = σ (w - 1) - (w - 1) := by
        rw [map_sub, map_one]
        ring
      rw [hsw]
      refine lt_of_le_of_lt (Valuation.map_sub Valued.v _ _) (max_lt ?_ hμζ)
      rw [hσv]
      exact hμζ
    rw [hone, map_div₀, hwv, div_one]
    exact hdiff
  -- the difference of the root and one contributes the partial geometric sum
  have hσμ : σ μ = (∑ i ∈ Finset.range a, ζ ^ i) * (ζ - 1) * σ w := by
    rw [hwμ, map_mul, map_sub, map_one, hσζ, geom_sum_mul]
  have hdiv : σ μ / μ = (∑ i ∈ Finset.range a, ζ ^ i) * (σ w / w) := by
    rw [hσμ, hwμ]
    field_simp
  have hSa : Valued.v ((∑ i ∈ Finset.range a, ζ ^ i) - (a : A)) < 1 :=
    valued_geomSum_sub_natCast_lt_one (le_of_eq hζv) hζ1 a
  have hkey : σ μ / μ - (a : A)
      = ((∑ i ∈ Finset.range a, ζ ^ i) - (a : A)) * (σ w / w) + (a : A) * (σ w / w - 1) := by
    rw [hdiv]
    ring
  rw [hkey]
  refine lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt ?_ ?_)
  · rw [Valuation.map_mul, hqw, mul_one]
    exact hSa
  · rw [Valuation.map_mul]
    calc Valued.v ((a : A)) * Valued.v (σ w / w - 1)
        ≤ 1 * Valued.v (σ w / w - 1) := mul_le_mul_left (valued_natCast_le_one a) _
      _ = Valued.v (σ w / w - 1) := one_mul _
      _ < 1 := hσw

/-- **An automorphism multiplies a radical of the opposite of the residue characteristic by the root
of unity of order dividing one less than the residue characteristic whose residue is the exponent to
which the automorphism raises the root of unity.**  The multiplier is such a root of unity and is
congruent to the exponent, and a root of unity of order prime to the residue characteristic is
determined by its residue. -/
theorem aut_eq_mul_of_pow_eq_one (h : HasResidueChar A q e) (hζ : IsPrimitiveRoot ζ q)
    (hσv : ∀ x : A, Valued.v (σ x) = Valued.v x) {a : ℕ} (hσζ : σ ζ = ζ ^ a)
    (hμ : μ ^ (q - 1) = -((q : ℕ) : A)) (hμζ : Valued.v (μ / (ζ - 1) - 1) < 1) {η : A}
    (hη : η ^ (q - 1) = 1) (hηa : Valued.v (η - (a : A)) < 1) : σ μ = η * μ := by
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  have hqne : ((q : ℕ) : A) ≠ 0 := h.natCast_ne_zero hq.ne_zero
  have hμ0 : μ ≠ 0 := by
    intro hz
    rw [hz, zero_pow hq10] at hμ
    exact hqne (neg_eq_zero.mp hμ.symm)
  have hnd : ¬ q ∣ (q - 1) := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hq1v : Valued.v (((q - 1 : ℕ) : A)) = 1 := by
    rw [h.valued_natCast hq10, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  have hroot : (σ μ / μ) ^ (q - 1) = 1 := pow_aut_div_eq_one h hμ
  have hres : Valued.v (σ μ / μ - (a : A)) < 1 :=
    valued_aut_div_sub_natCast_lt_one h hζ hσv hσζ hμζ
  have hsub : Valued.v (σ μ / μ - η) < 1 := by
    have hkey : σ μ / μ - η = (σ μ / μ - (a : A)) - (η - (a : A)) := by ring
    rw [hkey]
    exact lt_of_le_of_lt (Valuation.map_sub Valued.v _ _) (max_lt hres hηa)
  have heq := eq_of_valued_sub_lt_one hq10 hq1v hroot hη hsub
  rwa [div_eq_iff hμ0] at heq

end Action

/-! ### Recognising a primitive root of unity by its residue -/

section Primitive

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {q e : ℕ}

/-- **A root of unity congruent to a natural number of that multiplicative order modulo the residue
characteristic is primitive.**  Powers of the root of unity stay congruent to the corresponding
powers of the number, and a natural number congruent to one is divisible by the residue
characteristic after subtracting one, so a power of the root of unity is one only when the
corresponding power of the number is one modulo the residue characteristic. -/
theorem isPrimitiveRoot_of_valued_sub_natCast_lt_one (h : HasResidueChar A q e) {N : ℕ}
    (hN : N ≠ 0) {ξ : A} (hξ : ξ ^ N = 1) {b : ℕ} (hb : Valued.v (ξ - (b : A)) < 1)
    (hord : ∀ k : ℕ, q ∣ b ^ k - 1 → N ∣ k) : IsPrimitiveRoot ξ N := by
  have hqp := h.prime
  have hqv := valued_residueChar_lt_one h
  have hξv : Valued.v ξ = 1 := valued_eq_one_of_pow_eq_one₀ hN hξ
  have hbv : Valued.v ((b : A)) = 1 := by
    refine (Valuation.map_eq_of_sub_lt Valued.v ?_).trans hξv
    rw [Valuation.map_sub_swap, hξv]
    exact hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, map_zero] at hbv
    exact zero_ne_one hbv
  refine ⟨hξ, fun l hl => hord l ?_⟩
  have hpow : Valued.v (ξ ^ l - (b : A) ^ l) < 1 :=
    valued_sub_pow_lt_one hξv.le hbv.le hb l
  rw [hl] at hpow
  have hb1 : 1 ≤ b ^ l := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
  have hlt : Valued.v (((b ^ l - 1 : ℕ) : A)) < 1 := by
    rw [Nat.cast_sub hb1, Nat.cast_pow, Nat.cast_one,
      show (b : A) ^ l - 1 = -(1 - (b : A) ^ l) by ring, Valuation.map_neg]
    exact hpow
  by_contra hnd
  exact absurd (valued_natCast_eq_one_of_not_dvd hqp hqv hnd) (ne_of_lt hlt)

/-- **A root of unity of order prime to the residue characteristic congruent to a natural number
which is itself congruent to one is one.**  The number differs from one by a multiple of the residue
characteristic, so the root of unity is congruent to one, and a root of unity of order prime to the
residue characteristic is determined by its residue. -/
theorem eq_one_of_valued_sub_natCast_lt_one (h : HasResidueChar A q e) {N : ℕ} (hN : N ≠ 0)
    (hqN : ¬ q ∣ N) {ξ : A} (hξ : ξ ^ N = 1) {b : ℕ} (hb1 : 1 ≤ b)
    (hb : Valued.v (ξ - (b : A)) < 1) (hbq : q ∣ b - 1) : ξ = 1 := by
  have hNv : Valued.v ((N : ℕ) : A) = 1 :=
    valued_natCast_eq_one_of_not_dvd h.prime (valued_residueChar_lt_one h) hqN
  have hlt : Valued.v (((b - 1 : ℕ) : A)) < 1 := by
    obtain ⟨c, hc⟩ := hbq
    rw [hc, Nat.cast_mul, Valuation.map_mul]
    calc Valued.v ((q : ℕ) : A) * Valued.v ((c : ℕ) : A)
        ≤ Valued.v ((q : ℕ) : A) * 1 := mul_le_mul' le_rfl (valued_natCast_le_one c)
      _ = Valued.v ((q : ℕ) : A) := mul_one _
      _ < 1 := valued_residueChar_lt_one h
  rw [Nat.cast_sub hb1, Nat.cast_one] at hlt
  refine eq_one_of_valued_sub_one_lt_one hN hNv hξ ?_
  have hkey : ξ - 1 = (ξ - (b : A)) + ((b : A) - 1) := by ring
  rw [hkey]
  exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hb hlt)

/-- **The Teichmüller multiplier is trivial when its exponent is.**  The multiplier is congruent to
a power of a natural number, and that power is congruent to one modulo the residue characteristic,
so the multiplier is a root of unity of order prime to the residue characteristic congruent to
one. -/
theorem eq_one_of_dvd_pow_sub_one (h : HasResidueChar A q e) {M N : ℕ} (hN : N ≠ 0)
    (hqN : ¬ q ∣ N) {ξ : A} (hξ : ξ ^ N = 1) {a : ℕ} (ha : a ≠ 0)
    (hva : Valued.v (ξ - (a : A) ^ M) < 1) (hdvd : q ∣ a ^ M - 1) : ξ = 1 := by
  refine eq_one_of_valued_sub_natCast_lt_one h hN hqN hξ
    (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ha)) ?_ hdvd
  rwa [Nat.cast_pow]

end Primitive

/-! ### Descending the radical -/

section Descent

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {q e : ℕ} {ζ : A} {σ : A ≃+* A}

/-- **A radical of the opposite of the residue characteristic of any exponent dividing one less than
the residue characteristic, together with the root of unity by which a given automorphism multiplies
it.**  The power of the radical of full exponent by the complementary factor is such a radical, and
the automorphism multiplies it by the corresponding power of the Teichmüller lift, which is
congruent to the same power of the exponent to which the automorphism raises the root of unity. -/
theorem exists_pow_eq_neg_natCast_aut (h : HasResidueChar A q e) (hodd : Odd q)
    (hζ : IsPrimitiveRoot ζ q) (hσv : ∀ x : A, Valued.v (σ x) = Valued.v x) {a : ℕ}
    (hσζ : σ ζ = ζ ^ a) {M N : ℕ} (hMN : M * N = q - 1) :
    ∃ ν ξ : A, ν ^ N = -((q : ℕ) : A) ∧ σ ν = ξ * ν ∧ ξ ^ N = 1 ∧
      Valued.v (ξ - (a : A) ^ M) < 1 := by
  obtain ⟨μ, hμ, hμζ⟩ := exists_pow_eq_neg_natCast h hodd hζ
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  have hqne : ((q : ℕ) : A) ≠ 0 := h.natCast_ne_zero hq.ne_zero
  have hμ0 : μ ≠ 0 := by
    intro hz
    rw [hz, zero_pow hq10] at hμ
    exact hqne (neg_eq_zero.mp hμ.symm)
  have hηpow : (σ μ / μ) ^ (q - 1) = 1 := pow_aut_div_eq_one h hμ
  have hηa : Valued.v (σ μ / μ - (a : A)) < 1 :=
    valued_aut_div_sub_natCast_lt_one h hζ hσv hσζ hμζ
  have hσμ : σ μ = (σ μ / μ) * μ := (div_mul_cancel₀ _ hμ0).symm
  have hηv : Valued.v (σ μ / μ) = 1 := by
    rw [map_div₀, hσv, div_self ((Valuation.ne_zero_iff _).mpr hμ0)]
  refine ⟨μ ^ M, (σ μ / μ) ^ M, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, hMN, hμ]
  · rw [map_pow, ← mul_pow, ← hσμ]
  · rw [← pow_mul, hMN, hηpow]
  · exact valued_sub_pow_lt_one hηv.le (valued_natCast_le_one a) hηa M

/-- **One radical of the opposite of the residue characteristic serves every automorphism at
once.**  The radical is chosen before any automorphism is named, and each automorphism then
multiplies it by a root of unity congruent to the corresponding power of the exponent to which it
raises the root of unity; when that power is congruent to one modulo the prime, the automorphism
fixes the radical outright. -/
theorem exists_pow_eq_neg_natCast_forall_aut (h : HasResidueChar A q e) (hodd : Odd q)
    (hζ : IsPrimitiveRoot ζ q) {M N : ℕ} (hMN : M * N = q - 1) :
    ∃ ν : A, ν ^ N = -((q : ℕ) : A) ∧
      (∀ τ : A ≃+* A, (∀ x : A, Valued.v (τ x) = Valued.v x) → ∀ a : ℕ, τ ζ = ζ ^ a →
        ∃ ξ : A, τ ν = ξ * ν ∧ ξ ^ N = 1 ∧ Valued.v (ξ - (a : A) ^ M) < 1) ∧
      ∀ τ : A ≃+* A, (∀ x : A, Valued.v (τ x) = Valued.v x) → ∀ a : ℕ, τ ζ = ζ ^ a →
        q ∣ a ^ M - 1 → τ ν = ν := by
  obtain ⟨μ, hμ, hμζ⟩ := exists_pow_eq_neg_natCast h hodd hζ
  have hq := h.prime
  have hq1 : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  have hqne : ((q : ℕ) : A) ≠ 0 := h.natCast_ne_zero hq.ne_zero
  have hμ0 : μ ≠ 0 := by
    intro hz
    rw [hz, zero_pow hq10] at hμ
    exact hqne (neg_eq_zero.mp hμ.symm)
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hq10 (by simpa using hMN.symm)
  have hqN : ¬ q ∣ N := by
    intro hd
    have hle : N ≤ q - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hq10) ⟨M, by rw [← hMN, mul_comm]⟩
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd
    omega
  have hmain : ∀ τ : A ≃+* A, (∀ x : A, Valued.v (τ x) = Valued.v x) → ∀ a : ℕ, τ ζ = ζ ^ a →
      ∃ ξ : A, τ (μ ^ M) = ξ * μ ^ M ∧ ξ ^ N = 1 ∧ Valued.v (ξ - (a : A) ^ M) < 1 := by
    intro τ hτv a hτζ
    have hηpow : (τ μ / μ) ^ (q - 1) = 1 := pow_aut_div_eq_one h hμ
    have hηa : Valued.v (τ μ / μ - (a : A)) < 1 :=
      valued_aut_div_sub_natCast_lt_one h hζ hτv hτζ hμζ
    have hτμ : τ μ = (τ μ / μ) * μ := (div_mul_cancel₀ _ hμ0).symm
    have hηv : Valued.v (τ μ / μ) = 1 := by
      rw [map_div₀, hτv, div_self ((Valuation.ne_zero_iff _).mpr hμ0)]
    exact ⟨(τ μ / μ) ^ M, by rw [map_pow, ← mul_pow, ← hτμ], by rw [← pow_mul, hMN, hηpow],
      valued_sub_pow_lt_one hηv.le (valued_natCast_le_one a) hηa M⟩
  refine ⟨μ ^ M, by rw [← pow_mul, hMN, hμ], hmain, fun τ hτv a hτζ hdvd => ?_⟩
  obtain ⟨ξ, hξμ, hξN, hξa⟩ := hmain τ hτv a hτζ
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hτζ
    exact hζ.ne_one hq1 (τ.injective (by rw [hτζ, map_one]))
  rw [hξμ, eq_one_of_dvd_pow_sub_one h hN0 hqN hξN ha0 hξa hdvd, one_mul]

end Descent

end InverseGalois.CFT
