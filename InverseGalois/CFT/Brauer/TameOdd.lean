/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TamePower

/-!
# The tame norm residue symbol at a generator of the residues

For an exponent which is not prime the tame norm residue symbol of a uniformiser against an
arbitrary unit of the valuation ring is no longer determined by the power residue exponent of that
unit alone: a unit which is a power of prime order dividing the exponent, without being a power of
the full exponent, has a symbol which is a nontrivial root of unity while its level is a proper
subextension.

The way around this is to compute the symbol against a single unit and to propagate the answer by
multiplicativity.  A unit whose power residue exponent is one is not a power of any prime order
dividing the exponent, since otherwise the corresponding power of the chosen root of unity would be
congruent to one, hence equal to one; so the level of such a unit has the full degree and the
symbol of a uniformiser against it is the reciprocal of a primitive root of unity.  Any unit
congruent to a power of it is then that power times a unit congruent to one, and a unit congruent
to one is an exact power, whose symbol is trivial.

## Main results

* `InverseGalois.CFT.not_isPow_of_valued_sub_pow_lt_one`: **a unit of power residue exponent one is
  not a power of any prime order dividing the exponent.**
* `InverseGalois.CFT.localSymbol_uniformiser_eq_powerResidue_of_exponent_one`: **the tame norm
  residue symbol of a uniformiser against a unit of power residue exponent one** is the class,
  modulo the integers, of minus the reciprocal of the exponent.
* `InverseGalois.CFT.localSymbol_uniformiser_eq_powerResidue_of_congr`: **the tame norm residue
  symbol of a uniformiser against a unit congruent to a power of such a unit** is the class, modulo
  the integers, of the opposite of that power divided by the exponent.
* `InverseGalois.CFT.localSymbol_eq_powerResidue_of_congr`, and
  `InverseGalois.CFT.localSymbol_unit_eq_powerResidue_of_congr`: the same symbol for a uniformiser
  normalised the other way, and with the two arguments exchanged.

## Tags

norm residue symbol, power residue symbol, tame symbol, local field, residue field, Kummer theory,
class field theory
-/

namespace InverseGalois.CFT

open scoped Valued WithZero

/-! ### A unit of power residue exponent one -/

section Root

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

omit [CompleteSpace K] [PerfectField K] in
/-- **A unit of power residue exponent one is not a power of any prime order dividing the
exponent.**  Were it the power of order a prime divisor of the exponent, its power by the quotient
of one less than the number of residues by the exponent, raised to the complementary divisor of the
exponent, would be a power of the unit by one less than the number of residues, hence congruent to
one; so would then be the same power of the chosen root of unity, which is therefore one, and that
contradicts the primitivity of the root. -/
theorem not_isPow_of_valued_sub_pow_lt_one (hres : HasResidueChar K p e)
    (hζ : IsPrimitiveRoot ζ n) (hpn : ¬ p ∣ n) {u : Kˣ} (hu : Valued.v (u : K) = 1)
    (hu1 : Valued.v (ζ - (u : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) {ℓ : ℕ}
    (hl : ℓ.Prime) (hln : ℓ ∣ n) : ¬ ∃ c : Kˣ, c ^ ℓ = u := by
  rintro ⟨c, hc⟩
  have hn0 : n ≠ 0 := NeZero.ne n
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnv : Valued.v ((n : ℕ) : K) = 1 :=
    valued_natCast_eq_one_of_not_dvd hres.prime (valued_residueChar_lt_one hres) hpn
  have hdvd : n ∣ Nat.card (DivisionResidue K K) - 1 :=
    dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot (K := K) (L := K) hζ
      (norm_natCast_of_not_dvd hres hpn)
  set M := (Nat.card (DivisionResidue K K) - 1) / n with hM
  have hMn : n * M = Nat.card (DivisionResidue K K) - 1 := Nat.mul_div_cancel' hdvd
  have hζv : Valued.v ζ = 1 :=
    valued_eq_one_of_pow_valued_eq_one hn0 (by rw [hζ.pow_eq_one, map_one])
  have huM : Valued.v ((u : K) ^ M) ≤ 1 := le_of_eq (by rw [map_pow, hu, one_pow])
  have hstep : Valued.v (ζ ^ (n / ℓ) - ((u : K) ^ M) ^ (n / ℓ)) < 1 :=
    valued_sub_pow_lt_one (le_of_eq hζv) huM hu1 (n / ℓ)
  have hcu : (c : K) ^ ℓ = (u : K) := by rw [← Units.val_pow_eq_pow_val, hc]
  have hcv : Valued.v (c : K) = 1 :=
    valued_eq_one_of_pow_valued_eq_one hl.ne_zero (by rw [hcu, hu])
  have harith : ℓ * (M * (n / ℓ)) = Nat.card (DivisionResidue K K) - 1 := by
    have h1 : ℓ * (n / ℓ) = n := Nat.mul_div_cancel' hln
    calc ℓ * (M * (n / ℓ)) = M * (ℓ * (n / ℓ)) := by ring
      _ = M * n := by rw [h1]
      _ = n * M := by ring
      _ = Nat.card (DivisionResidue K K) - 1 := hMn
  have hsplit : ((u : K) ^ M) ^ (n / ℓ) = (c : K) ^ (Nat.card (DivisionResidue K K) - 1) := by
    rw [← hcu, ← pow_mul, ← pow_mul, harith]
  have hfermat : Valued.v ((c : K) ^ (Nat.card (DivisionResidue K K) - 1) - 1) < 1 :=
    valued_pow_card_sub_one_sub_one_lt_one hcv
  have hlt : Valued.v (ζ ^ (n / ℓ) - 1) < 1 := by
    have hkey : ζ ^ (n / ℓ) - 1
        = (ζ ^ (n / ℓ) - ((u : K) ^ M) ^ (n / ℓ))
          + ((c : K) ^ (Nat.card (DivisionResidue K K) - 1) - 1) := by
      rw [hsplit]
      ring
    rw [hkey]
    exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hstep hfermat)
  have hpz : (ζ ^ (n / ℓ)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have heq : ζ ^ (n / ℓ) = 1 := eq_one_of_valued_sub_one_lt_one hn0 hnv hpz hlt
  have hle : n ≤ n / ℓ :=
    Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hnpos hln) hl.pos) (hζ.dvd_of_pow_eq_one _ heq)
  exact absurd hle (Nat.not_le.mpr (Nat.div_lt_self hnpos hl.one_lt))

/-- **The tame norm residue symbol of a uniformiser against a unit of power residue exponent one**
is the class, modulo the integers, of minus the reciprocal of the exponent.  Such a unit is not a
power of any prime order dividing the exponent, so the symbol reads its power residue exponent. -/
theorem localSymbol_uniformiser_eq_powerResidue_of_exponent_one (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : IsRadicalExponent n) (hpn : ¬ p ∣ n)
    {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = 1) {u : Kˣ} (hu : Valued.v (u : K) = 1)
    (hu1 : Valued.v (ζ - (u : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) :
    localSymbol hres hm hζ π u = Multiplicative.ofAdd (zmodQModZ n (-(1 : ZMod n))) := by
  have hkey := localSymbol_uniformiser_eq_powerResidue hres hm hζ hn hpn hπ hu
    (fun ℓ hl hln => not_isPow_of_valued_sub_pow_lt_one hres hζ hpn hu hu1 hl hln) (j := 1)
    (by rwa [pow_one])
  rwa [Nat.cast_one] at hkey

/-! ### Propagating the symbol by multiplicativity -/

/-- **The tame norm residue symbol of a uniformiser against a unit congruent to a power of a unit
of power residue exponent one** is the class, modulo the integers, of the opposite of that power
divided by the exponent.  The quotient of the two is congruent to one, hence an exact power, and
the symbol against an exact power is trivial. -/
theorem localSymbol_uniformiser_eq_powerResidue_of_congr (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : IsRadicalExponent n) (hpn : ¬ p ∣ n)
    {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = 1) {u : Kˣ} (hu : Valued.v (u : K) = 1)
    (hu1 : Valued.v (ζ - (u : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) {b : Kˣ}
    {c : ℕ} (hbc : Valued.v ((b : K) - (u : K) ^ c) < 1) :
    localSymbol hres hm hζ π b = Multiplicative.ofAdd (zmodQModZ n (-(c : ZMod n))) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hucv : Valued.v ((u : K) ^ c) = 1 := by rw [map_pow, hu, one_pow]
  have hu0 : (u : K) ^ c ≠ 0 := pow_ne_zero c u.ne_zero
  have hinvv : Valued.v (((u : K) ^ c)⁻¹) = 1 := by rw [map_inv₀, hucv, inv_one]
  have hbv : Valued.v (b : K) = 1 := by
    have h := Valued.v.map_eq_of_sub_lt (x := (u : K) ^ c) (y := (b : K)) (by rw [hucv]; exact hbc)
    rwa [hucv] at h
  have hwval : ((b * (u ^ c)⁻¹ : Kˣ) : K) = (b : K) * ((u : K) ^ c)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hwv : Valued.v ((b * (u ^ c)⁻¹ : Kˣ) : K) = 1 := by
    rw [hwval, map_mul, hbv, hinvv, one_mul]
  have hw1 : Valued.v (((b * (u ^ c)⁻¹ : Kˣ) : K) - ((1 : Kˣ) : K) ^ n) < 1 := by
    have hkey : ((b * (u ^ c)⁻¹ : Kˣ) : K) - ((1 : Kˣ) : K) ^ n
        = ((b : K) - (u : K) ^ c) * ((u : K) ^ c)⁻¹ := by
      rw [hwval, Units.val_one, one_pow]
      field_simp
    rw [hkey, map_mul, hinvv, mul_one]
    exact hbc
  obtain ⟨y, hy⟩ := exists_pow_eq_of_valued_sub_lt_one hres hn0 hpn hwv hw1
  have hbw : b = u ^ c * (b * (u ^ c)⁻¹) := by
    rw [mul_comm b ((u ^ c)⁻¹), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hbw, map_mul, localSymbol_eq_one_of_isPow_right hres hm hζ π ⟨y, hy⟩, mul_one, map_pow,
    localSymbol_uniformiser_eq_powerResidue_of_exponent_one hres hm hζ hn hpn hπ hu hu1,
    ← ofAdd_nsmul, ← map_nsmul, nsmul_eq_mul, mul_neg_one]

/-- **The tame norm residue symbol of a uniformiser against a unit congruent to a power of a unit
of power residue exponent one**, for a uniformiser normalised so that its divided valuation is
minus one: the sign of the exponent then disappears.  The reciprocal of such a uniformiser has
divided valuation one, and the symbol is multiplicative. -/
theorem localSymbol_eq_powerResidue_of_congr (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hn : IsRadicalExponent n) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = -1) {u : Kˣ} (hu : Valued.v (u : K) = 1)
    (hu1 : Valued.v (ζ - (u : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) {b : Kˣ}
    {c : ℕ} (hbc : Valued.v ((b : K) - (u : K) ^ c) < 1) :
    localSymbol hres hm hζ π b = Multiplicative.ofAdd (zmodQModZ n (c : ZMod n)) := by
  have hinv : unitValDiv hm (Additive.ofMul π⁻¹) = 1 := by
    have hneg : Additive.ofMul π⁻¹ = -(Additive.ofMul π) := rfl
    rw [hneg, map_neg, hπ, neg_neg]
  have hkey :=
    localSymbol_uniformiser_eq_powerResidue_of_congr hres hm hζ hn hpn hinv hu hu1 hbc
  have hmul : localSymbol hres hm hζ π b * localSymbol hres hm hζ π⁻¹ b = 1 := by
    rw [← MonoidHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, MonoidHom.one_apply]
  rw [eq_inv_iff_mul_eq_one.2 hmul, hkey, map_neg, ofAdd_neg, inv_inv]

/-- **The tame norm residue symbol of a unit congruent to a power of a unit of power residue
exponent one against a uniformiser** whose divided valuation is minus one: it is the class, modulo
the integers, of the opposite of that power, divided by the exponent.  The symbol is skew
symmetric, so the two orders of the arguments differ by a sign. -/
theorem localSymbol_unit_eq_powerResidue_of_congr (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : IsRadicalExponent n) (hpn : ¬ p ∣ n)
    {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = -1) {u : Kˣ} (hu : Valued.v (u : K) = 1)
    (hu1 : Valued.v (ζ - (u : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) {b : Kˣ}
    {c : ℕ} (hbc : Valued.v ((b : K) - (u : K) ^ c) < 1) :
    localSymbol hres hm hζ b π = Multiplicative.ofAdd (zmodQModZ n (-(c : ZMod n))) := by
  have hswap := localSymbol_mul_swap hres hm hζ π b
  rw [localSymbol_eq_powerResidue_of_congr hres hm hζ hn hpn hπ hu hu1 hbc] at hswap
  rw [eq_inv_of_mul_eq_one_right hswap, map_neg, ofAdd_neg]

end Root

end InverseGalois.CFT
