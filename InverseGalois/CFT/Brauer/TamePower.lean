/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TameResidue

/-!
# The tame norm residue symbol against an arbitrary unit

The value of the tame norm residue symbol of a uniformiser against a unit of the valuation ring is
the class, modulo the integers, of the opposite of the power residue exponent of that unit divided
by the exponent, with no hypothesis on the unit at all.  Only the case of a unit which is a power
is new: there the symbol is trivial, and so is the power residue exponent.

Indeed the power of a unit by one less than the number of residues is congruent to one, so a unit
which is an exact power has its power by the quotient of one less than the number of residues by
the exponent congruent to one.  The power of the chosen root of unity naming the power residue
exponent is then congruent to one as well, hence equal to one, because a root of unity of order
prime to the residue characteristic is determined by its residue; the exponent therefore divides
the power residue exponent.

## Main results

* `InverseGalois.CFT.valued_pow_card_sub_one_sub_one_lt_one`: **an element of value one has its
  power by one less than the number of residues congruent to one.**
* `InverseGalois.CFT.natCast_eq_zero_of_isPow`: **the power residue exponent of a unit of the
  valuation ring which is an exact power vanishes.**
* `InverseGalois.CFT.localSymbol_uniformiser_eq_powerResidue_of_valued_eq_one`: **the tame norm
  residue symbol of a uniformiser against any unit of the valuation ring is the class, modulo the
  integers, of the opposite of the power residue exponent of the unit, divided by the exponent.**

## Tags

norm residue symbol, power residue symbol, tame symbol, local field, residue field, Kummer theory,
class field theory
-/

namespace InverseGalois.CFT

open scoped Valued WithZero

/-! ### Fermat's little theorem in the residue field -/

section Fermat

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]

omit [CompleteSpace K] [ProperSpace K] in
/-- The absolute value of a local field, read as the absolute value of the trivial extension. -/
theorem divisionNorm_self_eq_norm (x : K) : divisionNorm K K x = ‖x‖ := by
  simpa using divisionNorm_algebraMap (K := K) (D := K) x

omit [CompleteSpace K] in
/-- **An element of value one has its power by one less than the number of residues congruent to
one.**  The residues form a finite field, and that many elements lie in its multiplicative
group. -/
theorem valued_pow_card_sub_one_sub_one_lt_one {x : K} (hx : Valued.v x = 1) :
    Valued.v (x ^ (Nat.card (DivisionResidue K K) - 1) - 1) < 1 := by
  have hnx : divisionNorm K K x = 1 := by
    rw [divisionNorm_self_eq_norm]
    exact (norm_eq_one_iff_valued x).2 hx
  have hkey := divisionNorm_pow_card_sub_one_sub_lt_one hnx
  rw [divisionNorm_self_eq_norm] at hkey
  exact Valued.toNormedField.norm_lt_one_iff.1 hkey

omit [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K] in
/-- An element a nontrivial power of which has value one has value one. -/
theorem valued_eq_one_of_pow_valued_eq_one {x : K} {N : ℕ} (hN : N ≠ 0)
    (hx : Valued.v (x ^ N) = 1) : Valued.v x = 1 := by
  rw [map_pow] at hx
  rcases lt_trichotomy (Valued.v x) 1 with hlt | heq | hgt
  · exact absurd hx (ne_of_lt (pow_lt_one₀ zero_le' hlt hN))
  · exact heq
  · exact absurd hx (ne_of_gt (one_lt_pow₀ hgt hN))

end Fermat

/-! ### The power residue exponent of a power -/

section Root

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

omit [CompleteSpace K] [PerfectField K] in
/-- **The power residue exponent of a unit of the valuation ring which is an exact power
vanishes.**  The power of the unit by the quotient of one less than the number of residues by the
exponent is the power of its root by one less than the number of residues, hence congruent to one;
so is therefore the power of the chosen root of unity naming the exponent, and a root of unity of
order prime to the residue characteristic congruent to one is one. -/
theorem natCast_eq_zero_of_isPow (hres : HasResidueChar K p e) (hζ : IsPrimitiveRoot ζ n)
    (hpn : ¬ p ∣ n) {b : Kˣ} (hb : Valued.v (b : K) = 1) (hbp : ∃ c : Kˣ, c ^ n = b) {j : ℕ}
    (hj : Valued.v (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) :
    ((j : ℕ) : ZMod n) = 0 := by
  have hn0 : n ≠ 0 := NeZero.ne n
  have hnv : Valued.v ((n : ℕ) : K) = 1 :=
    valued_natCast_eq_one_of_not_dvd hres.prime (valued_residueChar_lt_one hres) hpn
  have hdvd : n ∣ Nat.card (DivisionResidue K K) - 1 :=
    dvd_card_divisionResidue_sub_one_of_isPrimitiveRoot (K := K) (L := K) hζ
      (norm_natCast_of_not_dvd hres hpn)
  obtain ⟨c, hc⟩ := hbp
  have hcb : ((c : K)) ^ n = (b : K) := by
    rw [← Units.val_pow_eq_pow_val, hc]
  have hcv : Valued.v ((c : K)) = 1 :=
    valued_eq_one_of_pow_valued_eq_one hn0 (by rw [hcb, hb])
  have hsplit : (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)
      = ((c : K)) ^ (Nat.card (DivisionResidue K K) - 1) := by
    rw [← hcb, ← pow_mul, Nat.mul_div_cancel' hdvd]
  have hfermat : Valued.v (((c : K)) ^ (Nat.card (DivisionResidue K K) - 1) - 1) < 1 :=
    valued_pow_card_sub_one_sub_one_lt_one hcv
  have hlt : Valued.v (ζ ^ j - 1) < 1 := by
    have hkey : ζ ^ j - 1
        = (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n))
          + (((c : K)) ^ (Nat.card (DivisionResidue K K) - 1) - 1) := by
      rw [hsplit]
      ring
    rw [hkey]
    exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hj hfermat)
  have hpz : (ζ ^ j) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have heq : ζ ^ j = 1 := eq_one_of_valued_sub_one_lt_one hn0 hnv hpz hlt
  exact (ZMod.natCast_eq_zero_iff j n).mpr (hζ.dvd_of_pow_eq_one j heq)

/-- **The tame norm residue symbol of a uniformiser against any unit of the valuation ring is the
power residue symbol of that unit**: it is the class, modulo the integers, of the opposite of an
exponent whose power of the chosen root of unity is congruent to the power of the unit by the
quotient of one less than the number of residues by the exponent, divided by the exponent.  No
hypothesis is made on the unit: if it is an exact power both sides are trivial. -/
theorem localSymbol_uniformiser_eq_powerResidue_of_valued_eq_one (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {b : Kˣ} (hb : Valued.v (b : K) = 1) {j : ℕ}
    (hj : Valued.v (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) :
    localSymbol hres hm hζ π b = Multiplicative.ofAdd (zmodQModZ n (-(j : ZMod n))) := by
  by_cases hnp : ∃ c : Kˣ, c ^ n = b
  · rw [localSymbol_eq_one_of_isPow_right hres hm hζ π hnp,
      natCast_eq_zero_of_isPow hres hζ hpn hb hnp hj, neg_zero, map_zero, ofAdd_zero]
  · exact localSymbol_uniformiser_eq_powerResidue hres hm hζ hn hpn hπ hb hnp hj

/-- **The tame norm residue symbol of a uniformiser against any unit of the valuation ring**, for a
uniformiser normalised so that its divided valuation is minus one: it is the class, modulo the
integers, of the power residue exponent of the unit, divided by the exponent.  The reciprocal of
such a uniformiser has divided valuation one, and the symbol is multiplicative. -/
theorem localSymbol_eq_powerResidue_of_unitValDiv_eq_neg_one (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = -1) {b : Kˣ} (hb : Valued.v (b : K) = 1) {j : ℕ}
    (hj : Valued.v (ζ ^ j - (b : K) ^ ((Nat.card (DivisionResidue K K) - 1) / n)) < 1) :
    localSymbol hres hm hζ π b = Multiplicative.ofAdd (zmodQModZ n (j : ZMod n)) := by
  have hinv : unitValDiv hm (Additive.ofMul π⁻¹) = 1 := by
    have hneg : Additive.ofMul π⁻¹ = -(Additive.ofMul π) := rfl
    rw [hneg, map_neg, hπ, neg_neg]
  have hkey :=
    localSymbol_uniformiser_eq_powerResidue_of_valued_eq_one hres hm hζ hn hpn hinv hb hj
  have hmul : localSymbol hres hm hζ π b * localSymbol hres hm hζ π⁻¹ b = 1 := by
    rw [← MonoidHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, MonoidHom.one_apply]
  rw [eq_inv_iff_mul_eq_one.2 hmul, hkey, map_neg, ofAdd_neg, inv_inv]

end Root

end InverseGalois.CFT
