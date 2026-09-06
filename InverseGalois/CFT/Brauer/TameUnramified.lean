/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TameEvaluation

/-!
# The tame norm residue symbol against an unramified argument

Call an element of a complete discretely valued field unramified for a given exponent when the
exponent divides its valuation, so that its class modulo powers is unramified.  The symbol of such
an element against anything is completely determined by its symbol against a single uniformiser,
raised to the valuation of the second argument.

The reason is that the symbol is killed by the exponent, so a power of a uniformiser whose exponent
is a multiple of the exponent pairs trivially with everything; an unramified element may therefore
be replaced by the unit of the valuation ring left after dividing by the matching power of the
uniformiser, without changing any of its symbols.  Splitting the second argument the same way
leaves the symbol of two units of the valuation ring, which is trivial, together with the symbol
against the power of the uniformiser.

Replacing an unramified element by that unit also computes the kernel: the symbol of a unit of the
valuation ring against a uniformiser is trivial exactly when the unit is a power, and multiplying
by the matching power of the uniformiser does not change whether an element is a power.  So the
symbol against a uniformiser is a faithful reading of the class of an unramified element.

## Main results

* `InverseGalois.CFT.localSymbol_zpow_eq_one_of_dvd`: a power of an element whose exponent is a
  multiple of the exponent pairs trivially with everything.
* `InverseGalois.CFT.localSymbol_mul_zpow_uniformiser`: an unramified element has the same symbols
  as the unit of the valuation ring left after dividing by the matching power of a uniformiser.
* `InverseGalois.CFT.localSymbol_eq_zpow_uniformiser`: **the symbol of an unramified element
  against anything is its symbol against a uniformiser, raised to the valuation of the second
  argument.**
* `InverseGalois.CFT.localSymbol_uniformiser_eq_one_iff_of_dvd`: **the symbol of an unramified
  element against a uniformiser is trivial exactly when that element is a power.**

## Tags

norm residue symbol, tame symbol, unramified, local field, uniformiser, class field theory
-/

namespace InverseGalois.CFT

open scoped Valued WithZero

section Unramified

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

/-- **A power of an element whose exponent is a multiple of the exponent pairs trivially with
everything**, the symbol being killed by the exponent. -/
theorem localSymbol_zpow_eq_one_of_dvd (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (a b : Kˣ) {i : ℤ} (hi : (n : ℤ) ∣ i) :
    localSymbol hres hm hζ (a ^ i) b = 1 := by
  obtain ⟨s, rfl⟩ := hi
  rw [localSymbol_zpow_left, zpow_mul, zpow_natCast, pow_localSymbol_eq_one, one_zpow]

/-- **An element whose valuation is divisible by the exponent has the same symbols as the unit of
the valuation ring left after dividing by the matching power of a uniformiser.** -/
theorem localSymbol_mul_zpow_uniformiser (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) {π a : Kˣ}
    (ha : (n : ℤ) ∣ unitValDiv hm (Additive.ofMul a)) (c : Kˣ) :
    localSymbol hres hm hζ a c
      = localSymbol hres hm hζ (a * π ^ (-unitValDiv hm (Additive.ofMul a))) c := by
  conv_lhs => rw [← zpow_mul_mul_zpow_neg π a (unitValDiv hm (Additive.ofMul a))]
  rw [map_mul, MonoidHom.mul_apply, localSymbol_zpow_eq_one_of_dvd hres hm hζ π c ha, one_mul]

/-- **The norm residue symbol of an element whose valuation is divisible by the exponent against
anything is its symbol against a uniformiser, raised to the valuation of the second argument.**
Both elements are split into a power of the uniformiser times a unit of the valuation ring; the
power carried by the first element pairs trivially, the two units pair trivially, and what is left
is the symbol against the power of the uniformiser carried by the second. -/
theorem localSymbol_eq_zpow_uniformiser (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {a : Kˣ}
    (ha : (n : ℤ) ∣ unitValDiv hm (Additive.ofMul a)) (b : Kˣ) :
    localSymbol hres hm hζ a b
      = localSymbol hres hm hζ a π ^ unitValDiv hm (Additive.ofMul b) := by
  have hu : Valued.v ((a * π ^ (-unitValDiv hm (Additive.ofMul a)) : Kˣ) : K) = 1 :=
    valued_mul_zpow_uniformiser hm hπ a
  have hw : Valued.v ((b * π ^ (-unitValDiv hm (Additive.ofMul b)) : Kˣ) : K) = 1 :=
    valued_mul_zpow_uniformiser hm hπ b
  rw [localSymbol_mul_zpow_uniformiser (π := π) hres hm hζ ha b,
    localSymbol_mul_zpow_uniformiser (π := π) hres hm hζ ha π]
  conv_lhs => rw [← zpow_mul_mul_zpow_neg π b (unitValDiv hm (Additive.ofMul b))]
  rw [map_mul, map_zpow, localSymbol_eq_one_of_valued_eq_one hres hm hζ hn hpn hu hw, mul_one]

/-- **The norm residue symbol of an element whose valuation is divisible by the exponent against a
uniformiser is trivial exactly when that element is a power.**  Dividing by the matching power of
the uniformiser changes neither the symbol nor the property of being a power, and for a unit of the
valuation ring the kernel of the symbol against a uniformiser is exactly the powers. -/
theorem localSymbol_uniformiser_eq_one_iff_of_dvd (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {a : Kˣ}
    (ha : (n : ℤ) ∣ unitValDiv hm (Additive.ofMul a)) :
    localSymbol hres hm hζ a π = 1 ↔ ∃ c : Kˣ, c ^ n = a := by
  obtain ⟨s, hs⟩ := ha
  have hu : Valued.v ((a * π ^ (-unitValDiv hm (Additive.ofMul a)) : Kˣ) : K) = 1 :=
    valued_mul_zpow_uniformiser hm hπ a
  rw [localSymbol_mul_zpow_uniformiser (π := π) hres hm hζ ⟨s, hs⟩ π,
    localSymbol_unit_uniformiser_eq_one_iff hres hm hζ hn hpn hπ hu]
  have hπs : π ^ (s * (n : ℤ)) = π ^ unitValDiv hm (Additive.ofMul a) := by
    rw [mul_comm, ← hs]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * π ^ s, ?_⟩
    rw [mul_pow, hc, ← zpow_natCast (π ^ s) n, ← zpow_mul, hπs, mul_assoc, ← zpow_add,
      neg_add_cancel, zpow_zero, mul_one]
  · rintro ⟨c, hc⟩
    refine ⟨c * π ^ (-s), ?_⟩
    rw [mul_pow, hc, ← zpow_natCast (π ^ (-s)) n, ← zpow_mul, neg_mul, hs, mul_comm (n : ℤ) s]

end Unramified

end InverseGalois.CFT
