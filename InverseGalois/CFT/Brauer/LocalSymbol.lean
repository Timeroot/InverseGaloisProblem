/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SmoothInvariant
import InverseGalois.CFT.Profinite.Symbol

/-!
# The norm residue symbol of a local field

Over a local field containing a primitive `n`-th root of unity the `n`-th power symbol of two units
is a class of the second cohomology of the absolute Galois group with coefficients in the roots of
unity.  Reading it in the units of an algebraic closure loses nothing, because an algebraic closure
is closed under `n`-th roots, and the invariant map of local class field theory then turns it into
a rational number modulo the integers, killed by `n`.

This is the norm residue symbol in its cohomological form: bimultiplicative, trivial as soon as one
of its arguments is an `n`-th power, and with values in the `n`-torsion of the rationals modulo the
integers.  The pairing of the roots of unity with themselves that it depends on is a choice of a
primitive root, which the integers modulo `n` carry for free.

## Main definitions

* `InverseGalois.CFT.localKummerSymbol`: **the norm residue symbol attached to Kummer data and a
  pairing of the coefficients.**
* `InverseGalois.CFT.localSymbol`: **the `n`-th power norm residue symbol attached to a primitive
  `n`-th root of unity of the base.**

## Main results

* `InverseGalois.CFT.pow_localKummerSymbol_eq_one`, `InverseGalois.CFT.pow_localSymbol_eq_one`:
  **the symbol is killed by `n`.**
* `InverseGalois.CFT.localKummerSymbol_eq_one_iff`: **the symbol vanishes exactly when the
  underlying cohomology class with roots of unity as coefficients is trivial.**
* `InverseGalois.CFT.localSymbol_eq_one_of_isPow_left`,
  `InverseGalois.CFT.localSymbol_eq_one_of_isPow_right`: the symbol is trivial on `n`-th powers.

## Tags

norm residue symbol, Hilbert symbol, local field, invariant map, Brauer group, Kummer theory,
class field theory
-/

namespace InverseGalois.CFT

open scoped Valued WithZero

/-! ### Roots in an algebraically closed field -/

section AlgClosed

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {n : ℕ} [NeZero n]

/-- Every unit of an algebraically closed field is an `n`-th power. -/
theorem exists_units_pow_eq_self (y : Ωˣ) : ∃ z : Ωˣ, z ^ n = y := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y : Ω) (NeZero.pos n)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne n)] at hz
    exact y.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

end AlgClosed

/-! ### The symbol of a local field -/

section Local

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ}
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(AlgebraicClosure K/K) M]
  {ι : M →* Kˣ} {n : ℕ} [NeZero n] [IsSmoothAction Gal(AlgebraicClosure K/K) M]

/-- **The norm residue symbol of a local field**: the invariant of the `n`-th power symbol of two
units, a rational number modulo the integers. -/
noncomputable def localKummerSymbol (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (h : IsKummerData K (AlgebraicClosure K) M ι n) (Φ : M →* M →* M) :
    Kˣ →* Kˣ →* Multiplicative QModZ :=
  (MonoidHom.compHom (smoothLocalInvariantEquiv K hres hm).toMonoidHom).comp
    (kummerSymbolUnits h Φ)

theorem localKummerSymbol_apply (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (h : IsKummerData K (AlgebraicClosure K) M ι n) (Φ : M →* M →* M) (a b : Kˣ) :
    localKummerSymbol hres hm h Φ a b
      = smoothLocalInvariantEquiv K hres hm (kummerSymbolUnits h Φ a b) := rfl

/-- **The symbol is killed by `n`.** -/
theorem pow_localKummerSymbol_eq_one (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (h : IsKummerData K (AlgebraicClosure K) M ι n) (Φ : M →* M →* M) (a b : Kˣ) :
    localKummerSymbol hres hm h Φ a b ^ n = 1 := by
  rw [localKummerSymbol_apply, ← map_pow, kummerSymbolUnits_apply, ← map_pow,
    pow_kummerSymbol_eq_one, map_one, map_one]

/-- **The symbol vanishes exactly when the underlying class with roots of unity as coefficients is
trivial.**  Both steps are injections: the invariant map is an isomorphism, and an algebraic
closure is closed under `n`-th roots. -/
theorem localKummerSymbol_eq_one_iff (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (h : IsKummerData K (AlgebraicClosure K) M ι n) (Φ : M →* M →* M) (a b : Kˣ) :
    localKummerSymbol hres hm h Φ a b = 1 ↔ kummerSymbol h Φ a b = 1 := by
  rw [localKummerSymbol_apply, ← kummerSymbolUnits_eq_one_iff h Φ exists_units_pow_eq_self a b]
  exact ⟨fun hz => (smoothLocalInvariantEquiv K hres hm).injective (by rw [hz, map_one]),
    fun hz => by rw [hz, map_one]⟩

/-- The symbol of an `n`-th power is trivial in the first argument. -/
theorem localKummerSymbol_eq_one_of_isPow_left (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (h : IsKummerData K (AlgebraicClosure K) M ι n) (Φ : M →* M →* M)
    {a : Kˣ} (ha : ∃ c : Kˣ, c ^ n = a) (b : Kˣ) : localKummerSymbol hres hm h Φ a b = 1 := by
  rw [localKummerSymbol_apply, kummerSymbolUnits_apply,
    kummerSymbol_eq_one_of_isPow_left h Φ ha b, map_one, map_one]

/-- The symbol of an `n`-th power is trivial in the second argument. -/
theorem localKummerSymbol_eq_one_of_isPow_right (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (h : IsKummerData K (AlgebraicClosure K) M ι n) (Φ : M →* M →* M)
    (a : Kˣ) {b : Kˣ} (hb : ∃ c : Kˣ, c ^ n = b) : localKummerSymbol hres hm h Φ a b = 1 := by
  rw [localKummerSymbol_apply, kummerSymbolUnits_apply,
    kummerSymbol_eq_one_of_isPow_right h Φ a hb, map_one, map_one]

end Local

/-! ### The symbol attached to a primitive root of unity -/

section Root

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

/-- **The `n`-th power norm residue symbol of a local field containing a primitive `n`-th root of
unity.**  The pairing of the roots of unity with themselves is multiplication in the integers
modulo `n`, transported by the chosen primitive root. -/
noncomputable def localSymbol (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) : Kˣ →* Kˣ →* Multiplicative QModZ :=
  letI := zmodTrivialAction K (AlgebraicClosure K) n
  haveI : IsSmoothAction Gal(AlgebraicClosure K/K) (Multiplicative (ZMod n)) :=
    isSmoothAction_of_trivial fun _ _ => rfl
  localKummerSymbol hres hm (isKummerData_zmod hζ exists_units_pow_eq) (mulZMod n)

/-- **The `n`-th power norm residue symbol is killed by `n`.** -/
theorem pow_localSymbol_eq_one (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (a b : Kˣ) : localSymbol hres hm hζ a b ^ n = 1 :=
  letI := zmodTrivialAction K (AlgebraicClosure K) n
  haveI : IsSmoothAction Gal(AlgebraicClosure K/K) (Multiplicative (ZMod n)) :=
    isSmoothAction_of_trivial fun _ _ => rfl
  pow_localKummerSymbol_eq_one hres hm (isKummerData_zmod hζ exists_units_pow_eq) (mulZMod n) a b

/-- The `n`-th power norm residue symbol of an `n`-th power is trivial in the first argument. -/
theorem localSymbol_eq_one_of_isPow_left (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) {a : Kˣ} (ha : ∃ c : Kˣ, c ^ n = a) (b : Kˣ) :
    localSymbol hres hm hζ a b = 1 :=
  letI := zmodTrivialAction K (AlgebraicClosure K) n
  haveI : IsSmoothAction Gal(AlgebraicClosure K/K) (Multiplicative (ZMod n)) :=
    isSmoothAction_of_trivial fun _ _ => rfl
  localKummerSymbol_eq_one_of_isPow_left hres hm (isKummerData_zmod hζ exists_units_pow_eq)
    (mulZMod n) ha b

/-- The `n`-th power norm residue symbol of an `n`-th power is trivial in the second argument. -/
theorem localSymbol_eq_one_of_isPow_right (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) {b : Kˣ} (hb : ∃ c : Kˣ, c ^ n = b) :
    localSymbol hres hm hζ a b = 1 :=
  letI := zmodTrivialAction K (AlgebraicClosure K) n
  haveI : IsSmoothAction Gal(AlgebraicClosure K/K) (Multiplicative (ZMod n)) :=
    isSmoothAction_of_trivial fun _ _ => rfl
  localKummerSymbol_eq_one_of_isPow_right hres hm (isKummerData_zmod hζ exists_units_pow_eq)
    (mulZMod n) a hb

end Root

end InverseGalois.CFT
