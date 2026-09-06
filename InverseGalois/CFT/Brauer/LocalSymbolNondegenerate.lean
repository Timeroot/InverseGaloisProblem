/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TameEvaluation

/-!
# The norm residue symbol of a local field is nondegenerate

The symbol of two units is trivial exactly when the first is a norm from the level of the second,
and the level of a unit which is not a power is a nontrivial cyclic extension of the base.  A
cyclic extension of a local field of degree bigger than one has an element of the base which is not
a norm from it, because the norm index of such an extension is its degree.  So an element which is
not a power always has a partner it pairs nontrivially with.

Skew symmetry turns that into the same statement on the other side, so the kernel of the symbol is
exactly the powers in either argument: **the norm residue symbol descends to a nondegenerate
pairing of the elements of a local field modulo powers with themselves.**

Nothing here needs the exponent to be prime, nor the residue characteristic to avoid it, nor a
choice of uniformiser: the whole argument runs through the level of a single element.

## Main results

* `InverseGalois.CFT.one_lt_finrank_kummerLevel`: the level of an element which is not a power is a
  nontrivial extension of the base.
* `InverseGalois.CFT.exists_kummerSymbolUnits_ne_one_of_not_isPow`: **an element of a local field
  which is not a power has a partner whose power symbol against it is nontrivial.**
* `InverseGalois.CFT.exists_localSymbol_ne_one_of_not_isPow`,
  `InverseGalois.CFT.exists_localSymbol_ne_one_of_not_isPow_left`: **the same for the norm residue
  symbol, in either argument.**
* `InverseGalois.CFT.forall_localSymbol_eq_one_iff_isPow`,
  `InverseGalois.CFT.forall_localSymbol_eq_one_iff_isPow'`: **an element pairing trivially with
  everything under the norm residue symbol is a power.**

## Tags

norm residue symbol, Hilbert symbol, local field, nondegenerate pairing, norm subgroup,
Kummer theory, local duality, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

/-! ### The level of an element which is not a power -/

section Level

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {n : ℕ} [NeZero n]
  {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- The level of an element which is not a power is a nontrivial extension of the base, an element
whose level is trivial being a power. -/
theorem one_lt_finrank_kummerLevel {b : Kˣ} (hnp : ¬ ∃ c : Kˣ, c ^ n = b) :
    1 < finrank K ↥(kummerLevel h b) := by
  have hcard : Nat.card Gal(↥(kummerLevel h b)/K) ≠ 1 := fun h1 =>
    hnp (exists_pow_eq_of_card_gal_kummerLevel_eq_one h b h1)
  have hpos : 0 < Nat.card Gal(↥(kummerLevel h b)/K) := Nat.card_pos
  rw [← IsGalois.card_aut_eq_finrank K ↥(kummerLevel h b)]
  omega

end Level

/-! ### The power symbol has no kernel beyond the powers -/

section KummerNondegenerate

variable {K Ω : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field Ω] [Algebra K Ω] [IsGalois K Ω] {n : ℕ} [NeZero n] {ζ : K}
  {hζ : IsPrimitiveRoot ζ n} {p e : ℕ}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **An element of a local field which is not a power has a partner whose power symbol against it
is nontrivial.**  Its level is a cyclic extension of degree bigger than one, so some element of the
base is not a norm from it, and the symbol is trivial exactly on the norms. -/
theorem exists_kummerSymbolUnits_ne_one_of_not_isPow (hres : HasResidueChar K p e) {b : Kˣ}
    (hnp : ¬ ∃ c : Kˣ, c ^ n = b) : ∃ a : Kˣ, kummerSymbolUnits h (mulZMod n) a b ≠ 1 := by
  obtain ⟨σ₀, -, hgen, -, -, -⟩ := exists_generator_kummerLevel_index h b
  haveI : IsCyclic Gal(↥(kummerLevel h b)/K) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, eq_top_iff.mpr fun x _ => hgen x⟩
  obtain ⟨a, ha⟩ := exists_notMem_normSubgroup K ↥(kummerLevel h b) hres
    (one_lt_finrank_kummerLevel h hnp)
  exact ⟨a, fun hs => ha ((mem_normSubgroup_iff a).mpr
    ((kummerSymbolUnits_eq_one_iff_norm_kummerLevel h a b).mp hs))⟩

end KummerNondegenerate

/-! ### The norm residue symbol is nondegenerate -/

section Root

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

/-- **The norm residue symbol of a local field is nondegenerate in its second argument**: an
element which is not a power has a partner whose symbol against it is nontrivial. -/
theorem exists_localSymbol_ne_one_of_not_isPow (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) {b : Kˣ} (hnp : ¬ ∃ c : Kˣ, c ^ n = b) :
    ∃ a : Kˣ, localSymbol hres hm hζ a b ≠ 1 := by
  letI := zmodTrivialAction K (AlgebraicClosure K) n
  haveI : IsSmoothAction Gal(AlgebraicClosure K/K) (Multiplicative (ZMod n)) :=
    isSmoothAction_of_trivial fun _ _ => rfl
  obtain ⟨a, ha⟩ := exists_kummerSymbolUnits_ne_one_of_not_isPow
    (isKummerData_zmod (Ω := AlgebraicClosure K) hζ exists_units_pow_eq) hres hnp
  exact ⟨a, fun hs => ha ((localKummerSymbol_eq_one_iff_kummerSymbolUnits hres hm
    (isKummerData_zmod hζ exists_units_pow_eq) (mulZMod n) a b).mp hs)⟩

/-- **The norm residue symbol of a local field is nondegenerate in its first argument**, by skew
symmetry. -/
theorem exists_localSymbol_ne_one_of_not_isPow_left (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) {a : Kˣ} (hnp : ¬ ∃ c : Kˣ, c ^ n = a) :
    ∃ b : Kˣ, localSymbol hres hm hζ a b ≠ 1 := by
  obtain ⟨b, hb⟩ := exists_localSymbol_ne_one_of_not_isPow hres hm hζ hnp
  refine ⟨b, fun hs => hb ?_⟩
  have hswap := localSymbol_mul_swap hres hm hζ b a
  rwa [hs, mul_one] at hswap

/-- **An element pairing trivially with everything on the right under the norm residue symbol is a
power.** -/
theorem forall_localSymbol_eq_one_iff_isPow (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) :
    (∀ b : Kˣ, localSymbol hres hm hζ a b = 1) ↔ ∃ c : Kˣ, c ^ n = a := by
  refine ⟨fun hall => ?_, fun hc b => localSymbol_eq_one_of_isPow_left hres hm hζ hc b⟩
  by_contra hnp
  obtain ⟨b, hb⟩ := exists_localSymbol_ne_one_of_not_isPow_left hres hm hζ hnp
  exact hb (hall b)

/-- **An element pairing trivially with everything on the left under the norm residue symbol is a
power.** -/
theorem forall_localSymbol_eq_one_iff_isPow' (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (b : Kˣ) :
    (∀ a : Kˣ, localSymbol hres hm hζ a b = 1) ↔ ∃ c : Kˣ, c ^ n = b := by
  refine ⟨fun hall => ?_, fun hc a => localSymbol_eq_one_of_isPow_right hres hm hζ a hc⟩
  by_contra hnp
  obtain ⟨a, ha⟩ := exists_localSymbol_ne_one_of_not_isPow hres hm hζ hnp
  exact ha (hall a)

end Root

end InverseGalois.CFT
