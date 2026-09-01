/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SymbolNorm

/-!
# The Steinberg relation for the power symbol

The chosen `n`-th root of a unit generates the level of that unit, and the minimal polynomial of
that root over the base is the difference of a power of the variable and a base element.  The
characteristic polynomial of multiplication by the root is that minimal polynomial, so evaluating
it at a base element computes the norm of the difference of that base element and the root.

One minus a base multiple of the root therefore has a norm that is one minus the corresponding
multiple of the base element, and the base elements arising this way are exactly the roots of the
polynomial whose value at one is one minus the unit.  Multiplying those norms together exhibits
one minus a unit as a norm from the level of that unit, so the power symbol of one minus a unit
against that unit is trivial.

Skew symmetry turns this around, and the identity that expresses the negative of a unit as a ratio
of one minus the unit and one minus its inverse gives the companion relation for the symbol of a
unit against its negative.

## Main results

* `InverseGalois.CFT.norm_algebraMap_sub_powerBasis_gen`: **the norm of the difference of a base
  element and the generator of a power basis is the minimal polynomial of that generator evaluated
  at the base element.**
* `InverseGalois.CFT.exists_norm_eq_one_sub`: **one minus a unit is a norm from the level of that
  unit.**
* `InverseGalois.CFT.kummerSymbolUnits_one_sub`: **the power symbol of one minus a unit against
  that unit is trivial.**
* `InverseGalois.CFT.kummerSymbolUnits_neg_self`: **the power symbol of a unit against its negative
  is trivial.**

## Tags

Steinberg relation, Hilbert symbol, norm residue symbol, Milnor K-theory, Kummer theory,
class field theory
-/

universe u

namespace InverseGalois.CFT

open groupCohomology IntermediateField Polynomial

section PowerBasisNorm

/-- **The norm of the difference of a base element and the generator of a power basis** is the
minimal polynomial of that generator, evaluated at the base element. -/
theorem norm_algebraMap_sub_powerBasis_gen {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (pb : PowerBasis K S) (r : K) :
    Algebra.norm K (algebraMap K S r - pb.gen) = (minpoly K pb.gen).eval r := by
  rw [Algebra.norm_eq_matrix_det pb.basis, ← charpoly_leftMulMatrix pb,
    Matrix.eval_charpoly, map_sub, AlgHom.commutes]
  congr 1

end PowerBasisNorm

section Steinberg

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {n : ℕ} [NeZero n]
  {ζ : k} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-! ### The power basis of the level -/

variable (b : kˣ)

/-- The power basis of the level of a unit given by the chosen root of that unit. -/
noncomputable def kummerLevelPowerBasis : PowerBasis k ↥(kummerLevel h b) :=
  IntermediateField.adjoin.powerBasis (isIntegral_kummerRoot h b)

variable {b}

omit [IsGalois k Ω] in
/-- The generator of the power basis of the level of a unit is the chosen root of that unit. -/
theorem kummerLevelPowerBasis_gen (b : kˣ) :
    (kummerLevelPowerBasis h b).gen = kummerLevelGen h b :=
  IntermediateField.adjoin.powerBasis_gen (isIntegral_kummerRoot h b)

/-! ### Norms of one minus a multiple of the root -/

omit [IsGalois k Ω] in
/-- The norm of the difference of a base element and the chosen root of a unit is the minimal
polynomial of that root, evaluated at the base element. -/
theorem norm_algebraMap_sub_kummerLevelGen (b : kˣ) (r : k) :
    Algebra.norm k (algebraMap k ↥(kummerLevel h b) r - kummerLevelGen h b)
      = (minpoly k (kummerLevelGen h b)).eval r := by
  have hb := norm_algebraMap_sub_powerBasis_gen (kummerLevelPowerBasis h b) r
  rw [kummerLevelPowerBasis_gen] at hb
  have hgoal : Algebra.norm k (algebraMap k ↥(kummerLevel h b) r - kummerLevelGen h b)
      = (minpoly k (kummerLevelGen h b)).eval r := hb
  exact hgoal

/-- **The norm, from the level of a unit, of one minus a base multiple of the chosen root** is one
minus the corresponding power of that base element times the base element the root powers to. -/
theorem norm_one_sub_algebraMap_mul_kummerLevelGen (b : kˣ) {c : k}
    (hc : algebraMap k ↥(kummerLevel h b) c
      = kummerLevelGen h b ^ Nat.card Gal(↥(kummerLevel h b)/k)) {e : k} (he : e ≠ 0) :
    Algebra.norm k (1 - algebraMap k ↥(kummerLevel h b) e * kummerLevelGen h b)
      = 1 - e ^ Nat.card Gal(↥(kummerLevel h b)/k) * c := by
  have hsplit : (1 : ↥(kummerLevel h b)) - algebraMap k ↥(kummerLevel h b) e * kummerLevelGen h b
      = algebraMap k ↥(kummerLevel h b) e
        * (algebraMap k ↥(kummerLevel h b) e⁻¹ - kummerLevelGen h b) := by
    rw [mul_sub, ← map_mul, mul_inv_cancel₀ he, map_one]
  rw [hsplit, map_mul, Algebra.norm_algebraMap, norm_algebraMap_sub_kummerLevelGen h b,
    minpoly_kummerLevelGen h b hc, eval_sub, eval_pow, eval_X, eval_C,
    ← IsGalois.card_aut_eq_finrank k ↥(kummerLevel h b), mul_sub, ← mul_pow,
    mul_inv_cancel₀ he, one_pow]

/-! ### One minus a unit is a norm from the level of that unit -/

/-- **One minus a unit of the base is the norm of an element of the level of that unit.** -/
theorem exists_norm_eq_one_sub (a : kˣ) (ha : (a : k) ≠ 1) :
    ∃ w : ↥(kummerLevel h a), w ≠ 0 ∧ Algebra.norm k w = 1 - (a : k) := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_pow_card h a
  obtain ⟨t, hmt⟩ := card_gal_kummerLevel_dvd h a
  have hn0 : n ≠ 0 := NeZero.ne n
  have hm0 : Nat.card Gal(↥(kummerLevel h a)/k) ≠ 0 := Nat.card_pos.ne'
  have htpos : 0 < t := Nat.pos_of_ne_zero fun ht0 => hn0 (by rw [hmt, ht0, Nat.mul_zero])
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn0
  have hct : c ^ t = (a : k) := by
    refine (algebraMap k ↥(kummerLevel h a)).injective ?_
    rw [map_pow, hc, ← pow_mul, ← hmt]
    refine (algebraMap ↥(kummerLevel h a) Ω).injective ?_
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    exact congrArg Units.val (h.root_pow a)
  have hdivn : n / Nat.card Gal(↥(kummerLevel h a)/k) = t := by
    have hd := Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hm0)
    rwa [← hmt] at hd
  have hξ : IsPrimitiveRoot (ζ ^ Nat.card Gal(↥(kummerLevel h a)/k)) t := by
    have hp := hζ.pow_of_dvd hm0 ⟨t, hmt⟩
    rwa [hdivn] at hp
  have hconv : ∀ j : ℕ, (ζ ^ j) ^ Nat.card Gal(↥(kummerLevel h a)/k)
      = (ζ ^ Nat.card Gal(↥(kummerLevel h a)/k)) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hprod : ∏ j ∈ Finset.range t,
      (1 - (ζ ^ Nat.card Gal(↥(kummerLevel h a)/k)) ^ j * c) = 1 - (a : k) := by
    have h1 := congrArg (Polynomial.eval (1 : k)) (X_pow_sub_C_eq_prod hξ htpos hct)
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod, one_pow] at h1
    exact h1.symm
  have hnorm : Algebra.norm k (∏ j ∈ Finset.range t,
      (1 - algebraMap k ↥(kummerLevel h a) (ζ ^ j) * kummerLevelGen h a)) = 1 - (a : k) := by
    rw [map_prod, Finset.prod_congr rfl fun j _ =>
      (norm_one_sub_algebraMap_mul_kummerLevelGen h a hc (pow_ne_zero j hζ0)).trans
        (by rw [hconv j]), hprod]
  refine ⟨_, ?_, hnorm⟩
  intro hw0
  rw [hw0, Algebra.norm_zero] at hnorm
  exact sub_ne_zero_of_ne (Ne.symm ha) hnorm.symm

/-! ### The Steinberg relation and the symbol of a unit against its negative -/

/-- **The power symbol of one minus a unit against that unit is trivial.** -/
theorem kummerSymbolUnits_one_sub (a u : kˣ) (hu : (u : k) = 1 - (a : k)) :
    kummerSymbolUnits h (mulZMod n) u a = 1 := by
  have ha : (a : k) ≠ 1 := by
    intro h1
    rw [h1, sub_self] at hu
    exact u.ne_zero hu
  obtain ⟨w, hw, hnw⟩ := exists_norm_eq_one_sub h a ha
  refine (kummerSymbolUnits_eq_one_iff_norm_kummerLevel h u a).mpr ⟨Units.mk0 w hw, ?_⟩
  rw [hu]
  exact hnw

/-- **The power symbol of a unit against one minus that unit is trivial.** -/
theorem kummerSymbolUnits_self_one_sub (a u : kˣ) (hu : (u : k) = 1 - (a : k)) :
    kummerSymbolUnits h (mulZMod n) a u = 1 := by
  have hswap := kummerSymbolUnits_mul_swap h u a
  rw [kummerSymbolUnits_one_sub h a u hu, one_mul] at hswap
  exact hswap

/-- **The power symbol of a unit against its negative is trivial.** -/
theorem kummerSymbolUnits_neg_self (a : kˣ) :
    kummerSymbolUnits h (mulZMod n) a (-a) = 1 := by
  rcases eq_or_ne a 1 with rfl | h1
  · rw [map_one, MonoidHom.one_apply]
  · have ha1 : (a : k) ≠ 1 := fun hh => h1 (Units.ext hh)
    have hai1 : ((a⁻¹ : kˣ) : k) ≠ 1 := fun hh => h1 (inv_eq_one.mp (Units.ext hh))
    have hune : (1 : k) - (a : k) ≠ 0 := sub_ne_zero_of_ne (Ne.symm ha1)
    have hvne : (1 : k) - ((a⁻¹ : kˣ) : k) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hai1)
    set u : kˣ := Units.mk0 (1 - (a : k)) hune with hudef
    set v : kˣ := Units.mk0 (1 - ((a⁻¹ : kˣ) : k)) hvne with hvdef
    have hu1 : kummerSymbolUnits h (mulZMod n) a u = 1 :=
      kummerSymbolUnits_self_one_sub h a u rfl
    have hv1 : kummerSymbolUnits h (mulZMod n) a⁻¹ v = 1 :=
      kummerSymbolUnits_self_one_sub h a⁻¹ v rfl
    have hav : kummerSymbolUnits h (mulZMod n) a v = 1 := by
      have hmul := congrArg (fun f => f v) (map_mul (kummerSymbolUnits h (mulZMod n)) a⁻¹ a)
      simp only [inv_mul_cancel, map_one, MonoidHom.one_apply, MonoidHom.mul_apply] at hmul
      rw [hv1, one_mul] at hmul
      exact hmul.symm
    have hkey : u = (-a) * v := by
      refine Units.ext ?_
      simp only [hudef, hvdef, Units.val_mul, Units.val_neg, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      ring
    have hneg : (-a : kˣ) = u * v⁻¹ := by rw [hkey, mul_inv_cancel_right]
    rw [hneg, map_mul, map_inv, hu1, hav, inv_one, one_mul]

end Steinberg

end InverseGalois.CFT
