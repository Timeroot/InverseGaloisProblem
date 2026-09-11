/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerConj
import InverseGalois.CFT.Profinite.SymbolCyclic

/-!
# The Kummer character of a conjugated unit, the base missing the roots of unity

Let `Ω` be a Galois extension of `k`, let `K` be an intermediate field normal over the base, and
let `K` contain a primitive `n`-th root of unity whose units all have an `n`-th root in `Ω`.
Kummer theory over `K` attaches to a unit `a` of `K` a character of the group of automorphisms of
`Ω` over `K`, with values in the residues modulo `n`.

An automorphism `σ` of `Ω` over the base moves that character in two ways at once: it moves the
unit, by restriction to `K`, and it moves the argument, by conjugation.  It also moves the chosen
root of unity, and this is what the base containing the roots of unity would rule out: in general
`σ` raises the chosen root of unity to some exponent, and the character picks up exactly that
factor.  So the character of the conjugated unit at an automorphism is that exponent times the
character of the unit at the conjugate automorphism.

The characterisation of the Kummer cochain is what makes this work: the cochain of a unit is the
only one whose image in the units of the extension is the coboundary of an `n`-th root, so applying
`σ` to the chosen root of `a` exhibits the cochain of the conjugated unit, and the exponent enters
through the coefficients alone.

## Main definitions

* `InverseGalois.CFT.galConj`: the conjugate of an automorphism over a normal intermediate field by
  an automorphism over the base.

## Main results

* `InverseGalois.CFT.cochain_smul_galConj`: **the Kummer cochain of a conjugated unit is a power of
  the conjugate of the Kummer cochain**, the exponent being the one by which the automorphism
  raises the roots of unity.
* `InverseGalois.CFT.kummerChar_smul_galConj`: the same, read on characters with values in the
  residues modulo `n`.
* `InverseGalois.CFT.kummerChar_conj_of_smul_eq_mul_pow`: **the Kummer character of a unit which an
  automorphism fixes up to an `n`-th power is multiplied by that exponent under conjugation.**

## Tags

Kummer theory, infinite Galois theory, root of unity, cyclotomic character, conjugation
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IntermediateField groupCohomology

/-! ### Conjugating an automorphism over a normal intermediate field -/

section Conj

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)

/-- An automorphism over an intermediate field is determined by the automorphism over the base
which it defines. -/
theorem galSubHom_injective : Function.Injective (galSubHom K) := fun τ τ' hτ =>
  AlgEquiv.ext fun x => by
    rw [← galSubHom_apply K τ x, ← galSubHom_apply K τ' x, hτ]

variable [Normal k ↥K]

/-- **The conjugate of an automorphism over a normal intermediate field** by an automorphism over
the base. -/
def galConj (σ : Gal(Ω/k)) (τ : Gal(Ω/↥K)) : Gal(Ω/↥K) :=
  fixingSubgroupEquiv K (conjMemHom (normal_fixingSubgroup K) σ ((fixingSubgroupEquiv K).symm τ))

/-- Conjugating an automorphism over a normal intermediate field is conjugating it over the
base. -/
theorem galSubHom_galConj (σ : Gal(Ω/k)) (τ : Gal(Ω/↥K)) :
    galSubHom K (galConj K σ τ) = σ⁻¹ * galSubHom K τ * σ := by
  have hsymm : (fixingSubgroupEquiv K).symm (galConj K σ τ)
      = conjMemHom (normal_fixingSubgroup K) σ ((fixingSubgroupEquiv K).symm τ) :=
    (fixingSubgroupEquiv K).symm_apply_apply _
  rw [← coe_fixingSubgroupEquiv_symm, hsymm, conjMemHom_coe, coe_fixingSubgroupEquiv_symm]

/-- Conjugating back the conjugate of an automorphism over a normal intermediate field. -/
theorem galConj_eq_of_galSubHom_conj {σ : Gal(Ω/k)} {τ τ' : Gal(Ω/↥K)}
    (hτ : galSubHom K τ' = σ * galSubHom K τ * σ⁻¹) : galConj K σ τ' = τ := by
  refine galSubHom_injective K ?_
  rw [galSubHom_galConj, hτ]
  group

end Conj

/-! ### The Kummer cochain of a conjugated unit -/

section Cochain

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω}
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {n : ℕ} [NeZero n]

/-- The Kummer cochain of an `n`-th power is trivial, the chosen root being the unit itself. -/
theorem cochain_pow_eq_one (h : IsKummerData ↥K Ω M ι n) (t : (↥K)ˣ) (τ : Gal(Ω/↥K)) :
    h.cochain (t ^ n) τ = 1 := by
  have key : (fun _ : Gal(Ω/↥K) => (1 : M)) = h.cochain (t ^ n) := by
    refine h.cochain_unique _ (β := Units.map (algebraMap ↥K Ω : ↥K →* Ω) t) ?_ ?_
    · rw [← _root_.map_pow]
    · intro ρ
      show Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι 1) = _
      rw [_root_.map_one, _root_.map_one, smul_units_algebraMap, div_self']
  exact (congrFun key τ).symm

variable [Normal k ↥K]

/-- **The Kummer cochain of a conjugated unit is a power of the conjugate of the Kummer cochain.**
Both are read off the conjugate of the chosen root, which is a root of the conjugate unit; the
hypothesis is the exponent by which an automorphism over the base raises the coefficients. -/
theorem cochain_smul_galConj (h : IsKummerData ↥K Ω M ι n) (σ : Gal(Ω/k)) (e : ℕ)
    (hfix : ∀ m : M, σ • h.unitsHom m = h.unitsHom (m ^ e)) (a : (↥K)ˣ) (τ : Gal(Ω/↥K)) :
    h.cochain (AlgEquiv.restrictNormalHom (↥K) σ • a) τ = h.cochain a (galConj K σ τ) ^ e := by
  have key : (fun ρ : Gal(Ω/↥K) => h.cochain a (galConj K σ ρ) ^ e)
      = h.cochain (AlgEquiv.restrictNormalHom (↥K) σ • a) := by
    refine h.cochain_unique _ (β := σ • h.root a) ?_ ?_
    · rw [← smul_pow', h.root_pow, smul_units_algebraMap_intermediateField]
    · intro ρ
      show h.unitsHom (h.cochain a (galConj K σ ρ) ^ e) = ρ • (σ • h.root a) / (σ • h.root a)
      rw [← hfix, h.unitsHom_apply, h.cochain_spec, smul_div']
      congr 1
      show σ • ((σ⁻¹ * galSubHom K ρ * σ) • h.root a) = ρ • (σ • h.root a)
      rw [← mul_smul, show σ * (σ⁻¹ * galSubHom K ρ * σ) = galSubHom K ρ * σ by group, mul_smul]
      rfl
  exact (congrFun key τ).symm

end Cochain

/-! ### The Kummer character of a conjugated unit -/

section Char

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω} [Normal k ↥K]
variable {n : ℕ} [NeZero n] {ζ : ↥K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData ↥K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

omit [IsGalois k Ω] [Normal k ↥K] in
/-- An automorphism over the base raises the coefficients of the Kummer situation to the exponent
by which it raises the chosen root of unity. -/
theorem unitsHom_smul_of_smul_kummerRootUnit {σ : Gal(Ω/k)} {e : ℕ}
    (hσ : σ • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e) (m : Multiplicative (ZMod n)) :
    σ • h.unitsHom m = h.unitsHom (m ^ e) := by
  have hcast : ((e * m.toAdd.val : ℕ) : ZMod n) = (m ^ e).toAdd := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, toAdd_pow, nsmul_eq_mul]
  have hval : (m ^ e).toAdd.val = e * m.toAdd.val % n := by
    rw [← hcast, ZMod.val_natCast]
  rw [unitsHom_eq_kummerRootUnit_pow, unitsHom_eq_kummerRootUnit_pow, smul_pow', hσ, ← pow_mul,
    hval, pow_mod_of_pow_eq_one kummerRootUnit_pow_eq_one]

/-- **The Kummer character of a conjugated unit is a multiple of the character at the conjugate
automorphism**, the multiplier being the exponent by which the automorphism raises the chosen root
of unity. -/
theorem kummerChar_smul_galConj {σ : Gal(Ω/k)} {e : ℕ}
    (hσ : σ • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e) (a : (↥K)ˣ) (τ : Gal(Ω/↥K)) :
    kummerChar h (AlgEquiv.restrictNormalHom (↥K) σ • a) τ
      = (e : ZMod n) * kummerChar h a (galConj K σ τ) := by
  rw [kummerChar_apply, kummerChar_apply,
    cochain_smul_galConj h σ e (unitsHom_smul_of_smul_kummerRootUnit h hσ) a τ, toAdd_pow,
    nsmul_eq_mul]

/-- **The Kummer character of a unit which an automorphism over the base fixes up to an `n`-th
power is multiplied, under conjugation of the argument by that automorphism, by the exponent by
which it raises the chosen root of unity.** -/
theorem kummerChar_conj_of_smul_eq_mul_pow {σ : Gal(Ω/k)} {e : ℕ}
    (hσ : σ • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e) {a t : (↥K)ˣ}
    (ha : AlgEquiv.restrictNormalHom (↥K) σ • a = a * t ^ n) {τ τ' : Gal(Ω/↥K)}
    (hτ : galSubHom K τ' = σ * galSubHom K τ * σ⁻¹) :
    kummerChar h a τ' = (e : ZMod n) * kummerChar h a τ := by
  have hpow : kummerChar h (a * t ^ n) τ' = kummerChar h a τ' := by
    show (h.cochain (a * t ^ n) τ').toAdd = (h.cochain a τ').toAdd
    rw [h.cochain_mul, Pi.mul_apply, cochain_pow_eq_one, mul_one]
  calc kummerChar h a τ'
      = kummerChar h (a * t ^ n) τ' := hpow.symm
    _ = kummerChar h (AlgEquiv.restrictNormalHom (↥K) σ • a) τ' := by rw [ha]
    _ = (e : ZMod n) * kummerChar h a (galConj K σ τ') := kummerChar_smul_galConj h hσ a τ'
    _ = (e : ZMod n) * kummerChar h a τ := by
        rw [galConj_eq_of_galSubHom_conj K hτ]

end Char

end InverseGalois.CFT
