/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.CFT.NormSubgroup
import InverseGalois.CFT.Tate.GaloisH0

/-!
# The invariant of an unramified extension of valued fields

For a Galois extension whose automorphisms preserve the valuation of the larger field, the norm of
an element is the product of its conjugates, all of the same value, so the value of a norm is the
degree-th power of a value.  Dividing by a generator of the value group turns this into a statement
about integers: the value of a norm is divisible by the degree.

The extension is *unramified* when every value attained on the larger field is already attained on
the smaller one.  Then the values of the smaller field also fill the whole value group, so reading
the value modulo the degree is a surjection of the units of the base field onto the integers modulo
the degree which kills the norms.  When the norm subgroup has index the degree — which it does for
a cyclic extension of complete fields — the surjection is an isomorphism of the quotient by the
norms with the integers modulo the degree.

## Main definitions

* `InverseGalois.CFT.IsUnramifiedValued`: every value of the larger field is a value of the
  smaller.
* `InverseGalois.CFT.unramifiedInvariantUnits`: the value of a unit of the base field, divided by a
  generator of the value group and read modulo the degree.

## Main results

* `InverseGalois.CFT.valued_algebraMap_norm`: **the value of a norm is the degree-th power of the
  value.**
* `InverseGalois.CFT.normSubgroup_le_ker_unramifiedInvariantUnits`: **the invariant kills the
  norms.**
* `InverseGalois.CFT.unramifiedInvariantUnits_surjective`: **the invariant of an unramified
  extension is surjective.**
* `InverseGalois.CFT.unramifiedNormEquiv`: **the units modulo the norms of an unramified extension
  of norm index the degree are the integers modulo the degree.**

## Tags

local field, valuation, unramified, norm, norm subgroup, invariant, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped WithZero

variable {K A : Type} [Field K] [Field A] [Algebra K A] [Valued A ℤᵐ⁰]

/-! ### The value of a norm -/

section Galois

variable [FiniteDimensional K A] [IsGalois K A]

/-- **The value of a norm is the degree-th power of the value**, when every automorphism preserves
the valuation: the norm is the product of the conjugates, which all have the same value. -/
theorem valued_algebraMap_norm
    (hv : ∀ (σ : A ≃ₐ[K] A) (x : A), Valued.v (σ x) = Valued.v x) (b : A) :
    Valued.v (algebraMap K A (Algebra.norm K b)) = Valued.v b ^ Nat.card (A ≃ₐ[K] A) := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, map_prod,
    Finset.prod_congr rfl fun σ _ => hv σ b, Finset.prod_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- **The value of a norm is the degree times a value.** -/
theorem unitVal_unitsAlgebraMap_of_norm
    (hv : ∀ (σ : A ≃ₐ[K] A) (x : A), Valued.v (σ x) = Valued.v x) (b : Aˣ) (a : Kˣ)
    (hab : (a : K) = Algebra.norm K (b : A)) :
    unitVal (Additive.ofMul (unitsAlgebraMap K A a))
      = Nat.card (A ≃ₐ[K] A) * unitVal (Additive.ofMul b) := by
  rw [unitVal_apply, unitVal_apply, coe_unitsAlgebraMap, hab, valued_algebraMap_norm hv,
    WithZero.log_pow, nsmul_eq_mul]

end Galois

/-! ### The invariant of an unramified extension -/

/-- **An unramified extension of valued fields**: every value attained on the larger field is
already attained on the smaller one. -/
def IsUnramifiedValued (K A : Type) [Field K] [Field A] [Algebra K A] [Valued A ℤᵐ⁰] : Prop :=
  ∀ x : Aˣ, ∃ c : Kˣ, Valued.v (algebraMap K A (c : K)) = Valued.v (x : A)

variable {m : ℤ}

variable (K) in
/-- **The invariant of a unit of the base field**: its value in the larger field, divided by a
generator of the value group and read modulo the degree. -/
noncomputable def unramifiedInvariantUnits (hm : IsUnitValGen A m) :
    Kˣ →* Multiplicative (ZMod (finrank K A)) where
  toFun a :=
    Multiplicative.ofAdd
      ((unitValDiv hm (Additive.ofMul (unitsAlgebraMap K A a)) : ZMod (finrank K A)))
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, ofMul_mul, map_add, Int.cast_add, ofAdd_add]

theorem unramifiedInvariantUnits_apply (hm : IsUnitValGen A m) (a : Kˣ) :
    unramifiedInvariantUnits K hm a
      = Multiplicative.ofAdd
        ((unitValDiv hm (Additive.ofMul (unitsAlgebraMap K A a)) : ZMod (finrank K A))) :=
  rfl

/-- A unit of the base field whose value generates the value group of the larger field. -/
theorem exists_unitValDiv_unitsAlgebraMap_eq_one (hur : IsUnramifiedValued K A)
    (hm : IsUnitValGen A m) :
    ∃ c : Kˣ, unitValDiv hm (Additive.ofMul (unitsAlgebraMap K A c)) = 1 := by
  obtain ⟨x, hx⟩ := hm.exists_eq
  obtain ⟨c, hc⟩ := hur (Additive.toMul x)
  refine ⟨c, ?_⟩
  have hval : unitVal (Additive.ofMul (unitsAlgebraMap K A c)) = m := by
    rw [unitVal_apply, coe_unitsAlgebraMap, hc, ← unitVal_apply]
    simpa using hx
  rw [unitValDiv_apply, hval, Int.ediv_self hm.ne_zero]

/-- **The invariant of an unramified extension is surjective**: the values of the base field fill
the whole value group. -/
theorem unramifiedInvariantUnits_surjective (hur : IsUnramifiedValued K A)
    (hm : IsUnitValGen A m) : Function.Surjective (unramifiedInvariantUnits K hm) := by
  obtain ⟨c, hc⟩ := exists_unitValDiv_unitsAlgebraMap_eq_one hur hm
  intro t
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (n := finrank K A) (Multiplicative.toAdd t)
  refine ⟨c ^ j, ?_⟩
  rw [map_zpow (unramifiedInvariantUnits K hm) c j, unramifiedInvariantUnits_apply, hc,
    ← ofAdd_zsmul]
  simpa [zsmul_eq_mul] using congrArg Multiplicative.ofAdd hj

section GaloisIndex

variable [FiniteDimensional K A] [IsGalois K A]

/-- **The invariant kills the norms.**  The value of a norm is the degree times a value, so its
quotient by a generator of the value group is a multiple of the degree. -/
theorem normSubgroup_le_ker_unramifiedInvariantUnits
    (hv : ∀ (σ : A ≃ₐ[K] A) (x : A), Valued.v (σ x) = Valued.v x) (hm : IsUnitValGen A m) :
    normSubgroup K A ≤ (unramifiedInvariantUnits K hm).ker := by
  intro a ha
  obtain ⟨b, hb⟩ := (mem_normSubgroup_iff a).1 ha
  have hn : Nat.card (A ≃ₐ[K] A) = finrank K A := IsGalois.card_aut_eq_finrank K A
  have h1 : unitVal (Additive.ofMul (unitsAlgebraMap K A a))
      = (finrank K A : ℤ) * unitVal (Additive.ofMul b) := by
    rw [← hn]
    exact unitVal_unitsAlgebraMap_of_norm hv b a hb.symm
  have h2 : m * unitValDiv hm (Additive.ofMul (unitsAlgebraMap K A a))
      = m * ((finrank K A : ℤ) * unitValDiv hm (Additive.ofMul b)) := by
    rw [← unitVal_eq_mul_unitValDiv hm, h1, unitVal_eq_mul_unitValDiv hm (Additive.ofMul b)]
    ring
  have h3 : unitValDiv hm (Additive.ofMul (unitsAlgebraMap K A a))
      = (finrank K A : ℤ) * unitValDiv hm (Additive.ofMul b) :=
    mul_left_cancel₀ hm.ne_zero h2
  rw [MonoidHom.mem_ker, unramifiedInvariantUnits_apply, h3]
  simp

/-- **The units modulo the norms of an unramified extension of norm index the degree are the
integers modulo the degree.**  Reading the value modulo the degree is a surjection killing the
norms, and the two groups have the same order. -/
noncomputable def unramifiedNormEquiv
    (hv : ∀ (σ : A ≃ₐ[K] A) (x : A), Valued.v (σ x) = Valued.v x) (hur : IsUnramifiedValued K A)
    (hm : IsUnitValGen A m) (hindex : (normSubgroup K A).index = finrank K A) :
    (Kˣ ⧸ normSubgroup K A) ≃* Multiplicative (ZMod (finrank K A)) := by
  haveI : NeZero (finrank K A) := ⟨(Module.finrank_pos_iff.2 inferInstance).ne'⟩
  haveI : (normSubgroup K A).FiniteIndex := ⟨by rw [hindex]; exact NeZero.ne _⟩
  haveI : Finite (Kˣ ⧸ normSubgroup K A) := Subgroup.finite_quotient_of_finiteIndex
  refine MulEquiv.ofBijective
    (QuotientGroup.lift _ (unramifiedInvariantUnits K hm)
      (normSubgroup_le_ker_unramifiedInvariantUnits hv hm)) ?_
  refine (Nat.bijective_iff_surjective_and_card _).2 ⟨?_, ?_⟩
  · intro t
    obtain ⟨a, ha⟩ := unramifiedInvariantUnits_surjective hur hm t
    exact ⟨QuotientGroup.mk a, ha⟩
  · rw [show Nat.card (Kˣ ⧸ normSubgroup K A) = (normSubgroup K A).index from rfl, hindex,
      ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod (finrank K A))), Nat.card_zmod]

end GaloisIndex

end InverseGalois.CFT
