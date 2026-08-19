/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.Descent.RegularFixedField
import InverseGalois.Rigidity.RET.Descent.BaseTransfer
import InverseGalois.Rigidity.RET.Descent.RegularBase
import InverseGalois.Rigidity.RET.Descent.ConstantDescent
import InverseGalois.Rigidity.RET.Descent.ConstantSubfield

/-!
# A regular realization over the number field cut out by a subgroup

The rigidity method produces a Galois tower `Ω / ℚ(T)` together with a surjection onto the target
group `G` from a subgroup `E'` of `Gal(Ω/ℚ(T))`.  When the prescribed conjugacy classes are
rational one may take `E' = Gal(Ω/ℚ(T))` and the realization is over `ℚ(T)`; when they are only
stable under a subgroup of the cyclotomic action, `E'` is a proper subgroup and the realization
lands over a **number field**.

This file identifies that number field and produces the realization.  Let `E'` be any subgroup
containing the geometric group `Gal(Ω / k_Ω(T))`.  Then

* its fixed field is `K(T)` for a number field `K ⊆ Ω` (`exists_constant_base`), and that field is
  the standard rational function field `RatFunc K` (`exists_ratFunc_algEquiv`);
* `RatFunc K` is regular over `K` (`algebraicClosure_ratFunc`), and `k_Ω(T)` is a geometric base
  above it containing every constant;
* so the fixed-field machine `isRegularGaloisGroupOverBase_fixedField` applies verbatim, and
  `of_algEquiv` rewrites the base into its standard form.

The result is `IsRegularGaloisGroupOver K G` — a **regular** Galois extension of `K(T)` with group
`G`, the conclusion of the rigidity method over a number field.

## Main result

* `Rigidity.RET.Descent.exists_regular_over_constant_base`
-/

open Polynomial

open scoped IntermediateField

set_option synthInstance.maxHeartbeats 800000

namespace Rigidity.RET.Descent

set_option maxHeartbeats 1600000 in
/-- **The rigidity method over a number field.**

Let `Ω / ℚ(T)` be finite Galois and let `E' ≤ Gal(Ω/ℚ(T))` be a subgroup containing the geometric
group `Gal(Ω / k_Ω(T))`, equipped with a surjection `ψ : E' ↠ G` that is already surjective on the
geometric part.  Then `G` is a **regular** Galois group over `K(T)` for the number field `K` of
constants cut out by `E'`. -/
theorem exists_regular_over_constant_base {G : Type} [Group G]
    (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω]
    [IsGalois (RatFunc ℚ) Ω] [CharZero Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]
    {E' : Subgroup (Ω ≃ₐ[RatFunc ℚ] Ω)} (hN : (constFieldBase Ω).fixingSubgroup ≤ E')
    (ψ : E' →* G) (hsurj : Function.Surjective ψ)
    (hgeom : ∀ g : G, ∃ n : E',
      (n : Ω ≃ₐ[RatFunc ℚ] Ω) ∈ (constFieldBase Ω).fixingSubgroup ∧ ψ n = g) :
    ∃ K : IntermediateField ℚ Ω, K ≤ algebraicClosure ℚ Ω ∧ IsRegularGaloisGroupOver ↥K G := by
  classical
  obtain ⟨K, hKac, hMK⟩ := exists_constant_base Ω E' hN
  refine ⟨K, hKac, ?_⟩
  set M : IntermediateField (RatFunc ℚ) Ω := IntermediateField.fixedField E' with hMdef
  -- `K` is a number field, hence algebraic over `ℚ`.
  haveI : FiniteDimensional ℚ ↥K :=
    Module.Finite.of_injective (IntermediateField.inclusion hKac).toLinearMap
      (IntermediateField.inclusion hKac).toRingHom.injective
  haveI : Algebra.IsAlgebraic ℚ ↥K := Algebra.IsAlgebraic.of_finite ℚ ↥K
  -- `K` sits inside `M`, so `M` is a `K`-algebra.
  have hKM : ∀ a : ↥K, algebraMap ↥K Ω a ∈ M := by
    intro a
    rw [hMK]
    exact IntermediateField.subset_adjoin _ _ a.2
  letI : Algebra ↥K ↥M := RingHom.toAlgebra
    { toFun := fun a => ⟨algebraMap ↥K Ω a, hKM a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI : IsScalarTower ↥K ↥M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois ↥M Ω := IsGalois.tower_top_of_isGalois (RatFunc ℚ) ↥M Ω
  -- `M` is the standard rational function field over `K`.
  have hrange : (K : Set Ω) = Set.range (algebraMap ↥K Ω) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩
  obtain ⟨e⟩ := exists_ratFunc_algEquiv (K := ↥K) M (by rw [hMK, hrange])
  -- `M / K` is regular.
  have hFreg : algebraicClosure ↥K ↥M = ⊥ :=
    algebraicClosure_eq_bot_of_algEquiv e (algebraicClosure_ratFunc ↥K)
  -- The geometric base `k_Ω(T)`, viewed over `M`.
  have hMle : M ≤ constFieldBase Ω := by
    intro x hx
    rw [← IsGalois.fixedField_fixingSubgroup (constFieldBase Ω),
      IntermediateField.mem_fixedField_iff]
    rw [hMdef, IntermediateField.mem_fixedField_iff] at hx
    exact fun σ hσ => hx σ (hN hσ)
  set gb : IntermediateField ↥M Ω := IntermediateField.extendScalars hMle with hgb
  have hconst : algebraicClosure ↥K Ω ≤ gb.restrictScalars ↥K := by
    intro x hx
    rw [IntermediateField.mem_restrictScalars, hgb, IntermediateField.mem_extendScalars]
    have hxQ : x ∈ algebraicClosure ℚ Ω :=
      mem_algebraicClosure_iff.mpr
        (IsAlgebraic.restrictScalars (R := ℚ) (mem_algebraicClosure_iff.mp hx))
    exact (IntermediateField.mem_restrictScalars ℚ).mp (const_le_constFieldBase Ω hxQ)
  -- Transport the monodromy from `E'` to `Gal(Ω/M)`.
  set τ : ↥E' ≃* (Ω ≃ₐ[↥M] Ω) := IntermediateField.subgroupEquivAlgEquiv E' with hτ
  set ψ' : (Ω ≃ₐ[↥M] Ω) →* G := ψ.comp τ.symm.toMonoidHom with hψ'
  have hψ'surj : Function.Surjective ψ' := hsurj.comp τ.symm.surjective
  have hψ'N : ∀ g : G, ∃ n' ∈ gb.fixingSubgroup, ψ' n' = g := by
    intro g
    obtain ⟨n, hnfix, hng⟩ := hgeom g
    refine ⟨τ n, ?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      rw [IntermediateField.mem_fixingSubgroup_iff] at hnfix
      exact hnfix x ((IntermediateField.mem_extendScalars hMle).mp hx)
    · show ψ (τ.symm (τ n)) = g
      rw [τ.symm_apply_apply, hng]
  -- Apply the fixed-field machine over the base `M / K`, then rename the base.
  exact IsRegularGaloisGroupOverBase.of_algEquiv
    (Rigidity.RET.isRegularGaloisGroupOverBase_fixedField hFreg gb hconst ψ' hψ'surj hψ'N) e.symm

end Rigidity.RET.Descent
