/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Statement

/-!
# The fixed field of a monodromy kernel is a regular realization

The field-theoretic engine of the descent's last module, isolated from the tower it is applied to
and from the particular base field.

The input is a finite Galois extension `Ω / F` whose base `F` is **regular over its constant field
`k`** (`algebraicClosure k F = ⊥`, the case of interest being `F = k(T)`), together with

* an intermediate field `geomBase` of `Ω / F` containing every element of `Ω` algebraic over `k`
  — the *geometric base* `k̄(T)`, whose fixing subgroup is the geometric monodromy group; and
* a surjection `ψ' : Gal(Ω / F) ↠ G` which is **already surjective on the geometric part**, i.e.
  every element of `G` is hit by an automorphism fixing `geomBase` pointwise.

The output is that `L' = Ω ^ (ker ψ')` is a Galois extension of `F` with group `G` in which `k`
stays relatively algebraically closed — a regular realization of `G` over `F / k`.

## The mathematics

`L'/F` is Galois with `Gal(L'/F) ≃ Gal(Ω/F) / ker ψ' ≃ G` by the fundamental theorem.  For
regularity, let `x ∈ L'` be algebraic over `k`.  Then `x` lies in `geomBase`, and every
`g ∈ Gal(Ω/F)` factors as `(g n'⁻¹) · n'` with `n'` fixing `geomBase` (hence `x`) and `g n'⁻¹` in
`ker ψ'` (hence fixing `x ∈ L'`) — this is exactly where surjectivity of `ψ'` on the geometric part
is spent.  So `x` is fixed by the whole Galois group, i.e. `x ∈ F`; and `F` is regular over `k`, so
`x ∈ k`.

## Main result

* `isRegularGaloisGroupOverBase_fixedField`
-/

open Polynomial

open scoped IntermediateField

namespace Rigidity.RET

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The fixed field of the monodromy kernel is a regular realization.**

For a finite Galois extension `Ω / F` with `F` regular over its constant field `k`, a surjection
`ψ' : Gal(Ω/F) ↠ G` that is already surjective on the fixing subgroup of a geometric base
`geomBase ⊇ {constants}` cuts out a **regular** Galois extension `Ω ^ (ker ψ')` of `F` with group
`G`. -/
theorem isRegularGaloisGroupOverBase_fixedField {G : Type} [Group G]
    {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] (hFreg : algebraicClosure k F = ⊥)
    {Ω : Type} [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
    [Algebra k Ω] [IsScalarTower k F Ω]
    (geomBase : IntermediateField F Ω)
    (hconst : algebraicClosure k Ω ≤ geomBase.restrictScalars k)
    (ψ' : (Ω ≃ₐ[F] Ω) →* G) (hψ'surj : Function.Surjective ψ')
    (hψ'N : ∀ g : G, ∃ n' ∈ geomBase.fixingSubgroup, ψ' n' = g) :
    IsRegularGaloisGroupOverBase k F G := by
  classical
  haveI : (ψ'.ker).Normal := ψ'.normal_ker
  -- The descended field `L' = Ω ^ (ker ψ')`.
  set L' : IntermediateField F Ω := IntermediateField.fixedField ψ'.ker with hL'
  haveI : IsGalois F L' := IsGalois.of_fixedField_normal_subgroup ψ'.ker
  haveI : FiniteDimensional F L' := inferInstance
  -- `L'` carries the canonical `SubfieldClass` `k`-action; coercion commutes with both scalar
  -- actions, so the tower reduces to `smul_assoc` on `Ω` itself.
  haveI : IsScalarTower k F L' := by
    refine ⟨fun q r x => ?_⟩
    apply Subtype.ext
    push_cast
    exact smul_assoc q r (x : Ω)
  -- **Regularity.**  Any `x ∈ L'` algebraic over `k` is a constant.
  let ι : L' →ₐ[k] Ω := (IntermediateField.val L').restrictScalars k
  let j : F →ₐ[k] Ω := IsScalarTower.toAlgHom k F Ω
  have hreg : algebraicClosure k L' = ⊥ := by
    refine bot_unique fun x hx => ?_
    -- `(x : Ω)` is algebraic over `k`, hence lies in the geometric base (all constants do).
    have hxΩac : (x : Ω) ∈ algebraicClosure k Ω := (map_mem_algebraicClosure_iff ι).mpr hx
    have hxgeom : (x : Ω) ∈ geomBase :=
      (IntermediateField.mem_restrictScalars k).mp (hconst hxΩac)
    -- `(x : Ω)` is fixed by *every* `g ∈ Gal(Ω/F)`: write `g = (g · n'⁻¹) · n'` with `n'` fixing
    -- `geomBase` (hence `x`) and `g · n'⁻¹ ∈ ker ψ'` (hence fixing `x ∈ L'`).
    have hfix : ∀ g : Ω ≃ₐ[F] Ω, g (x : Ω) = (x : Ω) := by
      intro g
      obtain ⟨n', hn'mem, hn'eq⟩ := hψ'N (ψ' g)
      have hker : g * n'⁻¹ ∈ ψ'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hn'eq, mul_inv_cancel]
      have hn'fix : n' (x : Ω) = (x : Ω) := by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hn'mem
        exact hn'mem _ hxgeom
      have hkfix : (g * n'⁻¹) (x : Ω) = (x : Ω) := by
        have hx2 : (x : Ω) ∈ IntermediateField.fixedField ψ'.ker := x.2
        rw [IntermediateField.mem_fixedField_iff] at hx2
        exact hx2 _ hker
      have hgrp : (g * n'⁻¹) * n' = g := by group
      have e1 : (g * n'⁻¹) (n' (x : Ω)) = g (x : Ω) :=
        (AlgEquiv.mul_apply (g * n'⁻¹) n' (x : Ω)).symm.trans (DFunLike.congr_fun hgrp (x : Ω))
      calc g (x : Ω) = (g * n'⁻¹) (n' (x : Ω)) := e1.symm
        _ = (g * n'⁻¹) (x : Ω) := congrArg _ hn'fix
        _ = (x : Ω) := hkfix
    -- Fixed by the whole group ⟹ `(x : Ω) ∈ fixedField ⊤ = ⊥ = F`.
    have hxbot : (x : Ω) ∈ (⊥ : IntermediateField F Ω) := by
      rw [← IsGalois.fixedField_top (F := F) (E := Ω), IntermediateField.mem_fixedField_iff]
      exact fun f _ => hfix f
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hxbot
    -- `y ∈ F` is algebraic over `k`, so by regularity of `F / k` it is a constant `q`.
    have hjy : j y ∈ algebraicClosure k Ω := by rw [show j y = (x : Ω) from hy]; exact hxΩac
    have hyac : y ∈ algebraicClosure k F := (map_mem_algebraicClosure_iff j).mp hjy
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp (hFreg ▸ hyac)
    rw [IntermediateField.mem_bot]
    refine ⟨q, ?_⟩
    apply Subtype.ext
    have hxq : (x : Ω) = algebraMap k Ω q := by rw [← hy, ← hq]; exact j.commutes q
    rw [hxq]
    exact ι.commutes q
  -- **The Galois group is `G`.**  `Gal(L'/F) ≃ Gal(Ω/F) / ker ψ' ≃ G`.
  have hgal : Nonempty ((L' ≃ₐ[F] L') ≃* G) :=
    ⟨(IsGalois.normalAutEquivQuotient ψ'.ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ'surj)⟩
  exact ⟨L', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hreg, hgal⟩

end Rigidity.RET
