/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.Data
import InverseGalois.Rigidity.RET.GeometricIrreducibility

/-!
# Module D — field translation: the fixed field of `ker ψ` is a regular `ℚ(T)`-extension

Over a `GeomTower G cert`, once the centerless extension lemma has produced the arithmetic monodromy
`ψ : E ↠ G` extending the geometric monodromy `φ : N ↠ G`, this module carries that homomorphism
back to a **regular** Galois extension of `ℚ(T)` realizing `G` — i.e. it discharges the `toRegular`
field of `BranchCycleDescentData`.

## The mathematics *(genuine field theory)*

Let `L' = Ω^{ker ψ}` be the fixed field of `ker ψ`.  Then:

* `L'/ℚ(T)` is Galois with `Gal(L'/ℚ(T)) ≃ E / ker ψ ≃ G` (`ψ` surjective) — the fundamental
  theorem of Galois theory (`IsGalois`, `IntermediateField.fixedField`, and the
  `Gal ≃ E/ker` isomorphism).
* **Regularity.**  Because `ψ|_N = φ` is *surjective*, `N` already surjects onto `G`, so
  `ker ψ · N = E` and `ker ψ ∩ N` has index `|G|` in `N`.  Equivalently the field of constants of
  `L'` is `ℚ`: `L' ∩ ℚ̄(T) = ℚ(T)`, i.e. `algebraicClosure ℚ L' = ⊥`.  This is the regularity
  condition of `IsRegularInverseGalois`, and it is exactly what the surjectivity of `ψ|_N` buys.

Both bullets are Mathlib-expressible Galois theory over the tower built in `Descent.Tower`; the
module has **no irreducible arithmetic-geometry input** — it is genuine field theory, contingent only
on the tower's field data (which is why `descentTranslation` takes the tower `tw`, not just abstract
groups: the regularity computation needs the field realization).

Sub-targets to formalize here:

* `fixedField_isGalois` / `gal_fixedField_equiv` — `Gal(L'/ℚ(T)) ≃* G` from `ψ` surjective.
* `regular_of_geom_surjective` — `ψ|_N` surjective ⟹ constant field `= ℚ` ⟹
  `algebraicClosure ℚ L' = ⊥`.

## Main result

* `descentTranslation` — the `toRegular` field of the descent datum.
-/

open Polynomial

open scoped IntermediateField

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Module D.**  The field translation: given the arithmetic monodromy `ψ : E ↠ G` extending the
geometric monodromy `φ : N ↠ G` over the tower `tw`, the fixed field `Ω^{ker ψ}` is a **regular**
Galois extension of `ℚ(T)` with group `G`.

This is genuine field theory (fixed fields + a regularity computation): the surjectivity of `ψ|_N`
forces the field of constants to be `ℚ`, giving `algebraicClosure ℚ L' = ⊥`.  There is no
irreducible arithmetic-geometry input — only the tower's field realization.  See
`DESCENT_ROADMAP.md` §1.4 and the module docstring. -/
theorem descentTranslation {G : Type} [Group G] [Finite G] {cert : RigidityCertificate G}
    (tw : GeomTower G cert) :
    (∃ ψ : tw.E →* G, Function.Surjective ψ ∧ ∀ n : tw.N, ψ (n : tw.E) = tw.φ n) →
      IsRegularInverseGalois G := by
  rintro ⟨ψ, hψsurj, hψext⟩
  classical
  -- Transport the abstract arithmetic monodromy to the actual Galois group `Gal(Ω/ℚ(T))`.
  let ψ' : (tw.Ω ≃ₐ[RatFunc ℚ] tw.Ω) →* G := ψ.comp tw.galE.symm.toMonoidHom
  have hψ'surj : Function.Surjective ψ' := hψsurj.comp tw.galE.symm.surjective
  haveI : (ψ'.ker).Normal := ψ'.normal_ker
  -- The descended field `L' = Ω^{ker ψ'}`.
  set L' : IntermediateField (RatFunc ℚ) tw.Ω := IntermediateField.fixedField ψ'.ker with hL'
  haveI : IsGalois (RatFunc ℚ) L' := IsGalois.of_fixedField_normal_subgroup ψ'.ker
  haveI : FiniteDimensional (RatFunc ℚ) L' := inferInstance
  -- `L'` carries the canonical `SubfieldClass` `ℚ`-action; because `Ω`'s `ℚ`-algebra is likewise the
  -- canonical `DivisionRing.toRatAlgebra`, coercion commutes with both scalar actions and the tower
  -- reduces to `smul_assoc` on `Ω` itself.
  haveI : IsScalarTower ℚ (RatFunc ℚ) L' := by
    refine ⟨fun q r x => ?_⟩
    apply Subtype.ext
    push_cast
    exact smul_assoc q r (x : tw.Ω)
  -- The geometric monodromy `φ` is surjective (its sphere hom `sphereHom base` is, and `pres` is).
  have hφsurj : Function.Surjective tw.φ := by
    intro g
    have hs : Function.Surjective (Rigidity.RET.sphereHom tw.base tw.base_mem.2.1) :=
      (Rigidity.RET.sphereHom_surjective_iff tw.base tw.base_mem.2.1).2 tw.base_mem.2.2
    obtain ⟨x, hx⟩ := hs g
    exact ⟨tw.pres x, by rw [tw.φ_pres x, hx]⟩
  -- `ψ'` is already surjective on `N' = Gal(Ω/ℚ̄(T)) = geomBase.fixingSubgroup`.
  have hψ'N : ∀ g : G, ∃ n' ∈ tw.geomBase.fixingSubgroup, ψ' n' = g := by
    intro g
    obtain ⟨n, hn⟩ := hφsurj g
    refine ⟨tw.galE (n : tw.E), (tw.galN_iff (n : tw.E)).mp n.2, ?_⟩
    show ψ (tw.galE.symm (tw.galE (n : tw.E))) = g
    rw [tw.galE.symm_apply_apply, hψext n, hn]
  -- **Regularity.**  Any `x ∈ L'` algebraic over `ℚ` is a constant.
  -- The `ℚ`-algebra embedding `L' ↪ Ω`.
  let ι : L' →ₐ[ℚ] tw.Ω := (IntermediateField.val L').restrictScalars ℚ
  -- The `ℚ`-algebra embedding `ℚ(T) ↪ Ω`.
  let j : RatFunc ℚ →ₐ[ℚ] tw.Ω := IsScalarTower.toAlgHom ℚ (RatFunc ℚ) tw.Ω
  have hreg : algebraicClosure ℚ L' = ⊥ := by
    refine bot_unique fun x hx => ?_
    -- `(x : Ω)` is algebraic over `ℚ`, hence lies in `ℚ̄(T) = geomBase` (all constants).
    have hxΩac : (x : tw.Ω) ∈ algebraicClosure ℚ tw.Ω :=
      (map_mem_algebraicClosure_iff ι).mpr hx
    have hxgeom : (x : tw.Ω) ∈ tw.geomBase :=
      (IntermediateField.mem_restrictScalars ℚ).mp (tw.const_le_geomBase hxΩac)
    -- `(x : Ω)` is fixed by *every* `g ∈ Gal(Ω/ℚ(T))`: write `g = (g·n'⁻¹)·n'` with
    -- `n' ∈ N' = geomBase.fixingSubgroup` (fixes `x ∈ geomBase`) and `g·n'⁻¹ ∈ ker ψ'`
    -- (fixes `x ∈ L' = Ω^{ker ψ'}`), using that `ψ'|_{N'}` is surjective.
    have hfix : ∀ g : tw.Ω ≃ₐ[RatFunc ℚ] tw.Ω, g (x : tw.Ω) = (x : tw.Ω) := by
      intro g
      obtain ⟨n', hn'mem, hn'eq⟩ := hψ'N (ψ' g)
      have hker : g * n'⁻¹ ∈ ψ'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hn'eq, mul_inv_cancel]
      have hn'fix : n' (x : tw.Ω) = (x : tw.Ω) := by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hn'mem
        exact hn'mem _ hxgeom
      have hkfix : (g * n'⁻¹) (x : tw.Ω) = (x : tw.Ω) := by
        have hx2 : (x : tw.Ω) ∈ IntermediateField.fixedField ψ'.ker := x.2
        rw [IntermediateField.mem_fixedField_iff] at hx2
        exact hx2 _ hker
      have hgrp : (g * n'⁻¹) * n' = g := by group
      have e1 : (g * n'⁻¹) (n' (x : tw.Ω)) = g (x : tw.Ω) :=
        (AlgEquiv.mul_apply (g * n'⁻¹) n' (x : tw.Ω)).symm.trans
          (DFunLike.congr_fun hgrp (x : tw.Ω))
      calc g (x : tw.Ω) = (g * n'⁻¹) (n' (x : tw.Ω)) := e1.symm
        _ = (g * n'⁻¹) (x : tw.Ω) := congrArg _ hn'fix
        _ = (x : tw.Ω) := hkfix
    -- Fixed by the whole group ⟹ `(x : Ω) ∈ fixedField ⊤ = ⊥ = ℚ(T)`.
    have hxbot : (x : tw.Ω) ∈ (⊥ : IntermediateField (RatFunc ℚ) tw.Ω) := by
      rw [← IsGalois.fixedField_top (F := RatFunc ℚ) (E := tw.Ω),
        IntermediateField.mem_fixedField_iff]
      exact fun f _ => hfix f
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hxbot
    -- `y ∈ ℚ(T)` is algebraic over `ℚ`, so by regularity of `ℚ(T)/ℚ` it is a constant `q`.
    have hjy : j y ∈ algebraicClosure ℚ tw.Ω := by rw [show j y = (x : tw.Ω) from hy]; exact hxΩac
    have hyac : y ∈ algebraicClosure ℚ (RatFunc ℚ) := (map_mem_algebraicClosure_iff j).mp hjy
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp (Rigidity.RET.regular_ratFunc ▸ hyac)
    -- Hence `x = q ∈ ⊥`.
    rw [IntermediateField.mem_bot]
    refine ⟨q, ?_⟩
    apply Subtype.ext
    have hxq : (x : tw.Ω) = algebraMap ℚ tw.Ω q := by
      rw [← hy, ← hq]; exact j.commutes q
    rw [hxq]
    exact ι.commutes q
  -- **The Galois group is `G`.**  `Gal(L'/ℚ(T)) ≃ Gal(Ω/ℚ(T))/ker ψ' ≃ G`.
  have hgal : Nonempty ((L' ≃ₐ[RatFunc ℚ] L') ≃* G) :=
    ⟨(IsGalois.normalAutEquivQuotient ψ'.ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ'surj)⟩
  exact ⟨L', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hreg, hgal⟩
