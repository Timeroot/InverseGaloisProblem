/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.ConstField
import InverseGalois.Rigidity.RET.Descent.FunctionFieldTower
import InverseGalois.Rigidity.RET.Descent.RegularityGen

/-!
# The regularity intersection leaf (`regularity_inf`), abstract form.

Inside a field `Ombar` that carries compatible `RatFunc ℚ` and `RatFunc ℚ̄`-algebra structures,
given a `RatFunc ℚ`-embedding `eΩ` of a finite Galois `RatFunc ℚ`-model `Ω`, the intersection of
`Ω`'s image with the constant subfield `ℚ̄(T)` is exactly the image of the constant field
`k₀(T) = constFieldBase Ω`.

This is the number-field generalization of `RET.GeometricIrreducibility.isField_baseChange_of_regular`,
delivered here at the required generality via `isField_baseChange_of_regular_gen`
(see `Descent.RegularityGen`) + `IntermediateField.LinearDisjoint.of_isField'` + `inf_eq_bot`.
-/

open Polynomial

namespace Rigidity.RET.Descent


attribute [local instance] Polynomial.algebra

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The genuine regularity content (the `⊆` inclusion).**  This is the number-field
generalization of `RET.GeometricIrreducibility.isField_baseChange_of_regular`.

Proof: let `k₀ := algebraicClosure ℚ Ω` (a number field, the constant field of `Ω`).  Equip `Ω` with
an `Algebra (RatFunc ↥k₀) Ω` structure (via `IsFractionRing.lift` of `aeval T`,
`T := algebraMap (RatFunc ℚ) Ω RatFunc.X`, transcendence lifted along `Transcendental.extendScalars`),
the scalar tower `IsScalarTower ↥k₀ (RatFunc ↥k₀) Ω`, and `FiniteDimensional (RatFunc ↥k₀) Ω`;
establish regularity `algebraicClosure ↥k₀ Ω = ⊥`.  Then `isField_baseChange_of_regular_gen` gives
`IsField (FractionRing (AlgebraicClosure ↥k₀)[X] ⊗[RatFunc ↥k₀] Ω)`, whence (via
`IntermediateField.LinearDisjoint.of_isField'` on the two embeddings `geom →ₐ Ombar`, `Ω →ₐ Ombar`
over `RatFunc ↥k₀`, then `.inf_eq_bot`) the base-`k₀(T)` intersection of `eΩ.fieldRange` with `ℚ̄(T)`
is `⊥`, i.e. the image of `k₀(T) = constFieldBase Ω`.  Finally translate carriers from `RatFunc ↥k₀`
back to `RatFunc ℚ`.

The geometric embedding `fa : geom →ₐ[RatFunc ↥k₀] Ombar` (whose range covers `ℚ̄(T)`) is built
inline: `AlgebraicClosure ↥k₀` and the copy of `AlgebraicClosure ℚ` inside `Ombar` are both algebraic
closures of `ℚ`, isomorphic compatibly with `eΩ` on constants — via `χ : ↥k₀ →ₐ[ℚ] AlgebraicClosure ℚ`
(from `AlgEquiv.ofInjective` + `codRestrict`) making `AlgebraicClosure ℚ` an `↥k₀`-algebra, then
`ψ := IsAlgClosure.equiv ↥k₀ (AlgebraicClosure ↥k₀) (AlgebraicClosure ℚ)` — and `fa` is the
`IsFractionRing.lift` of `aeval (eΩ T)` with constants routed through that isomorphism. -/
private theorem regularity_inf_subset
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra (RatFunc ℚ) Ω]
    [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]
    {Ombar : Type} [Field Ombar]
    [Algebra (RatFunc (AlgebraicClosure ℚ)) Ombar] [Algebra (RatFunc ℚ) Ombar]
    [@IsScalarTower (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar
      (instAlgRatFuncClosure).toSMul _ _]
    (eΩ : Ω →ₐ[RatFunc ℚ] Ombar) :
    eΩ.fieldRange ⊓
        ((⊥ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars (RatFunc ℚ))
      ≤ (constFieldBase Ω).map eΩ := by
  classical
  set k₀ := algebraicClosure ℚ Ω with hk₀
  haveI algQk₀ : Algebra.IsAlgebraic ℚ ↥k₀ := algebraicClosure.isAlgebraic ℚ Ω
  haveI ck₀ : CharZero ↥k₀ := inferInstance
  haveI towerQk₀Ω : IsScalarTower ℚ ↥k₀ Ω := IntermediateField.isScalarTower_mid' k₀
  -- Step 2: `T` transcendental over `k₀`.
  set T : Ω := algebraMap (RatFunc ℚ) Ω RatFunc.X with hT
  have hX : Transcendental ℚ (RatFunc.X : RatFunc ℚ) := by
    have h := RatFunc.transcendental_X (K := ℚ); convert h using 2; exact Subsingleton.elim _ _
  have hTQ : Transcendental ℚ T :=
    (transcendental_algebraMap_iff (S := RatFunc ℚ) (A := Ω)
      (algebraMap (RatFunc ℚ) Ω).injective).2 hX
  have hTk₀ : Transcendental ↥k₀ T := hTQ.extendScalars ↥k₀
  -- The injective ring hom `(↥k₀)[X] →+* Ω`, `X ↦ T`.
  have hginj : Function.Injective ⇑(Polynomial.aeval T : (↥k₀)[X] →ₐ[↥k₀] Ω) :=
    transcendental_iff_injective.1 hTk₀
  -- Step 2c: `Algebra (RatFunc ↥k₀) Ω` via the fraction-field lift.
  letI algRFk₀Ω : Algebra (RatFunc ↥k₀) Ω :=
    (IsFractionRing.lift (A := (↥k₀)[X]) (g := (Polynomial.aeval T : (↥k₀)[X] →ₐ[↥k₀] Ω).toRingHom)
      hginj).toAlgebra
  have hlift : ∀ x : (↥k₀)[X], algebraMap (RatFunc ↥k₀) Ω (algebraMap (↥k₀)[X] (RatFunc ↥k₀) x)
      = Polynomial.aeval T x := by
    intro x
    show IsFractionRing.lift (A := (↥k₀)[X]) hginj _ = _
    rw [IsFractionRing.lift_algebraMap]; rfl
  -- Tower `↥k₀ → RatFunc ↥k₀ → Ω`.
  haveI towerk₀RFΩ : IsScalarTower ↥k₀ (RatFunc ↥k₀) Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [IsScalarTower.algebraMap_apply ↥k₀ (↥k₀)[X] (RatFunc ↥k₀), hlift]
    simp [Polynomial.algebraMap_eq]
  -- Coefficient-extension algebra `RatFunc ℚ → RatFunc ↥k₀`.
  have hcoefinj : Function.Injective
      ((algebraMap (↥k₀)[X] (RatFunc ↥k₀)).comp (mapRingHom (algebraMap ℚ ↥k₀))) :=
    (IsFractionRing.injective (↥k₀)[X] (RatFunc ↥k₀)).comp
      (Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective ℚ ↥k₀))
  letI algRFQRFk₀ : Algebra (RatFunc ℚ) (RatFunc ↥k₀) :=
    (IsFractionRing.lift (A := ℚ[X]) hcoefinj).toAlgebra
  have hcoef : ∀ x : ℚ[X], algebraMap (RatFunc ℚ) (RatFunc ↥k₀) (algebraMap ℚ[X] (RatFunc ℚ) x)
      = algebraMap (↥k₀)[X] (RatFunc ↥k₀) (x.map (algebraMap ℚ ↥k₀)) := by
    intro x
    show IsFractionRing.lift (A := ℚ[X]) hcoefinj _ = _
    rw [IsFractionRing.lift_algebraMap]; rfl
  -- `algebraMap (RatFunc ℚ) Ω` acts on polynomials as `aeval T` over `ℚ`.
  have hliftQ : ∀ x : ℚ[X], algebraMap (RatFunc ℚ) Ω (algebraMap ℚ[X] (RatFunc ℚ) x)
      = Polynomial.aeval T x := by
    have key : (algebraMap (RatFunc ℚ) Ω).comp (algebraMap ℚ[X] (RatFunc ℚ))
        = (Polynomial.aeval T : ℚ[X] →ₐ[ℚ] Ω).toRingHom := by
      refine Polynomial.ringHom_ext ?_ ?_
      · intro a
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Polynomial.aeval_C]
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ),
          ← IsScalarTower.algebraMap_apply ℚ (RatFunc ℚ) Ω]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Polynomial.aeval_X, RatFunc.algebraMap_X, ← hT]
    intro x
    have := RingHom.congr_fun key x
    simpa using this
  -- Tower `RatFunc ℚ → RatFunc ↥k₀ → Ω`.
  haveI towerRFQRFk₀Ω : IsScalarTower (RatFunc ℚ) (RatFunc ↥k₀) Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
    refine RingHom.ext fun x => ?_
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hliftQ, hcoef, hlift, Polynomial.aeval_map_algebraMap]
  -- FiniteDimensional over `RatFunc ↥k₀`.
  haveI finΩ : FiniteDimensional (RatFunc ↥k₀) Ω :=
    Module.Finite.of_restrictScalars_finite (RatFunc ℚ) (RatFunc ↥k₀) Ω
  -- Step 3: regularity — `k₀` is relatively algebraically closed in `Ω` by construction.
  have hreg : algebraicClosure ↥k₀ Ω = ⊥ := algebraicClosure.algebraicClosure_eq_bot ℚ Ω
  -- Step 4: invoke the gen lemma (no type annotation, to avoid re-elaborating the tensor type).
  have hIsField := isField_baseChange_of_regular_gen (k₀ := ↥k₀) (L := Ω) hreg
  -- Constants images lie in `constFieldBase Ω`.
  have hT_mem : T ∈ constFieldBase Ω := by
    rw [hT]; exact IntermediateField.algebraMap_mem _ RatFunc.X
  have hpoly : ∀ p : (↥k₀)[X], Polynomial.aeval T p ∈ constFieldBase Ω := by
    intro p
    induction p using Polynomial.induction_on with
    | C c =>
        rw [Polynomial.aeval_C]
        exact const_le_constFieldBase Ω c.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a ih =>
        rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
        exact mul_mem ih hT_mem
  have hrange : ∀ r : RatFunc ↥k₀, algebraMap (RatFunc ↥k₀) Ω r ∈ constFieldBase Ω := by
    intro r
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := (↥k₀)[X]) r
    rw [map_div₀, hlift, hlift]
    exact div_mem (hpoly p) (hpoly q)
  -- Step 5: `Ombar` as a `RatFunc ↥k₀`-algebra via `eΩ`; the embedding `fb := eΩ`.
  letI algRFk₀Ombar : Algebra (RatFunc ↥k₀) Ombar :=
    (eΩ.toRingHom.comp (algebraMap (RatFunc ↥k₀) Ω)).toAlgebra
  let fb : Ω →ₐ[RatFunc ↥k₀] Ombar :=
    { eΩ.toRingHom with commutes' := fun _ => rfl }
  -- Step 6: the geometric embedding `fa` whose range covers `ℚ̄(T)` — built INLINE via the
  -- constant-field descent isomorphism `AlgebraicClosure ↥k₀ ≃ AlgebraicClosure ℚ` (inside Ombar).
  set Tb : Ombar := eΩ T with hTbdef
  -- STEP A: the copy of `ℚ̄` in Ombar and the ℚ-tower.
  letI algQbarOmbar : Algebra (AlgebraicClosure ℚ) Ombar :=
    ((algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar).comp
      (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)))).toAlgebra
  haveI towerQbarOmbar :
      IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI cOmbar : CharZero Ombar :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℚ) Ombar).injective
  letI algQOmbar : Algebra ℚ Ombar := DivisionRing.toRatAlgebra
  haveI towerQℚbarOmbar : IsScalarTower ℚ (AlgebraicClosure ℚ) Ombar :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let QbarHom : AlgebraicClosure ℚ →ₐ[ℚ] Ombar :=
    IsScalarTower.toAlgHom ℚ (AlgebraicClosure ℚ) Ombar
  have hQbarHominj : Function.Injective ⇑QbarHom := QbarHom.toRingHom.injective
  let ek₀ : ↥k₀ →ₐ[ℚ] Ombar := (eΩ.restrictScalars ℚ).comp (IsScalarTower.toAlgHom ℚ ↥k₀ Ω)
  -- STEP B: `eΩ`'s constants land in `QbarHom.range`.
  haveI algIntQk₀ : Algebra.IsIntegral ℚ ↥k₀ := algQk₀.isIntegral
  have hconst' : ∀ c : ↥k₀, ek₀ c ∈ QbarHom.range := by
    intro c
    set x : Ω := IsScalarTower.toAlgHom ℚ ↥k₀ Ω c with hxdef
    have hcint : IsIntegral ℚ c := Algebra.IsIntegral.isIntegral c
    have hxint : IsIntegral ℚ x := hcint.map (IsScalarTower.toAlgHom ℚ ↥k₀ Ω)
    have hyint : IsIntegral ℚ (eΩ x) := hxint.map (eΩ.restrictScalars ℚ)
    have hyalg : IsAlgebraic (AlgebraicClosure ℚ) (eΩ x) :=
      (hyint.isAlgebraic).tower_top (AlgebraicClosure ℚ)
    have hAdj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({eΩ x} : Set Ombar) = ⊥ := by
      haveI : Algebra.IsAlgebraic (AlgebraicClosure ℚ)
          (IntermediateField.adjoin (AlgebraicClosure ℚ) ({eΩ x} : Set Ombar)) :=
        (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic
            (F := AlgebraicClosure ℚ) (E := Ombar)).2
          (fun z hz => (Set.mem_singleton_iff.1 hz) ▸ hyalg)
      exact IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have hymem : eΩ x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({eΩ x} : Set Ombar) :=
      IntermediateField.subset_adjoin _ _ rfl
    rw [hAdj, IntermediateField.mem_bot] at hymem
    obtain ⟨c₀, hc₀⟩ := hymem
    refine ⟨c₀, ?_⟩
    show QbarHom c₀ = ek₀ c
    have hcoe : QbarHom c₀ = algebraMap (AlgebraicClosure ℚ) Ombar c₀ :=
      congrFun (IsScalarTower.coe_toAlgHom' ℚ (AlgebraicClosure ℚ) Ombar) c₀
    rw [hcoe]; exact hc₀
  -- STEP C: the field embedding `χ : ↥k₀ →ₐ[ℚ] AlgebraicClosure ℚ` compatible with `eΩ`.
  let eAlg : AlgebraicClosure ℚ ≃ₐ[ℚ] ↥QbarHom.range := AlgEquiv.ofInjective QbarHom hQbarHominj
  let ek₀' : ↥k₀ →ₐ[ℚ] ↥QbarHom.range := ek₀.codRestrict QbarHom.range hconst'
  let χ : ↥k₀ →ₐ[ℚ] AlgebraicClosure ℚ := eAlg.symm.toAlgHom.comp ek₀'
  have hχ : ∀ c : ↥k₀, QbarHom (χ c) = ek₀ c := by
    intro c
    have h1 : eAlg (χ c) = ek₀' c := by
      show eAlg (eAlg.symm (ek₀' c)) = ek₀' c
      exact eAlg.apply_symm_apply (ek₀' c)
    have h2 : QbarHom (χ c) = (↑(eAlg (χ c)) : Ombar) :=
      (AlgEquiv.ofInjective_apply QbarHom hQbarHominj (χ c)).symm
    rw [h2, h1]; rfl
  -- STEP D: give `AlgebraicClosure ℚ` an `↥k₀`-algebra structure via `χ`, and build `ψ`.
  letI algk₀Qbar : Algebra ↥k₀ (AlgebraicClosure ℚ) := χ.toAlgebra
  haveI towerℚk₀Qbar : IsScalarTower ℚ ↥k₀ (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun q => (χ.commutes q).symm)
  haveI towerℚk₀AC : IsScalarTower ℚ ↥k₀ (AlgebraicClosure ↥k₀) := inferInstance
  haveI algAlgk₀Qbar : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀ (A := AlgebraicClosure ℚ)
  haveI : IsAlgClosure ↥k₀ (AlgebraicClosure ℚ) := ⟨inferInstance, algAlgk₀Qbar⟩
  let ψ : AlgebraicClosure ↥k₀ ≃ₐ[↥k₀] AlgebraicClosure ℚ :=
    IsAlgClosure.equiv ↥k₀ (AlgebraicClosure ↥k₀) (AlgebraicClosure ℚ)
  -- STEP E: the ℚ-embedding `Φ : AlgebraicClosure ↥k₀ →ₐ[ℚ] Ombar`.
  let Φ : AlgebraicClosure ↥k₀ →ₐ[ℚ] Ombar :=
    QbarHom.comp ((ψ : AlgebraicClosure ↥k₀ →ₐ[↥k₀] AlgebraicClosure ℚ).restrictScalars ℚ)
  letI algACOmbar : Algebra (AlgebraicClosure ↥k₀) Ombar := Φ.toAlgebra
  haveI towerℚACOmbar : IsScalarTower ℚ (AlgebraicClosure ↥k₀) Ombar :=
    IsScalarTower.of_algebraMap_eq (fun q => (Φ.commutes q).symm)
  haveI algAlgℚAC : Algebra.IsAlgebraic ℚ (AlgebraicClosure ↥k₀) :=
    Algebra.IsAlgebraic.trans ℚ ↥k₀ (AlgebraicClosure ↥k₀)
  have hΦk₀ : ∀ c : ↥k₀,
      Φ (algebraMap ↥k₀ (AlgebraicClosure ↥k₀) c) = eΩ (algebraMap ↥k₀ Ω c) := by
    intro c
    have h1 : ψ (algebraMap ↥k₀ (AlgebraicClosure ↥k₀) c) = χ c := by
      rw [AlgEquiv.commutes]; rfl
    calc Φ (algebraMap ↥k₀ (AlgebraicClosure ↥k₀) c)
        = QbarHom (ψ (algebraMap ↥k₀ (AlgebraicClosure ↥k₀) c)) := rfl
      _ = QbarHom (χ c) := by rw [h1]
      _ = ek₀ c := hχ c
      _ = eΩ (algebraMap ↥k₀ Ω c) := rfl
  have hΦrange : Set.range Φ = Set.range QbarHom := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨ψ a, rfl⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := ψ.surjective b
      exact ⟨a, rfl⟩
  -- STEP F: the transcendental generator and `fa`.
  have hTb : Tb = algebraMap (RatFunc ℚ) Ombar RatFunc.X := by
    rw [hTbdef, hT]; exact eΩ.commutes RatFunc.X
  let eΩℚ : Ω →ₐ[ℚ] Ombar :=
    { eΩ.toRingHom with
      commutes' := fun q => RingHom.congr_fun
        (Subsingleton.elim (eΩ.toRingHom.comp (algebraMap ℚ Ω)) (algebraMap ℚ Ombar)) q }
  letI algΩOmbar : Algebra Ω Ombar := eΩℚ.toAlgebra
  haveI towerℚΩOmbar : IsScalarTower ℚ Ω Ombar :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hTbtrans : Transcendental ℚ Tb := by
    have hTbeq : Tb = algebraMap Ω Ombar T := by rw [hTbdef]; rfl
    rw [hTbeq]
    exact (transcendental_algebraMap_iff (S := Ω) (A := Ombar)
      (algebraMap Ω Ombar).injective).2 hTQ
  have hTbtransAC : Transcendental (AlgebraicClosure ↥k₀) Tb :=
    hTbtrans.extendScalars (AlgebraicClosure ↥k₀)
  have hgAC : Function.Injective
      ⇑(Polynomial.aeval Tb : (AlgebraicClosure ↥k₀)[X] →ₐ[AlgebraicClosure ↥k₀] Ombar) :=
    transcendental_iff_injective.1 hTbtransAC
  -- the key coefficient-compatibility: `aeval Tb ∘ (coeff-extend) = eΩ ∘ aeval T`.
  have hpush2 :
      (Polynomial.aeval Tb : (AlgebraicClosure ↥k₀)[X] →ₐ[AlgebraicClosure ↥k₀] Ombar).toRingHom.comp
          (Polynomial.mapRingHom (algebraMap ↥k₀ (AlgebraicClosure ↥k₀)))
        = eΩ.toRingHom.comp (Polynomial.aeval T : (↥k₀)[X] →ₐ[↥k₀] Ω).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
        Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
      show Φ (algebraMap ↥k₀ (AlgebraicClosure ↥k₀) a) = eΩ (algebraMap ↥k₀ Ω a)
      exact hΦk₀ a
    · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
        Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
      exact hTbdef
  have hfacomm :
      (IsFractionRing.lift (A := (AlgebraicClosure ↥k₀)[X])
          (g := (Polynomial.aeval Tb :
            (AlgebraicClosure ↥k₀)[X] →ₐ[AlgebraicClosure ↥k₀] Ombar).toRingHom) hgAC).comp
        (algebraMap (RatFunc ↥k₀) (FractionRing ((AlgebraicClosure ↥k₀)[X])))
      = algebraMap (RatFunc ↥k₀) Ombar := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (↥k₀)[X]) ?_
    refine RingHom.ext (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [algebraMap_ratFunc_geom_comp_gen (k₀ := ↥k₀) p, toClosureFrac_gen, RingHom.comp_apply,
      IsFractionRing.lift_algebraMap]
    have hRHS : algebraMap (RatFunc ↥k₀) Ombar (algebraMap (↥k₀)[X] (RatFunc ↥k₀) p)
        = eΩ.toRingHom ((Polynomial.aeval T : (↥k₀)[X] →ₐ[↥k₀] Ω).toRingHom p) := by
      rw [show algebraMap (RatFunc ↥k₀) Ombar (algebraMap (↥k₀)[X] (RatFunc ↥k₀) p)
            = eΩ (algebraMap (RatFunc ↥k₀) Ω (algebraMap (↥k₀)[X] (RatFunc ↥k₀) p)) from rfl,
        hlift]
      rfl
    rw [hRHS]
    exact RingHom.congr_fun hpush2 p
  let fa : FractionRing ((AlgebraicClosure ↥k₀)[X]) →ₐ[RatFunc ↥k₀] Ombar :=
    { IsFractionRing.lift (A := (AlgebraicClosure ↥k₀)[X])
        (g := (Polynomial.aeval Tb :
          (AlgebraicClosure ↥k₀)[X] →ₐ[AlgebraicClosure ↥k₀] Ombar).toRingHom) hgAC with
      commutes' := fun r => RingHom.congr_fun hfacomm r }
  -- STEP G: `fa`'s range covers `ℚ̄(T)`.
  have hval : ∀ q : (AlgebraicClosure ↥k₀)[X],
      fa (algebraMap ((AlgebraicClosure ↥k₀)[X]) (FractionRing ((AlgebraicClosure ↥k₀)[X])) q)
        = Polynomial.aeval Tb q := by
    intro q
    show IsFractionRing.lift (A := (AlgebraicClosure ↥k₀)[X]) hgAC (algebraMap _ _ q) = _
    rw [IsFractionRing.lift_algebraMap]; rfl
  have hTbmem : Tb ∈ fa.fieldRange := by
    refine AlgHom.mem_fieldRange.2
      ⟨algebraMap ((AlgebraicClosure ↥k₀)[X]) (FractionRing ((AlgebraicClosure ↥k₀)[X])) X, ?_⟩
    rw [hval, Polynomial.aeval_X]
  have hΦmem : ∀ d : AlgebraicClosure ↥k₀, Φ d ∈ fa.fieldRange := by
    intro d
    refine AlgHom.mem_fieldRange.2
      ⟨algebraMap ((AlgebraicClosure ↥k₀)[X]) (FractionRing ((AlgebraicClosure ↥k₀)[X])) (C d), ?_⟩
    rw [hval, Polynomial.aeval_C]; rfl
  have hQbarmem : ∀ c : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) Ombar c ∈ fa.fieldRange := by
    intro c
    have hmem : QbarHom c ∈ Set.range Φ := by rw [hΦrange]; exact ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hmem
    have hin : (QbarHom c : Ombar) ∈ fa.fieldRange := hd ▸ hΦmem d
    have hcoe : QbarHom c = algebraMap (AlgebraicClosure ℚ) Ombar c :=
      congrFun (IsScalarTower.coe_toAlgHom' ℚ (AlgebraicClosure ℚ) Ombar) c
    rwa [hcoe] at hin
  have hev : ∀ p : (AlgebraicClosure ℚ)[X],
      eval₂ (algebraMap (AlgebraicClosure ℚ) Ombar) Tb p ∈ fa.fieldRange := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => rw [eval₂_C]; exact hQbarmem a
    | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
    | monomial n a ih =>
        rw [pow_succ, ← mul_assoc, eval₂_mul, eval₂_X]
        exact mul_mem ih hTbmem
  have hRFX : algebraMap (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) RatFunc.X = RatFunc.X := by
    rw [← RatFunc.algebraMap_X (K := ℚ), algebraMap_ratFunc_closure_comp]
    simp [Polynomial.map_X, RatFunc.algebraMap_X]
  have hXbar : algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar RatFunc.X = Tb := by
    rw [hTb, IsScalarTower.algebraMap_apply (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar,
      hRFX]
  have hFG : (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar).comp
        (algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)))
      = Polynomial.eval₂RingHom (algebraMap (AlgebraicClosure ℚ) Ombar) Tb := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ)
        (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)),
        ← IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar]
    · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, RatFunc.algebraMap_X]
      exact hXbar
  have hpush : ∀ p : (AlgebraicClosure ℚ)[X],
      algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar
          (algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)) p)
        = eval₂ (algebraMap (AlgebraicClosure ℚ) Ombar) Tb p := by
    intro p
    have := RingHom.congr_fun hFG p
    simpa only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom] using this
  have hpolymem : ∀ p : (AlgebraicClosure ℚ)[X],
      algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar
          (algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)) p) ∈ fa.fieldRange := by
    intro p; rw [hpush p]; exact hev p
  have hfa_range : Set.range (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar)
      ⊆ (fa.fieldRange : Set Ombar) := by
    rintro y ⟨z, rfl⟩
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := (AlgebraicClosure ℚ)[X]) z
    rw [map_div₀]
    exact div_mem (hpolymem p) (hpolymem q)
  -- Step 7: linear disjointness ⟹ intersection is the base `k₀(T)`.
  have hLD : fa.fieldRange.LinearDisjoint fb.fieldRange :=
    IntermediateField.LinearDisjoint.of_isField' hIsField fa fb
  have hinf : fa.fieldRange ⊓ fb.fieldRange = ⊥ := hLD.inf_eq_bot
  rw [SetLike.le_def]
  intro y hy
  rw [IntermediateField.mem_inf] at hy
  obtain ⟨hyK, hyL⟩ := hy
  -- `y ∈ fb.fieldRange` (same carrier as `eΩ.fieldRange`).
  have hyKb : y ∈ fb.fieldRange := by
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 hyK
    exact ⟨a, ha⟩
  -- `y ∈ fa.fieldRange` (it lies in `ℚ̄(T)`).
  have hyLa : y ∈ fa.fieldRange := by
    rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot] at hyL
    exact hfa_range hyL
  -- Hence `y` lies in the base `k₀(T)` inside `Ombar`.
  have hy0 : y ∈ (⊥ : IntermediateField (RatFunc ↥k₀) Ombar) := by
    rw [← hinf, IntermediateField.mem_inf]; exact ⟨hyLa, hyKb⟩
  rw [IntermediateField.mem_bot] at hy0
  obtain ⟨r, hr⟩ := hy0
  -- `y = eΩ (algebraMap (RatFunc ↥k₀) Ω r)` with the argument in `constFieldBase Ω`.
  refine ⟨algebraMap (RatFunc ↥k₀) Ω r, hrange r, ?_⟩
  rw [← hr]; rfl

/-- **The regularity intersection leaf.**  Inside `Ombar` carrying compatible `RatFunc ℚ`- and
`RatFunc ℚ̄`-algebra structures, for a `RatFunc ℚ`-embedding `eΩ` of a finite Galois `RatFunc ℚ`-model
`Ω`, the intersection of `Ω`'s image with the geometric constant field `ℚ̄(T)` is exactly the image
of the constant-field base `k₀(T) = constFieldBase Ω`. -/
theorem regularity_inf_of_embedding
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra (RatFunc ℚ) Ω]
    [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]
    {Ombar : Type} [Field Ombar]
    [Algebra (RatFunc (AlgebraicClosure ℚ)) Ombar] [Algebra (RatFunc ℚ) Ombar]
    [@IsScalarTower (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar
      (instAlgRatFuncClosure).toSMul _ _]
    (eΩ : Ω →ₐ[RatFunc ℚ] Ombar) :
    eΩ.fieldRange ⊓
        ((⊥ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars (RatFunc ℚ))
      = (constFieldBase Ω).map eΩ := by
  classical
  haveI : CharZero Ombar :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℚ) Ombar).injective
  -- The copy of `ℚ̄` inside `Ombar`, and the compatibility towers over `ℚ`.
  letI algQbarOmbar : Algebra (AlgebraicClosure ℚ) Ombar :=
    ((algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar).comp
      (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)))).toAlgebra
  haveI towerQbarOmbar :
      IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- **Constants land in `ℚ̄(T)`.**
  have hconst : ∀ x ∈ (algebraicClosure ℚ Ω : Set Ω),
      eΩ x ∈ Set.range (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar) := by
    intro x hx
    have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.1 hx
    have hyint : IsIntegral ℚ (eΩ x) := hxint.map (eΩ.restrictScalars ℚ)
    have hyalg : IsAlgebraic (AlgebraicClosure ℚ) (eΩ x) :=
      (hyint.isAlgebraic).tower_top (AlgebraicClosure ℚ)
    have hAdj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({eΩ x} : Set Ombar) = ⊥ := by
      haveI : Algebra.IsAlgebraic (AlgebraicClosure ℚ)
          (IntermediateField.adjoin (AlgebraicClosure ℚ) ({eΩ x} : Set Ombar)) :=
        (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic
            (F := AlgebraicClosure ℚ) (E := Ombar)).2
          (fun z hz => (Set.mem_singleton_iff.1 hz) ▸ hyalg)
      exact IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have hymem : eΩ x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({eΩ x} : Set Ombar) :=
      IntermediateField.subset_adjoin _ _ rfl
    rw [hAdj, IntermediateField.mem_bot] at hymem
    obtain ⟨c, hc⟩ := hymem
    exact ⟨algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) c, by rw [← hc]; rfl⟩
  refine le_antisymm ?_ ?_
  · -- ⊆ : the genuine content, via regularity / linear disjointness.
    exact regularity_inf_subset eΩ
  · -- ⊇ : the image of the constant field lies in both `Kfr` and `Lfr`.
    apply le_inf
    · rw [AlgHom.fieldRange_eq_map]
      exact IntermediateField.map_mono eΩ le_top
    · rw [constFieldBase, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars, IntermediateField.mem_bot]
      exact hconst x hx

end Rigidity.RET.Descent
