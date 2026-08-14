/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.ModelDescent

/-!
# Enlarging the arithmetic model by roots of unity

The descent `ModelDescent` produces a `ℚ(T)`-model `Ω` of a geometric cover together with the
compositum `Ωbar = Ω · ℚ̄(T)`.  The branch-cycle argument reads tame inertia through a primitive
`N`-th root of unity, and that root has to live in the *arithmetic* model `Ω`, where the arithmetic
Galois group `Gal(Ω/ℚ(T))` acts on it by the cyclotomic character.  A model produced by the descent
need not contain one: the constant field of `Ω` is whatever the cover forces it to be.

The remedy is to enlarge the model *inside the compositum*, replacing `Ω` by `Ω(ζ_N)`.  Because
`ζ_N` is a constant, the compositum is unchanged — `Ω(ζ_N) · ℚ̄(T) = Ω · ℚ̄(T) = Ωbar` — so the
geometric group, the sub-cover, the primitive element and the branch locus all survive untouched.
The one piece that has to be rebuilt is the regularity comparison
`Gal(Ω/k₀(T)) ≃ Gal(Ωbar/ℚ̄(T))`, and that is available for *any* model of the compositum: it is
extracted here as `compareOfEmbedding`, depending only on the embedding of the model and the
compositum identity `Ω · ℚ̄(T) = Ωbar`.

## Main results

* `Rigidity.RET.Descent.compareOfEmbedding` — the regularity comparison for an arbitrary finite
  Galois `ℚ(T)`-model embedded in the compositum and generating it over `ℚ̄(T)`.
* `Rigidity.RET.Descent.GeomCompositum.enlarged` — the model of a compositum enlarged by the `N`-th
  roots of unity, with its normality, finiteness, the primitive `N`-th root of unity it contains,
  and the compositum identity it still satisfies.
-/

open Polynomial

namespace Rigidity.RET.Descent


/-- **The regularity comparison for a model of the compositum.**

If a finite Galois `ℚ(T)`-model `Ω` embeds in `Ωbar` and generates it over `ℚ̄(T)` — the compositum
identity `Ω · ℚ̄(T) = Ωbar`, here in the form `eΩ.fieldRange ⊔ ℚ̄(T) = ⊤` — then the geometric Galois
group `Gal(Ω/k₀(T))` of the model, over its own constant-field base `k₀(T) = constFieldBase Ω`, is
isomorphic to the Galois group `Gal(Ωbar/ℚ̄(T))` of the compositum, by an isomorphism carrying an
automorphism of the model to the automorphism of the compositum extending it.

The isomorphism is `IntermediateField.restrictRestrictAlgEquivMapHom`: it is injective by the
compositum identity, and surjective by the regularity intersection `Ω ∩ ℚ̄(T) = k₀(T)`
(`regularity_inf_of_embedding`), which says that `Ω/k₀(T)` is a regular extension. -/
theorem compareOfEmbedding
    {Ω : Type} [Field Ω] [CharZero Ω] [Algebra (RatFunc ℚ) Ω]
    [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]
    {Ombar : Type} [Field Ombar]
    [Algebra (RatFunc (AlgebraicClosure ℚ)) Ombar] [Algebra (RatFunc ℚ) Ombar]
    [@IsScalarTower (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar
      (instAlgRatFuncClosure).toSMul _ _]
    [FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) Ombar]
    [IsGalois (RatFunc (AlgebraicClosure ℚ)) Ombar]
    (eΩ : Ω →ₐ[RatFunc ℚ] Ombar)
    (hSup : eΩ.fieldRange ⊔
        ((⊥ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars (RatFunc ℚ))
      = ⊤) :
    ∃ cmp : (Ω ≃ₐ[constFieldBase Ω] Ω) ≃* (Ombar ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Ombar),
      ∀ (σ : Ω ≃ₐ[constFieldBase Ω] Ω) (x : Ω), cmp σ (eΩ x) = eΩ (σ x) := by
  classical
  set Kfr : IntermediateField (RatFunc ℚ) Ombar := eΩ.fieldRange with hKfrdef
  set Lfr : IntermediateField (RatFunc ℚ) Ombar :=
    (⊥ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars (RatFunc ℚ)
    with hLfrdef
  -- The regularity intersection: `Ω ∩ ℚ̄(T) = k₀(T)` inside `Ombar`.
  have regularity_inf : Kfr ⊓ Lfr = (constFieldBase Ω).map eΩ := regularity_inf_of_embedding eΩ
  set B := constFieldBase Ω with hBdef
  -- `Ω → Ombar` as an algebra (via `eΩ`), and the tower `ℚ(T) → Ω → Ombar`.
  letI algΩOmbar : Algebra Ω Ombar := (eΩ.toRingHom).toAlgebra
  haveI towerQΩOmbar : IsScalarTower (RatFunc ℚ) Ω Ombar :=
    IsScalarTower.of_algebraMap_eq (fun r => (eΩ.commutes r).symm)
  -- `B = k₀(T) → Ombar` (via `B → Ω → Ombar`), the two scalar towers.
  letI algBOmbar : Algebra B Ombar :=
    ((algebraMap Ω Ombar).comp (algebraMap B Ω)).toAlgebra
  haveI towerBΩOmbar : IsScalarTower B Ω Ombar := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hBOmbar_eq : ∀ b : B, algebraMap B Ombar b = eΩ (algebraMap B Ω b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B Ω Ombar]
    rfl
  haveI towerQBOmbar : IsScalarTower (RatFunc ℚ) B Ombar :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [hBOmbar_eq (algebraMap (RatFunc ℚ) B r),
        ← IsScalarTower.algebraMap_apply (RatFunc ℚ) B Ω, eΩ.commutes])
  -- `Bfr = eΩ(B)`, the carrier of both `⊥ : IntermediateField B Ombar` and `Kfr ⊓ Lfr`.
  have hBfr_range : ((B.map eΩ : IntermediateField (RatFunc ℚ) Ombar) : Set Ombar)
      = Set.range (algebraMap B Ombar) := by
    rw [IntermediateField.coe_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, (hBOmbar_eq ⟨y, hy⟩).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨algebraMap B Ω b, SetLike.coe_mem b, (hBOmbar_eq b).symm⟩
  have hBmapLe : B.map eΩ ≤ Lfr := regularity_inf ▸ inf_le_right
  -- `K := eΩ(Ω)` and `Lbase := ℚ̄(T)` inside `Ombar`, now as intermediate fields over the base `B`.
  let eΩB : Ω →ₐ[B] Ombar := IsScalarTower.toAlgHom B Ω Ombar
  let K : IntermediateField B Ombar := eΩB.fieldRange
  let Lbase : IntermediateField B Ombar :=
    Lfr.toSubfield.toIntermediateField (fun b => by
      have hb : algebraMap B Ombar b ∈ B.map eΩ := by
        rw [← SetLike.mem_coe, hBfr_range]; exact ⟨b, rfl⟩
      exact (IntermediateField.mem_toSubfield _ _).mpr (hBmapLe hb))
  have hKcoe : (K : Set Ombar) = (Kfr : Set Ombar) := by
    show (eΩB.fieldRange : Set Ombar) = (Kfr : Set Ombar)
    rw [AlgHom.coe_fieldRange eΩB, hKfrdef, AlgHom.coe_fieldRange eΩ]
    rfl
  have hLcoe : (Lbase : Set Ombar) = (Lfr : Set Ombar) := by
    rw [Subfield.coe_toIntermediateField, IntermediateField.coe_toSubfield]
  -- Base-changed compositum and intersection (carrier transports of `hSup` and `regularity_inf`).
  have hKrs : K.restrictScalars (RatFunc ℚ) = Kfr := by
    apply SetLike.coe_injective; rw [IntermediateField.coe_restrictScalars]; exact hKcoe
  have hLrs : Lbase.restrictScalars (RatFunc ℚ) = Lfr := by
    apply SetLike.coe_injective; rw [IntermediateField.coe_restrictScalars]; exact hLcoe
  have mono : ∀ {X Y : IntermediateField B Ombar}, X ≤ Y →
      X.restrictScalars (RatFunc ℚ) ≤ Y.restrictScalars (RatFunc ℚ) := by
    intro X Y h x hx
    rw [IntermediateField.mem_restrictScalars] at hx ⊢; exact h hx
  have hSupB : K ⊔ Lbase = ⊤ := by
    have hle : (⊤ : IntermediateField (RatFunc ℚ) Ombar)
        ≤ (K ⊔ Lbase).restrictScalars (RatFunc ℚ) := by
      rw [← hSup]
      refine sup_le ?_ ?_
      · rw [← hKrs]; exact mono le_sup_left
      · rw [← hLrs]; exact mono le_sup_right
    have hKL : (K ⊔ Lbase).restrictScalars (RatFunc ℚ) = ⊤ := top_le_iff.mp hle
    have htop : (⊤ : IntermediateField B Ombar).restrictScalars (RatFunc ℚ) = ⊤ := by
      apply SetLike.coe_injective
      rw [IntermediateField.coe_restrictScalars, IntermediateField.coe_top,
        IntermediateField.coe_top]
    exact IntermediateField.restrictScalars_injective (RatFunc ℚ) (hKL.trans htop.symm)
  have hInfB : K ⊓ Lbase = ⊥ := by
    apply SetLike.coe_injective
    rw [IntermediateField.coe_inf, IntermediateField.coe_bot, hKcoe, hLcoe,
      ← IntermediateField.coe_inf, regularity_inf]
    exact hBfr_range
  -- `Ω ≃ₐ[B] K`, and the induced `Gal(Ω/B) ≃* Gal(K/B)`.
  let e : Ω ≃ₐ[B] K := AlgEquiv.ofInjectiveField eΩB
  haveI galBΩ : IsGalois B Ω := inferInstance
  haveI : Normal B Ω := galBΩ.to_normal
  haveI normalBK : Normal B K := Normal.of_algEquiv e
  haveI findimBΩ : FiniteDimensional B Ω := inferInstance
  haveI findimBK : FiniteDimensional B K := Module.Finite.equiv e.toLinearEquiv
  -- `↥Lbase ≃+* ℚ̄(T)` (the corestriction of `algebraMap ℚ̄(T) Ombar`), for the base transport.
  have hmemL : ∀ r : RatFunc (AlgebraicClosure ℚ),
      algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar r ∈ Lbase := by
    intro r
    rw [← SetLike.mem_coe, hLcoe, SetLike.mem_coe, hLfrdef, IntermediateField.mem_restrictScalars,
      IntermediateField.mem_bot]
    exact ⟨r, rfl⟩
  let φL : RatFunc (AlgebraicClosure ℚ) →+* Lbase :=
    { toFun := fun r => ⟨algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar r, hmemL r⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  have hφLinj : Function.Injective φL := by
    intro a b hab
    exact (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar).injective (congrArg Subtype.val hab)
  have hφLsurj : Function.Surjective φL := by
    rintro ⟨y, hy⟩
    rw [← SetLike.mem_coe, hLcoe, SetLike.mem_coe, hLfrdef, IntermediateField.mem_restrictScalars,
      IntermediateField.mem_bot] at hy
    obtain ⟨r, hr⟩ := hy
    exact ⟨r, Subtype.ext hr⟩
  let fRE : RatFunc (AlgebraicClosure ℚ) ≃+* Lbase := RingEquiv.ofBijective φL ⟨hφLinj, hφLsurj⟩
  have hval : ∀ r, (algebraMap Lbase Ombar) (fRE r)
      = algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar r := fun r => rfl
  have hf_comp : (algebraMap Lbase Ombar).comp (fRE : RatFunc (AlgebraicClosure ℚ) →+* Lbase)
      = ((RingEquiv.refl Ombar : Ombar ≃+* Ombar) : Ombar →+* Ombar).comp
          (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar) := by
    ext r; simpa using hval r
  -- `Gal(Ombar/Lbase)` is finite and Galois (transported from `Gal(Ombar/ℚ̄(T))`).
  haveI : Algebra.IsAlgebraic (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI galLOmbar : IsGalois Lbase Ombar :=
    IsGalois.of_equiv_equiv (f := fRE) (g := RingEquiv.refl Ombar) hf_comp
  haveI findimLOmbar : FiniteDimensional Lbase Ombar :=
    Module.Finite.of_equiv_equiv fRE (RingEquiv.refl Ombar) hf_comp
  -- The regularity bijection `Gal(Ombar/Lbase) ≃* Gal(K/B)`.
  let bij : (Ombar ≃ₐ[Lbase] Ombar) ≃* (K ≃ₐ[B] K) :=
    MulEquiv.ofBijective _
      (⟨IntermediateField.restrictRestrictAlgEquivMapHom_injective K Lbase hSupB,
        IntermediateField.restrictRestrictAlgEquivMapHom_surjective K Lbase hInfB⟩ :
        Function.Bijective (IntermediateField.restrictRestrictAlgEquivMapHom B K Lbase Ombar))
  -- Base transport `Gal(Ombar/Lbase) ≃* Gal(Ombar/ℚ̄(T))` (same underlying ring automorphisms).
  let t3 : (Ombar ≃ₐ[Lbase] Ombar) ≃* (Ombar ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Ombar) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun r => by
        have hc := σ.commutes (fRE r)
        rw [hval r] at hc
        exact hc)
      invFun := fun τ => AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun l => by
        have key : (algebraMap Lbase Ombar) l
            = algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar (fRE.symm l) := by
          rw [← hval (fRE.symm l), RingEquiv.apply_symm_apply]
        rw [key]
        exact τ.commutes (fRE.symm l))
      left_inv := fun σ => by ext x; rfl
      right_inv := fun τ => by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  -- Assemble `cmp : Gal(Ω/B) ≃* Gal(Ombar/ℚ̄(T))`.
  refine ⟨(AlgEquiv.autCongr e).trans (bij.symm.trans t3), ?_⟩
  -- `cmp σ` extends `σ`: unwinding, the automorphism `τ := bij.symm (e σ e⁻¹)` of `Ombar` restricts
  -- on `K = eΩ(Ω)` to `e σ e⁻¹`, and `t3` does not change the underlying map.
  have hcoe : ∀ y : Ω, ((e y : K) : Ombar) = eΩ y := fun _ => rfl
  intro σ x
  have hbij : IntermediateField.restrictRestrictAlgEquivMapHom B K Lbase Ombar
      (bij.symm (AlgEquiv.autCongr e σ)) = AlgEquiv.autCongr e σ :=
    bij.apply_symm_apply (AlgEquiv.autCongr e σ)
  have hres := IntermediateField.restrictRestrictAlgEquivMapHom_apply K Lbase
    (bij.symm (AlgEquiv.autCongr e σ)) (e x)
  rw [hbij] at hres
  have hax : (AlgEquiv.autCongr e σ) (e x) = e (σ x) := by
    show e (σ (e.symm (e x))) = e (σ x)
    rw [e.symm_apply_apply]
  rw [hax] at hres
  rw [hcoe, hcoe] at hres
  exact hres.symm

/-- **The compositum identity in `⊔`-form.**

If the model generates the compositum over `ℚ̄(T)`, then the model together with the constant
extension generates it over `ℚ(T)`: the join of `eΩ.fieldRange` with the copy of `ℚ̄(T)` is
everything.  This is the hypothesis `compareOfEmbedding` consumes, and the adjoin-form is the one
the descent produces. -/
theorem sup_eq_top_of_adjoin_eq_top
    {Ω : Type} [Field Ω] [Algebra (RatFunc ℚ) Ω]
    {Ombar : Type} [Field Ombar]
    [Algebra (RatFunc (AlgebraicClosure ℚ)) Ombar] [Algebra (RatFunc ℚ) Ombar]
    [@IsScalarTower (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar
      (instAlgRatFuncClosure).toSMul _ _]
    (eΩ : Ω →ₐ[RatFunc ℚ] Ombar)
    (h : IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ)) (Set.range eΩ) = ⊤) :
    eΩ.fieldRange ⊔
        ((⊥ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars (RatFunc ℚ))
      = ⊤ := by
  set Lfr : IntermediateField (RatFunc ℚ) Ombar :=
    (⊥ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars (RatFunc ℚ)
    with hLfr
  set A : IntermediateField (RatFunc ℚ) Ombar := eΩ.fieldRange ⊔ Lfr with hA
  have hLA : Lfr ≤ A := le_sup_right
  have hKA : eΩ.fieldRange ≤ A := le_sup_left
  have hbase : ∀ r : RatFunc (AlgebraicClosure ℚ),
      algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar r ∈ A := by
    intro r
    refine hLA ?_
    rw [hLfr, IntermediateField.mem_restrictScalars]
    exact IntermediateField.algebraMap_mem _ r
  let A₂ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    A.toSubfield.toIntermediateField hbase
  have hA₂coe : (A₂ : Set Ombar) = (A : Set Ombar) := rfl
  have hle : (⊤ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar) ≤ A₂ := by
    rw [← h]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x ⟨y, rfl⟩
    exact hKA (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
  have hA₂top : A₂ = ⊤ := top_le_iff.mp hle
  apply SetLike.coe_injective
  rw [IntermediateField.coe_top, ← hA₂coe, hA₂top, IntermediateField.coe_top]

/-! ## Enlarging the model of a compositum by roots of unity -/

/-- The rational scalar action on `ℚ(T)` is multiplication by the constant rational function: the
scalar action `ℚ(T)` carries is the one of its `ℚ`-algebra structure through `ℚ[X]`, and there is
only one ring homomorphism `ℚ → ℚ(T)`. -/
theorem ratFunc_rat_smul (q : ℚ) (r : RatFunc ℚ) : q • r = (q : RatFunc ℚ) * r :=
  (@Algebra.smul_def ℚ (RatFunc ℚ) _ _ (RatFunc.instAlgebraOfPolynomial (R := ℚ) (K := ℚ)) q
      r).trans
    (congrArg (· * r) (eq_ratCast _ q))

/-- Every extension of `ℚ(T)` is an extension of `ℚ` in one way only: the scalar tower
`ℚ → ℚ(T) → X`.  Both rational actions are multiplication by a constant, so the tower law is
associativity. -/
theorem isScalarTower_rat_ratFunc (X : Type*) [Field X] [Algebra (RatFunc ℚ) X] :
    IsScalarTower ℚ (RatFunc ℚ) X := by
  refine ⟨fun q r x => ?_⟩
  rw [Algebra.smul_def, ratFunc_rat_smul, map_mul, Algebra.smul_def, Rat.smul_def,
    map_ratCast, mul_assoc]

namespace GeomCompositum

variable {G : Type} [Group G] [Finite G] (c : GeomCompositum G)

/-- The model of a compositum, as a `ℚ(T)`-embedding of the model into the compositum. -/
def modelHom : c.Ω →ₐ[RatFunc ℚ] c.Ωbar where
  toFun := algebraMap c.Ω c.Ωbar
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun q => ((c.algebraMap_Q_eq q).trans (c.algebraMap_comm q)).symm

@[simp] theorem modelHom_apply (x : c.Ω) : c.modelHom x = algebraMap c.Ω c.Ωbar x := rfl

/-- **The model enlarged by the `N`-th roots of unity**, taken inside the compositum: the subfield
generated over `ℚ(T)` by the model and the roots of `X ^ N - 1`. -/
def enlarged (N : ℕ) : IntermediateField (RatFunc ℚ) c.Ωbar :=
  c.modelHom.fieldRange ⊔
    IntermediateField.adjoin (RatFunc ℚ) ((X ^ N - C 1 : (RatFunc ℚ)[X]).rootSet c.Ωbar)

/-- The model is contained in its enlargement. -/
theorem modelHom_fieldRange_le_enlarged (N : ℕ) : c.modelHom.fieldRange ≤ c.enlarged N :=
  le_sup_left

/-- The compositum contains a primitive `N`-th root of unity: it is an extension of `ℚ̄(T)`, and
`ℚ̄` has all roots of unity. -/
theorem exists_primitiveRoot (N : ℕ) [NeZero N] : ∃ ζ : c.Ωbar, IsPrimitiveRoot ζ N := by
  haveI : NeZero ((N : ℕ) : AlgebraicClosure ℚ) := ⟨by
    simpa using (Nat.cast_ne_zero (R := AlgebraicClosure ℚ)).mpr (NeZero.ne N)⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  refine ⟨algebraMap (RatFunc (AlgebraicClosure ℚ)) c.Ωbar
    (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) ζ₀), ?_⟩
  exact (hζ₀.map_of_injective
      (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))).injective).map_of_injective
    (algebraMap (RatFunc (AlgebraicClosure ℚ)) c.Ωbar).injective

/-- The roots of `X ^ N - 1` in the compositum generate a splitting field of `X ^ N - 1` over
`ℚ(T)`. -/
theorem adjoinRoots_isSplittingField {N : ℕ} {ζ : c.Ωbar} (hζ : IsPrimitiveRoot ζ N) :
    IsSplittingField (RatFunc ℚ)
      ↥(IntermediateField.adjoin (RatFunc ℚ) ((X ^ N - C 1 : (RatFunc ℚ)[X]).rootSet c.Ωbar))
      (X ^ N - C 1) := by
  refine IntermediateField.adjoin_rootSet_isSplittingField ?_
  have hmap : ((X ^ N - C 1 : (RatFunc ℚ)[X]).map (algebraMap (RatFunc ℚ) c.Ωbar))
      = X ^ N - C (1 : c.Ωbar) := by
    simp
  rw [hmap]
  exact Polynomial.X_pow_sub_one_splits hζ

/-- The enlarged model is normal over `ℚ(T)`: it is the join of the model, which is Galois, with a
splitting field of `X ^ N - 1`. -/
theorem enlarged_normal (N : ℕ) [NeZero N] : Normal (RatFunc ℚ) ↥(c.enlarged N) := by
  obtain ⟨ζ, hζ⟩ := c.exists_primitiveRoot N
  haveI : Normal (RatFunc ℚ) c.Ω := IsGalois.to_normal
  haveI : Normal (RatFunc ℚ) ↥c.modelHom.fieldRange :=
    Normal.of_algEquiv (AlgEquiv.ofInjectiveField c.modelHom)
  haveI := c.adjoinRoots_isSplittingField hζ
  haveI : Normal (RatFunc ℚ)
      ↥(IntermediateField.adjoin (RatFunc ℚ) ((X ^ N - C 1 : (RatFunc ℚ)[X]).rootSet c.Ωbar)) :=
    Normal.of_isSplittingField (X ^ N - C 1)
  show Normal (RatFunc ℚ) ↥(c.modelHom.fieldRange ⊔
    IntermediateField.adjoin (RatFunc ℚ) ((X ^ N - C 1 : (RatFunc ℚ)[X]).rootSet c.Ωbar))
  infer_instance

/-- The enlarged model is finite over `ℚ(T)`. -/
theorem enlarged_finiteDimensional (N : ℕ) [NeZero N] :
    FiniteDimensional (RatFunc ℚ) ↥(c.enlarged N) := by
  obtain ⟨ζ, hζ⟩ := c.exists_primitiveRoot N
  haveI : FiniteDimensional (RatFunc ℚ) ↥c.modelHom.fieldRange :=
    (AlgEquiv.ofInjectiveField c.modelHom).toLinearEquiv.finiteDimensional
  haveI := c.adjoinRoots_isSplittingField hζ
  haveI : FiniteDimensional (RatFunc ℚ)
      ↥(IntermediateField.adjoin (RatFunc ℚ) ((X ^ N - C 1 : (RatFunc ℚ)[X]).rootSet c.Ωbar)) :=
    IsSplittingField.finiteDimensional _ (X ^ N - C 1)
  show FiniteDimensional (RatFunc ℚ) ↥(c.modelHom.fieldRange ⊔
    IntermediateField.adjoin (RatFunc ℚ) ((X ^ N - C 1 : (RatFunc ℚ)[X]).rootSet c.Ωbar))
  infer_instance

/-- The enlarged model contains a primitive `N`-th root of unity — that is what it was enlarged
for. -/
theorem exists_primitiveRoot_enlarged (N : ℕ) [NeZero N] :
    ∃ z : ↥(c.enlarged N), IsPrimitiveRoot z N := by
  obtain ⟨ζ, hζ⟩ := c.exists_primitiveRoot N
  have hle : IntermediateField.adjoin (RatFunc ℚ) ((X ^ N - C 1 : (RatFunc ℚ)[X]).rootSet c.Ωbar)
      ≤ c.enlarged N := le_sup_right
  have hmem : ζ ∈ c.enlarged N := by
    refine hle (IntermediateField.subset_adjoin _ _ ?_)
    rw [Polynomial.mem_rootSet]
    refine ⟨Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (NeZero.ne N)) 1, ?_⟩
    simp [hζ.pow_eq_one]
  have hinj : Function.Injective (algebraMap (↥(c.enlarged N)) c.Ωbar) :=
    (algebraMap (↥(c.enlarged N)) c.Ωbar).injective
  exact ⟨⟨ζ, hmem⟩,
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (↥(c.enlarged N)) c.Ωbar) hζ hinj⟩

/-- The enlarged model is an extension of `ℚ` through `ℚ(T)`: the rational scalars of the subfield
are those of the compositum, where the tower law holds. -/
theorem enlarged_isScalarTower (N : ℕ) : IsScalarTower ℚ (RatFunc ℚ) ↥(c.enlarged N) := by
  haveI := isScalarTower_rat_ratFunc c.Ωbar
  refine ⟨fun q r x => ?_⟩
  apply Subtype.ext
  push_cast
  exact smul_assoc q r (x : c.Ωbar)

/-- The enlarged model still generates the compositum over `ℚ̄(T)`: it contains the model, which
already does. -/
theorem enlarged_adjoin_eq_top (N : ℕ) :
    IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ))
      (Set.range (IntermediateField.val (c.enlarged N))) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← c.adjoin_model_eq_top]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x ⟨y, rfl⟩
  exact IntermediateField.subset_adjoin _ _
    ⟨⟨algebraMap c.Ω c.Ωbar y,
      c.modelHom_fieldRange_le_enlarged N (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)⟩, rfl⟩

end GeomCompositum

end Rigidity.RET.Descent
