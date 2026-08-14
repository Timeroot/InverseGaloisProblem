/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Existence
import InverseGalois.Rigidity.RET.Descent.ConstField
import InverseGalois.Rigidity.RET.Descent.ConstantNormal
import InverseGalois.Rigidity.RET.Descent.FunctionFieldTower
import InverseGalois.Rigidity.RET.Descent.RegularityInf

/-!
# Module A / A2 — the arithmetic model descent (`geomModel_descent`)

From an abstract geometric Galois cover `L/ℚ̄(T)` with deck group `G`, this module constructs a
*finite* Galois extension `Ω/ℚ(T)` (char 0) whose geometric Galois group `Gal(Ω/k_Ω(T))` — over its
own constant-field base `k_Ω(T) = constFieldBase Ω` — **surjects** onto `G`.

This is the genuine arithmetic-geometry content of the descent, isolated to the single sharply-typed
theorem `geomModel_descent`.  The construction:

* take a primitive element `θ` of `L/ℚ̄(T)`, its `ℚ(T)`-minimal polynomial `M := minpoly (ℚ(T)) θ`,
  and set `Ω := M.SplittingField` (finite Galois over `ℚ(T)`);
* form the compositum `Ombar := (M.map (ℚ(T)→ℚ̄(T))).SplittingField` over `ℚ̄(T)`, embedding both `Ω`
  and `L` into it;
* read off the monodromy `Gal(Ω/k_Ω(T)) ↠ G` via the base-change comparison over `ℚ̄(T)`
  (`IntermediateField.restrictRestrictAlgEquivMapHom` — bijective, injectivity from the compositum
  `Kfr ⊔ Lfr = ⊤`, surjectivity from the regularity intersection `Kfr ⊓ Lfr = k_Ω(T)`, the sole
  genuinely-absent fact, delivered by `regularity_inf_of_embedding` in `Descent.RegularityInf`)
  composed with the restriction `L ⊆ Ω·ℚ̄(T)` and the cover isomorphism `Gal(L/ℚ̄(T)) ≃* G`.

Only a **surjection** is asserted (not the classical iso): the field-of-moduli/field-of-definition
gap is the descent obstruction Module C handles, and the downstream (`GeomModel.toArithmeticModel`,
Module D `quotientKerEquivOfSurjective`) consumes only surjectivity.  See `DESCENT_ROADMAP.md` §1.
-/

open Polynomial

namespace Rigidity.RET.Descent


/-- **The descended model together with the geometric compositum it sits in.**

The arithmetic descent produces more than the `ℚ(T)`-model `Ω`: it produces the whole square

```
        ℚ̄(T) ⊆ Lsub ⊆ Ωbar = Ω · ℚ̄(T)
                            ∪
  ℚ(T) ⊆ k₀(T) ⊆            Ω
```

in which `Ωbar` is a finite Galois extension of `ℚ̄(T)` containing both the model `Ω` and a copy
`Lsub` of the original cover, and the regularity comparison identifies the geometric Galois group
`Gal(Ω/k₀(T))` of the model with the Galois group `Gal(Ωbar/ℚ̄(T))` of the compositum.  The bundle is
recorded here because the branch-cycle argument needs the *geometry* — places of `ℚ̄[X]` in `Ωbar`,
inertia there, the sub-cover `Lsub` whose deck group is `G` — and then needs to carry it back down
to the arithmetic model through `compare`.

The single compatibility `compare_apply` is what makes the identification usable: `compare σ` is the
automorphism of `Ωbar` extending `σ`. -/
structure GeomCompositum (G : Type) [Group G] [Finite G] where
  /-- the descended `ℚ(T)`-model. -/
  Ω : Type
  [fieldΩ : Field Ω]
  [algΩ : Algebra (RatFunc ℚ) Ω]
  [findimΩ : FiniteDimensional (RatFunc ℚ) Ω]
  [galΩ : IsGalois (RatFunc ℚ) Ω]
  [charZeroΩ : CharZero Ω]
  [towerΩ : IsScalarTower ℚ (RatFunc ℚ) Ω]
  /-- the geometric compositum `Ωbar = Ω · ℚ̄(T)`. -/
  Ωbar : Type
  [fieldΩbar : Field Ωbar]
  [algΩbar : Algebra (RatFunc (AlgebraicClosure ℚ)) Ωbar]
  [findimΩbar : FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) Ωbar]
  [galΩbar : IsGalois (RatFunc (AlgebraicClosure ℚ)) Ωbar]
  /-- the compositum is an extension of `ℚ(T)`, through the constant extension `ℚ(T) ⊆ ℚ̄(T)`. -/
  [algQΩbar : Algebra (RatFunc ℚ) Ωbar]
  /-- the `ℚ(T)`-structure on the compositum factors through the constant extension.  This is
  recorded as an equality of structure maps rather than as an `IsScalarTower` instance so that the
  scalar action of `ℚ(T)` on `ℚ̄(T)` never has to be pinned to a particular one of the several the
  library offers. -/
  algebraMap_Q_eq : ∀ q : RatFunc ℚ, algebraMap (RatFunc ℚ) Ωbar q
    = algebraMap (RatFunc (AlgebraicClosure ℚ)) Ωbar
        (algebraMap (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) q)
  /-- **the compositum is normal over `ℚ(T)`**, although it is infinite over it: it is generated
  over `ℚ̄(T)` by the roots of a `ℚ(T)`-polynomial, and the constants are algebraic over `ℚ`.  This
  is what makes the `ℚ(T)`-conjugates of the sub-cover reachable by automorphisms of `Ωbar`. -/
  [normalΩbar : Normal (RatFunc ℚ) Ωbar]
  /-- the model sits inside the compositum. -/
  [algΩΩbar : Algebra Ω Ωbar]
  /-- the two routes `ℚ(T) → ℚ̄(T) → Ωbar` and `ℚ(T) → Ω → Ωbar` into the compositum agree: the
  compositum is an extension of `ℚ(T)` in one way only. -/
  algebraMap_comm : ∀ q : RatFunc ℚ,
    algebraMap (RatFunc (AlgebraicClosure ℚ)) Ωbar
        (algebraMap (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) q)
      = algebraMap Ω Ωbar (algebraMap (RatFunc ℚ) Ω q)
  /-- the copy of the original cover inside the compositum. -/
  Lsub : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ωbar
  [normalLsub : Normal (RatFunc (AlgebraicClosure ℚ)) Lsub]
  /-- the deck group of the sub-cover is `G`. -/
  galLsub : (Lsub ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Lsub) ≃* G
  /-- **the regularity comparison**: the geometric Galois group of the model is the Galois group of
  the compositum. -/
  compare : (Ω ≃ₐ[constFieldBase Ω] Ω) ≃* (Ωbar ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Ωbar)
  /-- `compare σ` is the automorphism of the compositum extending `σ`. -/
  compare_apply : ∀ (σ : Ω ≃ₐ[constFieldBase Ω] Ω) (x : Ω),
    compare σ (algebraMap Ω Ωbar x) = algebraMap Ω Ωbar (σ x)
  /-- **the compositum is generated by the model over `ℚ̄(T)`**: `Ωbar = Ω · ℚ̄(T)`. -/
  adjoin_model_eq_top : IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ))
    (Set.range (algebraMap Ω Ωbar)) = ⊤
  /-- a primitive element of the sub-cover over `ℚ̄(T)`. -/
  prim : Ωbar
  /-- the sub-cover is generated by the primitive element. -/
  Lsub_eq_adjoin : Lsub = IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ)) {prim}
  /-- **the `ℚ(T)`-conjugates of the primitive element generate the compositum**: `Ωbar` is the
  splitting field over `ℚ̄(T)` of the `ℚ(T)`-minimal polynomial of `prim`.  This is what makes the
  compositum of the conjugates of the sub-cover all of `Ωbar`. -/
  adjoin_rootSet_eq_top : IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ))
    ((minpoly (RatFunc ℚ) prim).rootSet Ωbar) = ⊤

attribute [instance] GeomCompositum.fieldΩ GeomCompositum.algΩ GeomCompositum.findimΩ
  GeomCompositum.galΩ GeomCompositum.charZeroΩ GeomCompositum.towerΩ GeomCompositum.fieldΩbar
  GeomCompositum.algΩbar GeomCompositum.findimΩbar GeomCompositum.galΩbar
  GeomCompositum.algQΩbar GeomCompositum.normalΩbar
  GeomCompositum.algΩΩbar GeomCompositum.normalLsub

/-- The variable of `ℚ(T)` and the variable of `ℚ̄(T)` have the same image in the compositum. -/
theorem GeomCompositum.algebraMap_X {G : Type} [Group G] [Finite G] (c : GeomCompositum G) :
    algebraMap (RatFunc ℚ) c.Ωbar RatFunc.X
      = algebraMap (RatFunc (AlgebraicClosure ℚ)) c.Ωbar RatFunc.X := by
  rw [c.algebraMap_Q_eq, algebraMap_ratFunc_closure_X]

attribute [local instance] Polynomial.algebra

/-- The **geometric monodromy** of the compositum: restrict an automorphism of `Ωbar` to the
sub-cover `Lsub` and read the result in `G`. -/
noncomputable def GeomCompositum.toG {G : Type} [Group G] [Finite G] (c : GeomCompositum G) :
    (c.Ωbar ≃ₐ[RatFunc (AlgebraicClosure ℚ)] c.Ωbar) →* G :=
  c.galLsub.toMonoidHom.comp (AlgEquiv.restrictNormalHom c.Lsub)

/-- The geometric monodromy is surjective: restriction to a normal subextension is surjective on
Galois groups, and `galLsub` is an isomorphism. -/
theorem GeomCompositum.surjective_toG {G : Type} [Group G] [Finite G] (c : GeomCompositum G) :
    Function.Surjective c.toG :=
  c.galLsub.surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (F := RatFunc (AlgebraicClosure ℚ)) (K₁ := c.Lsub)
      (E := c.Ωbar))

/-- The monodromy of the *model*, `Gal(Ω/k₀(T)) ↠ G`: the geometric monodromy of the compositum
read through the regularity comparison. -/
noncomputable def GeomCompositum.monodromy {G : Type} [Group G] [Finite G] (c : GeomCompositum G) :
    (c.Ω ≃ₐ[constFieldBase c.Ω] c.Ω) →* G :=
  c.toG.comp c.compare.toMonoidHom

theorem GeomCompositum.surjective_monodromy {G : Type} [Group G] [Finite G]
    (c : GeomCompositum G) : Function.Surjective c.monodromy :=
  c.surjective_toG.comp c.compare.surjective

set_option maxHeartbeats 400000 in
/-- **The arithmetic descent core (A2's irreducible leaf).**  From an abstract geometric Galois cover
`L/ℚ̄(T)` with deck group `G`, there is a *finite* Galois extension `Ω/ℚ(T)` (char 0) whose geometric
Galois group `Gal(Ω/k_Ω(T))` — over its own constant-field base `k_Ω(T) = constFieldBase Ω` —
**surjects** onto `G`, and moreover the whole compositum square is available (`GeomCompositum`).

This is the genuine arithmetic-geometry content of the descent, isolated to a single sharply-typed
theorem: descend the cover `L/ℚ̄(T)` to a finite `ℚ(T)`-model `Ω` (primitive element `θ` of `L/ℚ̄(T)`,
its `ℚ(T)`-minimal polynomial `m := minpoly (ℚ(T)) θ`, and `Ω := m.SplittingField`), then read off the
monodromy `Gal(Ω/k_Ω(T)) ↠ G` via the base-change comparison over `ℚ̄(T)`
(`IntermediateField.restrictRestrictAlgEquivMapHom`, surjective by linear disjointness — `k_Ω` is
exactly `Ω ∩ ℚ̄`, i.e. `Ω/k_Ω(T)` is regular) composed with the restriction `L ⊆ Ω·ℚ̄(T)`.

Only a **surjection** is asserted (not the classical iso): the field-of-moduli/field-of-definition
gap is the descent obstruction Module C handles, and the downstream (`GeomModel.toArithmeticModel`,
Module D `quotientKerEquivOfSurjective`) consumes only surjectivity.  See `DESCENT_ROADMAP.md` §1.

The sub-cover of the compositum is not merely *some* cover with deck group `G`: it is a copy of the
given cover `L`, and the isomorphism is returned alongside, because the branch locus of `L` has to
travel with it. -/
theorem geomCompositum_exists_of_cover {G : Type} [Group G] [Finite G] (L : Type) [Field L]
    [Algebra (RatFunc (AlgebraicClosure ℚ)) L]
    [FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) L]
    [IsGalois (RatFunc (AlgebraicClosure ℚ)) L]
    (φG : (L ≃ₐ[RatFunc (AlgebraicClosure ℚ)] L) ≃* G) :
    ∃ (c : GeomCompositum G) (e : L ≃ₐ[RatFunc (AlgebraicClosure ℚ)] c.Lsub),
      ∀ σ : L ≃ₐ[RatFunc (AlgebraicClosure ℚ)] L, c.galLsub (AlgEquiv.autCongr e σ) = φG σ := by
  classical
  haveI galL : IsGalois (RatFunc (AlgebraicClosure ℚ)) L := inferInstance
  -- Tower `ℚ(T) → ℚ̄(T) → L`.
  letI algQTL : Algebra (RatFunc ℚ) L :=
    ((algebraMap (RatFunc (AlgebraicClosure ℚ)) L).comp toClosureRatFunc).toAlgebra
  -- Pin `SMul (RatFunc ℚ) (RatFunc ℚ̄)` to `instAlgRatFuncClosure`'s (Mathlib has a competing
  -- `RatFunc.instSMulOfFractionRingPolynomial` at higher priority, creating a diamond).
  letI smulRS : SMul (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    (instAlgRatFuncClosure).toSMul
  haveI towerL : IsScalarTower (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- `L / ℚ̄(T)` is separable and finite (from `IsGalois`), so it has a primitive element.
  haveI : Algebra.IsSeparable (RatFunc (AlgebraicClosure ℚ)) L := galL.to_isSeparable
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (RatFunc (AlgebraicClosure ℚ)) L
  -- `θ` is algebraic over `ℚ(T)` (transitivity along the tower).
  haveI algQbT : Algebra.IsAlgebraic (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    isAlgebraic_ratFunc_closure
  haveI algLQbT : Algebra.IsAlgebraic (RatFunc (AlgebraicClosure ℚ)) L :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI algLQT : Algebra.IsAlgebraic (RatFunc ℚ) L :=
    Algebra.IsAlgebraic.trans (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) L
  have hθint : IsIntegral (RatFunc ℚ) θ := (Algebra.IsAlgebraic.isAlgebraic θ).isIntegral
  -- The `ℚ(T)`-minimal polynomial of `θ`, and its separability (`ℚ(T)` is perfect, char 0).
  set M : (RatFunc ℚ)[X] := minpoly (RatFunc ℚ) θ with hMdef
  have hMsep : M.Separable := (minpoly.irreducible hθint).separable
  -- `Ω := SplittingField M` over `ℚ(T)`.
  haveI : FiniteDimensional (RatFunc ℚ) M.SplittingField :=
    IsSplittingField.finiteDimensional M.SplittingField M
  haveI galΩ : IsGalois (RatFunc ℚ) M.SplittingField := IsGalois.of_separable_splitting_field hMsep
  haveI charΩ : CharZero M.SplittingField :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℚ) M.SplittingField).injective
  -- Pin `Algebra ℚ Ω` to the char-zero `DivisionRing.toRatAlgebra` (what `constFieldBase` and the
  -- existential binder use), not the `SplittingField`-derived one; prove the tower via the
  -- uniqueness of ring homs out of `ℚ`.
  letI aQR : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial (K := ℚ) (R := ℚ)
  letI aRΩ : Algebra (RatFunc ℚ) M.SplittingField := inferInstance
  letI aQΩ : Algebra ℚ M.SplittingField := DivisionRing.toRatAlgebra
  haveI towerΩ :
      @IsScalarTower ℚ (RatFunc ℚ) M.SplittingField aQR.toSMul aRΩ.toSMul aQΩ.toSMul := by
    apply IsScalarTower.of_algebraMap_eq'
    exact Subsingleton.elim _ _
  ------------------------------------------------------------------------------------------------
  -- STAGE 1: the compositum `Ombar := P.SplittingField` over `ℚ̄(T)`, `P := M.map (ℚ(T)→ℚ̄(T))`.
  ------------------------------------------------------------------------------------------------
  set P : (RatFunc (AlgebraicClosure ℚ))[X] :=
    M.map (algebraMap (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ))) with hPdef
  have hPsep : P.Separable := hMsep.map
  set Ombar := P.SplittingField with hOmbardef
  -- `Ombar` is finite Galois over `ℚ̄(T)` (splitting field of the separable `P`).
  haveI findimOmbar : FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    IsSplittingField.finiteDimensional Ombar P
  haveI galOmbar : IsGalois (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    IsGalois.of_separable_splitting_field hPsep
  haveI normalOmbar : Normal (RatFunc (AlgebraicClosure ℚ)) Ombar := galOmbar.to_normal
  ------------------------------------------------------------------------------------------------
  -- STAGE 2a: `P` splits in `Ombar`, and `M` splits in `Ombar` over `ℚ(T)` (base change).
  ------------------------------------------------------------------------------------------------
  -- Scalar tower `ℚ(T) → ℚ̄(T) → Ombar` (`Algebra (RatFunc ℚ) Ombar` derived through `ℚ̄(T)`).
  haveI towerQOmbar : IsScalarTower (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    inferInstance
  have hPsplit : Splits (P.map (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar)) :=
    IsSplittingField.splits Ombar P
  -- `M.map (ℚ(T)→Ombar) = P.map (ℚ̄(T)→Ombar)`, hence splits.  (Avoid rewriting `P`, since
  -- `Field Ombar = SplittingField.instField P` depends on it; rewrite the `algebraMap` instead.)
  have hMmapP : M.map (algebraMap (RatFunc ℚ) Ombar)
      = P.map (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar) := by
    rw [IsScalarTower.algebraMap_eq (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar,
      ← Polynomial.map_map, ← hPdef]
  have hMsplit : Splits (M.map (algebraMap (RatFunc ℚ) Ombar)) := hMmapP ▸ hPsplit
  have hPmap_ne : P.map (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar) ≠ 0 :=
    (Polynomial.map_ne_zero_iff
      (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar).injective).2 hPsep.ne_zero
  ------------------------------------------------------------------------------------------------
  -- STAGE 2b: embeddings `eΩ : Ω →ₐ[ℚ(T)] Ombar` and `eL : L →ₐ[ℚ̄(T)] Ombar`.
  ------------------------------------------------------------------------------------------------
  -- `Ω = M.SplittingField` embeds into `Ombar` over `ℚ(T)` (`M` splits in `Ombar`).
  let eΩ : M.SplittingField →ₐ[RatFunc ℚ] Ombar := Polynomial.SplittingField.lift M hMsplit
  have heΩinj : Function.Injective eΩ := eΩ.injective
  -- `θ` is a root of `P` over `ℚ̄(T)`, so `minpoly ℚ̄(T) θ ∣ P` splits in `Ombar`.
  have hθP : (aeval θ) P = 0 := by
    rw [hPdef, aeval_map_algebraMap]; exact minpoly.aeval (RatFunc ℚ) θ
  have hθmin_dvd : minpoly (RatFunc (AlgebraicClosure ℚ)) θ ∣ P := minpoly.dvd _ _ hθP
  have hθmin_split :
      Splits ((minpoly (RatFunc (AlgebraicClosure ℚ)) θ).map
        (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar)) :=
    Polynomial.Splits.of_dvd hPsplit hPmap_ne
      (Polynomial.map_dvd (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar) hθmin_dvd)
  -- `L = ℚ̄(T)⟮θ⟯` embeds into `Ombar` over `ℚ̄(T)`.
  obtain ⟨eL⟩ :=
    IntermediateField.nonempty_algHom_of_adjoin_splits
      (F := RatFunc (AlgebraicClosure ℚ)) (E := L) (K := Ombar)
      (S := {θ})
      (fun s hs => by
        rw [Set.mem_singleton_iff] at hs; subst s
        exact ⟨IsIntegral.of_finite (RatFunc (AlgebraicClosure ℚ)) θ, hθmin_split⟩)
      hθ
  have heLinj : Function.Injective eL := eL.injective
  ------------------------------------------------------------------------------------------------
  -- STAGE 3: the reachable surjection `toG : Gal(Ombar/ℚ̄(T)) ↠ G`, via restriction to the image
  -- of the cover `L` and `φG`.
  ------------------------------------------------------------------------------------------------
  set Limg : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar := eL.fieldRange with hLimgdef
  let eL' : L ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Limg := AlgEquiv.ofInjectiveField eL
  haveI normalL : Normal (RatFunc (AlgebraicClosure ℚ)) L := galL.to_normal
  haveI normalLimg : Normal (RatFunc (AlgebraicClosure ℚ)) Limg := Normal.of_algEquiv eL'
  -- `Gal(Ombar/ℚ̄(T)) ↠ Gal(Limg/ℚ̄(T)) ≃ Gal(L/ℚ̄(T)) ≃ G`.
  let toG : (Ombar ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Ombar) →* G :=
    φG.toMonoidHom.comp
      ((AlgEquiv.autCongr eL').symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom Limg))
  have htoG_surj : Function.Surjective toG := by
    refine φG.surjective.comp ((AlgEquiv.autCongr eL').symm.surjective.comp ?_)
    exact AlgEquiv.restrictNormalHom_surjective
      (F := RatFunc (AlgebraicClosure ℚ)) (K₁ := Limg) (E := Ombar)
  ------------------------------------------------------------------------------------------------
  -- STAGE 4: the compositum `Kfr ⊔ Lfr = ⊤` (PROVEN) and the regularity intersection leaf.
  ------------------------------------------------------------------------------------------------
  -- `Kfr := eΩ(Ω)` and `Lfr := ℚ̄(T)` inside `Ombar`, as intermediate fields over `ℚ(T)`.
  set Kfr : IntermediateField (RatFunc ℚ) Ombar := eΩ.fieldRange with hKfrdef
  set Lfr : IntermediateField (RatFunc ℚ) Ombar :=
    (⊥ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars (RatFunc ℚ)
    with hLfrdef
  -- `M` and `P` have the *same* root set in `Ombar` (their `Ombar`-images coincide, `hMmapP`).
  have hrooteq : M.rootSet Ombar = P.rootSet Ombar := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hMmapP]
  -- The roots of `P` in `Ombar` all lie in `Kfr = eΩ(Ω)`: adjoining the roots of `M` over `ℚ(T)`
  -- gives exactly `eΩ.range` (`Ω` is the splitting field of `M`, `eΩ` a `ℚ(T)`-embedding).
  have hrange : Algebra.adjoin (RatFunc ℚ) (M.rootSet Ombar) = eΩ.range :=
    IsSplittingField.adjoin_rootSet_eq_range (K := RatFunc ℚ) (L := M.SplittingField)
      (F := Ombar) (f := M) (i := eΩ)
  have hrootsub : P.rootSet Ombar ⊆ (Kfr : Set Ombar) := by
    rw [← hrooteq]
    intro s hs
    have hmem : s ∈ Algebra.adjoin (RatFunc ℚ) (M.rootSet Ombar) := Algebra.subset_adjoin hs
    rw [hrange] at hmem
    exact AlgHom.mem_fieldRange.mpr ((AlgHom.mem_range eΩ).mp hmem)
  -- **Compositum.**  `Ombar = ℚ̄(T)(roots of P)`, and every root of `P` lies
  -- in `Kfr`, while `ℚ̄(T) = Lfr`; hence `Kfr ⊔ Lfr = ⊤`.  (This is the elementary half — it is the
  -- input to *injectivity* of `restrictRestrictAlgEquivMapHom`.)
  have hSup : Kfr ⊔ Lfr = ⊤ := by
    rw [eq_top_iff]
    intro x hxtop
    clear hxtop
    have hx : x ∈ Algebra.adjoin (RatFunc (AlgebraicClosure ℚ)) (P.rootSet Ombar) := by
      rw [IsSplittingField.adjoin_rootSet Ombar P]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem s hs => exact SetLike.coe_subset_coe.mpr le_sup_left (hrootsub hs)
    | algebraMap r =>
        have hmem : algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar r ∈ Lfr := by
          rw [hLfrdef, IntermediateField.mem_restrictScalars]
          exact IntermediateField.mem_bot.mpr ⟨r, rfl⟩
        exact SetLike.coe_subset_coe.mpr le_sup_right hmem
    | add x y hmx hmy hx hy => exact add_mem hx hy
    | mul x y hmx hmy hx hy => exact mul_mem hx hy
  -- **The regularity leaf — `regularity_inf`.**
  --
  -- Inside `Ombar`, the intersection of the `ℚ(T)`-model `Ω = eΩ(Ω) = Kfr` with the constant
  -- extension `ℚ̄(T) = Lfr` is exactly the image of the field of constants `k₀(T) = constFieldBase Ω`
  -- (`k₀ = algebraicClosure ℚ Ω`).  Equivalently: `Ω` and `ℚ̄(T)` are **linearly disjoint over
  -- `k₀(T)`** — `Ω/k₀(T)` is a *regular* extension.  This is the number-field generalization of
  -- `RET.GeometricIrreducibility.isField_baseChange_of_regular` (`ℚ` relatively algebraically closed
  -- in `ℚ(T)`, `RET.GeometricIrreducibility.regular_ratFunc`); it is delivered by
  -- `regularity_inf_of_embedding` (`Descent.RegularityInf`).
  --
  -- Base-changed to `k₀(T)`, this reads `Kfr ⊓ Lfr = ⊥`, which is the input to *surjectivity* of
  -- `restrictRestrictAlgEquivMapHom` — see `compare` below.
  have regularity_inf : Kfr ⊓ Lfr = (constFieldBase M.SplittingField).map eΩ :=
    regularity_inf_of_embedding eΩ
  ------------------------------------------------------------------------------------------------
  -- STAGE 5: assemble `f : Gal(Ω/k₀(T)) ↠ G` from the regularity comparison and `toG`.
  ------------------------------------------------------------------------------------------------
  -- **The regularity comparison isomorphism.**
  --
  -- `restrictRestrictAlgEquivMapHom (k₀(T)) Ω ℚ̄(T) Ombar : Gal(Ombar/ℚ̄(T)) →* Gal(Ω/k₀(T))` is a
  -- bijection: it is *injective* because `Kfr ⊔ Lfr = ⊤` (`hSup`, proven above), and *surjective*
  -- because, base-changed to `k₀(T)`, `Kfr ⊓ Lfr = ⊥` (from `regularity_inf`).
  -- All remaining content of `compare` is pure four-field-tower plumbing over the base `k₀(T)`.
  set B := constFieldBase M.SplittingField with hBdef
  -- `Ω → Ombar` as an algebra (via `eΩ`), and the tower `ℚ(T) → Ω → Ombar`.
  letI algΩOmbar : Algebra M.SplittingField Ombar := (eΩ.toRingHom).toAlgebra
  haveI towerQΩOmbar : IsScalarTower (RatFunc ℚ) M.SplittingField Ombar :=
    IsScalarTower.of_algebraMap_eq (fun r => (eΩ.commutes r).symm)
  -- `B = k₀(T) → Ombar` (via `B → Ω → Ombar`), the two scalar towers.
  letI algBOmbar : Algebra B Ombar :=
    ((algebraMap M.SplittingField Ombar).comp (algebraMap B M.SplittingField)).toAlgebra
  haveI towerBΩOmbar : IsScalarTower B M.SplittingField Ombar :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hBOmbar_eq : ∀ b : B, algebraMap B Ombar b = eΩ (algebraMap B M.SplittingField b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B M.SplittingField Ombar]
    rfl
  haveI towerQBOmbar : IsScalarTower (RatFunc ℚ) B Ombar :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [hBOmbar_eq (algebraMap (RatFunc ℚ) B r),
        ← IsScalarTower.algebraMap_apply (RatFunc ℚ) B M.SplittingField, eΩ.commutes])
  -- `Bfr = eΩ(B)`, the carrier of both `⊥ : IntermediateField B Ombar` and `Kfr ⊓ Lfr`.
  have hBfr_range : ((B.map eΩ : IntermediateField (RatFunc ℚ) Ombar) : Set Ombar)
      = Set.range (algebraMap B Ombar) := by
    rw [IntermediateField.coe_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, (hBOmbar_eq ⟨y, hy⟩).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨algebraMap B M.SplittingField b, SetLike.coe_mem b, (hBOmbar_eq b).symm⟩
  have hBmapLe : B.map eΩ ≤ Lfr := regularity_inf ▸ inf_le_right
  -- `K := eΩ(Ω)` and `L := ℚ̄(T)` inside `Ombar`, now as intermediate fields over the base `B`.
  let eΩB : M.SplittingField →ₐ[B] Ombar := IsScalarTower.toAlgHom B M.SplittingField Ombar
  let K : IntermediateField B Ombar := eΩB.fieldRange
  let L : IntermediateField B Ombar :=
    Lfr.toSubfield.toIntermediateField (fun b => by
      have hb : algebraMap B Ombar b ∈ B.map eΩ := by
        rw [← SetLike.mem_coe, hBfr_range]; exact ⟨b, rfl⟩
      exact (IntermediateField.mem_toSubfield _ _).mpr (hBmapLe hb))
  have hKcoe : (K : Set Ombar) = (Kfr : Set Ombar) := by
    show (eΩB.fieldRange : Set Ombar) = (Kfr : Set Ombar)
    rw [AlgHom.coe_fieldRange eΩB, hKfrdef, AlgHom.coe_fieldRange eΩ]
    rfl
  have hLcoe : (L : Set Ombar) = (Lfr : Set Ombar) := by
    rw [Subfield.coe_toIntermediateField, IntermediateField.coe_toSubfield]
  -- Base-changed compositum and intersection (carrier transports of `hSup` and `regularity_inf`).
  have hKrs : K.restrictScalars (RatFunc ℚ) = Kfr := by
    apply SetLike.coe_injective; rw [IntermediateField.coe_restrictScalars]; exact hKcoe
  have hLrs : L.restrictScalars (RatFunc ℚ) = Lfr := by
    apply SetLike.coe_injective; rw [IntermediateField.coe_restrictScalars]; exact hLcoe
  have mono : ∀ {X Y : IntermediateField B Ombar}, X ≤ Y →
      X.restrictScalars (RatFunc ℚ) ≤ Y.restrictScalars (RatFunc ℚ) := by
    intro X Y h x hx
    rw [IntermediateField.mem_restrictScalars] at hx ⊢; exact h hx
  have hSupB : K ⊔ L = ⊤ := by
    have hle : (⊤ : IntermediateField (RatFunc ℚ) Ombar) ≤ (K ⊔ L).restrictScalars (RatFunc ℚ) := by
      rw [← hSup]
      refine sup_le ?_ ?_
      · rw [← hKrs]; exact mono le_sup_left
      · rw [← hLrs]; exact mono le_sup_right
    have hKL : (K ⊔ L).restrictScalars (RatFunc ℚ) = ⊤ := top_le_iff.mp hle
    have htop : (⊤ : IntermediateField B Ombar).restrictScalars (RatFunc ℚ) = ⊤ := by
      apply SetLike.coe_injective
      rw [IntermediateField.coe_restrictScalars, IntermediateField.coe_top,
        IntermediateField.coe_top]
    exact IntermediateField.restrictScalars_injective (RatFunc ℚ) (hKL.trans htop.symm)
  have hInfB : K ⊓ L = ⊥ := by
    apply SetLike.coe_injective
    rw [IntermediateField.coe_inf, IntermediateField.coe_bot, hKcoe, hLcoe,
      ← IntermediateField.coe_inf, regularity_inf]
    exact hBfr_range
  -- `Ω ≃ₐ[B] K`, and the induced `Gal(Ω/B) ≃* Gal(K/B)`.
  let e : M.SplittingField ≃ₐ[B] K := AlgEquiv.ofInjectiveField eΩB
  haveI galBΩ : IsGalois B M.SplittingField := inferInstance
  haveI : Normal B M.SplittingField := galBΩ.to_normal
  haveI normalBK : Normal B K := Normal.of_algEquiv e
  haveI findimBΩ : FiniteDimensional B M.SplittingField := inferInstance
  haveI findimBK : FiniteDimensional B K := Module.Finite.equiv e.toLinearEquiv
  -- `↥L ≃+* ℚ̄(T)` (the corestriction of `algebraMap ℚ̄(T) Ombar`), for the base transport.
  have hmemL : ∀ r : RatFunc (AlgebraicClosure ℚ),
      algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar r ∈ L := by
    intro r
    rw [← SetLike.mem_coe, hLcoe, SetLike.mem_coe, hLfrdef, IntermediateField.mem_restrictScalars,
      IntermediateField.mem_bot]
    exact ⟨r, rfl⟩
  let φL : RatFunc (AlgebraicClosure ℚ) →+* L :=
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
  let fRE : RatFunc (AlgebraicClosure ℚ) ≃+* L := RingEquiv.ofBijective φL ⟨hφLinj, hφLsurj⟩
  have hval : ∀ r, (algebraMap L Ombar) (fRE r)
      = algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar r := fun r => rfl
  have hf_comp : (algebraMap L Ombar).comp (fRE : RatFunc (AlgebraicClosure ℚ) →+* L)
      = ((RingEquiv.refl Ombar : Ombar ≃+* Ombar) : Ombar →+* Ombar).comp
          (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar) := by
    ext r; simpa using hval r
  -- `Gal(Ombar/L)` is finite and Galois (transported from `Gal(Ombar/ℚ̄(T))`).
  haveI : Algebra.IsAlgebraic (RatFunc (AlgebraicClosure ℚ)) Ombar :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI galLOmbar : IsGalois L Ombar :=
    IsGalois.of_equiv_equiv (f := fRE) (g := RingEquiv.refl Ombar) hf_comp
  haveI findimLOmbar : FiniteDimensional L Ombar :=
    Module.Finite.of_equiv_equiv fRE (RingEquiv.refl Ombar) hf_comp
  -- The regularity bijection `Gal(Ombar/L) ≃* Gal(K/B)`.
  let bij : (Ombar ≃ₐ[L] Ombar) ≃* (K ≃ₐ[B] K) :=
    MulEquiv.ofBijective _
      (⟨IntermediateField.restrictRestrictAlgEquivMapHom_injective K L hSupB,
        IntermediateField.restrictRestrictAlgEquivMapHom_surjective K L hInfB⟩ :
        Function.Bijective (IntermediateField.restrictRestrictAlgEquivMapHom B K L Ombar))
  -- Base transport `Gal(Ombar/L) ≃* Gal(Ombar/ℚ̄(T))` (same underlying ring automorphisms).
  let t3 : (Ombar ≃ₐ[L] Ombar) ≃* (Ombar ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Ombar) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun r => by
        have hc := σ.commutes (fRE r)
        rw [hval r] at hc
        exact hc)
      invFun := fun τ => AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun l => by
        have key : (algebraMap L Ombar) l
            = algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar (fRE.symm l) := by
          rw [← hval (fRE.symm l), RingEquiv.apply_symm_apply]
        rw [key]
        exact τ.commutes (fRE.symm l))
      left_inv := fun σ => by ext x; rfl
      right_inv := fun τ => by ext x; rfl
      map_mul' := fun σ τ => by ext x; rfl }
  -- Assemble `compare : Gal(Ω/B) ≃* Gal(Ombar/ℚ̄(T))`.
  let compare :
      (M.SplittingField ≃ₐ[B] M.SplittingField) ≃*
        (Ombar ≃ₐ[RatFunc (AlgebraicClosure ℚ)] Ombar) :=
    (AlgEquiv.autCongr e).trans (bij.symm.trans t3)
  -- `compare σ` extends `σ`: unwinding `compare`, the automorphism `τ := bij.symm (e σ e⁻¹)` of
  -- `Ombar` restricts on `K = eΩ(Ω)` to `e σ e⁻¹`, and `t3` does not change the underlying map.
  have hcoe : ∀ y : M.SplittingField, ((e y : K) : Ombar)
      = algebraMap M.SplittingField Ombar y := fun _ => rfl
  have hcompare : ∀ (σ : M.SplittingField ≃ₐ[B] M.SplittingField) (x : M.SplittingField),
      compare σ (algebraMap M.SplittingField Ombar x)
        = algebraMap M.SplittingField Ombar (σ x) := by
    intro σ x
    have hbij : IntermediateField.restrictRestrictAlgEquivMapHom B K L Ombar
        (bij.symm (AlgEquiv.autCongr e σ)) = AlgEquiv.autCongr e σ :=
      bij.apply_symm_apply (AlgEquiv.autCongr e σ)
    have hres := IntermediateField.restrictRestrictAlgEquivMapHom_apply K L
      (bij.symm (AlgEquiv.autCongr e σ)) (e x)
    rw [hbij] at hres
    have hax : (AlgEquiv.autCongr e σ) (e x) = e (σ x) := by
      show e (σ (e.symm (e x))) = e (σ x)
      rw [e.symm_apply_apply]
    rw [hax] at hres
    rw [hcoe, hcoe] at hres
    exact hres.symm
  -- The two routes `ℚ(T) → ℚ̄(T) → Ombar` and `ℚ(T) → Ω → Ombar` agree: both are `eΩ` on `ℚ(T)`.
  have halgcomm : ∀ q : RatFunc ℚ,
      algebraMap (RatFunc (AlgebraicClosure ℚ)) Ombar
          (algebraMap (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) q)
        = algebraMap M.SplittingField Ombar (algebraMap (RatFunc ℚ) M.SplittingField q) := by
    intro q
    rw [← IsScalarTower.algebraMap_apply (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ombar]
    exact (eΩ.commutes q).symm
  ------------------------------------------------------------------------------------------------
  -- STAGE 6: the compositum as an extension of `ℚ(T)` — normality, and the primitive element of
  -- the sub-cover together with its conjugates.
  ------------------------------------------------------------------------------------------------
  -- `Ombar` is generated over `ℚ̄(T)` by the roots of `M`: they are the roots of `P`, which generate
  -- it as an algebra, hence a fortiori as a field.
  have hMtop : IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ)) (M.rootSet Ombar) = ⊤ := by
    rw [hrooteq]
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ Algebra.adjoin (RatFunc (AlgebraicClosure ℚ)) (P.rootSet Ombar) := by
      rw [IsSplittingField.adjoin_rootSet Ombar P]; exact Algebra.mem_top
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ hx
  -- Hence `Ombar/ℚ(T)` is normal, although it is infinite: the constants are algebraic over `ℚ`.
  haveI normalQOmbar : Normal (RatFunc ℚ) Ombar :=
    normal_of_adjoin_rootSet (Ω := Ombar) M hMsplit hMtop
  -- `eL θ` is a primitive element of the sub-cover, with the same `ℚ(T)`-minimal polynomial as `θ`.
  have hprim_minpoly : minpoly (RatFunc ℚ) (eL θ) = M := by
    rw [hMdef]
    exact minpoly.algHom_eq (eL.restrictScalars (RatFunc ℚ)) heLinj θ
  have hLimg_adjoin : Limg = IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ)) {eL θ} := by
    rw [hLimgdef, AlgHom.fieldRange_eq_map, ← hθ, IntermediateField.adjoin_map,
      Set.image_singleton]
  -- The compositum is generated over `ℚ̄(T)` by the model: the `ℚ(T)`-compositum `Kfr ⊔ Lfr = ⊤`
  -- read as a `ℚ̄(T)`-adjunction.
  have hmodel_top : IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ))
      (Set.range (algebraMap M.SplittingField Ombar)) = ⊤ := by
    set A := IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ))
      (Set.range (algebraMap M.SplittingField Ombar)) with hA
    have hKle : Kfr ≤ A.restrictScalars (RatFunc ℚ) := by
      intro x hx
      rw [hKfrdef, AlgHom.mem_fieldRange] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [IntermediateField.mem_restrictScalars]
      exact IntermediateField.subset_adjoin _ _ ⟨y, rfl⟩
    have hLle : Lfr ≤ A.restrictScalars (RatFunc ℚ) := by
      intro x hx
      rw [hLfrdef, IntermediateField.mem_restrictScalars, IntermediateField.mem_bot] at hx
      obtain ⟨r, rfl⟩ := hx
      rw [IntermediateField.mem_restrictScalars]
      exact A.algebraMap_mem r
    have hle : (⊤ : IntermediateField (RatFunc ℚ) Ombar) ≤ A.restrictScalars (RatFunc ℚ) := by
      rw [← hSup]; exact sup_le hKle hLle
    have htop : (⊤ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ombar).restrictScalars
        (RatFunc ℚ) = ⊤ := by
      apply SetLike.coe_injective
      rw [IntermediateField.coe_restrictScalars, IntermediateField.coe_top,
        IntermediateField.coe_top]
    exact IntermediateField.restrictScalars_injective (RatFunc ℚ)
      ((top_le_iff.mp hle).trans htop.symm)
  refine ⟨{
           Ω := M.SplittingField
           algΩ := aRΩ
           galΩ := galΩ
           charZeroΩ := charΩ
           towerΩ := towerΩ
           Ωbar := Ombar
           findimΩbar := findimOmbar
           galΩbar := galOmbar
           algebraMap_Q_eq := fun q => IsScalarTower.algebraMap_apply (RatFunc ℚ)
             (RatFunc (AlgebraicClosure ℚ)) Ombar q
           normalΩbar := normalQOmbar
           algΩΩbar := algΩOmbar
           algebraMap_comm := halgcomm
           Lsub := Limg
           normalLsub := normalLimg
           galLsub := (AlgEquiv.autCongr eL').symm.trans φG
           compare := compare
           compare_apply := hcompare
           adjoin_model_eq_top := hmodel_top
           prim := eL θ
           Lsub_eq_adjoin := hLimg_adjoin
           adjoin_rootSet_eq_top := by rw [hprim_minpoly]; exact hMtop }, eL', ?_⟩
  intro σ
  exact congrArg φG ((AlgEquiv.autCongr eL').symm_apply_apply σ)

/-- **The arithmetic descent core**, with the cover forgotten: from any geometric Galois cover with
deck group `G`, the compositum square exists. -/
theorem geomCompositum_exists {G : Type} [Group G] [Finite G]
    (cover : IsGeometricGaloisCover G) : Nonempty (GeomCompositum G) := by
  obtain ⟨L, _, _, _, _, ⟨φG⟩⟩ := cover
  obtain ⟨c, -⟩ := geomCompositum_exists_of_cover L φG
  exact ⟨c⟩

/-- **The arithmetic descent core**, in the form the tower packaging consumes: only the model `Ω`
and the surjection `Gal(Ω/k_Ω(T)) ↠ G`, the compositum forgotten. -/
theorem geomModel_descent {G : Type} [Group G] [Finite G] (cover : IsGeometricGaloisCover G) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (RatFunc ℚ) Ω)
      (_ : FiniteDimensional (RatFunc ℚ) Ω) (_ : IsGalois (RatFunc ℚ) Ω) (_ : CharZero Ω)
      (_ : IsScalarTower ℚ (RatFunc ℚ) Ω),
      ∃ f : (Ω ≃ₐ[constFieldBase Ω] Ω) →* G, Function.Surjective f := by
  obtain ⟨c⟩ := geomCompositum_exists cover
  exact ⟨c.Ω, c.fieldΩ, c.algΩ, c.findimΩ, c.galΩ, c.charZeroΩ, c.towerΩ,
    c.monodromy, c.surjective_monodromy⟩

end Rigidity.RET.Descent
