/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.InertiaTransport
import InverseGalois.Rigidity.RET.TamePi1

/-!
# Galois subcovers of a cover of the line, and restriction of branch cycles

A normal intermediate field `E` of a cover `M / ℚ̄(T)` of the line is again a cover of the line, and
restriction of automorphisms `Gal(M/ℚ̄(T)) ↠ Gal(E/ℚ̄(T))` is the map of deck groups underneath the
map of covers `M → E`.  Geometrically this is the statement that a cover factors through its
Galois subcovers; the fact recorded here is that **the branch cycles factor too**.

The mechanism is the one of `Rigidity.RET.InertiaTransport`.  A place `Q` of the big model
`ℚ̄[X] ⊆ integralClosure ℚ̄[X] M` contracts, along the inclusion of integral models
`integralClosure ℚ̄[X] E → integralClosure ℚ̄[X] M`, to a place of the small model lying over the
same point of the line; and the two Galois actions are intertwined along that inclusion by
`AlgEquiv.restrictNormalHom`, since restriction of an automorphism does not change its values on
the subfield.  Hence inertia at `Q` restricts to inertia at `Q ∩ E`, and a whole system of branch
cycles restricts to a system of branch cycles for the subcover.

## Main definitions

* `Rigidity.RET.subInclusion` — the inclusion of geometric integral models `B_E →+* B_M`.
* `Rigidity.RET.LineCover.sub` — a normal intermediate field, packaged as a cover of the line.
* `Rigidity.RET.LineCover.subHom` — the map of deck groups, restriction of automorphisms.

## Main results

* `Rigidity.RET.mem_inertia_of_subInclusion` — inertia contracts to inertia along the inclusion of
  integral models.
* `Rigidity.RET.LineCover.IsInertiaAt.restrict` — an inertia element at `t` restricts to an inertia
  element at `t` of the subcover.
* `Rigidity.RET.LineCover.IsBranchCycleSystem.restrict` — branch cycles restrict to branch cycles.
-/

open Polynomial

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral

section Generic

section Tower

variable (E M : Type) [Field E] [Field M]
  [Algebra (RatFunc k) E] [Algebra (Polynomial k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [Algebra (Polynomial k) M]
  [IsScalarTower (Polynomial k) (RatFunc k) M]
  [Algebra E M] [IsScalarTower (RatFunc k) E M]

/-- `ℚ̄[X] ⊆ E ⊆ M` is a scalar tower: both routes to `M` factor through `ℚ̄(T)`. -/
theorem isScalarTower_poly_sub : IsScalarTower (Polynomial k) E M := by
  refine IsScalarTower.of_algebraMap_eq fun p => ?_
  rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) M,
    IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) E,
    ← IsScalarTower.algebraMap_apply (RatFunc k) E M]

end Tower

variable {E M : Type} [Field E] [Field M]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [Algebra (Polynomial k) E] [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [Algebra (Polynomial k) M] [IsScalarTower (Polynomial k) (RatFunc k) M]
  [Algebra E M] [IsScalarTower (RatFunc k) E M] [IsScalarTower (Polynomial k) E M]

/-- **The inclusion of geometric integral models.**  An element of `E` integral over `ℚ̄[X]` stays
integral over `ℚ̄[X]` when pushed into `M`; this is the induced map
`integralClosure ℚ̄[X] E → integralClosure ℚ̄[X] M`. -/
def subInclusion : Bring E →+* Bring M where
  toFun x := ⟨algebraMap E M (x : E), x.2.map (IsScalarTower.toAlgHom (Polynomial k) E M)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

omit [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [IsScalarTower (Polynomial k) (RatFunc k) M] [IsScalarTower (RatFunc k) E M] in
@[simp] theorem coe_subInclusion (x : Bring E) :
    ((subInclusion x : Bring M) : M) = algebraMap E M (x : E) := rfl

omit [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [IsScalarTower (Polynomial k) (RatFunc k) M] [IsScalarTower (RatFunc k) E M] in
/-- The inclusion of integral models is a map of `ℚ̄[X]`-algebras. -/
theorem subInclusion_algebraMap (p : Polynomial k) :
    subInclusion (algebraMap (Polynomial k) (Bring E) p)
      = algebraMap (Polynomial k) (Bring M) p := by
  apply Subtype.ext
  rw [coe_subInclusion]
  rw [show ((algebraMap (Polynomial k) (Bring E) p : Bring E) : E) = algebraMap (Polynomial k) E p
    from (IsScalarTower.algebraMap_apply (Polynomial k) (Bring E) E p).symm]
  rw [show ((algebraMap (Polynomial k) (Bring M) p : Bring M) : M) = algebraMap (Polynomial k) M p
    from (IsScalarTower.algebraMap_apply (Polynomial k) (Bring M) M p).symm]
  rw [← IsScalarTower.algebraMap_apply (Polynomial k) E M]

omit [FiniteDimensional (RatFunc k) E] [FiniteDimensional (RatFunc k) M]
  [IsScalarTower (RatFunc k) E M] in
/-- The two Galois actions are intertwined along the inclusion of models by any homomorphism `ρ`
of deck groups which computes the values of an automorphism on the subfield — for the restriction
homomorphism this is the statement that restricting `σ` does not change its values on `E`. -/
theorem subInclusion_smul (ρ : (M ≃ₐ[RatFunc k] M) →* (E ≃ₐ[RatFunc k] E))
    (hres : ∀ (σ : M ≃ₐ[RatFunc k] M) (y : E), algebraMap E M (ρ σ y) = σ (algebraMap E M y))
    (σ : M ≃ₐ[RatFunc k] M) (x : Bring E) :
    subInclusion (E := E) (M := M) (ρ σ • x) = σ • subInclusion x := by
  apply Subtype.ext
  rw [coe_subInclusion, coe_smul_geom, coe_smul_geom, coe_subInclusion, hres]

omit [FiniteDimensional (RatFunc k) E] [FiniteDimensional (RatFunc k) M]
  [IsScalarTower (RatFunc k) E M] in
/-- **Inertia contracts to inertia along the inclusion of integral models.** -/
theorem mem_inertia_of_subInclusion (ρ : (M ≃ₐ[RatFunc k] M) →* (E ≃ₐ[RatFunc k] E))
    (hres : ∀ (σ : M ≃ₐ[RatFunc k] M) (y : E), algebraMap E M (ρ σ y) = σ (algebraMap E M y))
    (Q : Ideal (Bring M)) {σ : M ≃ₐ[RatFunc k] M} (hσ : σ ∈ geomInertia M Q) :
    ρ σ ∈ (Q.comap (subInclusion (E := E))).inertia (E ≃ₐ[RatFunc k] E) :=
  Rigidity.RET.mem_inertia_comap subInclusion ρ (subInclusion_smul ρ hres) Q hσ

omit [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [IsScalarTower (Polynomial k) (RatFunc k) M] [IsScalarTower (RatFunc k) E M] in
/-- The contracted place lies over the same point of the line. -/
theorem liesOver_comap_subInclusion (t : k) (Q : Ideal (Bring M)) [Q.LiesOver (placeP t)] :
    (Q.comap (subInclusion (E := E))).LiesOver (placeP t) := by
  constructor
  have hover : placeP t = Q.comap (algebraMap (Polynomial k) (Bring M)) := Ideal.LiesOver.over
  have hcomp : (Q.comap (subInclusion (E := E))).comap
      (algebraMap (Polynomial k) (Bring E))
      = Q.comap (algebraMap (Polynomial k) (Bring M)) := by
    rw [Ideal.comap_comap]
    congr 1
    exact RingHom.ext fun p => subInclusion_algebraMap p
  rw [Ideal.under_def, hcomp, ← hover]

omit [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [IsScalarTower (Polynomial k) (RatFunc k) M] [IsScalarTower (RatFunc k) E M] in
/-- The contracted place is maximal: it is prime and lies over the maximal place `X - t`, and the
small model is integral over `ℚ̄[X]`. -/
theorem isMaximal_comap_subInclusion (t : k) (Q : Ideal (Bring M)) [hQ : Q.IsPrime]
    [Q.LiesOver (placeP t)] : (Q.comap (subInclusion (E := E))).IsMaximal := by
  haveI : (Q.comap (subInclusion (E := E))).IsPrime := hQ.comap _
  haveI := liesOver_comap_subInclusion (E := E) t Q
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Polynomial k) _ ?_
  rw [show (Q.comap (subInclusion (E := E))).comap (algebraMap (Polynomial k) (Bring E))
      = placeP t from (Ideal.over_def _ (placeP t)).symm]
  exact placeP_max t

end Generic

namespace LineCover

variable (L : LineCover)

/-- A normal intermediate field of a Galois extension is Galois over the base: separability passes
to the bottom of a tower. -/
theorem sub_isGalois (E : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) E] :
    IsGalois (RatFunc k) E :=
  haveI : Algebra.IsSeparable (RatFunc k) E :=
    Algebra.isSeparable_tower_bot_of_isSeparable (RatFunc k) E L.M
  ⟨⟩

attribute [local instance] sub_isGalois

/-- **A normal intermediate field of a cover is again a cover of the line.**  Its integral model is
the one induced from the ambient cover. -/
def sub (E : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) E] : LineCover :=
  { M := (E : Type) }

@[simp] theorem sub_M (E : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) E] :
    (L.sub E).M = (E : Type) := rfl

/-- The map of deck groups underneath a Galois subcover: restriction of automorphisms. -/
def subHom (E : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) E] :
    L.deck →* (L.sub E).deck :=
  AlgEquiv.restrictNormalHom E

/-- Restriction computes the values of an automorphism on the subfield. -/
theorem subHom_commutes (E : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) E]
    (σ : L.deck) (y : E) :
    algebraMap (E : Type) L.M (L.subHom E σ y) = σ (algebraMap (E : Type) L.M y) :=
  AlgEquiv.restrictNormalHom_apply E σ y

theorem subHom_surjective (E : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) E] :
    Function.Surjective (L.subHom E) :=
  AlgEquiv.restrictNormalHom_surjective (F := RatFunc k) (K₁ := E) (E := L.M)

/-- **An inertia element restricts to an inertia element at the same point.** -/
theorem IsInertiaAt.restrict {E : IntermediateField (RatFunc k) L.M} [Normal (RatFunc k) E]
    {t : k} {σ : L.deck} (h : L.IsInertiaAt t σ) :
    (L.sub E).IsInertiaAt t (L.subHom E σ) := by
  haveI := isScalarTower_poly_sub (E : Type) L.M
  obtain ⟨Q, hQmax, hQover, hQin⟩ := h
  haveI := hQmax
  haveI : Q.IsPrime := hQmax.isPrime
  haveI := hQover
  refine ⟨(Q.comap (subInclusion (E := (E : Type)) (M := L.M)) : Ideal (Bring (E : Type))),
    ?_, ?_, ?_⟩
  · exact isMaximal_comap_subInclusion t Q
  · exact liesOver_comap_subInclusion t Q
  · exact mem_inertia_of_subInclusion (E := (E : Type)) (M := L.M)
      (L.subHom E) (L.subHom_commutes E) Q hQin

/-- **Branch cycles restrict to branch cycles.**  Each restricted cycle is inertia at the same
point; the restrictions generate because restriction is surjective; and the product-one relation is
preserved by a group homomorphism. -/
theorem IsBranchCycleSystem.restrict {E : IntermediateField (RatFunc k) L.M}
    [Normal (RatFunc k) E] {r : ℕ} {t : Fin r → k} {g : Fin r → L.deck}
    (h : L.IsBranchCycleSystem t g) :
    (L.sub E).IsBranchCycleSystem t (fun i => L.subHom E (g i)) where
  inertia i := IsInertiaAt.restrict L (h.inertia i)
  top := by
    have hrange : (Set.range fun i => L.subHom E (g i)) = (L.subHom E) '' Set.range g :=
      Set.range_comp _ _
    rw [hrange,
      show Subgroup.closure ((L.subHom E) '' (Set.range g))
          = ((Subgroup.closure (Set.range g)).map (L.subHom E)) from
        (MonoidHom.map_closure _ _).symm,
      h.top, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact L.subHom_surjective E
  prod := by
    rw [show List.ofFn (fun i => L.subHom E (g i)) = (List.ofFn g).map (L.subHom E) by
      rw [List.map_ofFn]; rfl]
    rw [← map_list_prod, h.prod, map_one]

/-! ## Transport along an isomorphism of covers -/

section Transport

variable {L L' : LineCover} (e : L.M ≃ₐ[RatFunc k] L'.M)

/-- **Inertia transports along an isomorphism of covers.**  Conjugating a deck transformation by an
isomorphism `e : M ≅ M'` of covers of the line carries inertia at `t` to inertia at `t`: the
isomorphism carries the integral model to the integral model and the places over `t` to the places
over `t`. -/
theorem IsInertiaAt.transport {t : k} {σ : L.deck} (h : L.IsInertiaAt t σ) :
    L'.IsInertiaAt t (AlgEquiv.autCongr e σ) := by
  letI : Algebra L'.M L.M :=
    (e.symm : L'.M ≃ₐ[RatFunc k] L.M).toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc k) L'.M L.M :=
    IsScalarTower.of_algebraMap_eq fun x => (e.symm.commutes x).symm
  haveI := isScalarTower_poly_sub L'.M L.M
  obtain ⟨Q, hQmax, hQover, hQin⟩ := h
  haveI := hQmax
  haveI : Q.IsPrime := hQmax.isPrime
  haveI := hQover
  have hres : ∀ (τ : L.M ≃ₐ[RatFunc k] L.M) (y : L'.M),
      algebraMap L'.M L.M (AlgEquiv.autCongr e τ y) = τ (algebraMap L'.M L.M y) := by
    intro τ y
    show e.symm (e (τ (e.symm y))) = τ (e.symm y)
    rw [e.symm_apply_apply]
  refine ⟨(Q.comap (subInclusion (E := L'.M) (M := L.M)) : Ideal (Bring L'.M)), ?_, ?_, ?_⟩
  · exact isMaximal_comap_subInclusion t Q
  · exact liesOver_comap_subInclusion t Q
  · exact mem_inertia_of_subInclusion (E := L'.M) (M := L.M)
      (AlgEquiv.autCongr e).toMonoidHom hres Q hQin

/-- **Branch cycles transport along an isomorphism of covers.** -/
theorem IsBranchCycleSystem.transport {r : ℕ} {t : Fin r → k} {g : Fin r → L.deck}
    (h : L.IsBranchCycleSystem t g) :
    L'.IsBranchCycleSystem t (fun i => AlgEquiv.autCongr e (g i)) where
  inertia i := IsInertiaAt.transport e (h.inertia i)
  top := by
    have hrange : (Set.range fun i => AlgEquiv.autCongr e (g i))
        = (AlgEquiv.autCongr e : L.deck →* L'.deck) '' Set.range g := Set.range_comp _ _
    rw [hrange,
      show Subgroup.closure ((AlgEquiv.autCongr e : L.deck →* L'.deck) '' (Set.range g))
          = ((Subgroup.closure (Set.range g)).map (AlgEquiv.autCongr e : L.deck →* L'.deck)) from
        (MonoidHom.map_closure _ _).symm,
      h.top, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact (AlgEquiv.autCongr e).surjective
  prod := by
    rw [show List.ofFn (fun i => AlgEquiv.autCongr e (g i))
        = (List.ofFn g).map (AlgEquiv.autCongr e : L.deck →* L'.deck) by
      rw [List.map_ofFn]; rfl]
    rw [← map_list_prod, h.prod, map_one]

end Transport

end LineCover

end Rigidity.RET
