/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.InertiaGen
import InverseGalois.Rigidity.RET.SubCover

/-!
# Inertia restricts *onto* the inertia of a Galois subcover

Inertia at a place of a cover contracts to inertia at the place below
(`Rigidity.RET.mem_inertia_of_subInclusion`); what makes the branch cycles of a big cover determine
the branch cycles of a subcover is the converse: the restriction map of deck groups carries the
inertia group at a place *onto* the inertia group at the place below.

The proof is the classical one for the surjectivity of a decomposition group onto the decomposition
group of a subextension, and it uses the geometric situation twice.  Given an element `τ` of the
inertia group of the contracted place `Q ∩ E`, lift it to any `σ₀` of the big deck group.  Over an
algebraically closed constant field the inertia group is the whole decomposition group
(`Rigidity.RET.geomInertia_eq_stabilizer`), so `τ` fixes `Q ∩ E`, and therefore `σ₀ • Q` contracts to
`Q ∩ E` just as `Q` does.  The subgroup `Gal(M/E)` acts transitively on the places of the big model
above a place of the small one (`Rigidity.RET.exists_relative_smul_eq`, Mathlib's transitivity for an
invariant extension applied to `B_E ⊆ B_M`), so some `ρ` in it carries `σ₀ • Q` back to `Q`; then
`ρ σ₀` fixes `Q`, hence lies in the inertia group at `Q`, and restricts to `τ`.

## Main results

* `Rigidity.RET.exists_relative_smul_eq` — `Gal(M/E)` is transitive on the places of the big
  integral model above a place of the small one.
* `Rigidity.RET.geomInertia_comap_eq_map` — inertia at the contracted place is the image of inertia.
* `Rigidity.RET.LineCover.IsInertiaGenAt.restrict` — a distinguished inertia element restricts to a
  distinguished inertia element of the subcover.
* `Rigidity.RET.LineCover.IsBranchCycleGenSystem.restrict` — distinguished branch cycles restrict.
-/

open Polynomial
open scoped Pointwise

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

section Relative

variable {E M : Type} [Field E] [Field M]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [Algebra (Polynomial k) E] [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [Algebra (Polynomial k) M] [IsScalarTower (Polynomial k) (RatFunc k) M]
  [Algebra E M] [IsScalarTower (RatFunc k) E M] [IsScalarTower (Polynomial k) E M]

/-- Restriction of scalars from `E` to `ℚ̄(T)`, as a homomorphism of automorphism groups. -/
def subRestrictScalars : (M ≃ₐ[E] M) →* (M ≃ₐ[RatFunc k] M) where
  toFun σ := σ.restrictScalars (RatFunc k)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

omit [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E] [Algebra (Polynomial k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E] [FiniteDimensional (RatFunc k) M]
  [IsGalois (RatFunc k) M] [Algebra (Polynomial k) M] [IsScalarTower (Polynomial k) (RatFunc k) M]
  [IsScalarTower (Polynomial k) E M] in
@[simp] theorem subRestrictScalars_apply (σ : M ≃ₐ[E] M) (x : M) :
    (subRestrictScalars (E := E) σ) x = σ x := rfl

/-- The small integral model as a subring of the big one. -/
local instance algBringSub : Algebra (Bring E) (Bring M) :=
  (subInclusion (E := E) (M := M)).toAlgebra

omit [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E] [Algebra (RatFunc k) M]
  [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [IsScalarTower (Polynomial k) (RatFunc k) M] [IsScalarTower (RatFunc k) E M] in
theorem algebraMap_bringSub :
    algebraMap (Bring E) (Bring M) = subInclusion (E := E) (M := M) :=
  RingHom.algebraMap_toAlgebra _

/-- The action of `Gal(M/E)` on the big integral model, through the deck group of the line. -/
local instance mulSemiringActionSub : MulSemiringAction (M ≃ₐ[E] M) (Bring M) :=
  MulSemiringAction.compHom _ (subRestrictScalars (E := E))

omit [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E] [Algebra (Polynomial k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E] [FiniteDimensional (RatFunc k) M]
  [IsScalarTower (Polynomial k) E M] in
theorem smul_bring_sub (σ : M ≃ₐ[E] M) (x : Bring M) :
    σ • x = (subRestrictScalars (E := E) σ) • x := rfl

omit [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E] [FiniteDimensional (RatFunc k) M] in
/-- An automorphism fixing `E` fixes the small integral model. -/
theorem smul_subInclusion (σ : M ≃ₐ[E] M) (x : Bring E) :
    σ • subInclusion (E := E) (M := M) x = subInclusion x := by
  apply Subtype.ext
  rw [smul_bring_sub, coe_smul_geom, coe_subInclusion]
  exact σ.commutes x

set_option synthInstance.maxHeartbeats 200000 in
local instance smulCommClassSub : SMulCommClass (M ≃ₐ[E] M) (Bring E) (Bring M) where
  smul_comm σ a b := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', algebraMap_bringSub, smul_subInclusion]

local instance isInvariantSub : Algebra.IsInvariant (Bring E) (Bring M) (M ≃ₐ[E] M) where
  isInvariant x hx := by
    haveI : IsGalois E M := IsGalois.tower_top_of_isGalois (RatFunc k) E M
    haveI : FiniteDimensional E M := FiniteDimensional.right (RatFunc k) E M
    have hfix : ∀ σ : M ≃ₐ[E] M, σ (x : M) = x := by
      intro σ
      have h1 : (subRestrictScalars (E := E) σ) • x = x := hx σ
      have h2 : ((subRestrictScalars (E := E) σ • x : Bring M) : M) = (x : M) := by rw [h1]
      rwa [coe_smul_geom] at h2
    obtain ⟨y, hy⟩ := (IntermediateField.mem_bot (F := E) (E := M)).mp
      ((IsGalois.mem_bot_iff_fixed (x : M)).mpr hfix)
    have hyint : IsIntegral (Polynomial k) y := by
      have hx' : IsIntegral (Polynomial k) (algebraMap E M y) := by
        rw [hy]; exact x.2
      exact hx'.tower_bot (FaithfulSMul.algebraMap_injective E M)
    exact ⟨⟨y, hyint⟩,
      Subtype.ext (by rw [algebraMap_bringSub, coe_subInclusion]; exact hy)⟩

omit [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E] in
set_option synthInstance.maxHeartbeats 200000 in
/-- **`Gal(M/E)` is transitive on the places of the big integral model above a place of the small
one.** -/
theorem exists_relative_smul_eq (Q Q' : Ideal (Bring M)) [Q.IsPrime] [Q'.IsPrime]
    (h : Q.comap (subInclusion (E := E)) = Q'.comap (subInclusion (E := E))) :
    ∃ σ : M ≃ₐ[E] M, Q' = (subRestrictScalars (E := E) σ) • Q := by
  haveI : FiniteDimensional E M := FiniteDimensional.right (RatFunc k) E M
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (Bring E) (Bring M)
    (M ≃ₐ[E] M) Q Q' (by rw [Ideal.under_def, Ideal.under_def, algebraMap_bringSub, h])
  exact ⟨σ, hσ⟩

end Relative

section Restriction

variable {E M : Type} [Field E] [Field M]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E]
  [Algebra (Polynomial k) E] [IsScalarTower (Polynomial k) (RatFunc k) E]
  [Algebra (RatFunc k) M] [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  [Algebra (Polynomial k) M] [IsScalarTower (Polynomial k) (RatFunc k) M]
  [Algebra E M] [IsScalarTower (RatFunc k) E M] [IsScalarTower (Polynomial k) E M]
  (ρ : (M ≃ₐ[RatFunc k] M) →* (E ≃ₐ[RatFunc k] E))
  (hres : ∀ (σ : M ≃ₐ[RatFunc k] M) (y : E), algebraMap E M (ρ σ y) = σ (algebraMap E M y))

include hres

omit [FiniteDimensional (RatFunc k) E] [IsGalois (RatFunc k) E] [Algebra (Polynomial k) E]
  [IsScalarTower (Polynomial k) (RatFunc k) E] [FiniteDimensional (RatFunc k) M]
  [IsGalois (RatFunc k) M] [Algebra (Polynomial k) M] [IsScalarTower (Polynomial k) (RatFunc k) M]
  [IsScalarTower (Polynomial k) E M] in
/-- An automorphism fixing `E` restricts to the identity of `E`. -/
theorem restrict_eq_one (σ : M ≃ₐ[E] M) : ρ (subRestrictScalars (E := E) σ) = 1 := by
  ext y
  apply FaithfulSMul.algebraMap_injective E M
  rw [hres]
  exact σ.commutes y

omit [FiniteDimensional (RatFunc k) E] [FiniteDimensional (RatFunc k) M]
  [IsScalarTower (RatFunc k) E M] in
/-- Contraction of places is equivariant for the restriction of automorphisms. -/
theorem comap_subInclusion_smul (σ : M ≃ₐ[RatFunc k] M) (Q : Ideal (Bring M)) :
    (σ • Q).comap (subInclusion (E := E)) = (ρ σ) • Q.comap (subInclusion (E := E)) := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap,
    show subInclusion (E := E) ((ρ σ)⁻¹ • x) = σ⁻¹ • subInclusion x from
      subInclusion_smul ρ hres σ⁻¹ x ▸ by rw [map_inv]]

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Inertia at the contracted place is the image of the inertia group.**

The inclusion of the image is `mem_inertia_of_subInclusion`; the reverse inclusion is the classical
lifting argument, available because over an algebraically closed constant field inertia is the whole
decomposition group and `Gal(M/E)` is transitive on the places above a place of the small model. -/
theorem geomInertia_comap_eq_map (t : k) (Q : Ideal (Bring M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] (hρ : Function.Surjective ρ) :
    geomInertia E (Q.comap (subInclusion (E := E))) = (geomInertia M Q).map ρ := by
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  haveI hmax : (Q.comap (subInclusion (E := E))).IsMaximal := isMaximal_comap_subInclusion t Q
  haveI hover : (Q.comap (subInclusion (E := E))).LiesOver (placeP t) :=
    liesOver_comap_subInclusion t Q
  refine le_antisymm (fun τ hτ => ?_) ?_
  · -- lift `τ` to the big deck group and correct it by an element of `Gal(M/E)`
    obtain ⟨σ₀, rfl⟩ := hρ τ
    have hstab : (ρ σ₀) • Q.comap (subInclusion (E := E)) = Q.comap (subInclusion (E := E)) := by
      have : ρ σ₀ ∈ MulAction.stabilizer (E ≃ₐ[RatFunc k] E)
          (Q.comap (subInclusion (E := E))) := by
        rw [← geomInertia_eq_stabilizer t]
        exact hτ
      exact this
    haveI : (σ₀ • Q).IsPrime := Ideal.IsPrime.smul _
    obtain ⟨σ', hσ'⟩ := exists_relative_smul_eq (E := E) (σ₀ • Q) Q
      (by rw [comap_subInclusion_smul ρ hres, hstab])
    refine ⟨subRestrictScalars (E := E) σ' * σ₀, ?_, ?_⟩
    · rw [geomInertia_eq_stabilizer t Q]
      show (subRestrictScalars (E := E) σ' * σ₀) • Q = Q
      rw [mul_smul, ← hσ']
    · rw [map_mul, restrict_eq_one ρ hres, one_mul]
  · rintro τ ⟨σ, hσ, rfl⟩
    exact mem_inertia_of_subInclusion ρ hres Q hσ

/-- A generator of the inertia group at `Q` restricts to a generator of the inertia group at the
contracted place. -/
theorem geomInertia_comap_eq_zpowers (t : k) (Q : Ideal (Bring M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] (hρ : Function.Surjective ρ) {σ : M ≃ₐ[RatFunc k] M}
    (h : geomInertia M Q = Subgroup.zpowers σ) :
    geomInertia E (Q.comap (subInclusion (E := E))) = Subgroup.zpowers (ρ σ) := by
  rw [geomInertia_comap_eq_map ρ hres t Q hρ, h, MonoidHom.map_zpowers]

end Restriction

namespace LineCover

variable (L : LineCover)

attribute [local instance] sub_isGalois

/-- **A distinguished inertia element restricts to a distinguished inertia element.** -/
theorem IsInertiaGenAt.restrict {E : IntermediateField (RatFunc k) L.M} [Normal (RatFunc k) E]
    {t : k} {σ : L.deck} (h : L.IsInertiaGenAt t σ) :
    (L.sub E).IsInertiaGenAt t (L.subHom E σ) := by
  haveI := isScalarTower_poly_sub (E : Type) L.M
  obtain ⟨Q, hQmax, hQover, hQin⟩ := h
  haveI := hQmax
  haveI : Q.IsPrime := hQmax.isPrime
  haveI := hQover
  refine ⟨(Q.comap (subInclusion (E := (E : Type)) (M := L.M)) : Ideal (Bring (E : Type))),
    isMaximal_comap_subInclusion t Q, liesOver_comap_subInclusion t Q, ?_⟩
  exact geomInertia_comap_eq_zpowers (E := (E : Type)) (M := L.M) (L.subHom E)
    (L.subHom_commutes E) t Q (L.subHom_surjective E) hQin

/-- **Distinguished branch cycles restrict to distinguished branch cycles.** -/
theorem IsBranchCycleGenSystem.restrict {E : IntermediateField (RatFunc k) L.M}
    [Normal (RatFunc k) E] {r : ℕ} {t : Fin r → k} {g : Fin r → L.deck}
    (h : L.IsBranchCycleGenSystem t g) :
    (L.sub E).IsBranchCycleGenSystem t (fun i => L.subHom E (g i)) where
  inertia i := IsInertiaGenAt.restrict L (h.inertia i)
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

end LineCover

/-! ## Transport of distinguished inertia along an isomorphism of covers -/

namespace LineCover

/-- **A distinguished inertia element transports along an isomorphism of covers.**  Conjugating by
an isomorphism `e : M ≅ M'` of covers of the line carries a generator of the inertia group at a
place over `t` to a generator of the inertia group at the corresponding place of the other cover. -/
theorem IsInertiaGenAt.transport {L L' : LineCover} (e : L.M ≃ₐ[RatFunc k] L'.M) {t : k}
    {σ : L.deck} (h : L.IsInertiaGenAt t σ) :
    L'.IsInertiaGenAt t (AlgEquiv.autCongr e σ) := by
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
  refine ⟨(Q.comap (subInclusion (E := L'.M) (M := L.M)) : Ideal (Bring L'.M)),
    isMaximal_comap_subInclusion t Q, liesOver_comap_subInclusion t Q, ?_⟩
  exact geomInertia_comap_eq_zpowers (E := L'.M) (M := L.M)
    (AlgEquiv.autCongr e).toMonoidHom hres t Q (AlgEquiv.autCongr e).surjective hQin

/-- **Distinguished branch cycles transport along an isomorphism of covers.** -/
theorem IsBranchCycleGenSystem.transport {L L' : LineCover} (e : L.M ≃ₐ[RatFunc k] L'.M) {r : ℕ}
    {t : Fin r → k} {g : Fin r → L.deck} (h : L.IsBranchCycleGenSystem t g) :
    L'.IsBranchCycleGenSystem t (fun i => AlgEquiv.autCongr e (g i)) where
  inertia i := IsInertiaGenAt.transport e (h.inertia i)
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

end LineCover

end Rigidity.RET
