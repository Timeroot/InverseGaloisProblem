/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.HasseLevel

/-!
# A locally trivial class comes from the field trivialising its coefficients

Let a Galois extension of a number field be given, together with coefficients on which the Galois
group acts through a finite Galois level.  That level trivialises the coefficients, so a one cocycle
restricted to the automorphisms over it is a homomorphism into the coefficients, and the extension
it cuts out is abelian over the level.

If the class is locally trivial then that homomorphism kills every decomposition group, and an
abelian extension in which every place splits completely is trivial.  So the cocycle vanishes on the
subgroup fixing the level, which is exactly the condition for the class to be inflated from the
Galois group of the level: the everywhere locally trivial classes of the first cohomology of the big
group all come from the finite group.

Restriction of scalars is the passage between the two pictures.  An automorphism of the big field
over the level is an automorphism over the base fixing the level pointwise, and every automorphism
fixing the level pointwise arises this way, so the subgroup fixing the level is the Galois group of
the big field over the level.

## Main definitions

* `InverseGalois.CFT.restrictScalarsOverHom`: the automorphisms of the top field over an
  intermediate field, as automorphisms over the base.
* `InverseGalois.CFT.cocycleHomOver`: **a one cocycle over the field trivialising the coefficients,
  as a homomorphism.**

## Main results

* `InverseGalois.CFT.exists_restrictScalars_eq`: an automorphism fixing an intermediate field
  pointwise is an automorphism over that field.
* `InverseGalois.CFT.eq_one_of_levelDecomposition_over`: **a cocycle whose restriction over the
  field trivialising the coefficients kills a level and every automorphism local at a place of that
  level vanishes there.**
* `InverseGalois.CFT.exists_galInflH1_eq_of_levelDecomposition`,
  `InverseGalois.CFT.exists_galInflH1_eq_of_levelDecompositionOutside`: **an everywhere locally
  trivial class is inflated from the field trivialising its coefficients.**
* `InverseGalois.CFT.exists_galInflH1_eq_of_forall_level`,
  `InverseGalois.CFT.exists_galInflH1_eq_of_forall_level_outside`: the same with the level supplied
  by smoothness rather than by hand.

## Tags

number field, Galois cohomology, inflation, decomposition group, local-global principle
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField groupCohomology

/-! ### Automorphisms over an intermediate field -/

section Restrict

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (F : IntermediateField k K)

/-- An automorphism of the top field over an intermediate field fixes that field pointwise. -/
theorem restrictScalars_mem_fixingSubgroup (ρ : K ≃ₐ[↥F] K) :
    ρ.restrictScalars k ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  simpa using ρ.commutes ⟨x, hx⟩

/-- The automorphisms of the top field over an intermediate field, as automorphisms over the
base. -/
def restrictScalarsOverHom : (K ≃ₐ[↥F] K) →* Gal(K/k) where
  toFun ρ := ρ.restrictScalars k
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp]
theorem restrictScalarsOverHom_apply (ρ : K ≃ₐ[↥F] K) :
    restrictScalarsOverHom F ρ = ρ.restrictScalars k := rfl

variable {F} in
/-- **An automorphism fixing an intermediate field pointwise is an automorphism over that
field.** -/
theorem exists_restrictScalars_eq {σ : Gal(K/k)} (hσ : σ ∈ F.fixingSubgroup) :
    ∃ ρ : K ≃ₐ[↥F] K, ρ.restrictScalars k = σ :=
  ⟨IntermediateField.fixingSubgroupEquiv F ⟨σ, hσ⟩, AlgEquiv.ext fun _ => rfl⟩

end Restrict

/-! ### A cocycle over the field trivialising the coefficients -/

section Over

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {M : Type*} [CommGroup M]
  [MulDistribMulAction Gal(K/k) M] (F : IntermediateField k K)
  (htriv : ∀ σ ∈ F.fixingSubgroup, ∀ m : M, σ • m = m)
  {u : Gal(K/k) → M} (hu : IsMulCocycle₁ u)

include htriv hu

/-- **A one cocycle over the field trivialising the coefficients, as a homomorphism.** -/
def cocycleHomOver : (K ≃ₐ[↥F] K) →* M where
  toFun ρ := u (ρ.restrictScalars k)
  map_one' := by
    rw [show ((1 : K ≃ₐ[↥F] K).restrictScalars k) = 1 from AlgEquiv.ext fun _ => rfl]
    exact map_one_of_isMulCocycle₁ hu
  map_mul' ρ τ := by
    rw [show ((ρ * τ).restrictScalars k) = ρ.restrictScalars k * τ.restrictScalars k from
      AlgEquiv.ext fun _ => rfl, hu,
      htriv _ (restrictScalars_mem_fixingSubgroup F ρ), mul_comm]

@[simp]
theorem cocycleHomOver_apply (ρ : K ≃ₐ[↥F] K) :
    cocycleHomOver F htriv hu ρ = u (ρ.restrictScalars k) := rfl

end Over

/-! ### A level over an intermediate field -/

section Level

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (F : IntermediateField k K)

/-- The automorphisms over an intermediate field fixing a finite subextension of it pointwise, and
so a finite subextension of the base, form an open subgroup. -/
theorem exists_isOpen_le_comap_fixingSubgroup (E : IntermediateField k K)
    [FiniteDimensional k E] :
    ∃ H : Subgroup (K ≃ₐ[↥F] K), IsOpen (H : Set (K ≃ₐ[↥F] K)) ∧
      ∀ ρ ∈ H, ρ.restrictScalars k ∈ E.fixingSubgroup := by
  obtain ⟨t, ht⟩ : E.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  haveI : FiniteDimensional ↥F (IntermediateField.adjoin ↥F (t : Set K)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨(IntermediateField.adjoin ↥F (t : Set K)).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen _, fun ρ hρ => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hρ
  have key : ∀ x ∈ (t : Set K), (ρ.restrictScalars k) • x = x := fun x hx =>
    hρ x (IntermediateField.subset_adjoin _ _ hx)
  have hfix := (IntermediateField.forall_mem_adjoin_smul_eq_self_iff k (S := (t : Set K))
    (ρ.restrictScalars k)).mpr key
  rw [← ht, IntermediateField.mem_fixingSubgroup_iff]
  exact fun x hx => hfix x hx

/-- **Inside every open normal subgroup of the Galois group of the base there is a finite Galois
level over an intermediate field.** -/
theorem exists_level_le {N : Subgroup Gal(K/k)} (hN : IsOpenNormal N) :
    ∃ L : IntermediateField ↥F K, FiniteDimensional ↥F L ∧ IsGalois ↥F L ∧
      ∀ ρ ∈ L.fixingSubgroup, (ρ : K ≃ₐ[↥F] K).restrictScalars k ∈ N := by
  obtain ⟨E, hfin, _, hle⟩ := exists_fixingSubgroup_le hN
  haveI := hfin
  obtain ⟨H, hHopen, hH⟩ := exists_isOpen_le_comap_fixingSubgroup F E
  have hopen : IsOpen ((N.comap (restrictScalarsOverHom F)) : Set (K ≃ₐ[↥F] K)) :=
    Subgroup.isOpen_mono (H₁ := H) (fun ρ hρ => Subgroup.mem_comap.mpr (hle (hH ρ hρ))) hHopen
  obtain ⟨L, hLfin, hLgal, hLle⟩ :=
    exists_fixingSubgroup_le (⟨hN.normal.comap _, hopen⟩ : IsOpenNormal _)
  exact ⟨L, hLfin, hLgal, fun ρ hρ => Subgroup.mem_comap.mp (hLle hρ)⟩

end Level

/-! ### The everywhere locally trivial classes are inflated -/

section Inflation

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M] [IsSmoothAction Gal(K/k) M]
  (F : IntermediateField k K) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  [MulDistribMulAction (F ≃ₐ[k] F) M]
  (hπ : ∀ (g : Gal(K/k)) (m : M), g • m = AlgEquiv.restrictNormalHom F g • m)

include hπ

omit [IsGalois k K] [IsSmoothAction Gal(K/k) M] [FiniteDimensional k F] [NumberField ↥F] in
/-- An automorphism fixing the field through which the group acts on the coefficients acts
trivially. -/
theorem smul_eq_self_of_mem_fixingSubgroup {σ : Gal(K/k)} (hσ : σ ∈ F.fixingSubgroup) (m : M) :
    σ • m = m := by
  have h1 : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥F σ = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hσ
  rw [hπ, h1, one_smul]

variable (L : IntermediateField ↥F K) [NumberField ↥L] [IsGalois ↥F ↥L]
  {u : Gal(K/k) → M} (hu : IsMulCocycle₁ u)

include hu

omit [IsSmoothAction Gal(K/k) M] [FiniteDimensional k F] in
/-- **A cocycle whose restriction over the field trivialising the coefficients kills a level and
every automorphism local at a place of that level vanishes there.** -/
theorem eq_one_of_levelDecomposition_over
    (hlev : ∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1)
    (hloc : ∀ ρ ∈ levelDecompositionSet L, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1)
    (ρ : K ≃ₐ[↥F] K) : u (ρ.restrictScalars k) = 1 :=
  eq_one_of_levelDecomposition L
    (cocycleHomOver F (fun _ hσ m => smul_eq_self_of_mem_fixingSubgroup F hπ hσ m) hu)
    (fun τ hτ => MonoidHom.mem_ker.mpr (hlev τ hτ)) (fun τ hτ => hloc τ hτ) ρ

omit [IsSmoothAction Gal(K/k) M] [FiniteDimensional k F] in
/-- **A cocycle whose restriction over the field trivialising the coefficients kills a level and
every automorphism local at a finite place of that level away from a finite set of places of that
field vanishes there.** -/
theorem eq_one_of_levelDecompositionOutside_over {S : Set (HeightOneSpectrum (𝓞 ↥F))}
    (hS : S.Finite) (hlev : ∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1)
    (hloc : ∀ ρ ∈ levelDecompositionSetOutside L S,
      u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) (ρ : K ≃ₐ[↥F] K) :
    u (ρ.restrictScalars k) = 1 :=
  eq_one_of_levelDecompositionOutside L
    (cocycleHomOver F (fun _ hσ m => smul_eq_self_of_mem_fixingSubgroup F hπ hσ m) hu)
    (fun τ hτ => MonoidHom.mem_ker.mpr (hlev τ hτ)) hS (fun τ hτ => hloc τ hτ) ρ

/-- **An everywhere locally trivial class is inflated from the field trivialising its
coefficients.** -/
theorem exists_galInflH1_eq_of_levelDecomposition (hs : IsSmooth₁ u)
    (hlev : ∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1)
    (hloc : ∀ ρ ∈ levelDecompositionSet L, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs := by
  refine exists_galInflH1_eq F hπ hu hs 1 fun σ hσ => ?_
  obtain ⟨ρ, rfl⟩ := exists_restrictScalars_eq hσ
  rw [smul_one, div_one, eq_one_of_levelDecomposition_over F hπ L hu hlev hloc ρ]

/-- **A class trivial at the places of a level away from a finite set is inflated from the field
trivialising its coefficients.** -/
theorem exists_galInflH1_eq_of_levelDecompositionOutside (hs : IsSmooth₁ u)
    {S : Set (HeightOneSpectrum (𝓞 ↥F))} (hS : S.Finite)
    (hlev : ∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1)
    (hloc : ∀ ρ ∈ levelDecompositionSetOutside L S,
      u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs := by
  refine exists_galInflH1_eq F hπ hu hs 1 fun σ hσ => ?_
  obtain ⟨ρ, rfl⟩ := exists_restrictScalars_eq hσ
  rw [smul_one, div_one,
    eq_one_of_levelDecompositionOutside_over F hπ L hu hS hlev hloc ρ]

end Inflation

/-! ### Local triviality at the levels that already see the class -/

section Automatic

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M] [IsSmoothAction Gal(K/k) M]
  (F : IntermediateField k K) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  [MulDistribMulAction (F ≃ₐ[k] F) M]
  (hπ : ∀ (g : Gal(K/k)) (m : M), g • m = AlgEquiv.restrictNormalHom F g • m)
  {u : Gal(K/k) → M} (hu : IsMulCocycle₁ u)

include hπ hu

/-- **A class of the first cohomology which is locally trivial at every level killing its cocycle is
inflated from the field trivialising its coefficients.**  Local triviality is asked only at the
levels the class already sees, which is what keeps the condition from degenerating: at the base
itself every automorphism is local at every place, and the requirement would then say outright that
the cocycle is trivial. -/
theorem exists_galInflH1_eq_of_forall_level (hs : IsSmooth₁ u)
    (hloc : ∀ L : IntermediateField ↥F K, ∀ _ : NumberField ↥L, ∀ _ : IsGalois ↥F ↥L,
      (∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) →
        ∀ ρ ∈ levelDecompositionSet L, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs := by
  obtain ⟨N, hN, hcon⟩ := id hs
  obtain ⟨L, hLfin, hLgal, hLle⟩ := exists_level_le F hN
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite ↥F ↥L
  have hlev : ∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1 := by
    intro ρ hρ
    have h1 := hcon 1 _ (hLle ρ hρ)
    rw [one_mul] at h1
    rw [h1, map_one_of_isMulCocycle₁ hu]
  exact exists_galInflH1_eq_of_levelDecomposition F hπ L hu hs hlev
    (hloc L inferInstance hLgal hlev)

/-- **A class of the first cohomology which is locally trivial away from a finite set of places at
every level killing its cocycle is inflated from the field trivialising its coefficients.** -/
theorem exists_galInflH1_eq_of_forall_level_outside (hs : IsSmooth₁ u)
    {S : Set (HeightOneSpectrum (𝓞 ↥F))} (hS : S.Finite)
    (hloc : ∀ L : IntermediateField ↥F K, ∀ _ : NumberField ↥L, ∀ _ : IsGalois ↥F ↥L,
      (∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) →
        ∀ ρ ∈ levelDecompositionSetOutside L S,
          u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1) :
    ∃ z : SmoothH1 (↥F ≃ₐ[k] ↥F) M, galInflH1 F hπ z = smoothH1Mk u hu hs := by
  obtain ⟨N, hN, hcon⟩ := id hs
  obtain ⟨L, hLfin, hLgal, hLle⟩ := exists_level_le F hN
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite ↥F ↥L
  have hlev : ∀ ρ ∈ L.fixingSubgroup, u ((ρ : K ≃ₐ[↥F] K).restrictScalars k) = 1 := by
    intro ρ hρ
    have h1 := hcon 1 _ (hLle ρ hρ)
    rw [one_mul] at h1
    rw [h1, map_one_of_isMulCocycle₁ hu]
  exact exists_galInflH1_eq_of_levelDecompositionOutside F hπ L hu hs hS hlev
    (hloc L inferInstance hLgal hlev)

end Automatic

end InverseGalois.CFT
