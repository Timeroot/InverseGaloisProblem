/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaSurjective
import InverseGalois.CFT.InertiaTransport
import InverseGalois.CFT.SplitCompositum

/-!
# Moving the abelianized inertia subgroup along a homomorphism

Cyclicity of the image of an inertia subgroup in the abelianization of its decomposition group is
inherited by any situation reached by a homomorphism of Galois groups which carries the
decomposition group into the decomposition group and the inertia subgroup *onto* the inertia
subgroup: the image of inertia in the abelianized decomposition group downstairs is then the image
of the one upstairs under the induced homomorphism of abelianizations.

Two such homomorphisms occur.  Restriction to a normal subextension maps the decomposition group of
a prime into the decomposition group of the prime below it and the inertia subgroup onto the
inertia subgroup below it.  And an isomorphism of number fields identifies the two Galois groups
compatibly with contracting a prime along the induced isomorphism of rings of integers.  Together
they carry the property from a Galois number field to a copy, inside a chosen algebraic closure, of
a normal subextension of it.

## Main definitions

* `InverseGalois.CFT.abelianInertia`: the image of the inertia subgroup at a prime in the
  abelianization of the decomposition group at that prime.

## Main results

* `InverseGalois.CFT.isCyclic_map_abelianization`: **a homomorphism carrying decomposition into
  decomposition and inertia onto inertia carries the abelianized inertia subgroup onto the
  abelianized inertia subgroup**, so cyclicity is inherited.
* `InverseGalois.CFT.isCyclic_abelianInertia_under`: cyclicity of the abelianized inertia subgroup
  passes to a normal subextension.
* `InverseGalois.CFT.isCyclic_abelianInertia_of_algEquiv`: cyclicity of the abelianized inertia
  subgroup transports along an isomorphism of number fields.

## Tags

inertia subgroup, decomposition group, abelianization, number field
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

set_option synthInstance.maxHeartbeats 400000

/-! ### The image of inertia in the abelianized decomposition group -/

variable {K : Type*} [Field K] [NumberField K]

/-- The image of the inertia subgroup at a prime in the abelianization of the decomposition group
at that prime. -/
def abelianInertia (P : Ideal (𝓞 K)) :
    Subgroup (Abelianization ↥(MulAction.stabilizer Gal(K/ℚ) P)) :=
  ((Ideal.inertia Gal(K/ℚ) P).subgroupOf (MulAction.stabilizer Gal(K/ℚ) P)).map Abelianization.of

/-! ### Transport along a homomorphism of groups -/

/-- **A homomorphism carrying one decomposition group into another and the first inertia subgroup
onto the second carries the abelianized inertia subgroup onto the abelianized inertia subgroup.**
Cyclicity therefore passes from the source to the target. -/
theorem isCyclic_map_abelianization {Γ Γ' : Type*} [Group Γ] [Group Γ'] (f : Γ' →* Γ)
    {D' I' : Subgroup Γ'} {D I : Subgroup Γ} (hI'D' : I' ≤ D') (hD : ∀ x ∈ D', f x ∈ D)
    (hI : I'.map f = I)
    (h : IsCyclic ↥((I'.subgroupOf D').map (Abelianization.of : ↥D' →* Abelianization ↥D'))) :
    IsCyclic ↥((I.subgroupOf D).map (Abelianization.of : ↥D →* Abelianization ↥D)) := by
  haveI := h
  set φ : ↥D' →* ↥D :=
    MonoidHom.codRestrict (f.comp D'.subtype) D (fun x => hD (x : Γ') x.2) with hφ
  have hφapp : ∀ x : ↥D', (φ x : Γ) = f (x : Γ') := fun _ => rfl
  have hmapφ : (I'.subgroupOf D').map φ = I.subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : Γ') ∈ I' := hy
      rw [Subgroup.mem_subgroupOf, hφapp, ← hI]
      exact ⟨(y : Γ'), hy', rfl⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← hI] at hx
      obtain ⟨y, hyI, hy⟩ := hx
      exact ⟨⟨y, hI'D' hyI⟩, Subgroup.mem_subgroupOf.mpr hyI, Subtype.ext hy⟩
  have hcomp : (Abelianization.map φ).comp (Abelianization.of : ↥D' →* Abelianization ↥D')
      = (Abelianization.of : ↥D →* Abelianization ↥D).comp φ := rfl
  have hkey : (I.subgroupOf D).map (Abelianization.of : ↥D →* Abelianization ↥D)
      = ((I'.subgroupOf D').map (Abelianization.of : ↥D' →* Abelianization ↥D')).map
        (Abelianization.map φ) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hmapφ]
  rw [hkey]
  exact isCyclic_of_surjective _
    (MonoidHom.subgroupMap_surjective (Abelianization.map φ)
      ((I'.subgroupOf D').map (Abelianization.of : ↥D' →* Abelianization ↥D')))

/-! ### Transport to a normal subextension -/

section Under

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ}

/-- **Cyclicity of the abelianized inertia subgroup passes to a normal subextension.**  Restriction
carries the decomposition group of a prime into the decomposition group of the prime below it and
the inertia subgroup onto the inertia subgroup below it. -/
theorem isCyclic_abelianInertia_under (A : IntermediateField ℚ N) [Normal ℚ ↥A]
    [NumberField ↥A] (hp : p.Prime) (P : Ideal (𝓞 N)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (h : IsCyclic ↥(abelianInertia P)) :
    IsCyclic ↥(abelianInertia (P.under (𝓞 ↥A))) :=
  isCyclic_map_abelianization (AlgEquiv.restrictNormalHom ↥A)
    (Ideal.inertia_le_stabilizer P) (fun _ hx => restrictNormal_mem_stabilizer A P hx)
    (map_inertia_eq_inertia A hp P) h

end Under

/-! ### Transport along an isomorphism of number fields -/

section Transport

variable {E F : Type*} [Field E] [NumberField E] [Field F] [NumberField F]

/-- Restricting an isomorphism of number fields to the rings of integers intertwines the two
Galois actions. -/
theorem mapAlgEquivInt_smul (e : E ≃ₐ[ℚ] F) (σ : Gal(E/ℚ)) (x : 𝓞 E) :
    mapAlgEquivInt (e : E ≃+* F) (σ • x)
      = AlgEquiv.autCongr e σ • mapAlgEquivInt (e : E ≃+* F) x := by
  apply RingOfIntegers.ext
  show e (σ (x : E)) = (AlgEquiv.autCongr e σ) (e (x : E))
  simp [AlgEquiv.autCongr]

/-- Contracting a prime along an isomorphism of number fields matches the two inertia subgroups. -/
theorem mem_inertia_autCongr_iff (e : E ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F)) (σ : Gal(E/ℚ)) :
    AlgEquiv.autCongr e σ ∈ Ideal.inertia Gal(F/ℚ) Q ↔
      σ ∈ Ideal.inertia Gal(E/ℚ)
        (Ideal.comap (mapAlgEquivInt (e : E ≃+* F) : 𝓞 E →+* 𝓞 F) Q) := by
  constructor
  · intro h x
    show mapAlgEquivInt (e : E ≃+* F) (σ • x - x) ∈ Q
    rw [map_sub, mapAlgEquivInt_smul]
    exact h (mapAlgEquivInt (e : E ≃+* F) x)
  · intro h y
    obtain ⟨x, rfl⟩ := (mapAlgEquivInt (e : E ≃+* F)).surjective y
    have hx : mapAlgEquivInt (e : E ≃+* F) (σ • x - x) ∈ Q := h x
    rw [map_sub, mapAlgEquivInt_smul] at hx
    exact hx

/-- Contracting a prime along an isomorphism of number fields matches the two decomposition
groups. -/
theorem mem_stabilizer_autCongr_iff (e : E ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F)) (σ : Gal(E/ℚ)) :
    AlgEquiv.autCongr e σ ∈ MulAction.stabilizer Gal(F/ℚ) Q ↔
      σ ∈ MulAction.stabilizer Gal(E/ℚ)
        (Ideal.comap (mapAlgEquivInt (e : E ≃+* F) : 𝓞 E →+* 𝓞 F) Q) := by
  have key : ∀ x : 𝓞 E, mapAlgEquivInt (e : E ≃+* F) (σ⁻¹ • x)
      = (AlgEquiv.autCongr e σ)⁻¹ • mapAlgEquivInt (e : E ≃+* F) x := by
    intro x
    rw [mapAlgEquivInt_smul, map_inv (AlgEquiv.autCongr e)]
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    refine SetLike.ext fun x => ?_
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    show mapAlgEquivInt (e : E ≃+* F) (σ⁻¹ • x) ∈ Q ↔ mapAlgEquivInt (e : E ≃+* F) x ∈ Q
    rw [key, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, h]
  · intro h
    refine SetLike.ext fun y => ?_
    obtain ⟨x, rfl⟩ := (mapAlgEquivInt (e : E ≃+* F)).surjective y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← key]
    show mapAlgEquivInt (e : E ≃+* F) (σ⁻¹ • x) ∈ Q ↔ mapAlgEquivInt (e : E ≃+* F) x ∈ Q
    have h1 : σ⁻¹ • x ∈ Ideal.comap (mapAlgEquivInt (e : E ≃+* F) : 𝓞 E →+* 𝓞 F) Q ↔
        x ∈ Ideal.comap (mapAlgEquivInt (e : E ≃+* F) : 𝓞 E →+* 𝓞 F) Q := by
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, h]
    exact h1

/-- The isomorphism of Galois groups induced by an isomorphism of number fields carries the
inertia subgroup at a contracted prime onto the inertia subgroup at the prime. -/
theorem map_inertia_autCongr (e : E ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F)) :
    (Ideal.inertia Gal(E/ℚ)
        (Ideal.comap (mapAlgEquivInt (e : E ≃+* F) : 𝓞 E →+* 𝓞 F) Q)).map
      (AlgEquiv.autCongr e).toMonoidHom = Ideal.inertia Gal(F/ℚ) Q := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (mem_inertia_autCongr_iff e Q σ).mpr hσ
  · intro hτ
    refine ⟨(AlgEquiv.autCongr e).symm τ, (mem_inertia_autCongr_iff e Q _).mp ?_, ?_⟩
    · rwa [MulEquiv.apply_symm_apply]
    · exact MulEquiv.apply_symm_apply _ _

/-- **Cyclicity of the abelianized inertia subgroup transports along an isomorphism of number
fields.** -/
theorem isCyclic_abelianInertia_of_algEquiv (e : E ≃ₐ[ℚ] F) (Q : Ideal (𝓞 F))
    (h : IsCyclic ↥(abelianInertia
      (Ideal.comap (mapAlgEquivInt (e : E ≃+* F) : 𝓞 E →+* 𝓞 F) Q))) :
    IsCyclic ↥(abelianInertia Q) :=
  isCyclic_map_abelianization (AlgEquiv.autCongr e).toMonoidHom
    (Ideal.inertia_le_stabilizer _)
    (fun _ hx => (mem_stabilizer_autCongr_iff e Q _).mpr hx)
    (map_inertia_autCongr e Q) h

end Transport

end InverseGalois.CFT
