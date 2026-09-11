/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Krull
import InverseGalois.Core.Basic

/-!
# A finite quotient of an infinite Galois group is a Galois group

Working over a fixed algebraic closure replaces the search for a finite extension with a prescribed
group by the search for a homomorphism of the whole Galois group onto that group.  The two are the
same problem provided the homomorphism is smooth: the finite Galois levels are cofinal among the
open normal subgroups, so a smooth homomorphism onto a discrete group kills the subgroup fixing one
of them and therefore factors through the Galois group of a finite Galois subextension.  If the
homomorphism was onto, so is the map it factors as, and a quotient of a finite Galois group is
again a finite Galois group.

This is the bridge every construction which builds its extension one open subgroup at a time has to
cross at the end, and it is stated here once in the forms wanted: the factorisation through a
finite level over an arbitrary base field, the same packaged as a finite Galois extension, and the
conclusion over the rationals.

## Main results

* `InverseGalois.CFT.exists_isOpenNormal_le_ker` — a smooth homomorphism to a discrete group has an
  open normal subgroup inside its kernel.
* `InverseGalois.CFT.exists_level_comp_restrictNormalHom_eq` — **a smooth homomorphism of an
  infinite Galois group to a discrete group factors through a finite Galois level.**
* `InverseGalois.CFT.exists_finiteGalois_surjective_of_smooth` — a smooth surjection is, up to that
  factorisation, a surjection of the Galois group of a finite Galois extension.
* `InverseGalois.CFT.exists_smooth_surjective_of_galEquiv` — conversely a finite Galois extension
  of the base embeds into an algebraically closed one and so gives a smooth surjection back.
* `InverseGalois.CFT.isInverseGalois_of_smooth_surjective` — **a smooth surjection of an infinite
  Galois group over the rationals onto a finite group realizes that group as a Galois group.**
* `InverseGalois.CFT.isInverseGalois_iff_exists_smooth_surjective` — **a group is an inverse Galois
  group exactly when it is a smooth quotient of the Galois group of an algebraic closure of the
  rationals.**

## Tags

infinite Galois theory, Krull topology, smooth homomorphism, inverse Galois problem
-/

namespace InverseGalois.CFT

/-! ### An open normal subgroup inside the kernel -/

section Ker

variable {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q]

/-- **A smooth homomorphism to a discrete group has an open normal subgroup inside its kernel.**
The trivial subgroup of a discrete group is open and normal, and smoothness applied to it is
exactly this. -/
theorem exists_isOpenNormal_le_ker {Φ : G →* Q} (hsm : IsSmoothHom Φ) :
    ∃ N : Subgroup G, IsOpenNormal N ∧ N ≤ Φ.ker := by
  obtain ⟨N, hN, hle⟩ := hsm ⊥ ⟨inferInstance, isOpen_discrete _⟩
  exact ⟨N, hN, hle⟩

end Ker

/-! ### Factoring through a finite Galois level -/

section Level

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K] {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G]

/-- **A smooth homomorphism of an infinite Galois group to a discrete group factors through the
Galois group of a finite Galois subextension.**  The finite Galois levels are cofinal among the
open normal subgroups, so one of them is small enough to be killed. -/
theorem exists_level_comp_restrictNormalHom_eq (Φ : Gal(K/k) →* G) (hsm : IsSmoothHom Φ) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (_ : IsGalois k E)
      (ψ : Gal(↥E/k) →* G), ∀ g : Gal(K/k), ψ (AlgEquiv.restrictNormalHom E g) = Φ g := by
  obtain ⟨N, hN, hNle⟩ := exists_isOpenNormal_le_ker hsm
  obtain ⟨E, hfin, hgal, hEle⟩ := exists_fixingSubgroup_le hN
  haveI := hfin
  haveI := hgal
  have hker : ∀ x ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E).ker, Φ x = 1 := by
    intro x hx
    rw [IntermediateField.restrictNormalHom_ker E] at hx
    exact hNle (hEle hx)
  have hsymm : ∀ g : Gal(K/k), (QuotientGroup.quotientKerEquivOfSurjective
      (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E)
      (restrictNormalHom_surjective_level E)).symm (AlgEquiv.restrictNormalHom E g)
      = (QuotientGroup.mk g :
          Gal(K/k) ⧸ (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E).ker) := by
    intro g
    rw [MulEquiv.symm_apply_eq]
    rfl
  refine ⟨E, hfin, hgal, (QuotientGroup.lift _ Φ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (restrictNormalHom_surjective_level E)).symm.toMonoidHom, fun g => ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hsymm g]
  rfl

end Level

/-! ### Packaging the level as a finite Galois extension -/

/-- **A smooth surjection of an infinite Galois group onto a discrete group is, after factoring
through a finite Galois level, a surjection of the Galois group of a finite Galois extension of the
base field.** -/
theorem exists_finiteGalois_surjective_of_smooth {k K : Type} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (Φ : Gal(K/k) →* G) (hsm : IsSmoothHom Φ) (hsurj : Function.Surjective Φ) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (ψ : Gal(L/k) →* G), Function.Surjective ψ := by
  obtain ⟨E, hfin, hgal, ψ, hψ⟩ := exists_level_comp_restrictNormalHom_eq Φ hsm
  refine ⟨↥E, inferInstance, inferInstance, hfin, hgal, ψ, fun x => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj x
  exact ⟨AlgEquiv.restrictNormalHom E g, hψ g⟩

/-! ### From a finite Galois extension back to the whole Galois group -/

/-- **A finite Galois extension of the base gives a smooth surjection of the Galois group of an
algebraically closed Galois extension onto its Galois group.**  The finite extension embeds into
the algebraically closed one, its image is a finite Galois level, and restriction to that level is
smooth and surjective. -/
theorem exists_smooth_surjective_of_galEquiv {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] [IsGalois k Ω] (L : Type*) [Field L] [Algebra k L] [FiniteDimensional k L]
    [IsGalois k L] {G : Type*} [Group G] [TopologicalSpace G] (e : Gal(L/k) ≃* G) :
    ∃ Φ : Gal(Ω/k) →* G, Function.Surjective Φ ∧ IsSmoothHom Φ := by
  let f : L →ₐ[k] Ω := IsAlgClosed.lift
  let E : IntermediateField k Ω := f.fieldRange
  let eE : L ≃ₐ[k] ↥E := AlgEquiv.ofInjectiveField f
  haveI : Normal k ↥E := Normal.of_algEquiv eE
  haveI : FiniteDimensional k ↥E := eE.toLinearEquiv.finiteDimensional
  let ρ : Gal(↥E/k) →* G := e.toMonoidHom.comp (AlgEquiv.autCongr eE).symm.toMonoidHom
  have hρinj : Function.Injective ρ :=
    e.injective.comp (AlgEquiv.autCongr eE).symm.injective
  have hρsurj : Function.Surjective ρ :=
    e.surjective.comp (AlgEquiv.autCongr eE).symm.surjective
  refine ⟨ρ.comp (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E),
    hρsurj.comp (restrictNormalHom_surjective_level E), ?_⟩
  have hkeq : (ρ.comp (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E)).ker
      = (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥E).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
    exact ⟨fun hx => (map_eq_one_iff _ hρinj).1 hx, fun hx => by rw [hx, _root_.map_one]⟩
  refine isSmoothHom_of_isOpenNormal_ker ?_
  rw [hkeq]
  exact isOpenNormal_ker_restrictNormalHom E

/-! ### Realizing the quotient over the rationals -/

/-- **A smooth surjection of an infinite Galois group over the rationals onto a finite group
realizes that group as a Galois group over the rationals.**  The surjection factors through a
finite Galois level, and a quotient of a finite Galois group is a Galois group. -/
theorem isInverseGalois_of_smooth_surjective {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] (Φ : Gal(K/ℚ) →* G)
    (hsm : IsSmoothHom Φ) (hsurj : Function.Surjective Φ) : IsInverseGalois G := by
  obtain ⟨L, _, _, _, _, ψ, hψ⟩ := exists_finiteGalois_surjective_of_smooth Φ hsm hsurj
  exact IsInverseGalois.of_surjective_galHom L ψ hψ

/-- **A group is an inverse Galois group exactly when it is a smooth quotient of the Galois group
of an algebraic closure of the rationals.** -/
theorem isInverseGalois_iff_exists_smooth_surjective {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] [IsGalois ℚ Ω] {G : Type} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : IsInverseGalois G ↔
      ∃ Φ : Gal(Ω/ℚ) →* G, Function.Surjective Φ ∧ IsSmoothHom Φ := by
  refine ⟨fun hG => ?_, fun ⟨Φ, hsurj, hsm⟩ => isInverseGalois_of_smooth_surjective Φ hsm hsurj⟩
  obtain ⟨L, _, _, _, _, ⟨e⟩⟩ := hG
  exact exists_smooth_surjective_of_galEquiv L e

end InverseGalois.CFT
