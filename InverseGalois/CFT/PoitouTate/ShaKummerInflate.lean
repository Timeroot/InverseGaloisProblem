/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaInflate
import InverseGalois.CFT.Profinite.KummerCoeff

/-!
# The obstruction to inflating a locally trivial class, as a demand on a finite group

An everywhere locally trivial class of the second cohomology whose coefficients a finite Galois
extension splits into a product of roots of unity dies on the subgroup fixing that extension, and
the obstruction to inflating it from the Galois group of the extension is a single everywhere
locally trivial class at the level.  A homomorphism of the kernels of two lifting problems which
annihilates that obstruction carries the class into the image of inflation.

This file states the demand where it can be met.  Twisted Kummer theory reads the obstruction group
as the first cohomology of the Galois group of the extension — a finite group — with coefficients
in the units of the extension tensored with the homomorphisms of the roots of unity into the
kernel, and the homomorphism of the kernels becomes a morphism of representations of that finite
group.  So the demand is that a morphism of representations annihilate a subgroup of the first
cohomology of a finite group: **a locally trivial class of the second cohomology is carried into
the image of inflation by any homomorphism of the kernels whose induced morphism of
representations kills the everywhere locally trivial classes read with the units as
coefficients.**

## Main results

* `InverseGalois.CFT.smul_eq_of_restrictNormal_fixingSubgroup`: the subgroup fixing a subextension
  acts trivially on coefficients whose action factors through the Galois group of that
  subextension.
* `InverseGalois.CFT.exists_galInflH2_eq_coeffH2_of_kummerSha1`: **a homomorphism of the kernels
  whose induced morphism of representations kills the everywhere locally trivial classes carries
  every everywhere locally trivial class of the second cohomology into the image of inflation.**
* `InverseGalois.CFT.coeffH2_sha2_le_range_galInflH2_of_kummerSha1`: the same, stated on the whole
  group of everywhere locally trivial classes.
* `InverseGalois.CFT.exists_kummerSha1_forall_coeffH2_of_mem_sha2`: **the demand is about a single
  named class**, read through twisted Kummer theory and produced before the homomorphism of the
  kernels is chosen.

## Tags

Galois cohomology, local-global principle, Kummer theory, inflation, representation
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IntermediateField groupCohomology

section Inflate

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
  [IsAlgClosure ↥K Ω]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] [IsCyclic M] {ι : M →* (↥K)ˣ} {p : ℕ} [NeZero p]
variable {E E' : Type} [CommGroup E] [CommGroup E'] [MulDistribMulAction Gal(Ω/k) E]
  [MulDistribMulAction Gal(Ω/↥K) E] [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E]
  [MulDistribMulAction Gal(Ω/k) E'] [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E']
variable (hπ : ∀ (g : Gal(Ω/k)) (e : E), g • e = AlgEquiv.restrictNormalHom ↥K g • e)
  (hπK : ∀ (g : Gal(Ω/↥K)) (e : E), g • e = galRestrictScalarsHom k ↥K Ω g • e)
  (hπ' : ∀ (g : Gal(Ω/k)) (e : E'), g • e = AlgEquiv.restrictNormalHom ↥K g • e)

omit [IsGalois k Ω] [Algebra.IsIntegral k Ω] [FiniteDimensional k ↥K] [NumberField ↥K]
  [IsAlgClosure ↥K Ω] [MulDistribMulAction Gal(Ω/↥K) E] in
include hπ in
/-- **The subgroup fixing a subextension acts trivially on coefficients whose action factors
through the Galois group of that subextension**, since it is the kernel of the restriction. -/
theorem smul_eq_of_restrictNormal_fixingSubgroup (x : ↥K.fixingSubgroup) (e : E) : x • e = e := by
  have hx : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (x : Gal(Ω/k)) = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
    exact x.2
  show (x : Gal(Ω/k)) • e = e
  rw [hπ (x : Gal(Ω/k)) e, hx, one_smul]

variable (h : IsKummerData ↥K Ω M ι p) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable (htrivE' : ∀ (x : ↥K.fixingSubgroup) (e : E'), x • e = e)
variable {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
variable (α : E ≃* (J → M)) (α' : E' ≃* (J' → M))
variable (hEp : ∀ e : E, e ^ p = 1) (hEp' : ∀ e : E', e ^ p = 1)
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
variable [ActsTrivially K.fixingSubgroup (M →* E)] [ActsTrivially K.fixingSubgroup (M →* E')]
variable (φ : E →* E') (hφ : ∀ (g : Gal(Ω/k)) (e : E), φ (g • e) = g • φ e)

include hπ hπK htrivE' α' hEp' in
/-- **A homomorphism of the kernels whose induced morphism of representations kills the everywhere
locally trivial classes carries every everywhere locally trivial class of the second cohomology
into the image of inflation from the splitting extension.**  The obstruction to inflating the class
is a single class at the level; twisted Kummer theory reads it inside the first cohomology of a
finite group with coefficients in the units of the extension tensored with the homomorphisms of the
roots of unity, and there the demand is one a theorem about representations can meet. -/
theorem exists_galInflH2_eq_coeffH2_of_kummerSha1
    (hzero : ∀ y ∈ kummerSha1 h htriv htrivE α hEp hfix K.fixingSubgroup_isOpen
        (decompositionSubgroups k Ω),
      (groupCohomology.map (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup))
        (kummerCoeffRepHom K M E E' φ hφ) 1).hom (Multiplicative.toAdd y) = 0)
    (z : SmoothH2 Gal(Ω/k) E) (hz : z ∈ sha2 E (decompositionSubgroups k Ω)) :
    ∃ x : SmoothH2 (↥K ≃ₐ[k] ↥K) E', galInflH2 K hπ' x = coeffH2 φ hφ z :=
  exists_galInflH2_eq_coeffH2_of_mem_sha2 K hπ hπK hπ' h.isPrimitiveRoot_primitiveRoot h.smul_eq α
    h.injective h.pow_eq_one h.exists_ι_eq φ hφ
    (coeffTransH1_inflH1_eq_one_of_kummerSha1 h htriv htrivE htrivE' α α' hEp hEp' hfix φ hφ
      K.fixingSubgroup_isOpen hzero) z hz

variable (E) in
include hπ hπK htrivE' α' hEp' in
/-- **The everywhere locally trivial classes of the second cohomology are carried into the image of
inflation from the splitting extension by any homomorphism of the kernels whose induced morphism of
representations kills the everywhere locally trivial classes read with the units of that extension
as coefficients.** -/
theorem coeffH2_sha2_le_range_galInflH2_of_kummerSha1
    (hzero : ∀ y ∈ kummerSha1 h htriv htrivE α hEp hfix K.fixingSubgroup_isOpen
        (decompositionSubgroups k Ω),
      (groupCohomology.map (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup))
        (kummerCoeffRepHom K M E E' φ hφ) 1).hom (Multiplicative.toAdd y) = 0) :
    (sha2 E (decompositionSubgroups k Ω)).map (coeffH2 φ hφ) ≤ (galInflH2 K hπ').range := by
  rintro y ⟨z, hz, rfl⟩
  exact exists_galInflH2_eq_coeffH2_of_kummerSha1 K hπ hπK hπ' h htriv htrivE htrivE' α α' hEp hEp'
    hfix φ hφ hzero z hz

include hπ hπK htrivE' α' hEp' in
/-- **An everywhere locally trivial class of the second cohomology names a single everywhere locally
trivial class of the first cohomology of the Galois group of the splitting extension, with the units
of that extension tensored with the homomorphisms of the roots of unity as coefficients, and every
homomorphism of the kernels whose induced morphism of representations annihilates that one class
carries the class of the second cohomology into the image of inflation.**  The named class is the
obstruction to inflating, read through twisted Kummer theory; it depends on the class alone, so the
homomorphism of the kernels may be chosen afterwards.  That is the ordering a counting argument
needs, since such arguments settle how many classes they can annihilate before seeing any of
them. -/
theorem exists_kummerSha1_forall_coeffH2_of_mem_sha2
    (z : SmoothH2 Gal(Ω/k) E) (hz : z ∈ sha2 E (decompositionSubgroups k Ω)) :
    ∃ y ∈ kummerSha1 h htriv htrivE α hEp hfix K.fixingSubgroup_isOpen
        (decompositionSubgroups k Ω),
      ∀ (ψ : E →* E') (hψ : ∀ (g : Gal(Ω/k)) (e : E), ψ (g • e) = g • ψ e),
        (groupCohomology.map (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup))
            (kummerCoeffRepHom K M E E' ψ hψ) 1).hom (Multiplicative.toAdd y) = 0 →
          ∃ w : SmoothH2 (↥K ≃ₐ[k] ↥K) E', galInflH2 K hπ' w = coeffH2 ψ hψ z := by
  obtain ⟨x, hx, hforall⟩ := exists_sha1Level_forall_coeffH2_of_mem_sha2 K hπ hπK hπ'
    h.isPrimitiveRoot_primitiveRoot h.smul_eq α h.injective h.pow_eq_one h.exists_ι_eq z hz
  refine ⟨kummerSmoothH1Equiv h htriv htrivE α hEp hfix K.fixingSubgroup_isOpen x,
    Subgroup.mem_map_of_mem _ hx, fun ψ hψ hzero => hforall ψ hψ ?_⟩
  exact coeffTransH1_inflH1_eq_one_of_map_kummerCoeffRepHom h htriv htrivE htrivE' α α' hEp hEp'
    hfix ψ hψ K.fixingSubgroup_isOpen x hzero

end Inflate

end InverseGalois.CFT
