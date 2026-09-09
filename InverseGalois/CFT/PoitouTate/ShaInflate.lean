/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.H2Congr
import InverseGalois.CFT.Profinite.ResInflate
import InverseGalois.CFT.Units.DecompositionRestrict

/-!
# The everywhere locally trivial classes come from the splitting field

The classes of the second cohomology of the absolute Galois group of a number field which die on
every decomposition subgroup are hard to reach directly, and the classical route to them runs
through a duality theorem.  For coefficients which are split by a finite Galois extension there is
a shorter road, and this file takes it: **every everywhere locally trivial class of the second
cohomology with coefficients split into a finite product of roots of unity by a finite Galois
extension is inflated from the Galois group of that extension.**

Two ingredients meet.  The first is the vanishing over the splitting field: the decomposition
subgroups over the bigger field sit inside those over the base, so a locally trivial class stays
locally trivial there, and over a number field containing the roots of unity a locally trivial
class of the second cohomology with those coefficients is trivial.  Read on the subgroup which
fixes the splitting field rather than on the Galois group over it — the two are the same, smoothly
in both directions — this says the class dies on the kernel of restriction to the splitting field.

The second is the transgression: a class dying on the kernel of a smooth surjection onto a discrete
group is inflated from that group as soon as the everywhere locally trivial classes of the first
cohomology of the quotient, with values in the first cohomology of the kernel, are trivial.  That
last group is exactly the obstruction the twisted Kummer theory of the splitting field computes.
It is enough, and this is the form a construction free to enlarge its coefficients can use, that a
homomorphism of the coefficients annihilate that obstruction: the conclusion is then about the image
of the class under the homomorphism, and the obstruction group itself may be as large as it likes.

The consequence is a surjection from a cohomology group of a *finite* group onto the everywhere
locally trivial classes.  That is what a counting argument over a finite field can consume, and it
is the shape in which the everywhere locally trivial classes enter an embedding problem.

## Main results

* `InverseGalois.CFT.exists_galInflH2_eq_of_mem_sha2`: **an everywhere locally trivial class of the
  second cohomology, with coefficients split by a finite Galois extension into a product of roots
  of unity, is inflated from the Galois group of that extension.**
* `InverseGalois.CFT.sha2_le_range_galInflH2`: **the everywhere locally trivial classes lie in the
  image of inflation from the splitting field.**
* `InverseGalois.CFT.exists_sha1Level_forall_coeffH2_of_mem_sha2`: **the obstruction is a single
  class of the level, produced before the homomorphism of the coefficients.**
* `InverseGalois.CFT.exists_galInflH2_eq_coeffH2_of_mem_sha2`,
  `InverseGalois.CFT.coeffH2_sha2_le_range_galInflH2`: **the same after a homomorphism of the
  coefficients which merely annihilates the obstruction at the level, without it vanishing.**

## Tags

number field, Galois cohomology, local-global principle, inflation, transgression, roots of unity
-/

namespace InverseGalois.CFT

open IntermediateField groupCohomology

section Inflate

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
  [IsAlgClosure ↥K Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M]
variable {E : Type*} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
  [MulDistribMulAction Gal(Ω/↥K) E] [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E]
variable (hπ : ∀ (g : Gal(Ω/k)) (e : E), g • e = AlgEquiv.restrictNormalHom ↥K g • e)
  (hπK : ∀ (g : Gal(Ω/↥K)) (e : E), g • e = galRestrictScalarsHom k ↥K Ω g • e)

include hπ hπK

/-- **An everywhere locally trivial class of the second cohomology whose coefficients a finite
Galois extension splits into a finite product of roots of unity is inflated from the Galois group
of that extension**, as soon as the everywhere locally trivial classes at the level of that group,
with values in the first cohomology of the subgroup fixing it, are trivial.  Over the splitting
field the class is trivial, because the roots of unity are there and local triviality is inherited;
so it dies on the subgroup fixing that field, which is the kernel of restriction to it, and a class
dying on that kernel is inflated. -/
theorem exists_galInflH2_eq_of_mem_sha2 {n : ℕ} [NeZero n] {ζ : ↥K} (hζ : IsPrimitiveRoot ζ n)
    (htrivM : ∀ (g : Gal(Ω/↥K)) (m : M), g • m = m)
    {J : Type*} [Fintype J] (α : E ≃* (J → M))
    {ι : M →* (↥K)ˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : (↥K)ˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (hsha1 : sha1Level E K.fixingSubgroup K.fixingSubgroup_isOpen (decompositionSubgroups k Ω) = ⊥)
    (z : SmoothH2 Gal(Ω/k) E) (hz : z ∈ sha2 E (decompositionSubgroups k Ω)) :
    ∃ x : SmoothH2 (↥K ≃ₐ[k] ↥K) E, galInflH2 K hπ x = z := by
  have hker : ∀ g : Gal(Ω/↥K),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (galRestrictScalarsHom k ↥K Ω g) = 1 := by
    intro g
    have hmem : galRestrictScalarsHom k ↥K Ω g ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact g.commutes ⟨x, hx⟩
    rwa [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker] at hmem
  have htrivE : ∀ (g : Gal(Ω/↥K)) (e : E), g • e = e := by
    intro g e
    rw [hπK g e, hπ _ e, hker g, one_smul]
  have hcomap := eq_one_of_mem_sha2_of_mulEquivPi_intermediate hπK hζ htrivE htrivM α
    hιinj hιpow hιsurj z hz
  have hres : resH2 K.fixingSubgroup z = 1 := resH2_fixingSubgroup_eq_one K hπK hcomap
  have htriv : ∀ g ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K).ker,
      ∀ e : E, g • e = e := by
    intro g hg e
    rw [hπ g e, MonoidHom.mem_ker.1 hg, one_smul]
  exact exists_comapH2_eq_of_resH2_eq_one_of_eq_ker hπ (hasOpenNormalBasis_of_compactSpace _)
    (isSmoothHom_restrictNormalHom K) (restrictNormalHom_surjective_level K) htriv
    (IntermediateField.restrictNormalHom_ker K).symm K.fixingSubgroup_isOpen hz hres hsha1

variable (E) in
/-- **The everywhere locally trivial classes of the second cohomology, with coefficients split by a
finite Galois extension into a finite product of roots of unity, lie in the image of inflation from
the Galois group of that extension.**  So a cohomology group of a finite group already carries all
of them. -/
theorem sha2_le_range_galInflH2 {n : ℕ} [NeZero n] {ζ : ↥K} (hζ : IsPrimitiveRoot ζ n)
    (htrivM : ∀ (g : Gal(Ω/↥K)) (m : M), g • m = m)
    {J : Type*} [Fintype J] (α : E ≃* (J → M))
    {ι : M →* (↥K)ˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : (↥K)ˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (hsha1 : sha1Level E K.fixingSubgroup K.fixingSubgroup_isOpen
      (decompositionSubgroups k Ω) = ⊥) :
    sha2 E (decompositionSubgroups k Ω) ≤ (galInflH2 K hπ).range := fun z hz =>
  exists_galInflH2_eq_of_mem_sha2 K hπ hπK hζ htrivM α hιinj hιpow hιsurj hsha1 z hz

variable {E' : Type*} [CommGroup E'] [MulDistribMulAction Gal(Ω/k) E']
  [MulDistribMulAction (↥K ≃ₐ[k] ↥K) E']
variable (hπ' : ∀ (g : Gal(Ω/k)) (e : E'), g • e = AlgEquiv.restrictNormalHom ↥K g • e)

/-- **A homomorphism of the coefficients killing the everywhere locally trivial obstructions at the
level of a finite Galois extension splitting them carries every everywhere locally trivial class of
the second cohomology into the image of inflation from that extension.**  Over the splitting field
the class is trivial, so it dies on the subgroup fixing that field; the obstruction to inflating it
is then a single class at the level, everywhere locally trivial there, and the hypothesis is that
the homomorphism annihilates it.  Nothing is asked of the obstruction group itself. -/
theorem exists_galInflH2_eq_coeffH2_of_mem_sha2 {n : ℕ} [NeZero n] {ζ : ↥K}
    (hζ : IsPrimitiveRoot ζ n) (htrivM : ∀ (g : Gal(Ω/↥K)) (m : M), g • m = m)
    {J : Type*} [Fintype J] (α : E ≃* (J → M))
    {ι : M →* (↥K)ˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : (↥K)ˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (φ : E →* E') (hφ : ∀ (g : Gal(Ω/k)) (e : E), φ (g • e) = g • φ e)
    (hkill : ∀ x ∈ sha1Level E K.fixingSubgroup K.fixingSubgroup_isOpen
        (decompositionSubgroups k Ω),
      coeffTransH1 K.fixingSubgroup φ hφ
        (inflH1 K.fixingSubgroup (SmoothH1 ↥K.fixingSubgroup E) K.fixingSubgroup_isOpen x) = 1)
    (z : SmoothH2 Gal(Ω/k) E) (hz : z ∈ sha2 E (decompositionSubgroups k Ω)) :
    ∃ x : SmoothH2 (↥K ≃ₐ[k] ↥K) E', galInflH2 K hπ' x = coeffH2 φ hφ z := by
  have hker : ∀ g : Gal(Ω/↥K),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (galRestrictScalarsHom k ↥K Ω g) = 1 := by
    intro g
    have hmem : galRestrictScalarsHom k ↥K Ω g ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact g.commutes ⟨x, hx⟩
    rwa [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker] at hmem
  have htrivE : ∀ (g : Gal(Ω/↥K)) (e : E), g • e = e := by
    intro g e
    rw [hπK g e, hπ _ e, hker g, one_smul]
  have hcomap := eq_one_of_mem_sha2_of_mulEquivPi_intermediate hπK hζ htrivE htrivM α
    hιinj hιpow hιsurj z hz
  have hres : resH2 K.fixingSubgroup z = 1 := resH2_fixingSubgroup_eq_one K hπK hcomap
  have htriv : ∀ g ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K).ker,
      ∀ e : E, g • e = e := by
    intro g hg e
    rw [hπ g e, MonoidHom.mem_ker.1 hg, one_smul]
  have htriv' : ∀ g ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K).ker,
      ∀ e : E', g • e = e := by
    intro g hg e
    rw [hπ' g e, MonoidHom.mem_ker.1 hg, one_smul]
  exact exists_comapH2_eq_coeffH2_of_resH2_eq_one_of_eq_ker hπ'
    (hasOpenNormalBasis_of_compactSpace _) (isSmoothHom_restrictNormalHom K)
    (restrictNormalHom_surjective_level K) htriv htriv' φ hφ
    (IntermediateField.restrictNormalHom_ker K).symm K.fixingSubgroup_isOpen hz hres hkill

/-- **An everywhere locally trivial class of the second cohomology has a single everywhere locally
trivial obstruction at the level of a finite Galois extension splitting the coefficients, and every
homomorphism of the coefficients annihilating that one class carries the class into the image of
inflation from that extension.**  The obstruction is read off the class alone, before the
homomorphism is named; that ordering is what an argument able to annihilate only a fixed number of
classes needs. -/
theorem exists_sha1Level_forall_coeffH2_of_mem_sha2 {n : ℕ} [NeZero n] {ζ : ↥K}
    (hζ : IsPrimitiveRoot ζ n) (htrivM : ∀ (g : Gal(Ω/↥K)) (m : M), g • m = m)
    {J : Type*} [Fintype J] (α : E ≃* (J → M))
    {ι : M →* (↥K)ˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : (↥K)ˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (z : SmoothH2 Gal(Ω/k) E) (hz : z ∈ sha2 E (decompositionSubgroups k Ω)) :
    ∃ x ∈ sha1Level E K.fixingSubgroup K.fixingSubgroup_isOpen (decompositionSubgroups k Ω),
      ∀ (φ : E →* E') (hφ : ∀ (g : Gal(Ω/k)) (e : E), φ (g • e) = g • φ e),
        coeffTransH1 K.fixingSubgroup φ hφ
            (inflH1 K.fixingSubgroup (SmoothH1 ↥K.fixingSubgroup E)
              K.fixingSubgroup_isOpen x) = 1 →
          ∃ y : SmoothH2 (↥K ≃ₐ[k] ↥K) E', galInflH2 K hπ' y = coeffH2 φ hφ z := by
  have hker : ∀ g : Gal(Ω/↥K),
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (galRestrictScalarsHom k ↥K Ω g) = 1 := by
    intro g
    have hmem : galRestrictScalarsHom k ↥K Ω g ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact g.commutes ⟨x, hx⟩
    rwa [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker] at hmem
  have htrivE : ∀ (g : Gal(Ω/↥K)) (e : E), g • e = e := by
    intro g e
    rw [hπK g e, hπ _ e, hker g, one_smul]
  have hcomap := eq_one_of_mem_sha2_of_mulEquivPi_intermediate hπK hζ htrivE htrivM α
    hιinj hιpow hιsurj z hz
  have hres : resH2 K.fixingSubgroup z = 1 := resH2_fixingSubgroup_eq_one K hπK hcomap
  have htriv : ∀ g ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K).ker,
      ∀ e : E, g • e = e := by
    intro g hg e
    rw [hπ g e, MonoidHom.mem_ker.1 hg, one_smul]
  have htriv' : ∀ g ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K).ker,
      ∀ e : E', g • e = e := by
    intro g hg e
    rw [hπ' g e, MonoidHom.mem_ker.1 hg, one_smul]
  exact exists_sha1Level_forall_coeffH2_of_resH2_eq_one_of_eq_ker hπ'
    (hasOpenNormalBasis_of_compactSpace _) (isSmoothHom_restrictNormalHom K)
    (restrictNormalHom_surjective_level K) htriv htriv'
    (IntermediateField.restrictNormalHom_ker K).symm K.fixingSubgroup_isOpen hz hres

variable (E) in
/-- **The image under a homomorphism of the coefficients killing the everywhere locally trivial
obstructions at the level of the everywhere locally trivial classes of the second cohomology lies in
the image of inflation from that level.** -/
theorem coeffH2_sha2_le_range_galInflH2 {n : ℕ} [NeZero n] {ζ : ↥K}
    (hζ : IsPrimitiveRoot ζ n) (htrivM : ∀ (g : Gal(Ω/↥K)) (m : M), g • m = m)
    {J : Type*} [Fintype J] (α : E ≃* (J → M))
    {ι : M →* (↥K)ˣ} (hιinj : Function.Injective ι) (hιpow : ∀ m : M, ι m ^ n = 1)
    (hιsurj : ∀ y : (↥K)ˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (φ : E →* E') (hφ : ∀ (g : Gal(Ω/k)) (e : E), φ (g • e) = g • φ e)
    (hkill : ∀ x ∈ sha1Level E K.fixingSubgroup K.fixingSubgroup_isOpen
        (decompositionSubgroups k Ω),
      coeffTransH1 K.fixingSubgroup φ hφ
        (inflH1 K.fixingSubgroup (SmoothH1 ↥K.fixingSubgroup E) K.fixingSubgroup_isOpen x) = 1) :
    (sha2 E (decompositionSubgroups k Ω)).map (coeffH2 φ hφ) ≤ (galInflH2 K hπ').range := by
  rintro y ⟨z, hz, rfl⟩
  exact exists_galInflH2_eq_coeffH2_of_mem_sha2 K hπ hπK hπ' hζ htrivM α hιinj hιpow hιsurj φ hφ
    hkill z hz

end Inflate

end InverseGalois.CFT
