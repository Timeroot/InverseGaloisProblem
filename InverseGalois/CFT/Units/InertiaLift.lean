/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaRestrict
import InverseGalois.CFT.Units.InfiniteDecomposition

/-!
# Inertia at a level is the restriction of inertia above

Restricting an automorphism of a Galois extension to a level sends the inertia subgroup at a prime
of the big ring of integers into the inertia subgroup at the place below, and the point of this
file is that nothing is lost: **every element of inertia at a place of a level is the restriction
of an element of inertia at a prescribed prime above it**, however large the extension.

The argument is in two steps.  Fixing the place, the element of inertia is first lifted to an
automorphism of the whole extension fixing the prescribed prime, which is what transitivity on the
primes above a place gives; the lift acts on the residue field of the prime, and its action there
is trivial over the residue field of the place precisely because the element one started from was
in inertia.  Correcting it is then a matter of finding an automorphism over the level, fixing the
prime, whose residue action is the inverse of that one; and the stabiliser of a prime of an
invariant extension surjects onto the automorphisms of the residue extension, for a profinite group
acting continuously just as for a finite one.  The corrected lift acts trivially on the residue
field, which is to say it lies in inertia.

Both steps are statements about an arbitrary, possibly infinite, Galois extension: neither the
finiteness of a level nor a choice of base field beyond the one the level is normal over enters.

## Main results

* `InverseGalois.CFT.exists_mem_inertia_restrictNormalHom_eq`: **an element of the inertia subgroup
  at a place of a level is the restriction of an element of the inertia subgroup at a prescribed
  prime above that place.**
* `InverseGalois.CFT.map_inertia_restrictNormalHom`: **restriction carries the inertia subgroup at
  a prime onto the inertia subgroup at the place below it.**

## Tags

inertia subgroup, ramification, Galois group, profinite group, residue field
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

section InertiaLift

variable {k K : Type*} [Field k] [NumberField k] [Field K] [Algebra k K] [IsGalois k K]
  (L : IntermediateField k K) [NumberField ↥L] [IsGalois k ↥L]

set_option synthInstance.maxHeartbeats 400000 in
omit [NumberField k] [NumberField ↥L] in
/-- **An element of the inertia subgroup at a place of a level is the restriction of an element of
the inertia subgroup at a prescribed prime above that place.**

An element of inertia fixes the place, so it lifts to an automorphism of the whole extension fixing
the prime; the residue action of the inverse of that lift is an automorphism of the residue field
of the prime over the residue field of the place, because the element one started from moves an
integer of the level by an element of the place.  The stabiliser of the prime in the Galois group
over the level surjects onto the automorphisms of the residue extension, so some automorphism over
the level, fixing the prime, has exactly that residue action; multiplying it into the lift leaves
the restriction to the level unchanged and makes the residue action trivial. -/
theorem exists_mem_inertia_restrictNormalHom_eq {P : Ideal (𝓞 K)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 ↥L)} (hv : v.asIdeal = Ideal.under (𝓞 ↥L) P) {τ : Gal(↥L/k)}
    (hτ : τ ∈ Ideal.inertia Gal(↥L/k) v.asIdeal) :
    ∃ ρ : Gal(K/k), ρ ∈ Ideal.inertia Gal(K/k) P ∧
      AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L ρ = τ := by
  haveI : P.LiesOver v.asIdeal := ⟨hv⟩
  haveI : P.LiesOver (Ideal.under (𝓞 k) P) := ⟨rfl⟩
  haveI := smulCommClass_ringOfIntegers k K
  -- a lift of the element of inertia fixing the prescribed prime
  have hvsmul : τ • v = v := HeightOneSpectrum.ext (by
    rw [asIdeal_smul]
    exact mem_stabilizer_iff.1 (Ideal.inertia_le_stabilizer _ hτ))
  obtain ⟨σ₀, hσ₀P, hσ₀L⟩ := exists_mem_stabilizer_restrictNormalHom_eq L hvsmul P hv.symm
  have hres : ∀ z : 𝓞 ↥L, σ₀⁻¹ • algebraMap (𝓞 ↥L) (𝓞 K) z
      = algebraMap (𝓞 ↥L) (𝓞 K) (τ⁻¹ • z) := by
    intro z
    have h1 : (σ₀⁻¹).restrictNormal ↥L = τ⁻¹ := by
      show AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ₀⁻¹ = τ⁻¹
      rw [_root_.map_inv, hσ₀L]
    rw [← algebraMap_smul_restrictNormal L σ₀⁻¹ z, h1]
  -- the residue action of the inverse of the lift, read over the residue field of the place
  set t : (𝓞 K ⧸ P) ≃ₐ[𝓞 k ⧸ Ideal.under (𝓞 k) P] (𝓞 K ⧸ P) :=
    Ideal.Quotient.stabilizerHom P (Ideal.under (𝓞 k) P) Gal(K/k)
      ⟨σ₀⁻¹, inv_mem (mem_stabilizer_iff.2 hσ₀P)⟩ with htdef
  have htapply : ∀ b : 𝓞 K, t (Ideal.Quotient.mk P b) = Ideal.Quotient.mk P (σ₀⁻¹ • b) :=
    fun _ => rfl
  have hcom : ∀ y : 𝓞 ↥L ⧸ v.asIdeal, t.toRingEquiv
      (algebraMap (𝓞 ↥L ⧸ v.asIdeal) (𝓞 K ⧸ P) y)
      = algebraMap (𝓞 ↥L ⧸ v.asIdeal) (𝓞 K ⧸ P) y := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    show t (algebraMap (𝓞 ↥L ⧸ v.asIdeal) (𝓞 K ⧸ P) (Ideal.Quotient.mk v.asIdeal z)) = _
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, htapply, hres, Ideal.Quotient.eq,
      ← _root_.map_sub]
    have hz : τ⁻¹ • z - z ∈ v.asIdeal := inv_mem hτ z
    rw [hv] at hz
    exact hz
  -- an automorphism over the level, fixing the prime, with that residue action
  haveI := isInvariant_ringOfIntegers_of_isGalois (↥L) K
  haveI := smulCommClass_ringOfIntegers (↥L) K
  letI : TopologicalSpace (𝓞 K) := ⊥
  haveI : DiscreteTopology (𝓞 K) := ⟨rfl⟩
  haveI := continuousSMul_ringOfIntegers (↥L) K
  obtain ⟨ρ₀, hρ₀⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Gal(K/↥L))
    v.asIdeal P (AlgEquiv.ofRingEquiv hcom)
  refine ⟨(ρ₀ : Gal(K/↥L)).restrictScalars k * σ₀, fun x => ?_, ?_⟩
  · have h1 : Ideal.Quotient.mk P ((ρ₀ : Gal(K/↥L)) • (σ₀ • x))
        = Ideal.Quotient.mk P (σ₀⁻¹ • (σ₀ • x)) :=
      DFunLike.congr_fun hρ₀ (Ideal.Quotient.mk P (σ₀ • x))
    rw [inv_smul_smul] at h1
    have h2 : ((ρ₀ : Gal(K/↥L)).restrictScalars k * σ₀) • x
        = (ρ₀ : Gal(K/↥L)) • (σ₀ • x) := by
      rw [mul_smul]
      exact RingOfIntegers.ext rfl
    show ((ρ₀ : Gal(K/↥L)).restrictScalars k * σ₀) • x - x ∈ P
    rw [h2]
    exact Ideal.Quotient.eq.1 h1
  · rw [map_mul, restrictNormalHom_restrictScalars k ↥L (ρ₀ : Gal(K/↥L)), one_mul, hσ₀L]

omit [NumberField k] [NumberField ↥L] in
/-- **Restriction carries the inertia subgroup at a prime onto the inertia subgroup at the place
below it.**  That the image is contained in the inertia subgroup below is the elementary direction;
the reverse inclusion is the lifting statement. -/
theorem map_inertia_restrictNormalHom {P : Ideal (𝓞 K)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 ↥L)} (hv : v.asIdeal = Ideal.under (𝓞 ↥L) P) :
    (Ideal.inertia Gal(K/k) P).map (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L)
      = Ideal.inertia Gal(↥L/k) v.asIdeal := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun σ hσ => ?_) fun τ hτ => ?_
  · rw [Subgroup.mem_comap]
    have hres := restrictNormal_mem_inertia L P hσ
    rw [← hv] at hres
    exact hres
  · obtain ⟨ρ, hρI, hρL⟩ := exists_mem_inertia_restrictNormalHom_eq L hv hτ
    exact Subgroup.mem_map.2 ⟨ρ, hρI, hρL⟩

end InertiaLift

end InverseGalois.CFT
