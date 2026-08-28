/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CutField
import InverseGalois.CFT.Scholz.CanonicalDefect

/-!
# The Scholz obstruction of a block, read on a subgroup

The residue correction of the Scholz–Reichardt construction asks that the Scholz obstructions of the
primes of each block of a family sum to zero.  That sum is recorded here as the **obstruction of the
block**, and the orthogonality condition the correction is stated with — a sum against the indicator
vector of the block over a finite set of primes containing it — is exactly that number.

Along the dyadic climb the fields whose obstructions are being computed are the subfields of a fixed
cover cut out by the normal subgroups of the group realised on it.  For such a subfield the
obstruction of a prime is a membership statement in the group: the prime has residue degree one in
the subfield cut out by a subgroup exactly when the image of an arithmetic Frobenius above it lies
in the inertia subgroup together with that subgroup.  Everything the climb has to know about the
obstructions therefore happens inside one group.

## Main definitions

* `InverseGalois.CFT.blockDefect`: the Scholz obstruction of a block of primes in a number field.

## Main results

* `InverseGalois.CFT.sum_blockVector_eq_blockDefect`: **the orthogonality condition of the residue
  correction at a block is the obstruction of that block.**
* `InverseGalois.CFT.isSplitInertiaAt_cutField_iff`: **a prime has residue degree one in the field
  cut out by a homomorphism exactly when the image of an arithmetic Frobenius above it lies in the
  image of the inertia subgroup.**
* `InverseGalois.CFT.isSplitInertiaAt_cutField_mk'_iff`: **a prime has residue degree one in the
  subfield cut out by a normal subgroup exactly when an arithmetic Frobenius above it lies in the
  inertia subgroup together with that subgroup.**

## Tags

Scholz–Reichardt, Scholz obstruction, block, inertia subgroup, Frobenius, cut field
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### The obstruction of a block -/

/-- **The Scholz obstruction of a block of primes in a number field**: the sum of the obstructions
of its members. -/
noncomputable def blockDefect (K : Type*) [Field K] [NumberField K] (B : Finset ℕ) : ZMod 2 :=
  ∑ p ∈ B, canonicalDefect K p

/-- A block all of whose primes have residue degree one carries no obstruction. -/
theorem blockDefect_eq_zero_of_forall {K : Type*} [Field K] [NumberField K] {B : Finset ℕ}
    (h : ∀ p ∈ B, IsSplitInertiaAt K p) : blockDefect K B = 0 :=
  Finset.sum_eq_zero fun p hp => canonicalDefect_eq_zero (h p hp)

/-- **The orthogonality condition of the residue correction at a block is the obstruction of that
block.**  The indicator vector of the block cuts the sum over the set of primes the correction is
tested at down to a sum over the block. -/
theorem sum_blockVector_eq_blockDefect {K : Type*} [Field K] [NumberField K] {S B : Finset ℕ}
    (hBS : B ⊆ S) :
    ∑ p : {q // q ∈ S}, canonicalDefect K (p : ℕ) * blockVector S B p = blockDefect K B := by
  classical
  have h : ∀ p : {q // q ∈ S}, canonicalDefect K (p : ℕ) * blockVector S B p
      = if (p : ℕ) ∈ B then canonicalDefect K (p : ℕ) else 0 := by
    intro p
    simp only [blockVector]
    split <;> simp
  rw [Finset.sum_congr rfl fun p _ => h p,
    Finset.sum_coe_sort S fun x => if x ∈ B then canonicalDefect K x else 0, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hBS, blockDefect]

/-! ### The subfield cut out by a subgroup -/

/-- The subfield cut out by a homomorphism out of the Galois group of a number field is a number
field. -/
instance numberField_cutField {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A]
    [IsGalois ℚ ↥A] {G : Type*} [Group G] (ψ : Gal(↥A/ℚ) →* G) : NumberField ↥(cutField ψ) := ⟨⟩

section Group

variable {G H : Type*} [Group G] [Group H]

/-- The kernel of a quotient map read through a homomorphism is the preimage of the subgroup. -/
theorem ker_mk'_comp (f : G →* H) (U : Subgroup H) [U.Normal] :
    ((QuotientGroup.mk' U).comp f).ker = U.comap f := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

end Group

section SplitInertia

variable {T : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥T] [IsGalois ℚ ↥T]
  {G : Type*} [Group G] {q : ℕ}

/-- **A prime has residue degree one in the field cut out by a homomorphism exactly when the image
of an arithmetic Frobenius above it lies in the image of the inertia subgroup.**  The homomorphism
is restriction to the cut field followed by an isomorphism, so this is the statement downstairs. -/
theorem isSplitInertiaAt_cutField_iff (ψ : Gal(↥T/ℚ) →* G) (hψ : Function.Surjective ψ)
    (hq : q.Prime) (P : Ideal (𝓞 ↥T)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})]
    {σ : Gal(↥T/ℚ)} (hσ : IsArithFrobAt ℤ σ P) :
    IsSplitInertiaAt ↥(cutField ψ) q ↔ ψ σ ∈ (Ideal.inertia Gal(↥T/ℚ) P).map ψ :=
  (mem_map_inertia_iff_isSplitInertiaAt (cutField_le ψ) (galEquivCutField ψ hψ) ψ
    (fun τ => (galEquivCutField_galRestrictLE ψ hψ τ).symm) hq P hσ).symm

/-- **A prime has residue degree one in the subfield cut out by a normal subgroup exactly when an
arithmetic Frobenius above it lies in the inertia subgroup together with that subgroup.** -/
theorem isSplitInertiaAt_cutField_mk'_iff (Ψ : Gal(↥T/ℚ) ≃* G) (U : Subgroup G) [U.Normal]
    (hq : q.Prime) (P : Ideal (𝓞 ↥T)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})]
    {σ : Gal(↥T/ℚ)} (hσ : IsArithFrobAt ℤ σ P) :
    IsSplitInertiaAt ↥(cutField ((QuotientGroup.mk' U).comp Ψ.toMonoidHom)) q
      ↔ Ψ σ ∈ (Ideal.inertia Gal(↥T/ℚ) P).map Ψ.toMonoidHom ⊔ U := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' U).comp Ψ.toMonoidHom) :=
    (QuotientGroup.mk'_surjective U).comp Ψ.surjective
  rw [isSplitInertiaAt_cutField_iff _ hsurj hq P hσ, ← Subgroup.map_map,
    show ((QuotientGroup.mk' U).comp Ψ.toMonoidHom) σ = QuotientGroup.mk' U (Ψ σ) from rfl,
    ← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

end SplitInertia

end InverseGalois.CFT
