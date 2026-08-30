/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.DecompositionOutside

/-!
# A homomorphism killing every decomposition group is trivial

The decomposition groups of a Galois extension of number fields generate the whole Galois group as
soon as it is solvable, and the finite places away from a prescribed finite set already suffice.
That statement is about the subgroup they generate; here it is read as a statement about
homomorphisms out of the Galois group.

A homomorphism into a commutative group has a normal kernel, and the Galois group of the fixed field
of that kernel is a quotient of the Galois group which embeds in the commutative group, hence is
commutative, hence solvable.  So the fixed field is a solvable subextension, and if every
automorphism fixing a place lies in the kernel then every place of the base field splits completely
in it and it is the base field: the kernel is everything and the homomorphism is trivial.  No
solvability of the whole Galois group is needed, only of the piece the homomorphism sees.

The extension over which the homomorphism is taken is arbitrary, so this is the statement that an
abelian extension in which every place splits completely is trivial, and that finitely many places,
together with all the infinite places, may be discarded from the hypothesis.  It is the vanishing of
the everywhere locally trivial classes of the first cohomology with trivial coefficients.

## Main results

* `InverseGalois.CFT.eq_top_of_decompositionSet_subset`,
  `InverseGalois.CFT.eq_top_of_decompositionSetOutside_subset`: **a normal subgroup with solvable
  fixed field containing every automorphism fixing a place is everything.**
* `InverseGalois.CFT.eq_one_of_forall_mem_decompositionSet`,
  `InverseGalois.CFT.eq_one_of_forall_mem_decompositionSetOutside`: **a homomorphism into a
  commutative group killing every decomposition group is trivial.**
* `InverseGalois.CFT.eq_one_of_forall_fixing_place`,
  `InverseGalois.CFT.eq_one_of_forall_fixing_prime_outside`: the same, read off the places
  themselves.

## Tags

number field, place, decomposition group, splitting, local-global principle, abelian extension
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section EqTop

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (H : Subgroup Gal(K/k)) [H.Normal]
  [IsSolvable Gal(↥(IntermediateField.fixedField H)/k)]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **A normal subgroup whose fixed field is solvable over the base and which contains every
automorphism fixing a place is everything.**  In the fixed field every place of the base field
splits completely, and a solvable extension in which every place splits completely is trivial. -/
theorem eq_top_of_decompositionSet_subset (h : decompositionSet k K ⊆ (H : Set Gal(K/k))) :
    H = ⊤ := by
  refine eq_top_of_subsingleton_gal_fixedField _ ?_
  have key : ∀ σ : Gal(K/k), σ ∈ decompositionSet k K →
      AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField H) σ = 1 := by
    intro σ hσ
    refine MonoidHom.mem_ker.mp ?_
    rw [ker_restrictNormalHom_fixedField]
    exact h hσ
  refine subsingleton_gal_of_isSolvable_of_free k ↥(IntermediateField.fixedField H)
    (fun τ u hu => ?_) (fun τ w hw => ?_)
  · obtain ⟨σ, hσ, hres⟩ := exists_restrictNormalHom_eq_of_prime K τ hu
    rw [← hres]
    exact key σ (Or.inl hσ)
  · obtain ⟨σ, hσ, hres⟩ := exists_restrictNormalHom_eq_of_infinitePlace K τ hw
    rw [← hres]
    exact key σ (Or.inr hσ)

/-- **A normal subgroup whose fixed field is solvable over the base and which contains every
automorphism fixing a finite place away from a finite set of places of the base field is
everything.** -/
theorem eq_top_of_decompositionSetOutside_subset {S : Set (HeightOneSpectrum (𝓞 k))}
    (hS : S.Finite) (h : decompositionSetOutside k K S ⊆ (H : Set Gal(K/k))) : H = ⊤ := by
  refine eq_top_of_subsingleton_gal_fixedField _ ?_
  have key : ∀ σ : Gal(K/k), σ ∈ decompositionSetOutside k K S →
      AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField H) σ = 1 := by
    intro σ hσ
    refine MonoidHom.mem_ker.mp ?_
    rw [ker_restrictNormalHom_fixedField]
    exact h hσ
  refine subsingleton_gal_of_isSolvable_of_splits_outside hS fun u hu => ?_
  refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => ?_
  obtain ⟨σ, ⟨v, hvu, hv⟩, hres⟩ := exists_restrictNormalHom_eq_of_prime_above K τ hτ
  have hvS : primeUnder (𝓞 k) v ∉ S := by
    rwa [← primeUnder_primeUnder k ↥(IntermediateField.fixedField H) v, hvu]
  rw [← hres]
  exact key σ ⟨v, hvS, hv⟩

end EqTop

section Hom

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {M : Type*} [CommGroup M] (u : Gal(K/k) →* M)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- The fixed field of the kernel of a homomorphism into a commutative group is abelian, hence
solvable, over the base: restriction to it is surjective, and two automorphisms of the top field
commute after restriction because their commutator is killed by the homomorphism. -/
theorem isSolvable_gal_fixedField_ker :
    IsSolvable Gal(↥(IntermediateField.fixedField u.ker)/k) := by
  refine isSolvable_of_comm fun a b => ?_
  obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k)
    (K₁ := ↥(IntermediateField.fixedField u.ker)) (E := K) a
  obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k)
    (K₁ := ↥(IntermediateField.fixedField u.ker)) (E := K) b
  rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
    ker_restrictNormalHom_fixedField, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [mul_comm (u y) (u x), mul_inv_cancel]

/-- **A homomorphism of the Galois group of a Galois extension of number fields into a commutative
group which kills every automorphism fixing a place is trivial.** -/
theorem eq_one_of_forall_mem_decompositionSet (h : ∀ σ ∈ decompositionSet k K, u σ = 1)
    (σ : Gal(K/k)) : u σ = 1 := by
  haveI := isSolvable_gal_fixedField_ker u
  have htop : u.ker = ⊤ :=
    eq_top_of_decompositionSet_subset u.ker fun ρ hρ => MonoidHom.mem_ker.mpr (h ρ hρ)
  refine MonoidHom.mem_ker.mp ?_
  rw [htop]
  exact Subgroup.mem_top σ

/-- **A homomorphism of the Galois group of a Galois extension of number fields into a commutative
group which kills every automorphism fixing a finite place away from a finite set of places of the
base field is trivial.** -/
theorem eq_one_of_forall_mem_decompositionSetOutside {S : Set (HeightOneSpectrum (𝓞 k))}
    (hS : S.Finite) (h : ∀ σ ∈ decompositionSetOutside k K S, u σ = 1) (σ : Gal(K/k)) :
    u σ = 1 := by
  haveI := isSolvable_gal_fixedField_ker u
  have htop : u.ker = ⊤ :=
    eq_top_of_decompositionSetOutside_subset u.ker hS fun ρ hρ => MonoidHom.mem_ker.mpr (h ρ hρ)
  refine MonoidHom.mem_ker.mp ?_
  rw [htop]
  exact Subgroup.mem_top σ

/-- **A homomorphism into a commutative group trivial on the automorphisms fixing a finite place and
on those fixing an infinite place is trivial.** -/
theorem eq_one_of_forall_fixing_place
    (hfin : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), σ • v = v → u σ = 1)
    (hinf : ∀ (σ : Gal(K/k)) (w : InfinitePlace K), σ • w = w → u σ = 1) (σ : Gal(K/k)) :
    u σ = 1 := by
  refine eq_one_of_forall_mem_decompositionSet u (fun ρ hρ => ?_) σ
  rcases hρ with ⟨v, hv⟩ | ⟨w, hw⟩
  · exact hfin ρ v hv
  · exact hinf ρ w hw

/-- **A homomorphism into a commutative group trivial on the automorphisms fixing a finite place
whose place below avoids a finite set is trivial.** -/
theorem eq_one_of_forall_fixing_prime_outside {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite)
    (hfin : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), primeUnder (𝓞 k) v ∉ S →
      σ • v = v → u σ = 1) (σ : Gal(K/k)) : u σ = 1 := by
  refine eq_one_of_forall_mem_decompositionSetOutside u hS (fun ρ hρ => ?_) σ
  obtain ⟨v, hvS, hv⟩ := hρ
  exact hfin ρ v hvS hv

/-- **A homomorphism into a commutative group trivial on the stabilizer of every place is
trivial.** -/
theorem eq_one_of_stabilizer_le_ker
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), stabilizer Gal(K/k) v ≤ u.ker)
    (hinf : ∀ w : InfinitePlace K, stabilizer Gal(K/k) w ≤ u.ker) (σ : Gal(K/k)) : u σ = 1 :=
  eq_one_of_forall_fixing_place u (fun _ v hv => MonoidHom.mem_ker.mp (hfin v hv))
    (fun _ w hw => MonoidHom.mem_ker.mp (hinf w hw)) σ

end Hom

end InverseGalois.CFT
