/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CentralLift

/-!
# Lifting a surjection through an extension with abelian kernel

Let `f : G →* H` be a homomorphism of groups and `t : H → G` a set-theoretic section of `f`.  The
factor set of `t` measures the failure of `t` to be a homomorphism.  When the kernel of `f` is
central it obeys the two-cocycle identity for the trivial action, and correcting a section by a
trivialising cochain lifts a homomorphism into `H` to a homomorphism into `G`; that is the content
of `InverseGalois.CFT.GroupCohomology.CentralLift`.

Here the kernel is only assumed abelian.  Conjugation by the section then makes it a module over
`H`, and over any group `Γ` mapping to `H`, and the factor set obeys the two-cocycle identity for
*that* action: the two bracketings of a triple product of section values differ by conjugating one
factor-set contribution past a section value.  The identity is an identity in `G`, and it becomes
the two-cocycle identity of the ambient library once the kernel is presented as an abstract abelian
group `A` with an injection `ι : A →* G`.  Presenting it that way, rather than as the subgroup
`f.ker` itself, is what lets a caller supply the module structure it already has — a Galois module,
say — instead of having to transport one onto a subtype.

A homomorphism `π : Γ →* H` therefore has an obstruction class: the factor set pulled back along
`π`, read in `A`.  It is a coboundary exactly when `π` lifts to a homomorphism `Γ →* G`, and when
the kernel additionally lies inside the Frattini subgroup of a finite `G` and `π` is surjective,
the lift is automatically surjective.  This is the group-theoretic engine of an embedding problem
with abelian, not necessarily central, kernel.

## Main results

* `InverseGalois.CFT.sectionFactorSet_cocycle_conj`: the factor set of a section satisfies the
  two-cocycle identity for the conjugation action, with no hypothesis on the kernel.
* `InverseGalois.CFT.isMulCocycle₂_of_sectionFactorSet`: **the factor set pulled back along a
  homomorphism into `H` and read in an abelian kernel is a two-cocycle.**
* `InverseGalois.CFT.exists_hom_comp_eq_of_sectionFactorSet_eq_conj`: **a homomorphism whose
  pulled-back factor set is a coboundary lifts through an extension with abelian kernel.**
* `InverseGalois.CFT.isMulCoboundary₂_of_hom_comp_eq`: the converse, **the pulled-back factor set
  of a homomorphism that does lift is a coboundary.**
* `InverseGalois.CFT.exists_surjective_hom_comp_eq_of_sectionFactorSet_eq_conj`: **a surjection
  whose pulled-back factor set is a coboundary lifts to a surjection** through an extension with
  abelian Frattini kernel.

## Tags

abelian extension, factor set, two-cocycle, conjugation action, Frattini subgroup, embedding
problem
-/

open groupCohomology

namespace InverseGalois.CFT

section Conj

variable {G H : Type*} [Group G] [Group H]

/-- **The factor set of a section satisfies the two-cocycle identity for the conjugation action.**
Both bracketings of a triple product of section values reduce the product to two factor-set
contributions times the section at the product; in the bracketing which multiplies the last two
factors first, the inner contribution has to be moved past a section value, and conjugating it
there is exactly the action for which the identity is the two-cocycle identity. -/
theorem sectionFactorSet_cocycle_conj (t : H → G) (a b c : H) :
    sectionFactorSet t a b * sectionFactorSet t (a * b) c
      = t a * sectionFactorSet t b c * (t a)⁻¹ * sectionFactorSet t a (b * c) := by
  simp only [sectionFactorSet]
  rw [← mul_assoc a b c]
  group

end Conj

section AbelianKernel

variable {G H Γ A : Type*} [Group G] [Group H] [Group Γ] [CommGroup A]
  [MulDistribMulAction Γ A]

/-- **The factor set of a section, pulled back along a homomorphism and read in an abelian group
mapping to the kernel, is a two-cocycle.**  The identity is the one satisfied by the factor set in
the ambient group, transported through the injection; the two factors on the left commute because
they come from an abelian group. -/
theorem isMulCocycle₂_of_sectionFactorSet (π : Γ →* H) {t : H → G}
    {ι : A →* G} (hinj : Function.Injective ι)
    (hconj : ∀ (x : Γ) (a : A), ι (x • a) = t (π x) * ι a * (t (π x))⁻¹)
    {α : Γ × Γ → A} (hα : ∀ x y : Γ, ι (α (x, y)) = sectionFactorSet t (π x) (π y)) :
    IsMulCocycle₂ α := by
  intro x y z
  refine hinj ?_
  rw [mul_comm (α (x * y, z)) (α (x, y)), map_mul ι, map_mul ι, hconj, hα, hα, hα, hα,
    map_mul π x y, map_mul π y z]
  exact sectionFactorSet_cocycle_conj t (π x) (π y) (π z)

/-- **A homomorphism whose pulled-back factor set is a coboundary lifts through an extension with
abelian kernel.**  Correcting the section `t` by the trivialising cochain yields the map
`x ↦ (ι (c x))⁻¹ * t (π x)`, whose multiplicativity is exactly the coboundary relation once the
correction terms are conjugated past the section values, and which lifts `π` because the correction
takes values in the kernel. -/
theorem exists_hom_comp_eq_of_sectionFactorSet_eq_conj (f : G →* H) (π : Γ →* H)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    {ι : A →* G} (hker : ∀ a : A, ι a ∈ f.ker)
    (hconj : ∀ (x : Γ) (a : A), ι (x • a) = t (π x) * ι a * (t (π x))⁻¹)
    {α : Γ × Γ → A} (hα : ∀ x y : Γ, ι (α (x, y)) = sectionFactorSet t (π x) (π y))
    (hcob : IsMulCoboundary₂ α) :
    ∃ φ : Γ →* G, ∀ x, f (φ x) = π x := by
  obtain ⟨c, hc⟩ := hcob
  have hmul : ∀ x y : Γ, (ι (c x))⁻¹ * t (π x) * ((ι (c y))⁻¹ * t (π y))
      = (ι (c (x * y)))⁻¹ * t (π (x * y)) := by
    intro x y
    have hcomm : (ι (c x))⁻¹ * (ι (c (x * y)))⁻¹ = (ι (c (x * y)))⁻¹ * (ι (c x))⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, ← map_mul ι, ← map_mul ι, mul_comm (c (x * y)) (c x)]
    have hF : sectionFactorSet t (π x) (π y)
        = t (π x) * ι (c y) * (t (π x))⁻¹ * (ι (c (x * y)))⁻¹ * ι (c x) := by
      rw [← hα x y, ← hc x y, div_eq_mul_inv, map_mul ι, map_mul ι, map_inv, hconj]
    have hST : t (π x) * t (π y) = sectionFactorSet t (π x) (π y) * t (π (x * y)) := by
      rw [map_mul π]
      exact mul_eq_sectionFactorSet_mul t (π x) (π y)
    calc (ι (c x))⁻¹ * t (π x) * ((ι (c y))⁻¹ * t (π y))
        = (ι (c x))⁻¹ * (t (π x) * ι (c y) * (t (π x))⁻¹)⁻¹ * (t (π x) * t (π y)) := by group
      _ = (ι (c x))⁻¹ * (t (π x) * ι (c y) * (t (π x))⁻¹)⁻¹
            * (sectionFactorSet t (π x) (π y) * t (π (x * y))) := by rw [hST]
      _ = (ι (c x))⁻¹ * (t (π x) * ι (c y) * (t (π x))⁻¹)⁻¹
            * (t (π x) * ι (c y) * (t (π x))⁻¹ * (ι (c (x * y)))⁻¹ * ι (c x)
              * t (π (x * y))) := by rw [hF]
      _ = (ι (c x))⁻¹ * (ι (c (x * y)))⁻¹ * (ι (c x) * t (π (x * y))) := by group
      _ = (ι (c (x * y)))⁻¹ * (ι (c x))⁻¹ * (ι (c x) * t (π (x * y))) := by rw [hcomm]
      _ = (ι (c (x * y)))⁻¹ * t (π (x * y)) := by group
  refine ⟨MonoidHom.mk' (fun x => (ι (c x))⁻¹ * t (π x)) (fun x y => (hmul x y).symm),
    fun x => ?_⟩
  show f ((ι (c x))⁻¹ * t (π x)) = π x
  rw [map_mul, map_inv, MonoidHom.mem_ker.1 (hker (c x)), inv_one, one_mul, ht]

/-- **The pulled-back factor set of a homomorphism that lifts through an extension with abelian
kernel is a coboundary.**  The trivialising cochain is the difference between the section and the
lift, which lies in the kernel and hence comes from the abelian group; the lift being a
homomorphism is exactly what makes the correction terms cancel. -/
theorem isMulCoboundary₂_of_hom_comp_eq (f : G →* H) (π : Γ →* H)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    {ι : A →* G} (hinj : Function.Injective ι) (hrange : ∀ g ∈ f.ker, ∃ a : A, ι a = g)
    (hconj : ∀ (x : Γ) (a : A), ι (x • a) = t (π x) * ι a * (t (π x))⁻¹)
    {α : Γ × Γ → A} (hα : ∀ x y : Γ, ι (α (x, y)) = sectionFactorSet t (π x) (π y))
    {φ : Γ →* G} (hφ : ∀ x, f (φ x) = π x) :
    IsMulCoboundary₂ α := by
  choose c hc using fun x : Γ => hrange _ (mem_ker_mul_inv f ht π hφ x)
  refine ⟨c, fun x y => hinj ?_⟩
  have hcm : Commute (ι (c x)) (ι (c (x * y))) := by
    show ι (c x) * ι (c (x * y)) = ι (c (x * y)) * ι (c x)
    rw [← map_mul ι, ← map_mul ι, mul_comm]
  have hgoal : t (π x) * ι (c y) * (t (π x))⁻¹ * (ι (c (x * y)))⁻¹ * ι (c x)
      = sectionFactorSet t (π x) (π y) := by
    calc t (π x) * ι (c y) * (t (π x))⁻¹ * (ι (c (x * y)))⁻¹ * ι (c x)
        = t (π x) * ι (c y) * (t (π x))⁻¹ * ((ι (c (x * y)))⁻¹ * ι (c x)) :=
          mul_assoc (t (π x) * ι (c y) * (t (π x))⁻¹) _ _
      _ = t (π x) * ι (c y) * (t (π x))⁻¹ * (ι (c x) * (ι (c (x * y)))⁻¹) := by
          rw [hcm.inv_right.eq]
      _ = sectionFactorSet t (π x) (π y) := by
          rw [hc x, hc y, hc (x * y), sectionFactorSet, map_mul π, map_mul φ]
          group
  rw [hα, div_eq_mul_inv, map_mul ι, map_mul ι, map_inv, hconj]
  exact hgoal

/-- **A surjection whose pulled-back factor set is a coboundary lifts to a surjection through an
extension with abelian Frattini kernel.**  This is a proper solution of the embedding problem posed
by the extension and the given surjection. -/
theorem exists_surjective_hom_comp_eq_of_sectionFactorSet_eq_conj [Finite G] (f : G →* H)
    (hfr : f.ker ≤ frattini G) (π : Γ →* H) (hπ : Function.Surjective π)
    {t : H → G} (ht : ∀ h, f (t h) = h)
    {ι : A →* G} (hker : ∀ a : A, ι a ∈ f.ker)
    (hconj : ∀ (x : Γ) (a : A), ι (x • a) = t (π x) * ι a * (t (π x))⁻¹)
    {α : Γ × Γ → A} (hα : ∀ x y : Γ, ι (α (x, y)) = sectionFactorSet t (π x) (π y))
    (hcob : IsMulCoboundary₂ α) :
    ∃ φ : Γ →* G, Function.Surjective φ ∧ ∀ x, f (φ x) = π x := by
  obtain ⟨φ, hφ⟩ := exists_hom_comp_eq_of_sectionFactorSet_eq_conj f π ht hker hconj hα hcob
  exact ⟨φ, surjective_of_le_frattini hfr hπ hφ, hφ⟩

end AbelianKernel

end InverseGalois.CFT
