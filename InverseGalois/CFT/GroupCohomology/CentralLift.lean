/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Lifting a surjection through a central extension along a trivialised factor set

Let `f : G →* H` be a homomorphism of groups whose kernel is central, and let `t : H → G` be a
set-theoretic section of `f`.  The *factor set* of `t` measures the failure of `t` to be a
homomorphism: it is the element `t h * t h' * (t (h * h'))⁻¹`, which lies in the kernel of `f`.
Because the kernel is central, the factor set obeys the two-cocycle identity for the trivial
action.

Given a further group `Γ` and a homomorphism `π : Γ →* H`, the factor set pulled back along `π`
is a two-cocycle on `Γ`.  If that cocycle is a coboundary — that is, if it can be written as
`c x * c y * (c (x * y))⁻¹` for a function `c : Γ → G` taking values in the kernel — then
correcting the section by `c` produces an honest homomorphism `φ : Γ →* G` lifting `π`.  When the
kernel additionally lies inside the Frattini subgroup of `G` and `π` is surjective, the lift is
automatically surjective, since its image together with the kernel generates `G` and the Frattini
subgroup consists of non-generating elements.

This is the group-theoretic engine of the embedding problem: the arithmetic input is exactly the
statement that the pulled-back factor set is a coboundary, and this file converts that statement
into a proper solution.

## Main definitions

* `InverseGalois.CFT.sectionFactorSet`: the factor set of a set-theoretic section.

## Main results

* `InverseGalois.CFT.sectionFactorSet_mem_ker`: the factor set takes values in the kernel.
* `InverseGalois.CFT.sectionFactorSet_cocycle`: for a central kernel the factor set is a
  two-cocycle for the trivial action.
* `InverseGalois.CFT.exists_hom_comp_eq_of_sectionFactorSet_eq`: **a homomorphism whose pulled-back
  factor set is a coboundary lifts through a central extension.**
* `InverseGalois.CFT.surjective_of_le_frattini`: a lift of a surjection through a surjection whose
  kernel lies in the Frattini subgroup is itself surjective.
* `InverseGalois.CFT.exists_surjective_hom_comp_eq_of_sectionFactorSet_eq`: **the two combined: a
  surjection whose pulled-back factor set is a coboundary lifts to a surjection.**
* `InverseGalois.CFT.sectionFactorSet_eq_of_hom_comp_eq`: the converse, **the pulled-back factor
  set of a homomorphism that does lift is a coboundary.**

## Tags

central extension, factor set, two-cocycle, Frattini subgroup, embedding problem
-/

namespace InverseGalois.CFT

section FactorSet

variable {G H : Type*} [Group G] [Group H]

/-- The factor set of a set-theoretic section `t` of a surjection: the element measuring the
failure of `t` to be a homomorphism at a pair of arguments. -/
def sectionFactorSet (t : H → G) (h h' : H) : G := t h * t h' * (t (h * h'))⁻¹

/-- The factor set of a set-theoretic section of `f` takes its values in the kernel of `f`. -/
theorem sectionFactorSet_mem_ker (f : G →* H) {t : H → G} (ht : ∀ h, f (t h) = h) (h h' : H) :
    sectionFactorSet t h h' ∈ f.ker := by
  rw [MonoidHom.mem_ker, sectionFactorSet, map_mul, map_mul, map_inv, ht, ht, ht, mul_inv_cancel]

/-- A product of two values of a section is its value at the product, corrected by the factor
set. -/
theorem mul_eq_sectionFactorSet_mul (t : H → G) (h h' : H) :
    t h * t h' = sectionFactorSet t h h' * t (h * h') := by
  rw [sectionFactorSet, inv_mul_cancel_right]

/-- **For a central kernel the factor set of a section satisfies the two-cocycle identity for the
trivial action.**  Both bracketings of a triple product of section values reduce the product to a
factor-set contribution times the section at the product, and the two contributions agree because
the factor set is central and the product of section values is associative. -/
theorem sectionFactorSet_cocycle (f : G →* H) (hZ : f.ker ≤ Subgroup.center G)
    {t : H → G} (ht : ∀ h, f (t h) = h) (a b c : H) :
    sectionFactorSet t a b * sectionFactorSet t (a * b) c
      = sectionFactorSet t b c * sectionFactorSet t a (b * c) := by
  have hcom : ∀ h h' : H, ∀ g : G, Commute (sectionFactorSet t h h') g := fun h h' g =>
    (Subgroup.mem_center_iff.1 (hZ (sectionFactorSet_mem_ker f ht h h')) g).symm
  have h1 : t a * t b * t c
      = sectionFactorSet t a b * sectionFactorSet t (a * b) c * t (a * b * c) := by
    rw [mul_eq_sectionFactorSet_mul t a b, mul_assoc, mul_eq_sectionFactorSet_mul t (a * b) c,
      ← mul_assoc]
  have h2 : t a * t b * t c
      = sectionFactorSet t b c * sectionFactorSet t a (b * c) * t (a * b * c) := by
    rw [mul_assoc, mul_eq_sectionFactorSet_mul t b c, ← mul_assoc, ((hcom b c (t a)).symm).eq,
      mul_assoc, mul_eq_sectionFactorSet_mul t a (b * c), ← mul_assoc, ← mul_assoc, mul_assoc a b c]
  exact mul_right_cancel (h1.symm.trans h2)

end FactorSet

section Lift

variable {G H Γ : Type*} [Group G] [Group H] [Group Γ]

/-- **A homomorphism whose pulled-back factor set is a coboundary lifts through a central
extension.**  Correcting the section `t` by the cochain `c` yields the map `x ↦ t (π x) * (c x)⁻¹`,
whose multiplicativity is exactly the coboundary relation once the central values of `c` are moved
past the section, and which lifts `π` because `c` takes values in the kernel. -/
theorem exists_hom_comp_eq_of_sectionFactorSet_eq (f : G →* H) (hZ : f.ker ≤ Subgroup.center G)
    (π : Γ →* H) {t : H → G} (ht : ∀ h, f (t h) = h)
    {c : Γ → G} (hc : ∀ x, c x ∈ f.ker)
    (hcob : ∀ x y : Γ, sectionFactorSet t (π x) (π y) = c x * c y * (c (x * y))⁻¹) :
    ∃ φ : Γ →* G, ∀ x, f (φ x) = π x := by
  have hcom : ∀ (x : Γ) (g : G), Commute (c x) g := fun x g =>
    (Subgroup.mem_center_iff.1 (hZ (hc x)) g).symm
  have hmul : ∀ x y : Γ, t (π x) * (c x)⁻¹ * (t (π y) * (c y)⁻¹)
      = t (π (x * y)) * (c (x * y))⁻¹ := by
    intro x y
    have hfs : t (π x) * t (π y) * (t (π x * π y))⁻¹ = c x * c y * (c (x * y))⁻¹ := hcob x y
    rw [← map_mul] at hfs
    have e2 : t (π x) * t (π y) = c x * c y * (c (x * y))⁻¹ * t (π (x * y)) :=
      mul_inv_eq_iff_eq_mul.mp hfs
    have e1 : t (π x) * (c x)⁻¹ * (t (π y) * (c y)⁻¹)
        = t (π x) * t (π y) * ((c x)⁻¹ * (c y)⁻¹) := by
      rw [mul_assoc, ← mul_assoc ((c x)⁻¹), ((hcom x (t (π y))).inv_left).eq, mul_assoc,
        ← mul_assoc]
    have hinvmul : (c x)⁻¹ * (c y)⁻¹ = (c x * c y)⁻¹ := by
      rw [mul_inv_rev, ((hcom x (c y)).inv_inv).eq]
    have hZW : c x * c y * (c (x * y))⁻¹ * ((c x)⁻¹ * (c y)⁻¹) = (c (x * y))⁻¹ := by
      rw [hinvmul, ← ((hcom (x * y) (c x * c y)).inv_left).eq, mul_assoc, mul_inv_cancel, mul_one]
    have hZT : Commute (c x * c y * (c (x * y))⁻¹) (t (π (x * y))) :=
      ((hcom x _).mul_left (hcom y _)).mul_left ((hcom (x * y) _).inv_left)
    rw [e1, e2, hZT.eq, mul_assoc, hZW]
  refine ⟨MonoidHom.mk' (fun x => t (π x) * (c x)⁻¹) (fun x y => (hmul x y).symm), fun x => ?_⟩
  show f (t (π x) * (c x)⁻¹) = π x
  rw [map_mul, map_inv, ht, MonoidHom.mem_ker.1 (hc x), inv_one, mul_one]

/-- The difference between a section and a lift lies in the kernel. -/
theorem mem_ker_mul_inv (f : G →* H) {t : H → G} (ht : ∀ h, f (t h) = h) (π : Γ →* H)
    {φ : Γ →* G} (hφ : ∀ x, f (φ x) = π x) (x : Γ) : t (π x) * (φ x)⁻¹ ∈ f.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, ht, hφ, mul_inv_cancel]

/-- **The pulled-back factor set of a homomorphism that lifts through a central extension is a
coboundary.**  The cochain is the difference between the section and the lift, which lies in the
kernel and is therefore central; the lift being a homomorphism is exactly what makes the
correction terms cancel. -/
theorem sectionFactorSet_eq_of_hom_comp_eq (f : G →* H) (hZ : f.ker ≤ Subgroup.center G)
    (π : Γ →* H) {t : H → G} (ht : ∀ h, f (t h) = h)
    {φ : Γ →* G} (hφ : ∀ x, f (φ x) = π x) (x y : Γ) :
    sectionFactorSet t (π x) (π y)
      = (t (π x) * (φ x)⁻¹) * (t (π y) * (φ y)⁻¹) * (t (π (x * y)) * (φ (x * y))⁻¹)⁻¹ := by
  have hcom : ∀ (z : Γ) (g : G), Commute (t (π z) * (φ z)⁻¹) g := fun z g =>
    (Subgroup.mem_center_iff.1 (hZ (mem_ker_mul_inv f ht π hφ z)) g).symm
  set c : Γ → G := fun z => t (π z) * (φ z)⁻¹ with hcdef
  have ht' : ∀ z : Γ, t (π z) = c z * φ z := fun z => (inv_mul_cancel_right _ _).symm
  have hL : sectionFactorSet t (π x) (π y) * t (π x * π y) = t (π x) * t (π y) :=
    (mul_eq_sectionFactorSet_mul t (π x) (π y)).symm
  have hR : (c x * c y * (c (x * y))⁻¹) * t (π x * π y) = t (π x) * t (π y) := by
    rw [← map_mul, ht' (x * y), mul_assoc, inv_mul_cancel_left, map_mul, ht' x, ht' y,
      mul_assoc (c x), ← mul_assoc (c y), (hcom y (φ x)).eq, mul_assoc (φ x), ← mul_assoc (c x)]
  exact mul_right_cancel (hL.trans hR.symm)

/-- **A lift of a surjection through a surjection whose kernel lies in the Frattini subgroup is
itself surjective.**  Every element of the source differs from a value of the lift by an element of
the kernel, so the image of the lift together with the kernel generates everything; the Frattini
subgroup consists of non-generating elements, so the image is already everything. -/
theorem surjective_of_le_frattini [Finite G] {f : G →* H} (hfr : f.ker ≤ frattini G)
    {π : Γ →* H} (hπ : Function.Surjective π) {φ : Γ →* G} (hφ : ∀ x, f (φ x) = π x) :
    Function.Surjective φ := by
  have hsup : φ.range ⊔ f.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hx⟩ := hπ (f g)
    have hmem : (φ x)⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hx, inv_mul_cancel]
    have hg := Subgroup.mul_mem_sup (φ.mem_range.mpr ⟨x, rfl⟩) hmem
    rwa [mul_inv_cancel_left] at hg
  rw [← MonoidHom.range_eq_top]
  exact frattini_nongenerating (eq_top_iff.mpr (hsup.ge.trans (sup_le_sup_left hfr _)))

/-- **A surjection whose pulled-back factor set is a coboundary lifts to a surjection through a
central extension with Frattini kernel.**  This is a solution of the embedding problem posed by the
extension and the given surjection. -/
theorem exists_surjective_hom_comp_eq_of_sectionFactorSet_eq [Finite G] (f : G →* H)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    (π : Γ →* H) (hπ : Function.Surjective π) {t : H → G} (ht : ∀ h, f (t h) = h)
    {c : Γ → G} (hc : ∀ x, c x ∈ f.ker)
    (hcob : ∀ x y : Γ, sectionFactorSet t (π x) (π y) = c x * c y * (c (x * y))⁻¹) :
    ∃ φ : Γ →* G, Function.Surjective φ ∧ ∀ x, f (φ x) = π x := by
  obtain ⟨φ, hφ⟩ := exists_hom_comp_eq_of_sectionFactorSet_eq f hZ π ht hc hcob
  exact ⟨φ, surjective_of_le_frattini hfr hπ hφ, hφ⟩

end Lift

end InverseGalois.CFT
