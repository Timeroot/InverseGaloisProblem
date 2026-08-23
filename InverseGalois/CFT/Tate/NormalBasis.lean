/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.CyclicInduced
import InverseGalois.CFT.Tate.InducedLattice

/-!
# The additive group of a Galois extension is induced

A finite group acting faithfully on a field makes the field a Galois extension of the subfield it
fixes, and the normal basis theorem produces an element whose orbit is a basis.  Reading an element
of the field in that basis identifies the field with the functions on the group, the action becoming
translation of the argument.  For a cyclic group this is the module induced from the trivial action,
whose Tate groups vanish; so the additive group of a Galois extension with cyclic group has
vanishing Tate groups and Herbrand quotient one.

## Main definitions

* `InverseGalois.CFT.normalElt`: an element whose orbit is a basis of the field over the fixed
  field.
* `InverseGalois.CFT.normalBasisOfGroup`: that orbit, indexed by the group.
* `InverseGalois.CFT.normalCoordEquiv`: the identification of the functions on the group with the
  field.

## Main results

* `InverseGalois.CFT.normalCoordEquiv_equivariant`: **the identification turns the action into
  translation of the argument.**
* `InverseGalois.CFT.subsingleton_tateH0_of_normalBasis`,
  `InverseGalois.CFT.subsingleton_tateHm1_of_normalBasis`: **both Tate groups of the additive group
  of a Galois extension with cyclic group vanish.**
* `InverseGalois.CFT.herbrand_eq_one_of_normalBasis`: **its Herbrand quotient is one.**

## Tags

Galois extension, normal basis, induced module, Tate cohomology, Herbrand quotient
-/

namespace InverseGalois.CFT

variable {G A : Type*} [Group G] [Fintype G] [Field A] [MulSemiringAction G A] [FaithfulSMul G A]

/-! ### The orbit of a normal basis element -/

variable (G A) in
/-- **An element whose orbit is a basis of the field over the fixed field.** -/
noncomputable def normalElt : A :=
  IsGalois.normalBasis ↥(FixedPoints.subfield G A) A 1

variable (G A) in
/-- **The orbit of a normal basis element, indexed by the group.** -/
noncomputable def normalBasisOfGroup :
    Module.Basis G ↥(FixedPoints.subfield G A) A :=
  (IsGalois.normalBasis ↥(FixedPoints.subfield G A) A).reindex
    (FixedPoints.toAlgAutMulEquiv G A).symm.toEquiv

@[simp]
theorem normalBasisOfGroup_apply (g : G) : normalBasisOfGroup G A g = g • normalElt G A := by
  rw [normalBasisOfGroup, Module.Basis.reindex_apply, IsGalois.normalBasis_apply]
  rfl

omit [Fintype G] [FaithfulSMul G A] in
/-- An automorphism moves an element of the fixed field past a scalar multiplication. -/
theorem smul_smul_fixed (σ : G) (c : ↥(FixedPoints.subfield G A)) (x : A) :
    σ • (c • x) = c • (σ • x) := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
  congr 1
  exact c.2 σ

/-! ### The coordinates of the normal basis -/

variable (G A) in
/-- **The identification of the functions on the group with the field**, reading an element in the
orbit of a normal basis element. -/
noncomputable def normalCoordEquiv : (G → ↥(FixedPoints.subfield G A)) ≃+ A :=
  (normalBasisOfGroup G A).equivFun.symm.toAddEquiv

theorem normalCoordEquiv_apply (f : G → ↥(FixedPoints.subfield G A)) :
    normalCoordEquiv G A f = ∑ g : G, f g • normalBasisOfGroup G A g :=
  (normalBasisOfGroup G A).equivFun_symm_apply f

/-- **The identification turns the action into translation of the argument.** -/
theorem normalCoordEquiv_equivariant (σ : G) (f : G → ↥(FixedPoints.subfield G A)) :
    normalCoordEquiv G A (translateAut σ f) = σ • normalCoordEquiv G A f := by
  rw [normalCoordEquiv_apply, normalCoordEquiv_apply, Finset.smul_sum]
  simp only [translateAut_apply]
  refine Fintype.sum_equiv (Equiv.mulLeft σ⁻¹) _ _ fun g => ?_
  show f (σ⁻¹ * g) • normalBasisOfGroup G A g
    = σ • f (σ⁻¹ * g) • normalBasisOfGroup G A (σ⁻¹ * g)
  rw [smul_smul_fixed, normalBasisOfGroup_apply, normalBasisOfGroup_apply, smul_smul]
  simp

/-! ### The field as an induced module -/

variable {σ : G} {d : ℕ} [NeZero d]

/-- **The field is the module induced from the trivial action of a cyclic group on the fixed
field.** -/
noncomputable def normalIndEquiv (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) : (ZMod d → ↥(FixedPoints.subfield G A)) ≃+ A :=
  (cyclicIndEquiv hgen hσ hcard).trans (normalCoordEquiv G A)

theorem normalIndEquiv_equivariant (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) {σA : A ≃+ A} (hσA : ∀ x : A, σA x = σ • x)
    (f : ZMod d → ↥(FixedPoints.subfield G A)) :
    normalIndEquiv hgen hσ hcard (indAut (1 : ↥(FixedPoints.subfield G A) ≃+ _) d f)
      = σA (normalIndEquiv hgen hσ hcard f) := by
  rw [normalIndEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, cyclicIndEquiv_equivariant,
    normalCoordEquiv_equivariant, hσA]

/-- **The upper Tate group of the additive group of a Galois extension with cyclic group
vanishes.** -/
theorem subsingleton_tateH0_of_normalBasis (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hσ : σ ^ d = 1) (hcard : Nat.card G = d) {σA : A ≃+ A} (hσA : ∀ x : A, σA x = σ • x) :
    Subsingleton (tateH0 σA d) :=
  subsingleton_tateH0_of_indAutEquiv (normalIndEquiv hgen hσ hcard)
    (normalIndEquiv_equivariant hgen hσ hcard hσA)

/-- **The lower Tate group of the additive group of a Galois extension with cyclic group
vanishes.** -/
theorem subsingleton_tateHm1_of_normalBasis (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hσ : σ ^ d = 1) (hcard : Nat.card G = d) {σA : A ≃+ A} (hσA : ∀ x : A, σA x = σ • x) :
    Subsingleton (tateHm1 σA d) :=
  subsingleton_tateHm1_of_indAutEquiv (normalIndEquiv hgen hσ hcard)
    (normalIndEquiv_equivariant hgen hσ hcard hσA)

/-- The Tate groups of the additive group of a Galois extension with cyclic group are finite. -/
theorem finite_tate_of_normalBasis (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) {σA : A ≃+ A} (hσA : ∀ x : A, σA x = σ • x) :
    Finite (tateH0 σA d) ∧ Finite (tateHm1 σA d) :=
  haveI := subsingleton_tateH0_of_normalBasis hgen hσ hcard hσA
  haveI := subsingleton_tateHm1_of_normalBasis hgen hσ hcard hσA
  ⟨Finite.of_subsingleton, Finite.of_subsingleton⟩

/-- **The Herbrand quotient of the additive group of a Galois extension with cyclic group is
one.** -/
theorem herbrand_eq_one_of_normalBasis (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) {σA : A ≃+ A} (hσA : ∀ x : A, σA x = σ • x) : herbrand σA d = 1 := by
  haveI := subsingleton_tateH0_of_normalBasis hgen hσ hcard hσA
  haveI := subsingleton_tateHm1_of_normalBasis hgen hσ hcard hσA
  rw [herbrand, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩,
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
  norm_num

end InverseGalois.CFT
