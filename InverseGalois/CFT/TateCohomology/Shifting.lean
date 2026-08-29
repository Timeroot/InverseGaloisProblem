/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Acyclic
import InverseGalois.CFT.TateCohomology.Shift

/-!
# Dimension shifting in every integer degree

A representation sits inside the functions on the group as the record of all the translates of a
vector, and the functions on the group map onto it by summing the values after undoing the
translation.  The cokernel of the first map is the shift of the representation and the kernel of
the second is its coshift, so each of the two maps is one half of a short exact sequence whose
middle term is the functions on the group.

The complete cohomology of the functions on the group vanishes in every degree, so the connecting
map of either sequence is bijective in every degree.  The complete cohomology of the shift in a
degree is therefore the complete cohomology of the representation in the following degree, and the
complete cohomology of a representation in a degree is the complete cohomology of its coshift in
the following degree.  Iterating either identification moves a statement about the complete
cohomology to any degree at all, starting from the two middle degrees where it can be read off
from the invariants and the coinvariants.

## Main definitions

* `InverseGalois.CFT.Tate.mkHom`: the morphism of representations attached to a linear map that
  commutes with the action.
* `InverseGalois.CFT.Tate.indObj`, `InverseGalois.CFT.Tate.shiftObj`,
  `InverseGalois.CFT.Tate.coshiftObj`: the functions on the group with values in a representation,
  and the shift and the coshift of a representation.
* `InverseGalois.CFT.Tate.shiftSeq`, `InverseGalois.CFT.Tate.coshiftSeq`: the two short exact
  sequences whose middle term is the functions on the group.

## Main results

* `InverseGalois.CFT.Tate.shortExact_of_linearMap`: a short complex of representations is short
  exact as soon as its underlying maps are.
* `InverseGalois.CFT.Tate.tateShiftEquiv`: **the complete cohomology of the shift in a degree is
  the complete cohomology of the representation in the following degree.**
* `InverseGalois.CFT.Tate.tateCoshiftEquiv`: **the complete cohomology of a representation in a
  degree is the complete cohomology of its coshift in the following degree.**

## Tags

Tate cohomology, dimension shifting, connecting homomorphism, induced representation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-! ### Building short exact sequences of representations -/

omit [Fintype G] in
/-- **A linear map commuting with the action is a morphism of representations.** -/
def mkHom {A B : Rep k G} (f : A →ₗ[k] B) (hf : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) : A ⟶ B where
  hom := ModuleCat.ofHom f
  comm g := by
    ext x
    exact LinearMap.congr_fun (hf g) x

omit [Fintype G] in
@[simp]
theorem mkHom_hom {A B : Rep k G} (f : A →ₗ[k] B) (hf : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) :
    (mkHom f hf).hom.hom = f := rfl

omit [Fintype G] in
/-- **A short complex of representations is short exact as soon as its underlying maps are.** -/
theorem shortExact_of_linearMap {X : ShortComplex (Rep k G)}
    (hf : Function.Injective X.f.hom.hom) (hg : Function.Surjective X.g.hom.hom)
    (hex : ∀ x : X.X₂, X.g.hom.hom x = 0 → ∃ y, X.f.hom.hom y = x) : X.ShortExact where
  exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 hex
  mono_f := (Rep.mono_iff_injective _).2 hf
  epi_g := (Rep.epi_iff_surjective _).2 hg

/-! ### The shift and the coshift as representations -/

variable (A : Rep k G)

/-- **The functions on the group with values in a representation.** -/
def indObj : Rep k G := Rep.of (inducedRep k G A)

/-- **The shift of a representation**: the cokernel of the record of all the translates. -/
def shiftObj : Rep k G := Rep.of (shiftRep A.ρ)

/-- **The coshift of a representation**: the kernel of the summation map. -/
def coshiftObj : Rep k G := Rep.of (coshiftRep A.ρ)

/-- **The functions on the group have no complete cohomology.** -/
theorem isZero_tateModule_indObj (n : ℤ) : Limits.IsZero (tateModule (indObj A) n) :=
  isZero_tateModule_inducedRep n

/-! ### The two sequences -/

/-- **The short exact sequence defining the shift**, in which a vector is replaced by the record of
all of its translates. -/
def shiftSeq : ShortComplex (Rep k G) where
  X₁ := A
  X₂ := indObj A
  X₃ := shiftObj A
  f := mkHom (coindEmb A.ρ) (coindEmb_equivariant A.ρ)
  g := mkHom (LinearMap.range (coindEmb A.ρ)).mkQ (mkQ_comp_inducedRep A.ρ)
  zero := by
    ext v
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨v, rfl⟩

omit [Fintype G] in
theorem shiftSeq_shortExact : (shiftSeq A).ShortExact :=
  shortExact_of_linearMap (coindEmb_injective A.ρ) (Submodule.mkQ_surjective _)
    fun _ hx => (Submodule.Quotient.mk_eq_zero _).1 hx

/-- **The short exact sequence defining the coshift**, in which the values of a function are summed
after undoing the translation. -/
def coshiftSeq : ShortComplex (Rep k G) where
  X₁ := coshiftObj A
  X₂ := indObj A
  X₃ := A
  f := mkHom (LinearMap.ker (augMap A.ρ)).subtype (subtype_comp_coshiftRep A.ρ)
  g := mkHom (augMap A.ρ) (augMap_comp_inducedRep A.ρ)
  zero := by
    ext x
    exact x.2

theorem coshiftSeq_shortExact : (coshiftSeq A).ShortExact :=
  shortExact_of_linearMap (Submodule.injective_subtype _) (augMap_surjective A.ρ)
    fun x hx => ⟨⟨x, hx⟩, rfl⟩

/-! ### The two identifications -/

/-- **The complete cohomology of the shift in a degree is the complete cohomology of the
representation in the following degree.** -/
def tateShiftEquiv (n : ℤ) : tateModule (shiftObj A) n ≃ₗ[k] tateModule A (n + 1) :=
  LinearEquiv.ofBijective (tateδ (shiftSeq_shortExact A) n).hom
    (bijective_tateδ (shiftSeq_shortExact A) n (isZero_tateModule_indObj A n)
      (isZero_tateModule_indObj A (n + 1)))

/-- **The complete cohomology of a representation in a degree is the complete cohomology of its
coshift in the following degree.** -/
def tateCoshiftEquiv (n : ℤ) : tateModule A n ≃ₗ[k] tateModule (coshiftObj A) (n + 1) :=
  LinearEquiv.ofBijective (tateδ (coshiftSeq_shortExact A) n).hom
    (bijective_tateδ (coshiftSeq_shortExact A) n (isZero_tateModule_indObj A n)
      (isZero_tateModule_indObj A (n + 1)))

end

end InverseGalois.CFT.Tate
