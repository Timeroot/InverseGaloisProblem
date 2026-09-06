/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DeltaShift

/-!
# The comparison of a split extension with the sequence defining the shift

An extension whose sub is a direct summand of its middle term, as a module, compares with the
sequence defining the shift of that sub.  Reading all the translates of an element of the middle
term through a retraction gives an equivariant map into the functions on the group which restores
the embedding of the sub, and modulo the translates of the sub the result depends only on the image
in the quotient, because two elements with the same image differ by an element of the sub.  The
comparison so obtained is the identity on the sub.

The connecting map of such an extension is therefore the map induced on the quotients followed by
the identification of the shift, with no connecting map left in it.  Together with the dual
statement for the coshift this covers the two ways of removing a connecting map, and each is
available in the range of degrees where the other is not.

## Main definitions

* `InverseGalois.CFT.Tate.retractMid`: all the translates of an element of the middle term, read on
  the sub through a retraction.
* `InverseGalois.CFT.Tate.retractSeqHom`: the comparison with the sequence defining the shift.

## Main results

* `InverseGalois.CFT.Tate.tateδ_eq_retractQuot`: **the connecting map of an extension whose sub is a
  direct summand of its middle term is the induced map on the quotients followed by the
  identification of the shift.**

## Tags

Tate cohomology, connecting homomorphism, dimension shifting, split extension
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
  (r : ↥X.X₂.V →ₗ[k] ↥X.X₁.V) (hr : ∀ a : ↥X.X₁.V, r (X.f.hom.hom a) = a)
  (s : ↥X.X₃.V →ₗ[k] ↥X.X₂.V) (hs : ∀ v : ↥X.X₃.V, X.g.hom.hom (s v) = v)

/-! ### The translates read through a retraction -/

/-- **All the translates of an element of the middle term of an extension, read on the sub through
a retraction.** -/
def retractMid : ↥X.X₂.V →ₗ[k] ↥(indObj X.X₁).V := r.compLeft G ∘ₗ coindEmb X.X₂.ρ

omit [Finite G] in
theorem retractMid_apply (x : ↥X.X₂.V) (g : G) : retractMid r x g = r (X.X₂.ρ g x) := rfl

omit [Finite G] in
/-- **Reading the translates through a retraction is equivariant.** -/
theorem retractMid_equivariant (h : G) :
    retractMid r ∘ₗ X.X₂.ρ h = (indObj X.X₁).ρ h ∘ₗ retractMid r := by
  refine LinearMap.ext fun x => funext fun g => ?_
  show r (X.X₂.ρ g (X.X₂.ρ h x)) = r (X.X₂.ρ (g * h) x)
  rw [map_mul, Module.End.mul_apply]

omit [Finite G] in
include hr in
/-- **On the sub, reading the translates through a retraction is the embedding into the functions on
the group.** -/
theorem retractMid_f (a : ↥X.X₁.V) : retractMid r (X.f.hom.hom a) = coindEmb X.X₁.ρ a :=
  funext fun g => by
    have h : X.f.hom.hom (X.X₁.ρ g a) = X.X₂.ρ g (X.f.hom.hom a) :=
      LinearMap.congr_fun (hom_equivariant X.f g) a
    show r (X.X₂.ρ g (X.f.hom.hom a)) = X.X₁.ρ g a
    rw [← h, hr]

/-- **The comparison of the quotient of an extension with the shift of its sub.** -/
def retractQuot : ↥X.X₃.V →ₗ[k] ↥(shiftObj X.X₁).V :=
  (LinearMap.range (coindEmb X.X₁.ρ)).mkQ ∘ₗ retractMid r ∘ₗ s

omit [Finite G] in
include hX hr hs in
/-- **Modulo the translates of the sub, reading the translates through a retraction depends only on
the image in the quotient.** -/
theorem mkQ_retractMid (x : ↥X.X₂.V) :
    Submodule.Quotient.mk (p := LinearMap.range (coindEmb X.X₁.ρ)) (retractMid r x)
      = retractQuot r s (X.g.hom.hom x) := by
  obtain ⟨a, ha⟩ : x - s (X.g.hom.hom x) ∈ LinearMap.range X.f.hom.hom := by
    rw [shortExact_range_eq_ker hX, LinearMap.mem_ker, map_sub, hs, sub_self]
  have hx : retractMid r x - retractMid r (s (X.g.hom.hom x)) = coindEmb X.X₁.ρ a := by
    rw [← map_sub, ← ha, retractMid_f r hr]
  show Submodule.Quotient.mk (p := LinearMap.range (coindEmb X.X₁.ρ)) (retractMid r x)
    = Submodule.Quotient.mk (p := LinearMap.range (coindEmb X.X₁.ρ))
      (retractMid r (s (X.g.hom.hom x)))
  refine (Submodule.Quotient.eq _).2 ?_
  rw [hx]
  exact ⟨a, rfl⟩

omit [Finite G] in
include hX hr hs in
/-- **The comparison of the quotient with the shift of the sub is equivariant.** -/
theorem retractQuot_equivariant (h : G) :
    retractQuot r s ∘ₗ X.X₃.ρ h = (shiftObj X.X₁).ρ h ∘ₗ retractQuot r s := by
  refine LinearMap.ext fun v => ?_
  have hg : X.g.hom.hom (X.X₂.ρ h (s v)) = X.X₃.ρ h v :=
    (LinearMap.congr_fun (hom_equivariant X.g h) (s v)).trans (congrArg (X.X₃.ρ h) (hs v))
  have h1 : retractQuot r s (X.X₃.ρ h v)
      = Submodule.Quotient.mk (p := LinearMap.range (coindEmb X.X₁.ρ))
        (retractMid r (X.X₂.ρ h (s v))) := by
    rw [← hg]
    exact (mkQ_retractMid hX r hr s hs (X.X₂.ρ h (s v))).symm
  have h2 : retractMid r (X.X₂.ρ h (s v)) = (indObj X.X₁).ρ h (retractMid r (s v)) :=
    LinearMap.congr_fun (retractMid_equivariant r h) (s v)
  have h3 : Submodule.Quotient.mk (p := LinearMap.range (coindEmb X.X₁.ρ))
        ((indObj X.X₁).ρ h (retractMid r (s v)))
      = (shiftObj X.X₁).ρ h (Submodule.Quotient.mk (p := LinearMap.range (coindEmb X.X₁.ρ))
        (retractMid r (s v))) :=
    LinearMap.congr_fun (mkQ_comp_inducedRep X.X₁.ρ h) (retractMid r (s v))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, h3]
  rfl

/-! ### The comparison -/

/-- **Reading the translates through a retraction, as a morphism of representations.** -/
def retractMidHom : X.X₂ ⟶ indObj X.X₁ := mkHom (retractMid r) (retractMid_equivariant r)

/-- **The comparison of the quotient with the shift of the sub, as a morphism of
representations.** -/
def retractQuotHom : X.X₃ ⟶ shiftObj X.X₁ :=
  mkHom (retractQuot r s) (retractQuot_equivariant hX r hr s hs)

/-- **The comparison of an extension whose sub is a direct summand of its middle term with the
sequence defining the shift of that sub.** -/
def retractSeqHom : X ⟶ shiftSeq X.X₁ where
  τ₁ := 𝟙 X.X₁
  τ₂ := retractMidHom r
  τ₃ := retractQuotHom hX r hr s hs
  comm₁₂ :=
    Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun a => (retractMid_f r hr a).symm))
  comm₂₃ := Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext (mkQ_retractMid hX r hr s hs)))

/-- **The connecting map of an extension whose sub is a direct summand of its middle term is the
induced map on the quotients followed by the identification of the shift.** -/
theorem tateδ_eq_retractQuot (n : ℤ) (x : ↥(tateModule X.X₃ n)) :
    tateδ hX n x = tateShiftEquiv X.X₁ n (tateMap (retractQuotHom hX r hr s hs) n x) :=
  tateδ_eq_tateShiftEquiv hX (retractSeqHom hX r hr s hs) rfl n x

end

end InverseGalois.CFT.Tate
