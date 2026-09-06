/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyProduct
import InverseGalois.CFT.Tate.FamilyTensor

/-!
# The orbit decomposition of the sections of a family tensored with coefficients

The sections of a family of modules over a set with a group action decompose, in complete
cohomology, into a product of local contributions, one for each orbit, each computed in the
stabiliser of a chosen point of the orbit.  Tensoring the family with a fixed representation gives
another family over the same index set, whose sections are the sections of the original family
tensored with the coefficients as soon as every module of the family is killed by a prime and the
coefficients are of finite rank over the field with that many elements; at a base point of an orbit
the stabiliser sees the module there tensored with the restriction of the coefficients.

Putting the two together turns the decomposition into a statement about the tensored sections:
**the complete cohomology of the sections of a family tensored with the coefficients is the
product, over the orbits of the index set, of the complete cohomology of the stabiliser of a point
of the orbit with coefficients in the module there tensored with the restricted coefficients.**
The same holds for the elements killed by the prime, which is the form the roots of unity in the
group of ideles take.

This is the identification, not merely the vanishing that follows from it: a long exact sequence
built out of these groups needs the isomorphism itself.

## Main definitions

* `InverseGalois.CFT.tateTensorOrbitsEquiv`: **the complete cohomology of the sections of a family
  tensored with the coefficients, as a product of local contributions.**
* `InverseGalois.CFT.tateTensorTorsionEquiv`: the same for the sections killed by a prime.

## Tags

Tate cohomology, tensor product, orbit, Shapiro's lemma, decomposition group, idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

open scoped TensorProduct

noncomputable section

/-! ### Transporting along an equality of actions -/

section Cast

variable {G A : Type} [Group G] [Finite G] [AddCommGroup A] {φ ψ : G →* AddAut A} (W : Rep ℤ G)

/-- The complete cohomology of the elements killed by an integer, tensored with coefficients, is
carried along an equality of actions on the module. -/
def tateTensorTorsionCast (h : φ = ψ) (m n : ℤ) :
    tateModule (tensorObj (torsionRep φ m) W) n ≃+
      tateModule (tensorObj (torsionRep ψ m) W) n := by
  subst h
  exact AddEquiv.refl _

end Cast

/-! ### One orbit -/

section Orbit

variable {G X : Type} [Group G] [MulAction G X] [Finite G] {M : X → Type}
  [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (W : Rep ℤ G) {p : ℕ}
  {ω : orbitRel.Quotient G X} (x₀ : ω.orbit) {H : Subgroup G}
  (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)

include hH' in
/-- **Over one orbit the complete cohomology of the sections killed by a prime, tensored with the
coefficients, is read at a base point.** -/
def tateTensorTorsionOrbitEquiv (n : ℤ) :
    tateModule (tensorObj (orbitStabRep x₀ hH' (orbitFamily (F.torsion (p : ℤ)) ω))
        (resObj H W)) n ≃ₗ[ℤ]
      tateModule (tensorObj (torsionRep (stabAut x₀ hH' (orbitFamily F ω)) (p : ℤ))
        (resObj H W)) n := by
  rw [orbitStabRep_torsion F (p : ℤ) x₀ hH']

end Orbit

/-! ### All the orbits -/

section Orbits

variable {G X : Type} [Group G] [MulAction G X] [Finite G] {M : X → Type}
  [∀ x, AddCommGroup (M x)] (F : FamilyAction M G) (W : Rep ℤ G) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p)) (hM : ∀ (x : X) (a : M x), p • a = 0)
  (x₀ : ∀ ω : orbitRel.Quotient G X, ω.orbit) {H : orbitRel.Quotient G X → Subgroup G}
  (hH : ∀ (ω : orbitRel.Quotient G X) (g : G), g • x₀ ω = x₀ ω → g ∈ H ω)
  (hH' : ∀ (ω : orbitRel.Quotient G X) (g : ↥(H ω)), (g : G) • x₀ ω = x₀ ω)

include e hM hH hH' in
/-- **The complete cohomology of the sections of a family tensored with the coefficients is the
product, over the orbits of the index set, of the complete cohomology of the stabiliser of a chosen
point of the orbit with coefficients in the module there tensored with the restricted
coefficients.**  The coefficients pass through the sections because they are finite over the prime
field and every module of the family is killed by the prime, and the orbit decomposition then
applies to the tensored family unchanged. -/
def tateTensorOrbitsEquiv (n : ℤ) :
    tateModule (tensorObj (orbitSectionsRep F) W) n ≃+
      ∀ ω : orbitRel.Quotient G X,
        tateModule (tensorObj (orbitStabRep (x₀ ω) (hH' ω) (orbitFamily F ω))
          (resObj (H ω) W)) n :=
  (tateMapIso (tensorSectionsIso F W e hM) n).toLinearEquiv.toAddEquiv.trans <|
    (tateOrbitsLocalEquiv (F.tensorRight W) x₀ hH hH' n).trans <|
      AddEquiv.piCongrRight fun ω =>
        (tateMapIso (orbitStabTensorIso F W (x₀ ω) (hH' ω)) n).toLinearEquiv.toAddEquiv

include e hH hH' in
/-- **The complete cohomology of the sections of a family killed by a prime, tensored with the
coefficients, is the product over the orbits of the local contributions.**  This is the shape the
roots of unity in the group of ideles take: the contribution at a place is the roots of unity of
the completion tensored with the coefficients, read in the decomposition group. -/
def tateTensorTorsionEquiv (n : ℤ) :
    tateModule (tensorObj (torsionRep F.familyAut (p : ℤ)) W) n ≃+
      ∀ ω : orbitRel.Quotient G X,
        tateModule (tensorObj (torsionRep (stabAut (x₀ ω) (hH' ω) (orbitFamily F ω)) (p : ℤ))
          (resObj (H ω) W)) n :=
  let e₀ := tateMapIso (tensorIsoLeft W (torsionSectionsIso F (p : ℤ))) n
  e₀.symm.toLinearEquiv.toAddEquiv.trans <|
    (tateTensorOrbitsEquiv (F.torsion (p : ℤ)) W e (fun _ a => nsmul_eq_zero_torsionBy a) x₀ hH
        hH' n).trans <|
      AddEquiv.piCongrRight fun ω =>
        (tateTensorTorsionOrbitEquiv F W (x₀ ω) (hH' ω) n).toAddEquiv

end Orbits

end

end InverseGalois.CFT
