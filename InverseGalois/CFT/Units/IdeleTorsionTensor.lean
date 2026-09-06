/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTensorOrbit
import InverseGalois.CFT.TateCohomology.TensorPair
import InverseGalois.CFT.Units.IdeleTorsion

/-!
# The elements of the ideles killed by a prime, with coefficients, place by place

The elements of the ideles killed by a nonzero integer are the elements killed by it of the whole
product of the local unit groups, and that product splits into the infinite places and the finite
ones, each half being the sections of a family of modules over the places of the extension.  This
is the description that the theory of tori needs, and it needs it with coefficients: the modules
that appear there are not the elements of the ideles killed by a prime but those elements tensored
with a representation of the Galois group.

Tensoring does not commute with an infinite product in general, so the description does not follow
formally.  It does follow when the coefficients are killed by the prime and have finite rank over
the field with that many elements, because then a choice of basis turns the tensor product into a
finite power, and a finite power does commute with any product.  That hypothesis is exactly what
the coefficients of the theory of tori satisfy.

The result is therefore the same place-by-place description, with coefficients: **in every degree
the elements of the ideles killed by a prime, tensored with coefficients of finite rank over the
field with that many elements, have no complete cohomology as soon as no local factor has any,**
the local factor at a place of the base field being the decomposition group of a place above it
acting on the elements killed by the prime of the units of the completion there, tensored with the
restriction of the coefficients.

## Main definitions

* `InverseGalois.CFT.adicIdeleTorsionTensorTateEquiv`,
  `InverseGalois.CFT.infiniteIdeleTorsionTensorTateEquiv`: each half of the product, as a product
  over the places of the base field of the local contributions.
* `InverseGalois.CFT.ideleTorsionTensorTateEquiv`: **the complete cohomology of the elements of the
  ideles killed by a prime, tensored with coefficients of finite rank over the field with that many
  elements, is the product over the places of the base field of the complete cohomology of a
  decomposition group with coefficients in the roots of unity of a completion tensored with the
  restricted coefficients.**

## Main results

* `InverseGalois.CFT.isZero_tateModule_tensor_adicIdeleTorsion`,
  `InverseGalois.CFT.isZero_tateModule_tensor_infiniteIdeleTorsion`: each half of the product has
  no complete cohomology in a degree as soon as no local factor has any.
* `InverseGalois.CFT.isZero_tateModule_tensor_ideleTorsion`: **the elements of the ideles killed by
  a prime, tensored with coefficients of finite rank over the field with that many elements, have
  no complete cohomology in a degree as soon as no local factor has any.**

## Tags

number field, idele, root of unity, decomposition group, Tate cohomology, tensor product
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

open scoped TensorProduct

noncomputable section

/-! ### The finite places -/

section Finite

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)

include e in
/-- **The complete cohomology of the elements killed by a prime of the finite part of the group of
ideles, tensored with coefficients of finite rank over the field with that many elements, is the
product over the finite places of the base field of the complete cohomology of the decomposition
group of a place above it with coefficients in the roots of unity of the completion there tensored
with the restricted coefficients.** -/
def adicIdeleTorsionTensorTateEquiv (n : ℤ) :
    tateModule (tensorObj (torsionRep
      (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)) W) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
        tateModule (tensorObj (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
          (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n :=
  (tateTensorTorsionEquiv (adicRingFamily (k := k) (K := K)).unitsFamily W e v₀
      (H := fun ω => stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
      (fun ω g hg => mem_stabilizer_of_smul_orbit (v₀ ω) g hg)
      (fun ω g => smul_orbit_of_mem_stabilizer (v₀ ω) g) n).trans <|
    AddEquiv.piCongrRight fun ω =>
      tateTensorTorsionCast (resObj _ W) (stabAut_adicUnits_eq (v₀ ω)) (p : ℤ) n

include e in
/-- **The elements killed by a prime of the finite part of the group of ideles, tensored with
coefficients of finite rank over the field with that many elements, have no complete cohomology in
a degree as soon as no local factor has any.** -/
theorem isZero_tateModule_tensor_adicIdeleTorsion (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n)) :
    Limits.IsZero (tateModule (tensorObj (torsionRep
      (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)) W) n) := by
  refine isZero_tateModule_tensor_torsionRep (adicRingFamily (k := k) (K := K)).unitsFamily W e v₀
    (H := fun ω => stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
    (fun ω g hg => mem_stabilizer_of_smul_orbit (v₀ ω) g hg)
    (fun ω g => smul_orbit_of_mem_stabilizer (v₀ ω) g) n fun ω => ?_
  rw [stabAut_adicUnits_eq (v₀ ω)]
  exact h ω

end Finite

/-! ### The infinite places -/

section Archimedean

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite Gal(K/k)]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)

include e in
/-- **The complete cohomology of the elements killed by a prime of the infinite part of the group
of ideles, tensored with coefficients of finite rank over the field with that many elements, is the
product over the infinite places of the base field of the complete cohomology of the decomposition
group of a place above it with coefficients in the roots of unity of the completion there tensored
with the restricted coefficients.** -/
def infiniteIdeleTorsionTensorTateEquiv (n : ℤ) :
    tateModule (tensorObj (torsionRep
      (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)) W) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
        tateModule (tensorObj (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ))
          (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n :=
  (tateTensorTorsionEquiv (infiniteRingFamily (k := k) (K := K)).unitsFamily W e w₀
      (H := fun ω => stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K))
      (fun ω g hg => mem_stabilizer_of_smul_orbit_infinite (w₀ ω) g hg)
      (fun ω g => smul_orbit_of_mem_stabilizer_infinite (w₀ ω) g) n).trans <|
    AddEquiv.piCongrRight fun ω =>
      tateTensorTorsionCast (resObj _ W) (stabAut_infiniteUnits_eq (w₀ ω)) (p : ℤ) n

include e in
/-- **The elements killed by a prime of the infinite part of the group of ideles, tensored with
coefficients of finite rank over the field with that many elements, have no complete cohomology in
a degree as soon as no local factor has any.** -/
theorem isZero_tateModule_tensor_infiniteIdeleTorsion (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n)) :
    Limits.IsZero (tateModule (tensorObj (torsionRep
      (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)) W) n) := by
  refine isZero_tateModule_tensor_torsionRep (infiniteRingFamily (k := k) (K := K)).unitsFamily W e
    w₀ (H := fun ω => stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K))
    (fun ω g hg => mem_stabilizer_of_smul_orbit_infinite (w₀ ω) g hg)
    (fun ω g => smul_orbit_of_mem_stabilizer_infinite (w₀ ω) g) n fun ω => ?_
  rw [stabAut_infiniteUnits_eq (w₀ ω)]
  exact h ω

end Archimedean

/-! ### All the places at once -/

section Total

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)

include e in
/-- **The complete cohomology of the elements of the ideles killed by a prime, tensored with
coefficients of finite rank over the field with that many elements, is the product, over the places
of the base field, of the complete cohomology of the decomposition group of a place above it with
coefficients in the roots of unity of the completion there tensored with the restricted
coefficients.**  Being killed by a prime forces the local valuations to vanish everywhere, so the
finiteness condition defining the ideles is no restriction on such elements, and the product over
all places splits into the infinite half and the finite half, each of which is the sections of a
family of modules over the places of the extension. -/
def ideleTorsionTensorTateEquiv (n : ℤ) :
    tateModule (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W) n ≃+
      (∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
        tateModule (tensorObj (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ))
          (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n) ×
      (∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
        tateModule (tensorObj (torsionRep (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
          (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n) :=
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let e₁ := tateMapIso (tensorIsoLeft W (ideleTorsionIso k K hp)) n
  let e₂ := tateMapIso (tensorIsoLeft W (fullIdeleTorsionIso k K (p : ℤ))) n
  e₁.toLinearEquiv.toAddEquiv.trans <| e₂.toLinearEquiv.toAddEquiv.trans <|
    (tateTensorPairEquiv _ _ W e (fun a => nsmul_eq_zero_torsionBy a)
        (fun a => nsmul_eq_zero_torsionBy a) n).trans <|
      (infiniteIdeleTorsionTensorTateEquiv W e w₀ n).prodCongr
        (adicIdeleTorsionTensorTateEquiv W e v₀ n)

include e in
/-- **The elements of the ideles killed by a prime, tensored with coefficients of finite rank over
the field with that many elements, have no complete cohomology in a degree as soon as no local
factor has any.**  Being killed by a prime forces the local valuations to vanish everywhere, so
such an element is nothing but a root of unity at every place, with no restriction at all; the
product over all places splits into the infinite half and the finite half, and each half is the
sections of a family of modules over the places of the extension, whose complete cohomology is
computed orbit by orbit. -/
theorem isZero_tateModule_tensor_ideleTorsion (n : ℤ)
    (h₁ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n))
    (h₂ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), Limits.IsZero
      (tateModule (tensorObj (torsionRep (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (p : ℤ))
        (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n)) :
    Limits.IsZero (tateModule (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W) n) := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine isZero_tateModule_of_iso (tensorIsoLeft W (ideleTorsionIso k K hp)) n ?_
  refine isZero_tateModule_of_iso (tensorIsoLeft W (fullIdeleTorsionIso k K (p : ℤ))) n ?_
  refine isZero_tateModule_tensorObj_piRep (pairFamily _ _) W e ?_ n ?_
  · intro b
    cases b <;> exact fun a => nsmul_eq_zero_torsionBy a
  · intro b
    cases b
    · exact isZero_tateModule_tensor_adicIdeleTorsion W e v₀ n h₂
    · exact isZero_tateModule_tensor_infiniteIdeleTorsion W e w₀ n h₁

end Total

end

end InverseGalois.CFT
