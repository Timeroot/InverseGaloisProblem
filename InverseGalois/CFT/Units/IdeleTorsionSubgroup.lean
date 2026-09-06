/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyConst
import InverseGalois.CFT.Tate.FamilyResGroup
import InverseGalois.CFT.Units.IdeleTorsionTensor

/-!
# The elements of the ideles killed by a prime, read on a subgroup of the Galois group

The elements of the ideles killed by a prime, tensored with coefficients of finite rank over the
field with that many elements, are the product over the places of the base field of the roots of
unity of a completion tensored with the restricted coefficients — a statement about the whole Galois
group.  A criterion formulated over a Sylow subgroup needs the same statement over that subgroup,
and the subgroup does not fix the places of the base field: it moves the places of the extension in
orbits of its own, generally finer, and the stabiliser at one of them is the intersection of the
subgroup with the decomposition group there.

Nothing new has to be computed.  The units of the completions are a family of modules over the
places of the extension, and a subgroup acts on that family by the restricted action, so the orbit
decomposition of the complete cohomology of the sections of a family applies to the subgroup
verbatim.  The only thing to identify is the local factor: the transport by an element of the
subgroup fixing a place is the transport by that element of the whole group, hence the action of the
decomposition group there read along the inclusion of the stabiliser in the subgroup into the
stabiliser in the group.

**The conclusion is the place-by-place description over an arbitrary subgroup:** in every degree the
complete cohomology of the subgroup with coefficients in the elements of the ideles killed by a
prime, tensored with coefficients of finite rank over the field with that many elements, is the
product over the orbits of the subgroup on the places of the extension of the complete cohomology of
the stabiliser there with coefficients in the roots of unity of the completion tensored with the
restricted coefficients.

## Main definitions

* `InverseGalois.CFT.adicIdeleTorsionTensorTateResEquiv`,
  `InverseGalois.CFT.infiniteIdeleTorsionTensorTateResEquiv`: each half of the product, read on a
  subgroup, as a product over the orbits of that subgroup of the local contributions.
* `InverseGalois.CFT.ideleTorsionTensorTateResEquiv`: **the complete cohomology of a subgroup with
  coefficients in the elements of the ideles killed by a prime, tensored with coefficients of finite
  rank over the field with that many elements, is the product over the orbits of the subgroup on the
  places of the extension of the complete cohomology of the stabiliser there with coefficients in
  the roots of unity of a completion tensored with the restricted coefficients.**

## Main results

* `InverseGalois.CFT.stabAut_resGroup_adicUnits_eq`,
  `InverseGalois.CFT.stabAut_resGroup_infiniteUnits_eq`: the action of the stabiliser of a place in
  a subgroup on the units of the completion there is the action of the decomposition group, read
  along the inclusion.
* `InverseGalois.CFT.isZero_tateModule_tensor_ideleTorsionRes`: those elements have no complete
  cohomology over the subgroup in a degree as soon as no local factor has any.

## Tags

number field, idele, root of unity, decomposition group, Sylow subgroup, Tate cohomology, Shapiro's
lemma
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

/-! ### The finite places -/

section Finite

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
  (S : Subgroup Gal(K/k))

/-- **The action of the stabiliser of a finite place in a subgroup on the units of the completion
there** is the action of the decomposition group, read along the inclusion of that stabiliser into
the decomposition group. -/
theorem stabAut_resGroup_adicUnits_eq
    {ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K))} (v₀ : ω.orbit) :
    stabAut v₀ (smul_orbit_of_mem_stabilizer_val v₀)
        (orbitFamily ((adicRingFamily (k := k) (K := K)).unitsFamily.resGroup S) ω)
      = (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
        (stabilizerSubgroupHom S (v₀ : HeightOneSpectrum (𝓞 K))) := by
  refine MonoidHom.ext fun g => AddEquiv.ext fun a => ?_
  refine (stabAut_orbitFamily ((adicRingFamily (k := k) (K := K)).unitsFamily.resGroup S) v₀
    (smul_orbit_of_mem_stabilizer_val v₀) (fun s => mem_stabilizer_iff.mp s.2) g a).trans ?_
  exact transport_adicUnitsFamily _ _ _ a

variable [Finite Gal(K/k)] (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p))
  (v₀ : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), ω.orbit)

include e in
/-- **The complete cohomology of a subgroup with coefficients in the elements killed by a prime of
the finite part of the group of ideles, tensored with coefficients of finite rank over the field
with that many elements, is the product over the orbits of the subgroup on the finite places of the
extension of the complete cohomology of the stabiliser there with coefficients in the roots of unity
of the completion tensored with the restricted coefficients.** -/
def adicIdeleTorsionTensorTateResEquiv (n : ℤ) :
    tateModule (resObj S (tensorObj (torsionRep
      (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)) W)) n ≃+
      ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)),
        tateModule (tensorObj (torsionRep ((smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
            (stabilizerSubgroupHom S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) (p : ℤ))
          (resObj (stabilizer ↥S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
            (resObj S W))) n :=
  (tateTensorTorsionEquiv ((adicRingFamily (k := k) (K := K)).unitsFamily.resGroup S)
      (resObj S W) e v₀
      (H := fun ω => stabilizer ↥S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
      (fun ω g hg => mem_stabilizer_val_of_smul_orbit (v₀ ω) g hg)
      (fun ω g => smul_orbit_of_mem_stabilizer_val (v₀ ω) g) n).trans <|
    AddEquiv.piCongrRight fun ω =>
      tateTensorTorsionCast (resObj _ (resObj S W))
        (stabAut_resGroup_adicUnits_eq S (v₀ ω)) (p : ℤ) n

end Finite

/-! ### The infinite places -/

section Archimedean

variable {k K : Type} [Field k] [Field K] [Algebra k K] (S : Subgroup Gal(K/k))

/-- **The action of the stabiliser of an infinite place in a subgroup on the units of the completion
there** is the action of the decomposition group, read along the inclusion of that stabiliser into
the decomposition group. -/
theorem stabAut_resGroup_infiniteUnits_eq
    {ω : orbitRel.Quotient ↥S (InfinitePlace K)} (w₀ : ω.orbit) :
    stabAut w₀ (smul_orbit_of_mem_stabilizer_val w₀)
        (orbitFamily ((infiniteRingFamily (k := k) (K := K)).unitsFamily.resGroup S) ω)
      = (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
          (R := (w₀ : InfinitePlace K).Completion)).comp
        (stabilizerSubgroupHom S (w₀ : InfinitePlace K)) := by
  refine MonoidHom.ext fun g => AddEquiv.ext fun a => ?_
  refine (stabAut_orbitFamily ((infiniteRingFamily (k := k) (K := K)).unitsFamily.resGroup S) w₀
    (smul_orbit_of_mem_stabilizer_val w₀) (fun s => mem_stabilizer_iff.mp s.2) g a).trans ?_
  exact transport_infiniteUnitsFamily _ _ _ a

variable [Finite Gal(K/k)] (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p))
  (w₀ : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), ω.orbit)

include e in
/-- **The complete cohomology of a subgroup with coefficients in the elements killed by a prime of
the infinite part of the group of ideles, tensored with coefficients of finite rank over the field
with that many elements, is the product over the orbits of the subgroup on the infinite places of
the extension of the complete cohomology of the stabiliser there with coefficients in the roots of
unity of the completion tensored with the restricted coefficients.** -/
def infiniteIdeleTorsionTensorTateResEquiv (n : ℤ) :
    tateModule (resObj S (tensorObj (torsionRep
      (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)) W)) n ≃+
      ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K),
        tateModule (tensorObj (torsionRep ((smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)).comp
            (stabilizerSubgroupHom S ((w₀ ω : ω.orbit) : InfinitePlace K))) (p : ℤ))
          (resObj (stabilizer ↥S ((w₀ ω : ω.orbit) : InfinitePlace K)) (resObj S W))) n :=
  (tateTensorTorsionEquiv ((infiniteRingFamily (k := k) (K := K)).unitsFamily.resGroup S)
      (resObj S W) e w₀
      (H := fun ω => stabilizer ↥S ((w₀ ω : ω.orbit) : InfinitePlace K))
      (fun ω g hg => mem_stabilizer_val_of_smul_orbit (w₀ ω) g hg)
      (fun ω g => smul_orbit_of_mem_stabilizer_val (w₀ ω) g) n).trans <|
    AddEquiv.piCongrRight fun ω =>
      tateTensorTorsionCast (resObj _ (resObj S W))
        (stabAut_resGroup_infiniteUnits_eq S (w₀ ω)) (p : ℤ) n

end Archimedean

/-! ### All the places at once -/

section Total

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  (S : Subgroup Gal(K/k)) (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p))
  (w₀ : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), ω.orbit)
  (v₀ : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), ω.orbit)

include e in
/-- **The complete cohomology of a subgroup with coefficients in the elements of the ideles killed
by a prime, tensored with coefficients of finite rank over the field with that many elements, is the
product over the orbits of the subgroup on the places of the extension of the complete cohomology of
the stabiliser there with coefficients in the roots of unity of the completion tensored with the
restricted coefficients.**  Being killed by a prime forces the local valuations to vanish
everywhere, so the finiteness condition defining the ideles is no restriction on such elements, and
the product over all places splits into the infinite half and the finite half, each of which is the
sections of a family of modules on which the subgroup acts by the restricted action. -/
def ideleTorsionTensorTateResEquiv (n : ℤ) :
    tateModule (resObj S (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W)) n ≃+
      (∀ ω : orbitRel.Quotient ↥S (InfinitePlace K),
        tateModule (tensorObj (torsionRep ((smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)).comp
            (stabilizerSubgroupHom S ((w₀ ω : ω.orbit) : InfinitePlace K))) (p : ℤ))
          (resObj (stabilizer ↥S ((w₀ ω : ω.orbit) : InfinitePlace K)) (resObj S W))) n) ×
      (∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)),
        tateModule (tensorObj (torsionRep ((smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
            (stabilizerSubgroupHom S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) (p : ℤ))
          (resObj (stabilizer ↥S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
            (resObj S W))) n) :=
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let e₁ := tateMapIso ((Action.res _ S.subtype).mapIso
    (tensorIsoLeft W (ideleTorsionIso k K hp))) n
  let e₂ := tateMapIso ((Action.res _ S.subtype).mapIso
    (tensorIsoLeft W (fullIdeleTorsionIso k K (p : ℤ)))) n
  let e₃ := tateMapIso (tensorIsoLeft (resObj S W) (eqToIso (resObj_pairRep S
    (torsionRep (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ))
    (torsionRep (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ))))) n
  e₁.toLinearEquiv.toAddEquiv.trans <| e₂.toLinearEquiv.toAddEquiv.trans <|
    e₃.toLinearEquiv.toAddEquiv.trans <|
      (tateTensorPairEquiv
          (resObj S (torsionRep
            (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)))
          (resObj S (torsionRep
            (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut (p : ℤ)))
          (resObj S W) e (fun a => nsmul_eq_zero_torsionBy a)
          (fun a => nsmul_eq_zero_torsionBy a) n).trans <|
        (infiniteIdeleTorsionTensorTateResEquiv S W e w₀ n).prodCongr
          (adicIdeleTorsionTensorTateResEquiv S W e v₀ n)

include e in
/-- **The elements of the ideles killed by a prime, tensored with coefficients of finite rank over
the field with that many elements, have no complete cohomology over a subgroup in a degree as soon
as no local factor has any**, the local factors now being indexed by the orbits of the subgroup on
the places of the extension. -/
theorem isZero_tateModule_tensor_ideleTorsionRes (n : ℤ)
    (h₁ : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), Limits.IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)).comp
          (stabilizerSubgroupHom S ((w₀ ω : ω.orbit) : InfinitePlace K))) (p : ℤ))
        (resObj (stabilizer ↥S ((w₀ ω : ω.orbit) : InfinitePlace K)) (resObj S W))) n))
    (h₂ : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), Limits.IsZero
      (tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
          (stabilizerSubgroupHom S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) (p : ℤ))
        (resObj (stabilizer ↥S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
          (resObj S W))) n)) :
    Limits.IsZero
      (tateModule (resObj S (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W)) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient ↥S (InfinitePlace K), Subsingleton
      ↥(tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)).comp
          (stabilizerSubgroupHom S ((w₀ ω : ω.orbit) : InfinitePlace K))) (p : ℤ))
        (resObj (stabilizer ↥S ((w₀ ω : ω.orbit) : InfinitePlace K)) (resObj S W))) n) :=
    fun ω => ModuleCat.isZero_iff_subsingleton.1 (h₁ ω)
  haveI : ∀ ω : orbitRel.Quotient ↥S (HeightOneSpectrum (𝓞 K)), Subsingleton
      ↥(tateModule (tensorObj (torsionRep ((smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)).comp
          (stabilizerSubgroupHom S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))) (p : ℤ))
        (resObj (stabilizer ↥S ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)))
          (resObj S W))) n) :=
    fun ω => ModuleCat.isZero_iff_subsingleton.1 (h₂ ω)
  exact (ideleTorsionTensorTateResEquiv S W e w₀ v₀ n).injective.subsingleton

end Total

end

end InverseGalois.CFT
