/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTensorFinsupp
import InverseGalois.CFT.Tate.LiftInvariants
import InverseGalois.CFT.Units.IdeleValuationSplit

/-!
# The ideles and the product of all the local unit groups in degree one

An element of the product of all the local unit groups is an idele exactly when its vector of local
valuations has finite support, and that vector is a section of the family with a copy of the
integers at every finite place.  Coefficients of finite rank over a prime field pass through the
sections of that family, so after tensoring with them finiteness of support is still read place by
place.

An element of the tensored product all of whose Galois translates differ from it by ideles therefore
has a vector of valuations which the Galois group moves in finitely many places only.  The group
being finite, the places it moves have a finite invariant saturation, and clearing the vector of
valuations there leaves an invariant vector differing from it by one of finite support.  Feeding
that invariant vector back through a Galois invariant choice of local units produces an invariant
element of the tensored product differing from the original one by an idele.

That is exactly the lifting of invariants which makes the map of complete cohomology in degree zero
out of the quotient surjective, and the long exact sequence then makes the map induced in degree one
by the inclusion of the ideles injective.

## Main definitions

* `InverseGalois.CFT.fullIdeleValHom`, `InverseGalois.CFT.valSectionHom`: the vector of local
  valuations and its right inverse, as maps of representations.
* `InverseGalois.CFT.finsuppTensor`: the elements of the tensored vectors of integers which spread
  to a section of finite support.

## Main results

* `InverseGalois.CFT.exists_invariant_sub_mem_range_ideleToFullIdele`: **an element of the tensored
  product of all the local unit groups all of whose Galois translates differ from it by ideles
  differs by an idele from a Galois invariant one.**
* `InverseGalois.CFT.injective_tateMap_one_tensor_ideleToFullIdele`: **the twisted complete
  cohomology of the ideles in degree one injects into that of the product of all the local unit
  groups.**

## Tags

number field, idele, restricted product, Tate cohomology, invariants, valuation, finite support
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

open scoped TensorProduct

noncomputable section

/-! ### Tensoring a map of representations -/

section TensorAux

variable {G : Type} [Group G] (W : Rep ℤ G)

/-- Tensoring a map of representations with the coefficients acts on a pure tensor factorwise. -/
theorem tensorHomLeft_tmul {A B : Rep ℤ G} (Φ : A ⟶ B) (a : ↥A.V) (w : ↥W.V) :
    (tensorHomLeft W Φ).hom.hom (a ⊗ₜ[ℤ] w) = Φ.hom.hom a ⊗ₜ[ℤ] w := rfl

/-- Tensoring a map of representations with the coefficients is equivariant. -/
theorem tensorHomLeft_equivariant {A B : Rep ℤ G} (Φ : A ⟶ B) (g : G) (t : ↥(tensorObj A W).V) :
    (tensorHomLeft W Φ).hom.hom ((tensorObj A W).ρ g t)
      = (tensorObj B W).ρ g ((tensorHomLeft W Φ).hom.hom t) :=
  LinearMap.congr_fun (Tate.hom_equivariant (tensorHomLeft W Φ) g) t

variable {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))

/-- Tensoring a map of representations with coefficients of finite rank over the prime field acts
coordinatewise. -/
theorem tensorHomLeft_coordInv {A B : Rep ℤ G} (Φ : A ⟶ B) (u : Fin d → ↥A.V) :
    (tensorHomLeft W Φ).hom.hom (coordInv (↥A.V) e u)
      = coordInv (↥B.V) e (fun j => Φ.hom.hom (u j)) :=
  Tate.coordInv_map e Φ.hom.hom u

end TensorAux

/-! ### The comparison maps as maps of representations -/

section Hom

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **The vector of local valuations**, as a map of representations of the Galois group. -/
def fullIdeleValHom : fullIdeleRep k K ⟶ placeIntRep k K where
  hom := ModuleCat.ofHom (fullIdeleVal (K := K)).toIntLinearMap
  comm g := by
    ext a
    exact fullIdeleVal_equivariant g a

variable {k K}

omit [NumberField k] in
theorem fullIdeleValHom_apply (a : FullIdele K) :
    (fullIdeleValHom k K).hom.hom a = fullIdeleVal a := rfl

omit [NumberField k] in
theorem ideleToFullIdele_apply (a : ↥(idele K)) :
    (ideleToFullIdele k K).hom.hom a = (a : FullIdele K) := rfl

/-- **A right inverse of the vector of local valuations**, as a map of representations of the
Galois group, for a choice of local units carried onto itself by the Galois action. -/
def valSectionHom {s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ}
    (hs : ∀ g : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut g s = s) :
    placeIntRep k K ⟶ fullIdeleRep k K where
  hom := ModuleCat.ofHom (valSection s).toIntLinearMap
  comm g := by
    ext n
    exact (valSection_equivariant hs g n).symm

omit [NumberField k] in
theorem valSectionHom_apply
    {s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ}
    (hs : ∀ g : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut g s = s)
    (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    (valSectionHom hs).hom.hom n = valSection s n := rfl

end Hom

/-! ### Spreading a tensor over the places -/

section Finsupp

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (W : Rep ℤ Gal(K/k))

/-- **The elements of the tensored vectors of integers which spread to a section of finite
support.** -/
def finsuppTensor : AddSubgroup ↥(tensorObj (placeIntRep k K) W).V :=
  AddSubgroup.comap (sectionsTensorMap (placeIntFamily k K) W).toAddMonoidHom
    (finsuppSections fun _ : HeightOneSpectrum (𝓞 K) => ℤ ⊗[ℤ] ↥W.V)

omit [NumberField k] [NumberField K] in
theorem mem_finsuppTensor {t : ↥(tensorObj (placeIntRep k K) W).V} :
    t ∈ finsuppTensor W ↔ sectionsTensorMap (placeIntFamily k K) W t
      ∈ finsuppSections fun _ : HeightOneSpectrum (𝓞 K) => ℤ ⊗[ℤ] ↥W.V := Iff.rfl

omit [NumberField k] in
/-- **The vector of valuations of an idele spreads to a section of finite support**, after
tensoring with the coefficients. -/
theorem mem_finsuppTensor_of_mem_range {t : ↥(tensorObj (fullIdeleRep k K) W).V}
    (ht : t ∈ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom) :
    (tensorHomLeft W (fullIdeleValHom k K)).hom.hom t ∈ finsuppTensor W := by
  obtain ⟨u, rfl⟩ := ht
  induction u using TensorProduct.induction_on with
  | zero =>
    rw [_root_.map_zero, _root_.map_zero]
    exact zero_mem _
  | tmul x w =>
    rw [tensorHomLeft_tmul, tensorHomLeft_tmul, ideleToFullIdele_apply, fullIdeleValHom_apply,
      mem_finsuppTensor, mem_finsuppSections]
    refine (mem_finsuppSections.1 (fullIdeleVal_mem_finsuppSections x)).subset fun v hv hc => hv ?_
    rw [sectionsTensorMap_tmul, hc, TensorProduct.zero_tmul]
  | add u u' hu hu' =>
    rw [_root_.map_add, _root_.map_add]
    exact add_mem hu hu'

end Finsupp

/-! ### Correcting an element of the tensored product into an idele -/

section Correct

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  {s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ}

/-- **Subtracting off the chosen local units raised to the valuations leaves an idele**, after
tensoring with the coefficients. -/
theorem sub_valSectionHom_mem_range (hs : ∀ v ∈ fixedUniformizerPlaces k K, unitVal (s v) = 1)
    (hsg : ∀ g : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut g s = s)
    (t : ↥(tensorObj (fullIdeleRep k K) W).V) :
    t - (tensorHomLeft W (valSectionHom hsg)).hom.hom
        ((tensorHomLeft W (fullIdeleValHom k K)).hom.hom t)
      ∈ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [_root_.map_zero, _root_.map_zero, sub_zero]
    exact zero_mem _
  | tmul a w =>
    refine LinearMap.mem_range.2
      ⟨(⟨_, sub_valSection_mem_idele hs a⟩ : ↥(idele K)) ⊗ₜ[ℤ] w, ?_⟩
    rw [tensorHomLeft_tmul, tensorHomLeft_tmul, tensorHomLeft_tmul, fullIdeleValHom_apply,
      valSectionHom_apply]
    exact TensorProduct.sub_tmul _ _ _
  | add t t' ht ht' =>
    rw [_root_.map_add, _root_.map_add, ← sub_add_sub_comm]
    exact add_mem ht ht'

omit [NumberField k] in
include e in
/-- **A vector of integers spreading to a section of finite support is carried by the chosen local
units into the ideles**, after tensoring with the coefficients. -/
theorem valSectionHom_mem_range_of_finsuppTensor
    (hsg : ∀ g : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut g s = s)
    {t : ↥(tensorObj (placeIntRep k K) W).V} (ht : t ∈ finsuppTensor W) :
    (tensorHomLeft W (valSectionHom hsg)).hom.hom t
      ∈ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom := by
  obtain ⟨u, hu, rfl⟩ := exists_coordInv_finsupp (placeIntFamily k K) W e t ht
  rw [tensorHomLeft_coordInv]
  refine LinearMap.mem_range.2 ⟨coordInv (↥(ideleRep k K).V) e
    (fun j => (⟨valSection s (u j), valSection_mem_idele (hu j)⟩ : ↥(idele K))), ?_⟩
  rw [tensorHomLeft_coordInv]
  rfl

end Correct

/-! ### Lifting an invariant of the quotient -/

section Lift

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  {s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ}

include e in
/-- **An element of the tensored product of all the local unit groups all of whose Galois translates
differ from it by ideles differs by an idele from a Galois invariant one.**  Its vector of
valuations is moved by the Galois group in finitely many places only, so clearing that vector on the
finite invariant saturation of those places leaves an invariant vector, and the chosen local units
raised to that vector give the required invariant element. -/
theorem exists_invariant_sub_mem_range_ideleToFullIdele
    (hs : ∀ v ∈ fixedUniformizerPlaces k K, unitVal (s v) = 1)
    (hsg : ∀ g : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut g s = s)
    (a₀ : ↥(tensorObj (fullIdeleRep k K) W).V)
    (h : ∀ g : Gal(K/k), (tensorObj (fullIdeleRep k K) W).ρ g a₀ - a₀
      ∈ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom) :
    ∃ a : ↥(tensorObj (fullIdeleRep k K) W).V,
      (∀ g : Gal(K/k), (tensorObj (fullIdeleRep k K) W).ρ g a = a) ∧
        a - a₀ ∈ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom := by
  obtain ⟨n', hn'inv, hn'sub⟩ :=
    exists_rho_invariant_sub_finsuppTensor (placeIntFamily k K) W e
      ((tensorHomLeft W (fullIdeleValHom k K)).hom.hom a₀) fun g => by
        have hg := (mem_finsuppTensor W).1 (mem_finsuppTensor_of_mem_range W (h g))
        rwa [_root_.map_sub, tensorHomLeft_equivariant] at hg
  refine ⟨(tensorHomLeft W (valSectionHom hsg)).hom.hom n', fun g => ?_, ?_⟩
  · rw [← tensorHomLeft_equivariant, hn'inv g]
  · have h1 : (tensorHomLeft W (valSectionHom hsg)).hom.hom
        ((tensorHomLeft W (fullIdeleValHom k K)).hom.hom a₀ - n')
        ∈ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom :=
      valSectionHom_mem_range_of_finsuppTensor W e hsg ((mem_finsuppTensor W).2 hn'sub)
    have h2 : a₀ - (tensorHomLeft W (valSectionHom hsg)).hom.hom
        ((tensorHomLeft W (fullIdeleValHom k K)).hom.hom a₀)
        ∈ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom :=
      sub_valSectionHom_mem_range W hs hsg a₀
    have h3 : (tensorHomLeft W (valSectionHom hsg)).hom.hom n' - a₀
        = -((tensorHomLeft W (valSectionHom hsg)).hom.hom
              ((tensorHomLeft W (fullIdeleValHom k K)).hom.hom a₀ - n'))
          - (a₀ - (tensorHomLeft W (valSectionHom hsg)).hom.hom
              ((tensorHomLeft W (fullIdeleValHom k K)).hom.hom a₀)) := by
      rw [_root_.map_sub]
      abel
    rw [h3]
    exact sub_mem (neg_mem h1) h2

include e in
/-- **The twisted complete cohomology of the ideles in degree one injects into that of the product
of all the local unit groups.**  Every invariant of the quotient lifts to an invariant of the
product, so the map of complete cohomology in degree zero out of the quotient is surjective and the
connecting map out of that degree vanishes. -/
theorem injective_tateMap_one_tensor_ideleToFullIdele :
    Function.Injective (Tate.tateMap (tensorHomLeft W (ideleToFullIdele k K)) 1) := by
  obtain ⟨s, hsg, hs⟩ := exists_familyAut_eq_self_unitVal_eq_one k K
  have hXT : (Tate.tensorSeq W (ideleFullShortComplex k K)).ShortExact :=
    Tate.tensorSeq_shortExact_of_injective_modNsmul (ideleFullShortComplex_shortExact k K) W
      (Tate.nsmul_eq_zero_of_equivPi e)
      (injective_modNsmulHom_ideleToFullIdele k K (Fact.out : Nat.Prime p).ne_zero)
  have hsurj : Function.Surjective (tensorHomLeft W (fullIdeleToDefect k K)).hom.hom :=
    Tate.shortExact_surjective hXT
  have hker : LinearMap.ker (tensorHomLeft W (fullIdeleToDefect k K)).hom.hom
      ≤ LinearMap.range (tensorHomLeft W (ideleToFullIdele k K)).hom.hom :=
    (Tate.shortExact_range_eq_ker hXT).ge
  have hlift : ∀ c : (tensorObj (ideleDefectRep k K) W).ρ.invariants,
      ∃ a : (tensorObj (fullIdeleRep k K) W).ρ.invariants,
        (tensorHomLeft W (fullIdeleToDefect k K)).hom.hom a.1 = c.1 := by
    intro c
    obtain ⟨a₀, ha₀⟩ := hsurj c.1
    obtain ⟨a, hainv, hasub⟩ :=
      exists_invariant_sub_mem_range_ideleToFullIdele W e hs hsg a₀ fun g =>
        hker (LinearMap.mem_ker.2 (by
          rw [_root_.map_sub, tensorHomLeft_equivariant, ha₀, c.2 g, sub_self]))
    have hzero : (tensorHomLeft W (fullIdeleToDefect k K)).hom.hom (a - a₀) = 0 := by
      obtain ⟨y, hy⟩ := hasub
      rw [← hy]
      exact LinearMap.mem_ker.1
        ((Tate.shortExact_range_eq_ker hXT).le (LinearMap.mem_range_self _ y))
    rw [_root_.map_sub, sub_eq_zero] at hzero
    exact ⟨⟨a, hainv⟩, hzero.trans ha₀⟩
  have hfeq : (Tate.tensorSeq W (ideleFullShortComplex k K)).f
      = tensorHomLeft W (ideleToFullIdele k K) := rfl
  rw [← hfeq]
  exact Tate.injective_tateMap_one_of_lift_invariants hXT hlift

end Lift

end

end InverseGalois.CFT
