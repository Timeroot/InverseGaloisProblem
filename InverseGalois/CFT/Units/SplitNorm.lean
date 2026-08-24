/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyFree
import InverseGalois.CFT.Units.SolvableNorm

/-!
# An extension in which every place splits completely is trivial

If every place of the base field splits completely in a Galois extension then the decomposition
group at every place is trivial, so the Galois group permutes the places above a given place freely.
An idele of the base field, read in the extension, is fixed by the Galois group; a section supported
on one place above each place of the base field, taking there the value of that fixed idele, has
sum of conjugates the fixed idele itself, because exactly one automorphism carries the chosen place
to any given one.  So every idele of the base field is a norm.

Together with the solvable case of the first inequality this says that a solvable extension in which
every place splits completely is trivial, which is the statement that makes the decomposition groups
generate the Galois group.

## Main results

* `InverseGalois.CFT.ideleNorm_surjective_of_free`: **if the Galois group acts freely on the places
  then every idele of the base field is a norm.**
* `InverseGalois.CFT.subsingleton_gal_of_isSolvable_of_free`: **a solvable extension of number
  fields in which every place splits completely is trivial.**

## Tags

number field, idele, norm, split completely, decomposition group, free action
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section SplitNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable (k K) in
/-- **If the Galois group acts freely on the places of the extension then every idele of the base
field is a norm.**  The idele read in the extension is fixed, so the section supported on one place
above each place of the base field, taking there its value, has that idele as its sum of
conjugates. -/
theorem ideleNorm_surjective_of_free
    (hfin : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), σ • v = v → σ = 1)
    (hinf : ∀ (σ : Gal(K/k)) (w : InfinitePlace K), σ • w = w → σ = 1) :
    Function.Surjective (ideleNorm k K) := by
  intro y
  have hfix : ∀ σ : Gal(K/k),
      fullIdeleAut (k := k) σ (ideleComap k K y : FullIdele K) = (ideleComap k K y : FullIdele K) :=
    fun σ => by rw [← coe_ideleAut, ideleAut_ideleComap]
  obtain ⟨t₁, ht₁supp, ht₁⟩ := FamilyAction.exists_sum_familyAut_eq
    (infiniteRingFamily (k := k) (K := K)).unitsFamily hinf fun σ => congrArg Prod.fst (hfix σ)
  obtain ⟨t₂, ht₂supp, ht₂⟩ := FamilyAction.exists_sum_familyAut_eq
    (adicRingFamily (k := k) (K := K)).unitsFamily hfin fun σ => congrArg Prod.snd (hfix σ)
  have htmem : ((t₁, t₂) : FullIdele K) ∈ idele K := by
    have hsm : (ideleComap k K y : FullIdele K) ∈ idele K := (ideleComap k K y).2
    rw [mem_idele] at hsm ⊢
    filter_upwards [hsm] with v hv
    rcases ht₂supp v with h | h
    · show unitVal (t₂ v) = 0
      rw [h]
      exact hv
    · show unitVal (t₂ v) = 0
      rw [h]
      exact map_zero _
  have hsum : ∑ g : Gal(K/k), fullIdeleAut (k := k) g ((t₁, t₂) : FullIdele K)
      = (ideleComap k K y : FullIdele K) :=
    Prod.ext (Prod.fst_sum.trans ht₁) (Prod.snd_sum.trans ht₂)
  refine ⟨⟨(t₁, t₂), htmem⟩, ideleComap_injective k K ?_⟩
  rw [ideleComap_ideleNorm, galSum_apply]
  exact Subtype.ext ((map_sum ((idele K).subtype) _ _).trans hsum)

variable (k K) in
/-- **A solvable extension of number fields in which every place splits completely is trivial.**
Every idele of the base field is then a norm, so the principal ideles and the norms exhaust the
ideles, and the solvable case of the first inequality applies. -/
theorem subsingleton_gal_of_isSolvable_of_free [IsSolvable Gal(K/k)]
    (hfin : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), σ • v = v → σ = 1)
    (hinf : ∀ (σ : Gal(K/k)) (w : InfinitePlace K), σ • w = w → σ = 1) :
    Subsingleton Gal(K/k) := by
  have hr : (ideleNorm k K).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr (ideleNorm_surjective_of_free k K hfin hinf)
  exact subsingleton_gal_of_isSolvable_of_ideleDiag_sup_le le_rfl (by rw [hr, sup_top_eq])

end SplitNorm

end InverseGalois.CFT
