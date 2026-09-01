/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.PlaceIdele
import InverseGalois.CFT.Units.SplitNorm

/-!
# An idele supported at a place that splits completely is a norm

An idele of the base field supported at a single finite place, read in a Galois extension, is a
section of the family of local unit groups which vanishes away from the places above that one
place.  If the Galois group permutes those places freely, then a section supported on one of them
in each orbit has the fixed section as its sum of conjugates, and the idele is a norm.

Nothing is required of the group at the other places: the freeness is only ever used where the
section does not vanish.  This is what makes an auxiliary prime chosen to split completely in an
extension supply a norm from that extension, whatever the ramification elsewhere.

## Main results

* `InverseGalois.CFT.adicPlaceIdele_mem_range_ideleNorm`: **an idele supported at a finite place
  whose places above have trivial stabiliser is a norm.**

## Tags

number field, idele, norm, split completely, decomposition group, free action, place
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section SplitPlaceNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable (k K) in
/-- **An idele supported at a finite place whose places above have trivial stabiliser is a
norm.**  The idele read in the extension vanishes away from the places above the chosen place, so
the section supported on one place of each orbit there, taking its value, has the idele as its sum
of conjugates. -/
theorem adicPlaceIdele_mem_range_ideleNorm (v₀ : HeightOneSpectrum (𝓞 k))
    (hfree : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      primeUnder (𝓞 k) v = v₀ → σ • v = v → σ = 1) (u : Additive (v₀.adicCompletion k)ˣ) :
    adicPlaceIdele k v₀ u ∈ (ideleNorm k K).range := by
  set y : ↥(idele k) := adicPlaceIdele k v₀ u with hy
  have hfix : ∀ σ : Gal(K/k),
      fullIdeleAut (k := k) σ (ideleComap k K y : FullIdele K) = (ideleComap k K y : FullIdele K) :=
    fun σ => by rw [← coe_ideleAut, ideleAut_ideleComap]
  have hinf : ∀ (σ : Gal(K/k)) (w : InfinitePlace K),
      (ideleComap k K y : FullIdele K).1 w ≠ 0 → σ • w = w → σ = 1 := by
    intro σ w hw _
    refine absurd ?_ hw
    show infiniteUnitsComap k w ((fullPlaceIdele k v₀ u).1 (w.comap (algebraMap k K))) = 0
    rw [fullPlaceIdele_fst]
    exact map_zero _
  have hfin : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      (ideleComap k K y : FullIdele K).2 v ≠ 0 → σ • v = v → σ = 1 := by
    intro σ v hv hσ
    refine hfree σ v ?_ hσ
    by_contra hne
    refine hv ?_
    show adicUnitsComap k v ((fullPlaceIdele k v₀ u).2 (primeUnder (𝓞 k) v)) = 0
    rw [fullPlaceIdele_snd_of_ne hne]
    exact map_zero _
  obtain ⟨t₁, ht₁supp, ht₁⟩ := FamilyAction.exists_sum_familyAut_eq_of_free_on_support
    (infiniteRingFamily (k := k) (K := K)).unitsFamily (fun σ => congrArg Prod.fst (hfix σ)) hinf
  obtain ⟨t₂, ht₂supp, ht₂⟩ := FamilyAction.exists_sum_familyAut_eq_of_free_on_support
    (adicRingFamily (k := k) (K := K)).unitsFamily (fun σ => congrArg Prod.snd (hfix σ)) hfin
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

end SplitPlaceNorm

end InverseGalois.CFT
