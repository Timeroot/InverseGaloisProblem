/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NegOnePow
import InverseGalois.CFT.PoitouTate.InfiniteClasses
import InverseGalois.CFT.PoitouTate.ThreePlaces
import InverseGalois.CFT.PoitouTate.TwoPlacesFree

/-!
# Completely split places carrying a prescribed local behaviour, at any exponent

At an odd exponent a prescribed local behaviour on a stable finite set of places is realised by a
unit ramified at exactly *two* places completely split in an auxiliary field; at the exponent two
the same is true of *three* places, the inverse of a local class being the class itself there.  The
two statements are the same statement once the odd one is read as producing three places of which
the last two coincide: the clauses distinguishing the places are never used by what consumes them,
and what is used — the prescription on the fixed set, the divisibility away from the places
produced, the indivisibility at the first of them, and the triviality at their nontrivial
conjugates — reads the same either way.

Recorded in that common shape the construction no longer mentions the parity of the exponent.  The
price is that the distinguished part of the fixed set, where the prescription must be trivial, is
now asked to carry the places ramified over the base as well as the places over the exponent; at an
odd exponent that part may be taken to be the places over the exponent alone, and at the exponent
two it is exactly what the three-place recursion needs to read the local behaviour at a place of
the base.

## Main results

* `InverseGalois.CFT.exists_places_sUnit_class_eq_of_split`: **three places completely split in the
  auxiliary field and a unit ramified only at them realising a prescribed local behaviour**, at
  every prime exponent.

## Tags

number field, place, completely split, local class, prescription, quadratic
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The two constructions in a common shape -/

section Places

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Three places completely split in the auxiliary field and a unit ramified only at them,
realising a prescribed local behaviour on a stable finite set of places, at any prime exponent.**
The distinguished part of the fixed set carries the places over the exponent and the places
ramified over the base, and the prescription is trivial there; the unit is a local power at every
infinite place.  At an odd exponent the last two places coincide. -/
theorem exists_places_sUnit_class_eq_of_split (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {B T : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hBT : B ⊆ T)
    (hBstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ B → σ • v ∈ B)
    (hBwild : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ B)
    (hBram : ∀ v : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) v ≠ 1 → v ∈ B)
    {y : Kˣ}
    (hysplit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → Rigidity.RET.ord K v (y : K) ≠ 0 →
      ∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = v ∧
        stabilizer Gal(↥Ω/k) w = ⊥)
    (hyinf : ∀ w : InfinitePlace K, infClassHom w p y = 1)
    (hyunr : ∀ v ∈ T, localClassHom v p y ∈ localUnramified v p)
    (hyB : ∀ v ∈ B, localClassHom v p y = 1) :
    ∃ Q R E : HeightOneSpectrum (𝓞 K), Q ∉ T ∧ R ∉ T ∧ E ∉ T ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = Q ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = R ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = E ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      stabilizer Gal(K/k) Q = ⊥ ∧ stabilizer Gal(K/k) R = ⊥ ∧ stabilizer Gal(K/k) E = ⊥ ∧
      ∃ z : Kˣ, (∀ v ∈ T, localClassHom v p z = localClassHom v p y) ∧
        (∀ u : InfinitePlace K, infClassHom u p z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → v ≠ R → v ≠ E → (p : ℤ) ∣ placeValue v z) ∧
        ¬ (p : ℤ) ∣ placeValue Q z ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Q) p z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • R) p z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • E) p z = 1) := by
  classical
  have hpT : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ T :=
    fun v hv => hBT (hBwild v hv)
  have hyp : ∀ v ∈ T, Pc v ∣ p → localClassHom v p y = 1 := fun v _ hdvd =>
    hyB v (hBwild v fun hone => not_dvd_of_finitePlace_natCast_eq_one (hres v) hone hdvd)
  rcases eq_or_ne p 2 with rfl | hne2
  · obtain ⟨T', S₀, hTT', hT'S, hT'stable, hSstable, hSsplit, hreprS, hyS, hy0⟩ :=
      exists_stable_ord_repr_sUnit_of_split (Ω := Ω) hTstable hysplit
    have hyunr' : ∀ v ∈ T', localClassHom v 2 y ∈ localUnramified v 2 := by
      intro v hv
      by_cases hvT : v ∈ T
      · exact hyunr v hvT
      · refine (localClassHom_mem_localUnramified_iff v y).2 ?_
        rw [placeValue_eq_neg_ord, hy0 v hv hvT, neg_zero]
        exact dvd_zero _
    obtain ⟨Q, R, E, hQT, hRT, hET, hQspl, hRspl, hEspl, -, -, -, hQstab, hRstab, hEstab,
        z, hzT, hzinf, hzunr, hzQ, -, -, hzQc, hzRc, hzEc⟩ :=
      exists_three_places_sUnit_prescribed (Ω := Ω) hζ hres hT'stable (hBT.trans hTT')
        hBstable hBwild hBram hT'S hSstable hSsplit hreprS hyS hyinf hyunr' hyB
    exact ⟨Q, R, E, fun hc => hQT (hTT' hc), fun hc => hRT (hTT' hc), fun hc => hET (hTT' hc),
      hQspl, hRspl, hEspl, hQstab, hRstab, hEstab, z, fun v hv => hzT v (hTT' hv), hzinf,
      hzunr, hzQ, hzQc, hzRc, hzEc⟩
  · have hodd : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hne2)
    obtain ⟨Q, R, hQT, hRT, hQspl, hRspl, -, hQstab, hRstab, z, hzT, hzunr, hzQ, -, hzQc, hzRc⟩ :=
      exists_two_places_sUnit_class_eq_of_split (Ω := Ω) (Tr := ∅) hp hodd hζ hres hTstable
        (Finset.empty_subset T) (fun _ v hv => absurd hv (Finset.notMem_empty v)) hpT hysplit
        (fun v hv _ => hyunr v hv) (fun _ _ v hv => absurd hv (Finset.notMem_empty v)) hyp
    have hneg : IsNegOnePow K p := isNegOnePow_of_odd (hp.odd_of_ne_two hne2)
    exact ⟨Q, R, R, hQT, hRT, hRT, hQspl, hRspl, hRspl, hQstab, hRstab, hRstab, z, hzT,
      fun u => infClassHom_eq_one_of_isNegOnePow hp hneg hζ u z,
      fun v h1 h2 _ => hzunr v (Finset.notMem_empty v) h1 h2, hzQ, hzQc, hzRc, hzRc⟩

end Places

end InverseGalois.CFT
