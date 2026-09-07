/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConjugatePlace
import InverseGalois.CFT.PoitouTate.RecursionClose

/-!
# Two completely split places carrying a prescribed local behaviour

The construction of an algebraic number with prescribed local behaviour produces one place at a
time, and the place it produces is completely split in a chosen auxiliary field.  Running that
construction repeatedly, past a bound read off from a pigeonhole argument, and prescribing at the
conjugates of each place produced the inverse of the class of the unit attached to it, yields two
such places and a single unit which is ramified exactly at the two of them, realises the square of
the given prescription on the fixed set, and has trivial class at every nontrivial conjugate of
either place.

This is what the recursion is for: a unit ramified at only one place cannot have trivial class at
the conjugates of that place, since the value at the Frobenius automorphism of a place attached to
a ramified unit is a nontrivial root of unity; a product of two of them can, and that is exactly
the shape the induction on the size of the module being realised needs.

## Main results

* `InverseGalois.CFT.exists_two_places_sUnit_prescribed`: **two places completely split in the
  auxiliary field, and a unit ramified exactly at those two places realising the square of a
  prescribed local behaviour and trivial at all their nontrivial conjugates.**

## Tags

number field, place, completely split, local class, prescription, recursion
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Assembling the recursion over an auxiliary field -/

section Assemble

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Two places completely split in the auxiliary field, and a unit ramified exactly at those two
places.**  The unit realises the square of the prescribed behaviour on the fixed set and has
trivial class at every nontrivial conjugate of either place; it is the product of the two units
attached to the two stages of the recursion which the pigeonhole principle makes agree. -/
theorem exists_two_places_sUnit_prescribed (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hpT : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ T)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (T : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {g : Kˣ} (hg : g ∈ sUnits K (T : Set (HeightOneSpectrum (𝓞 K))))
    (hgunr : ∀ v ∈ T, localClassHom v p g ∈ localUnramified v p)
    (hgp : ∀ v ∈ T, Pc v ∣ p → localClassHom v p g = 1) :
    ∃ Q R : HeightOneSpectrum (𝓞 K), Q ∉ T ∧ R ∉ T ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = Q ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = R ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∀ σ : Gal(K/k), Q ≠ σ • R) ∧
      stabilizer Gal(K/k) Q = ⊥ ∧ stabilizer Gal(K/k) R = ⊥ ∧
      ∃ z : Kˣ, (∀ v ∈ T, localClassHom v p z = localClassHom v p (g ^ 2)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → v ≠ R → (p : ℤ) ∣ placeValue v z) ∧
        ¬ (p : ℤ) ∣ placeValue Q z ∧ ¬ (p : ℤ) ∣ placeValue R z ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Q) p z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • R) p z = 1) := by
  classical
  haveI : IsGalois k ↥Ω := ⟨⟩
  refine exists_prescribed_two_places (Spl := fun v => ∃ w : HeightOneSpectrum (𝓞 ↥Ω),
    primeUnder (𝓞 K) w = v ∧ stabilizer Gal(↥Ω/k) w = ⊥) hp (by omega) hres hζ ?_ hTstable hpT
    hgunr hgp ?_
  · rintro σ v ⟨w, rfl, hw⟩
    exact exists_primeUnder_eq_smul_stabilizer_eq_bot (K := K) hw σ
  · intro S hTS _ c hcunr hc hsplit
    obtain ⟨V, -, hVstab, -, hVnew, z, -, hzS, hzunr, hzram⟩ :=
      exists_place_sUnit_prescribed (Ω := Ω) hp hodd hζ hres
        (Finset.image (primeUnder (𝓞 k)) S) hTS (fun v hv => Finset.mem_image_of_mem _ hv)
        (fun v hv => hTS (hpT v hv))
        (fun m hm => by
          obtain ⟨a, ha⟩ := hrepr m hm
          exact ⟨a, fun v hv => ha v fun hvT => hv (Finset.mem_coe.2 (hTS (Finset.mem_coe.1 hvT)))⟩)
        hcunr (sUnits_mono (Finset.coe_subset.2 hTS) hg) hc hsplit
    exact ⟨primeUnder (𝓞 K) V, hVnew, ⟨V, rfl, hVstab⟩,
      stabilizer_primeUnder_eq_bot (K := K) hVstab, z, hzS, hzunr, hzram⟩

end Assemble

end InverseGalois.CFT
