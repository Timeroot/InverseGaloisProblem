/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConjugatePlace
import InverseGalois.CFT.PoitouTate.EvenClose
import InverseGalois.CFT.PoitouTate.RecursionStep

/-!
# Three completely split places carrying a prescribed local behaviour at the exponent two

The construction of an algebraic number with prescribed local behaviour produces one place at a
time, and the place it produces is completely split in a chosen auxiliary field.  At an odd
exponent, running that construction past a pigeonhole bound and prescribing at the conjugates of
each place produced the inverse of the class of the unit attached to it yields *two* such places
and a single unit ramified exactly at them.  At the exponent two the inverse of a class is the
class itself, so no prescription can make two stages cancel; *three* stages do, once the
prescription is allowed to read which member of a pair of mutually inverse automorphisms comes
first and how many stages carrying the same invariant have intervened.

Assembling that recursion over the auxiliary field gives three places, completely split there, and
a single unit ramified exactly at the three of them, realising the prescribed behaviour on the
fixed set exactly: the cube costs nothing at the exponent two, since the square of a local class is
already trivial.

## Main results

* `InverseGalois.CFT.exists_three_places_sUnit_prescribed`: **three places completely split in the
  auxiliary field, and a unit ramified exactly at those three places realising a prescribed local
  behaviour and trivial at all their nontrivial conjugates.**

## Tags

number field, place, completely split, local class, prescription, recursion, quadratic
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Assembling the recursion at the exponent two over an auxiliary field -/

section Assemble

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Three places completely split in the auxiliary field, and a unit ramified exactly at those
three places.**  The unit realises the prescribed behaviour on the fixed set, is a local square at
every infinite place, and has trivial class at every nontrivial conjugate of any of the three; it
is the product of the three units attached to the three stages of the recursion which the
pigeonhole principle makes agree.  The distinguished part of the fixed set carries the places above
the exponent and the places ramified over the base, and the prescription is trivial there. -/
theorem exists_three_places_sUnit_prescribed
    {ζ : K} (hζ : IsPrimitiveRoot ζ 2)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {B T S₀ : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hBT : B ⊆ T)
    (hBstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ B → σ • v ∈ B)
    (hBwild : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((2 : ℕ) : K) ≠ 1 → v ∈ B)
    (hBram : ∀ v : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) v ≠ 1 → v ∈ B)
    (hTS : T ⊆ S₀)
    (hSstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S₀ → σ • v ∈ S₀)
    (hSsplit : ∀ v ∈ S₀, v ∉ T → ∃ w : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(↥Ω/k) w = ⊥)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (S₀ : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {g : Kˣ} (hg : g ∈ sUnits K (S₀ : Set (HeightOneSpectrum (𝓞 K))))
    (hginf : ∀ w : InfinitePlace K, infClassHom w 2 g = 1)
    (hgunr : ∀ v ∈ T, localClassHom v 2 g ∈ localUnramified v 2)
    (hgB : ∀ v ∈ B, localClassHom v 2 g = 1) :
    ∃ Q R S : HeightOneSpectrum (𝓞 K), Q ∉ T ∧ R ∉ T ∧ S ∉ T ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = Q ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = R ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = S ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∀ σ : Gal(K/k), Q ≠ σ • R) ∧ (∀ σ : Gal(K/k), Q ≠ σ • S) ∧
      (∀ σ : Gal(K/k), R ≠ σ • S) ∧
      stabilizer Gal(K/k) Q = ⊥ ∧ stabilizer Gal(K/k) R = ⊥ ∧ stabilizer Gal(K/k) S = ⊥ ∧
      ∃ z : Kˣ, (∀ v ∈ T, localClassHom v 2 z = localClassHom v 2 g) ∧
        (∀ u : InfinitePlace K, infClassHom u 2 z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → v ≠ R → v ≠ S → (2 : ℤ) ∣ placeValue v z) ∧
        ¬ (2 : ℤ) ∣ placeValue Q z ∧ ¬ (2 : ℤ) ∣ placeValue R z ∧
        ¬ (2 : ℤ) ∣ placeValue S z ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Q) 2 z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • R) 2 z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • S) 2 z = 1) := by
  classical
  haveI : IsGalois k ↥Ω := ⟨⟩
  have hpT : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((2 : ℕ) : K) ≠ 1 → v ∈ T :=
    fun v hv => hBT (hBwild v hv)
  have hwild : ∀ v : HeightOneSpectrum (𝓞 K), Pc v ∣ 2 → v ∈ B := fun v hv =>
    hBwild v fun hone => not_dvd_of_finitePlace_natCast_eq_one (hres v) hone hv
  have hcube : ∀ v : HeightOneSpectrum (𝓞 K),
      localClassHom v 2 (g ^ 3) = localClassHom v 2 g := by
    intro v
    rw [_root_.map_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ,
      pow_eq_one_of_quotient_range_powMonoidHom 2 (localClassHom v 2 g)]
    exact one_mul (localClassHom v 2 g)
  obtain ⟨Q, R, S, hQT, hRT, hST, hQspl, hRspl, hSspl, hQR, hQS, hRS, hQstab, hRstab, hSstab,
      z, hzT, hzinf, hzunr, hzQ, hzR, hzS, hzQc, hzRc, hzSc⟩ :=
    exists_prescribed_three_places (Spl := fun v => ∃ w : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) w = v ∧ stabilizer Gal(↥Ω/k) w = ⊥) hres hζ
      (by
        rintro σ v ⟨w, rfl, hw⟩
        exact exists_primeUnder_eq_smul_stabilizer_eq_bot (K := K) hw σ)
      hTstable hBT hBstable hwild hBram hTS hSstable hSsplit hgunr hgB
      (by
        intro S₁ hSS _ c hcunr hc hsplit
        obtain ⟨V, -, hVstab, -, hVnew, w, hwmem, hwinf, hwS, hwunr, hwram⟩ :=
          exists_place_sUnit_prescribed (Ω := Ω) (Tr := ∅) Nat.prime_two hζ hres
            (Finset.image (primeUnder (𝓞 k)) S₁) (hTS.trans hSS)
            (fun v hv => Finset.mem_image_of_mem _ hv)
            (fun v hv => hSS (hTS (hpT v hv)))
            (fun m hm => by
              obtain ⟨a, ha⟩ := hrepr m hm
              exact ⟨a, fun v hv =>
                ha v fun hvT => hv (Finset.mem_coe.2 (hSS (Finset.mem_coe.1 hvT)))⟩)
            (fun v _ _ => hcunr v) (sUnits_mono (Finset.coe_subset.2 hSS) hg) hginf hc hsplit
        refine ⟨primeUnder (𝓞 K) V, hVnew, ⟨V, rfl, hVstab⟩,
          stabilizer_primeUnder_eq_bot (K := K) hVstab, w, hwS, hwinf,
          fun v hv => hwunr v (Finset.notMem_empty v) hv, fun v hv hvne => ?_, hwram⟩
        refine placeValue_eq_zero_of_mem_sUnits hwmem ?_
        simp only [Set.mem_insert_iff, Finset.mem_coe, not_or]
        exact ⟨hvne, hv⟩)
  exact ⟨Q, R, S, hQT, hRT, hST, hQspl, hRspl, hSspl, hQR, hQS, hRS, hQstab, hRstab, hSstab, z,
    fun v hv => (hzT v hv).trans (hcube v), hzinf, hzunr, hzQ, hzR, hzS, hzQc, hzRc, hzSc⟩

end Assemble

end InverseGalois.CFT
