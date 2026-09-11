/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.SplitFamily
import InverseGalois.CFT.Units.PrimeAbove
import InverseGalois.Solvable.Shafarevich.LevelOneFamily

/-!
# The first rung from a stable set of places

The arithmetic input of the first rung is a family of units of a level, one for each element of the
layer, each ramified at exactly one place of its own and a local power at every other place the
family touches.  Such a family is built by the two-place construction of the Poitou-Tate directory,
which works over a Galois stable finite set of places carrying the ideal classes and the places
above the exponent, and which asks in addition for an auxiliary field in which the places outside
that set are unramified and the places inside it split completely.  The level itself serves as that
auxiliary field: the places the construction spends outside the prescribed set are exactly the ones
whose decomposition group in the level is trivial, which is what the construction already
guarantees, and every prime is unramified in a field over itself.

With the auxiliary field taken this way the whole of the two-place construction is available with no
data beyond the stable set, and the family it returns, cut down to the size of the layer, is exactly
what the first rung consumes.

## Main results

* `hasLevelOneCharacter_of_stable`: a Galois stable finite set of places carrying the ideal classes
  and the places above the exponent gives the first rung of the ladder its character.

## Tags

Shafarevich, embedding problem, Kummer theory, S-units, two-place construction
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### A level as its own auxiliary field -/

section Self

variable {K : Type*} [Field K] [NumberField K]

/-- The prime below a prime of the integers of a field, taken in that field, is the prime one
started from. -/
theorem primeUnder_self (v : HeightOneSpectrum (𝓞 K)) : primeUnder (𝓞 K) v = v :=
  HeightOneSpectrum.ext (Ideal.comap_id _)

end Self

/-! ### The character of the first rung over a stable set of places -/

section Places

variable {ℓ : ℕ} {U S : Type} [Group U] [Finite U] [Group S] [Finite S]
  {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]

attribute [local instance] zmodTrivialAction

/-- **A Galois stable finite set of places carrying the class group and the places above the
exponent gives the first rung of the ladder its character.** -/
theorem hasLevelOneCharacter_of_stable (hℓ : ℓ.Prime) (hodd : 2 < ℓ) (n : ℕ)
    {φ : Gal(Ω/k) →* U} (hsurj : Function.Surjective φ) (Tf : Set (Subgroup Gal(Ω/k)))
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y)
    {Tn : Finset (HeightOneSpectrum (𝓞 ↥K))}
    (hTnst : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 ↥K), FinitePlace.mk v ((ℓ : ℕ) : ↥K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 ↥K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 ↥K) in Filter.cofinite, m v = 0) →
      ∃ a : (↥K)ˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 ↥K))),
        Rigidity.RET.ord ↥K v (a : ↥K) = m v)
    (hTfsh : ∀ E ∈ Tf, (∃ P : Ideal (𝓞 Ω), ∃ _ : P.IsPrime,
        (∃ v ∈ Tn, v.asIdeal = Ideal.under (𝓞 ↥K) P) ∧ E = stabilizer Gal(Ω/k) P) ∨
      ∃ w : InfinitePlace Ω, E = stabilizer Gal(Ω/k) w) :
    HasLevelOneCharacter ℓ U S φ Tf n := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  choose Pc Ec hres using
    fun v : HeightOneSpectrum (𝓞 ↥K) => exists_hasResidueChar_adicCompletion v
  obtain ⟨Sp, Q, R, z, hfam⟩ :=
    exists_isTwoPlaceFamily (A := Ω) (K := ↥K) (Ω := K) (Pc := Pc) (Ec := Ec) hℓ hodd hζ hres
      (T := ∅) (Finset.empty_subset _) hTnst hpTn hrepr (c := fun _ _ => 1)
      (fun _ v _ => one_mem _) (g := fun _ => 1) (fun _ => one_mem _)
      (fun _ v hv => absurd hv (Finset.notMem_empty v))
      (fun _ _ _ _ => rfl) (fun _ v hv => absurd hv (Finset.notMem_empty v))
      (fun v _ _ => ⟨v, primeUnder_self v, Subgroup.eq_bot_of_subsingleton _⟩)
      (fun v _ => ⟨v, primeUnder_self v, ramIdx_eq_one_of_isUnramifiedAt v⟩)
      (Nat.card ↥(layerSub ℓ (Generic U n S) 0))
  refine hasLevelOneCharacter_of_places_nat hℓ hodd.ne' n hsurj Tf K hKker hζ hmu
    (Tn := (Tn : Set (HeightOneSpectrum (𝓞 ↥K)))) (fun σ v hv => hTnst σ v hv)
    (fun v hv => hpTn v fun hc => (finitePlace_natCast_eq_one_iff v ℓ).1 hc hv) hTfsh _ le_rfl
    Q R z (fun i hi v hv => hfam.prescribed i hi v hv)
    (fun i hi v => hfam.unram i hi v (Finset.notMem_empty v)) hfam.ramQ hfam.conjQ hfam.conjR
    hfam.crossQ hfam.crossR hfam.stabQ hfam.stabR

end Places

end InverseGalois.Shafarevich
