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
family touches.  Such a family is built by the split place construction of the Poitou-Tate
directory, which works over a Galois stable finite set of places carrying the ideal classes, the
places above the exponent and the places ramified over the base, and which asks in addition for an
auxiliary field in which the places outside that set are unramified and the places inside it split
completely.  The level itself serves as that auxiliary field: the places the construction spends
outside the prescribed set are exactly the ones whose decomposition group in the level is trivial,
which is what the construction already guarantees, and every prime is unramified in a field over
itself.

Enlarging the stable set costs nothing.  The places ramified over the base are the prime divisors of
the different, so there are only finitely many of them, and the union of their orbits with the set
one started from is again a finite stable set; the condition on systems of orders away from the set
only weakens when the set grows.  Over the enlarged set the prescription can be taken trivial, so
the whole of the construction is available with no data beyond the stable set, and the family it
returns, cut down to the size of the layer, is exactly what the first rung consumes.

## Main results

* `InverseGalois.Shafarevich.finite_setOf_ramIdx_ne_one`: only finitely many places of a number
  field are ramified over a subfield.
* `hasLevelOneCharacter_of_stable`: a Galois stable finite set of places carrying the ideal classes
  and the places above the exponent gives the first rung of the ladder its character.

## Tags

Shafarevich, embedding problem, Kummer theory, S-units, different, split place construction
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

/-! ### The places ramified over the base -/

section Ram

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- **Only finitely many places of a number field are ramified over a subfield.**  A place is
unramified exactly when it does not divide the different, the different is nonzero, and a nonzero
ideal has finitely many prime divisors. -/
theorem finite_setOf_ramIdx_ne_one (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] :
    {W : HeightOneSpectrum (𝓞 K) | ramIdx (𝓞 k) W ≠ 1}.Finite := by
  have hD : differentIdeal (𝓞 k) (𝓞 K) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using (differentIdeal_ne_bot (A := 𝓞 k) (B := 𝓞 K))
  refine (Ideal.finite_factors hD).subset fun W hW => ?_
  by_contra hnd
  haveI : W.asIdeal.IsPrime := W.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 k) W.asIdeal := not_dvd_differentIdeal_iff.1 hnd
  exact hW (ramIdx_eq_one_of_isUnramifiedAt W)

end Ram

/-! ### The character of the first rung over a stable set of places -/

section Places

variable {ℓ : ℕ} {U S : Type} [Group U] [Finite U] [Group S] [Finite S]
  {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]

attribute [local instance] zmodTrivialAction

/-- **A Galois stable finite set of places carrying the class group and the places above the
exponent gives the first rung of the ladder its character.** -/
theorem hasLevelOneCharacter_of_stable (hℓ : ℓ.Prime) (n : ℕ)
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
  haveI : Finite Gal(↥K/k) := Finite.of_fintype _
  choose Pc Ec hres using
    fun v : HeightOneSpectrum (𝓞 ↥K) => exists_hasResidueChar_adicCompletion v
  obtain ⟨Bs, hBs, hBsfin, hBsst⟩ := exists_finite_stable_superset (G := Gal(↥K/k))
    {W : HeightOneSpectrum (𝓞 ↥K) | ramIdx (𝓞 k) W ≠ 1} (finite_setOf_ramIdx_ne_one k ↥K)
  obtain ⟨B, hBdef⟩ : ∃ B : Finset (HeightOneSpectrum (𝓞 ↥K)), B = Tn ∪ hBsfin.toFinset :=
    ⟨_, rfl⟩
  have hBTn : ∀ v : HeightOneSpectrum (𝓞 ↥K), v ∈ Tn → v ∈ B := by
    intro v hv
    rw [hBdef]
    exact Finset.mem_union_left _ hv
  have hBram : ∀ v : HeightOneSpectrum (𝓞 ↥K), ramIdx (𝓞 k) v ≠ 1 → v ∈ B := by
    intro v hv
    rw [hBdef]
    exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 (hBs hv))
  have hBst : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ B → σ • v ∈ B := by
    intro σ v hv
    rw [hBdef, Finset.mem_union] at hv ⊢
    refine hv.elim (fun h => Or.inl (hTnst σ v h)) fun h => Or.inr ?_
    rw [Set.Finite.mem_toFinset] at h ⊢
    exact (hBsst σ v).2 h
  obtain ⟨Sp, Q, R, E, z, hfam⟩ :=
    exists_isTwoPlaceFamily (A := Ω) (K := ↥K) (Ω := K) (Pc := Pc) (Ec := Ec) hℓ hζ hres
      (B := B) (T := B) (Tn := B) (Finset.Subset.refl B) (Finset.Subset.refl B) hBst
      (fun v hv => hBTn v (hpTn v hv)) hBram hBst
      (fun m hm => by
        obtain ⟨a, ha⟩ := hrepr m hm
        exact ⟨a, fun v hv => ha v fun hc => hv (hBTn v hc)⟩)
      (c := fun _ _ => 1) (fun _ v _ => one_mem _) (fun _ _ _ => rfl)
      (g := fun _ => 1) (fun _ => one_mem _) (fun _ u => _root_.map_one (infClassHom u ℓ))
      (fun _ v _ => (_root_.map_one (localClassHom v ℓ)).symm) (fun _ _ _ _ => rfl)
      (fun v hv hvn => absurd hv hvn)
      (fun v _ => ⟨v, primeUnder_self v, ramIdx_eq_one_of_isUnramifiedAt v⟩)
      (Nat.card ↥(layerSub ℓ (Generic U n S) 0))
  refine hasLevelOneCharacter_of_places_nat hℓ n hsurj Tf K hKker hζ hmu
    (Tn := (Tn : Set (HeightOneSpectrum (𝓞 ↥K)))) (fun σ v hv => hTnst σ v hv)
    (fun v hv => hpTn v fun hc => (finitePlace_natCast_eq_one_iff v ℓ).1 hc hv) hTfsh _ le_rfl
    Q R E z (fun i hi v hv => hfam.prescribed i hi v (hBTn v hv)) hfam.inf
    (fun i hi v => hfam.unram i hi v (Finset.notMem_empty v)) hfam.ramQ hfam.conjQ hfam.conjR
    hfam.conjE hfam.crossQ hfam.crossR hfam.crossE hfam.stabQ hfam.stabR hfam.stabE

end Places

end InverseGalois.Shafarevich
