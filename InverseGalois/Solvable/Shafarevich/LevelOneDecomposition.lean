/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.InertiaFinite
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.CFT.Units.StablePlaces
import InverseGalois.Solvable.Shafarevich.ElementaryQuotientDecomposition
import InverseGalois.Solvable.Shafarevich.LevelObstruction
import InverseGalois.Solvable.Shafarevich.LevelOneTwoPlace

/-!
# The finite family of decomposition subgroups of the first rung

The ladder of the descending central series is climbed along a finite family of subgroups of the
absolute Galois group, the family the local conditions are read on.  In the arithmetic that family
is a family of decomposition subgroups at finite places, one for each place of a stable finite set
of places of the level the base realization cuts out, and this file builds it.

The set of places is the one carrying the ideal classes and the places above the exponent, enlarged
so as to contain the places which ramify in the level and any prescribed finite set of places;
above each of its members a prime of the integers of the whole extension is chosen, and the
stabilisers of those primes are the family.  Three things are then true of the family at once.
Each of its members, cut down by the kernel of the base realization, has a finite elementary
quotient, because that is what local class field theory says of a decomposition subgroup.  The
first rung of the ladder has its character over it, because the places the two-place construction
spends are places of the set the family is indexed by, so the character the construction produces
dies on every member.  And away from the conjugates of the family the base realization kills
inertia: a prime whose place of the level is not in the set is a prime whose place is unramified,
so the inertia there already fixes the level, while a prime whose place is in the set is, the
Galois group acting transitively on the primes above a prime of the level, a conjugate of one of
the chosen primes.

## Main results

* `InverseGalois.Shafarevich.exists_decomposition_family`: a finite family of primes of the whole
  extension, containing one above each member of a prescribed finite set of places of the level and
  one above each prime of the whole extension carrying the exponent, whose stabilisers have finite
  elementary quotients against the kernel of the base realization, carry the character of the first
  rung of the ladder, and outside whose conjugates the base realization is unramified.

## Tags

Shafarevich, embedding problem, decomposition subgroup, Frattini layer, two-place construction
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The family and the character it carries -/

section Family

variable {ℓ : ℕ} {U S : Type} [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U]
  [Group S] [Finite S]
  {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]

attribute [local instance] zmodTrivialAction

/-- **A prescribed finite set of places of a level is covered by a finite family of primes of the
whole extension whose stabilisers have finite elementary quotients, carry the character of the
first rung of the ladder, and outside whose conjugates the base realization kills inertia.**

The set of places the family is indexed by carries the places above the exponent whatever is
prescribed, so every prime of the whole extension carrying the exponent is a conjugate of a member
of the family, and its whole decomposition subgroup is carried into a member by that conjugation. -/
theorem exists_decomposition_family (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    {φ : Gal(Ω/k) →* U} (hsurj : Function.Surjective φ) (hsm : IsSmoothHom φ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y)
    (X : Set (HeightOneSpectrum (𝓞 ↥K))) (hX : X.Finite) :
    ∃ (t : ℕ) (Pr : Fin t → Ideal (𝓞 Ω)), (∀ ν, (Pr ν).IsPrime) ∧ (∀ ν, Pr ν ≠ ⊥) ∧
      (∀ v ∈ X, ∃ ν, Ideal.under (𝓞 ↥K) (Pr ν) = v.asIdeal) ∧
      (∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → (ℓ : 𝓞 Ω) ∈ P →
        ∃ (ν : Fin t) (ρ : Gal(Ω/k)), ∀ y ∈ stabilizer Gal(Ω/k) P,
          ρ * y * ρ⁻¹ ∈ stabilizer Gal(Ω/k) (Pr ν)) ∧
      (∀ ν, HasFiniteElementaryQuotient ℓ (stabilizer Gal(Ω/k) (Pr ν) ⊓ φ.ker)) ∧
      (∀ n : ℕ, HasLevelOneCharacter ℓ U S φ
        (Set.range fun ν => stabilizer Gal(Ω/k) (Pr ν)) n) ∧
      ∀ Q : Ideal (𝓞 Ω), Q.IsPrime → Q ≠ ⊥ →
        stabilizer Gal(Ω/k) Q ∉ conjFamily (fun ν => stabilizer Gal(Ω/k) (Pr ν)) →
        ∀ x ∈ Ideal.inertia Gal(Ω/k) Q, φ x = 1 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Tn, hXTn, hTnst, hpTn, hrepr⟩ :=
    exists_stable_ord_places k ↥K (ℓ := ℓ) hℓ.ne_zero
      (X ∪ {v : HeightOneSpectrum (𝓞 ↥K) | Ideal.inertia Gal(↥K/k) v.asIdeal ≠ ⊥})
      (hX.union (finite_setOf_inertia_ne_bot (k := k) (K := ↥K)))
  choose Pf hPfp hPfbot hPfunder using fun v : HeightOneSpectrum (𝓞 ↥K) =>
    exists_stabilizer_prime_restrictNormalHom_eq (K := Ω) K (τ := 1) (v := v) (one_smul _ v)
  refine ⟨Tn.card, fun ν => Pf (Tn.equivFin.symm ν), fun ν => hPfp _, fun ν => hPfbot _,
    fun v hv => ⟨Tn.equivFin ⟨v, hXTn (Or.inl hv)⟩, ?_⟩, fun P hPp hPbot hPℓ => ?_,
    fun ν => ?_, fun n => ?_, fun Q hQp hQbot hQnot x hx => ?_⟩
  · simp only [Equiv.symm_apply_apply]
    exact (hPfunder v).1
  · haveI := hPp
    haveI : (Ideal.under (𝓞 ↥K) P).IsPrime := Ideal.IsPrime.under _ P
    set w : HeightOneSpectrum (𝓞 ↥K) :=
      ⟨Ideal.under (𝓞 ↥K) P, inferInstance, Ideal.under_ne_bot _ hPbot⟩
    have hmkmem : (ℓ : 𝓞 ↥K) ∈ w.asIdeal := by
      show (ℓ : 𝓞 ↥K) ∈ Ideal.under (𝓞 ↥K) P
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hPℓ
    have hmk : FinitePlace.mk w ((ℓ : ℕ) : ↥K) ≠ 1 := fun hc =>
      (finitePlace_natCast_eq_one_iff w ℓ).1 hc hmkmem
    have hkk : Ideal.under (𝓞 k) (Pf w) = Ideal.under (𝓞 k) P := by
      rw [← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) (Pf w),
        ← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) P, (hPfunder w).1]
    haveI := hPfp w
    obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_under_eq_ringOfIntegers (F := k) (K := Ω) (Pf w) P hkk
    refine ⟨Tn.equivFin ⟨w, hpTn w hmk⟩, ρ⁻¹, ?_⟩
    simp only [Equiv.symm_apply_apply]
    intro y hy
    rw [mem_stabilizer_iff] at hy ⊢
    rw [inv_inv, mul_smul, mul_smul, ← hρ, hy, hρ, inv_smul_smul]
  · haveI := hPfp (Tn.equivFin.symm ν : HeightOneSpectrum (𝓞 ↥K))
    exact hasFiniteElementaryQuotient_stabilizer_inf (hPfbot _)
      (isOpenNormal_ker_of_isSmoothHom hsm)
  · refine hasLevelOneCharacter_of_stable hℓ hodd n hsurj _ K hKker hζ hmu hTnst hpTn hrepr ?_
    rintro E ⟨ν, rfl⟩
    exact Or.inl ⟨Pf (Tn.equivFin.symm ν), hPfp _,
      ⟨((Tn.equivFin.symm ν : { x // x ∈ Tn }) : HeightOneSpectrum (𝓞 ↥K)),
        (Tn.equivFin.symm ν).2, (hPfunder _).1.symm⟩, rfl⟩
  · haveI := hQp
    haveI : (Ideal.under (𝓞 ↥K) Q).IsPrime := Ideal.IsPrime.under _ Q
    set w : HeightOneSpectrum (𝓞 ↥K) :=
      ⟨Ideal.under (𝓞 ↥K) Q, inferInstance, Ideal.under_ne_bot _ hQbot⟩ with hwdef
    by_cases hw : w ∈ Tn
    · refine absurd ?_ hQnot
      have hkk : Ideal.under (𝓞 k) (Pf w) = Ideal.under (𝓞 k) Q := by
        rw [← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) (Pf w),
          ← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) Q, (hPfunder w).1]
      haveI := hPfp w
      obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_under_eq_ringOfIntegers (F := k) (K := Ω) (Pf w) Q hkk
      refine ⟨Tn.equivFin ⟨w, hw⟩, ρ, ?_⟩
      simp only [Equiv.symm_apply_apply]
      rw [hρ]
      exact stabilizer_smul_eq_stabilizer_map_conj ρ (Pf w)
    · have hbot : Ideal.inertia Gal(↥K/k) w.asIdeal = ⊥ := by
        by_contra hc
        exact hw (hXTn (Or.inr hc))
      have hunr := (inertia_eq_bot_iff_isUnramifiedAt_base (k := k) (K := ↥K) w.asIdeal
        w.ne_bot).1 hbot
      have hfix := inertia_le_fixingSubgroup_of_isUnramifiedAt (k := k) (Ω := Ω) K hQbot hunr hx
      rw [hKker, MonoidHom.mem_ker] at hfix
      exact hfix

end Family

end InverseGalois.Shafarevich
