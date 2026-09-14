/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.FlatSylowUnits

/-!
# The obstruction, bought with a unit fixed on the nose

The units the obstruction is bought with are asked to be fixed modulo exponent-th powers under a
subgroup of the decomposition group whose order is a power of the exponent.  This file trades that
demand for the sharper one of a unit fixed on the nose under that subgroup, and for a demand which
asks nothing equivariant beyond that: the divisor class statement of a reachable place, with a unit
the subgroup fixes.

Asking the unit to be fixed outright is more than the obstruction reads, and it is what the
arithmetic of the fixed field of the subgroup supplies.  A group of order a power of the exponent
acts trivially on the roots of unity of order the exponent, so those roots already lie in the fixed
field; a place fixed by the subgroup and unramified in the level over the fixed field is the only
place of the level lying over its own trace there; and a unit of the fixed field is fixed by the
subgroup by construction, with the order it has below read unchanged above.

The passage from a unit fixed on the nose to the unit the obstruction is bought with costs only a
power.  The order at the named place is prime to the exponent, so raising to a power inverse to it
modulo the exponent brings that order back to one, and leaves every other order divisible by the
exponent and the unit fixed.  Nothing is left to spend the invariance modulo exponent-th powers on,
so the witness of that invariance is the trivial unit.

Which places admit such a unit is settled by the ramification alone: the units the subgroup fixes
are the units of its fixed field, and their orders at the place are the multiples of the
ramification index there, so an order prime to the exponent is available exactly when the exponent
does not divide that index.  The places the obstruction is read at all carry that much for free.
They arrive with their order already taken by an element the whole group of automorphisms fixes —
the named primes are unramified in the level, so a uniformiser of the place below is such an element
— and a unit the whole group fixes is in particular one any subgroup fixes.

## Main definitions

* `InverseGalois.Shafarevich.IsFixedReachablePlace`: the divisor the prescription asks for at a
  named place, cut out by a unit a given subgroup of the automorphisms fixing the place fixes.
* `InverseGalois.Shafarevich.HasFixedReachablePlaces`: every place of a level already reached by a
  unit fixed under a subgroup of order a power of the exponent, reached with all of the
  prescription.
* `Shafarevich.FixedReachableEP`: the same, made of every level.

## Main results

* `InverseGalois.Shafarevich.hasSylowConfinedUnits_of_hasFixedReachablePlaces`: **a unit fixed on
  the nose buys the units the obstruction is bought with**.
* `Shafarevich.genericLevelStepEPRoots_of_fixedReachableEP`: the step of the ladder over an odd
  prime, in exchange for the demand.

## Tags

Shafarevich's theorem, embedding problem, S-unit, confined unit, decomposition group, obstruction
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

/-! ### Reaching a place under a subgroup of order a prime power -/

section Reachable

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **The divisor the prescription asks for at a named place, cut out by a unit a given subgroup of
the automorphisms fixing the place fixes.**

This is the divisor class statement of a reachable place with one clause added: the unit is fixed by
the subgroup outright.  Everything else is unchanged — the order at the named place is prime to the
exponent, the unit is a local power at the places the radicand is kept inert at, its order is
divisible by the exponent at a prescribed finite set the named place avoids, and elsewhere an order
prime to the exponent is allowed only at places lying below primes completely decomposed in the
bigger level.

The subgroup is meant to have order a power of the exponent and to fix the place, which is what
makes the demand meetable: its fixed field carries the roots of unity of order the exponent, and the
place has a single place of the fixed field below it whose own extension to the level is
unramified. -/
def IsFixedReachablePlace (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K]
    (E : IntermediateField k Ω) (P : Subgroup Gal(↥K/k))
    (Tz : Set (HeightOneSpectrum (𝓞 ↥K))) (w : HeightOneSpectrum (𝓞 ↥K)) : Prop :=
  w ∉ Tz → ∀ Xex : Set (HeightOneSpectrum (𝓞 ↥K)), Xex.Finite → w ∉ Xex →
    ∃ u : (↥K)ˣ, (∀ σ ∈ P, σ • u = u) ∧ ¬ (ℓ : ℤ) ∣ placeValue w u ∧
      (∀ v ∈ Tz, localClassHom v ℓ u = 1) ∧
      (∀ v ∈ Xex, (ℓ : ℤ) ∣ placeValue v u) ∧
      ∀ v : HeightOneSpectrum (𝓞 ↥K), v ≠ w → ¬ (ℓ : ℤ) ∣ placeValue v u →
        ∀ Q : Ideal (𝓞 Ω), Q.IsPrime → Q ≠ ⊥ → Ideal.under (𝓞 ↥K) Q = v.asIdeal →
          stabilizer Gal(Ω/k) Q ≤ E.fixingSubgroup

/-- **Every place of a level a fixed unit already reaches is reached with all of the prescription,
under every subgroup of order a power of the exponent which fixes it.**

The set of places the radicand is kept inert at is a stable one, as it is where the demand is
consumed, and the subgroup is arbitrary among those of order a power of the exponent fixing the
place, so the demand is made of the Sylow subgroups of each decomposition group and of nothing
larger.

A single unit the subgroup fixes and whose order at the place is prime to the exponent is asked for
in advance.  That much is a statement about the ramification alone: the fixed units of the level are
the units of the fixed field, and their orders at the place run over the multiples of the
ramification index of the place there, so such a unit exists exactly when the exponent does not
divide that index.  What the demand adds is the rest of the prescription — the local powers, the
avoided orders, and the decomposition of the remaining places in the bigger level — at a place where
the ramification already allows it.

The subgroup is cyclic, which the unit asked for in advance already forces: its order at the place
being prime to the exponent makes the ramification index there prime to the exponent, so a subgroup
of order a power of the exponent fixing the place meets inertia trivially and embeds in the cyclic
quotient of the decomposition group by inertia. -/
def HasFixedReachablePlaces (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ Tz : Set (HeightOneSpectrum (𝓞 ↥K)), Tz.Finite →
      ∀ P : Subgroup Gal(↥K/k), IsPGroup ℓ ↥P → IsCyclic ↥P →
        ∀ w : HeightOneSpectrum (𝓞 ↥K), (∀ σ ∈ P, σ • w = w) →
          (∃ x : (↥K)ˣ, (∀ σ ∈ P, σ • x = x) ∧ ¬ (ℓ : ℤ) ∣ placeValue w x) →
          IsFixedReachablePlace ℓ K E P (stableHull k ↥K Tz) w

end Reachable

/-! ### The units, bought from a unit fixed on the nose -/

section Units

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **A unit fixed on the nose buys the units the obstruction is bought with, at the places whose
ramification allows one.**

The unit reaching the place is confined: it is a local power where the radicand is kept inert, and
where its order is prime to the exponent the place either is the named one, or lies in the hull of
the named ones and so is excluded in advance, or lies below primes completely decomposed in the
bigger level.  Its order at the named place is prime to the exponent and divisible by it at the
other places of the hull, so a power of it with exponent inverse to that order modulo the exponent
has the vector of orders asked for.  Being fixed survives the power, and a unit fixed outright is
fixed modulo exponent-th powers by the trivial witness.

A unit of order prime to the exponent fixed by the subgroup is available for free: the place arrives
with its order taken by an element the whole group of automorphisms fixes. -/
theorem hasSylowConfinedUnits_of_hasFixedReachablePlaces {ℓ : ℕ} [Fact ℓ.Prime]
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K] [FiniteDimensional k ↥K]
    (h : HasFixedReachablePlaces ℓ K) :
    HasSylowConfinedUnits ℓ K := by
  classical
  intro E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz _hreach hfin _hsurj y hyTz hybase _hyσ P hP hPcyc hPfix
  haveI := hfin
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI := isGaloisStablePlaces_decomposedPlaces (K := K) (E := E)
  obtain ⟨x, hxfix, hxord⟩ := hybase
  have hx : ∃ x : (↥K)ˣ, (∀ σ ∈ P, σ • x = x) ∧
      ¬ (ℓ : ℤ) ∣ placeValue (y : HeightOneSpectrum (𝓞 ↥K)) x :=
    ⟨x, fun σ _ => hxfix σ, hxord⟩
  have hXexfin : ((stableHull k ↥K Xs₀) \ {(y : HeightOneSpectrum (𝓞 ↥K))}).Finite :=
    (stableHull_finite hXs₀).subset Set.diff_subset
  obtain ⟨u, hinv, hordy, hTzu, hXex, hconf⟩ :=
    h E hEfin hEgal hKE Tz hTz P hP hPcyc (y : HeightOneSpectrum (𝓞 ↥K))
      (fun σ hσ => congrArg Subtype.val (hPfix σ hσ)) hx hyTz _ hXexfin fun hc => hc.2 rfl
  have hmem : u ∈ confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) := by
    refine ⟨hTzu, fun v hv => ?_⟩
    have hpv : (ℓ : ℤ) ∣ placeValue v u := by
      by_contra hcon
      by_cases hvy : v = (y : HeightOneSpectrum (𝓞 ↥K))
      · exact hv (mem_allowedPlaces.2 (Or.inl (hvy ▸ y.2)))
      · refine hv (mem_allowedPlaces.2 (Or.inr ?_))
        rw [stableCore_eq_self (k := k) (S := decomposedPlaces K E)]
        exact hconf v hvy hcon
    rwa [placeValue_eq_neg_ord, dvd_neg] at hpv
  obtain ⟨U, rfl⟩ : ∃ U : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
      (U : (↥K)ˣ) = u := ⟨⟨u, hmem⟩, rfl⟩
  have hval : ∀ z : ↥(stableHull k ↥K Xs₀),
      confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀)
        (Additive.ofMul U) z
        = - placeValue (z : HeightOneSpectrum (𝓞 ↥K)) (U : (↥K)ˣ) := fun z => by
    rw [confinedOrd_apply, placeValue_eq_neg_ord, neg_neg]
    rfl
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)
      (stableHull k ↥K Xs₀) (Additive.ofMul U) y := ⟨_, rfl⟩
  have hAne : ((A : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, hA, hval y]
    exact fun hc => hordy ((dvd_neg).1 hc)
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m' = (((A : ℤ) : ZMod ℓ)⁻¹).val := ⟨_, rfl⟩
  have hmm' : (ℓ : ℤ) ∣ (m' : ℤ) * A - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hm', ZMod.natCast_val, ZMod.cast_id, inv_mul_cancel₀ hAne, sub_self]
  have hpow : ∀ (n : ℕ) (z : ↥(stableHull k ↥K Xs₀)),
      confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀)
          (Additive.ofMul (U ^ n)) z
        = (n : ℤ) * confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)
          (stableHull k ↥K Xs₀) (Additive.ofMul U) z := by
    intro n z
    rw [_root_.ofMul_pow, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  refine ⟨U ^ m', fun z => ?_, fun σ hσ => ⟨1, ?_⟩⟩
  · rw [hpow]
    by_cases hzy : z = y
    · rw [hzy, Finsupp.single_eq_same, ← hA]
      exact hmm'
    · rw [Finsupp.single_eq_of_ne hzy, sub_zero, hval z]
      exact dvd_mul_of_dvd_right
        (dvd_neg.2 (hXex _ ⟨z.2, fun hc => hzy (Subtype.ext hc)⟩)) _
  · rw [one_pow, mul_one, smul_pow']
    congr 1
    exact Subtype.ext (by rw [coe_smul_stableSubgroup, hinv σ hσ])

end Units

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

/-! ### The units fixed on the nose, made of every level -/

/-- **Every finite Galois level of a number field inside an algebraic closure carrying a primitive
root of unity of the exponent reaches, with all of the prescription, every one of its places already
reached by a unit fixed under a subgroup of order a power of the exponent.** -/
def FixedReachableEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasFixedReachablePlaces ℓ K

/-- **A unit fixed on the nose buys the units asked under a subgroup of order a power of the
exponent**, at every level. -/
theorem sylowConfinedUnitsEP_of_fixedReachableEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : FixedReachableEP ℓ) : SylowConfinedUnitsEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ hζ
  exact hasSylowConfinedUnits_of_hasFixedReachablePlaces (h k Ω K hζ)

/-- **The step of the ladder over an odd prime**, in exchange for units fixed on the nose by a
subgroup of order a power of the prime. -/
theorem genericLevelStepEPRoots_of_fixedReachableEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hfix : FixedReachableEP ℓ) :
    GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_sylowConfinedUnitsEP ℓ hodd
    (sylowConfinedUnitsEP_of_fixedReachableEP ℓ hfix)

end Shafarevich
