/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaAbelian
import InverseGalois.CFT.Units.AdicLocalNorm
import InverseGalois.CFT.Units.AdicUnitGen
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.IdeleQuotCyclic

/-!
# A class of the right order over the rationals

The computation of the norm quotient of a cyclic extension ramified at a single place applies over
any base whose ring of integers has principal ideals and at which the local conditions can be
checked.  Over the rationals all of that is available: the ring of integers is a principal ideal
ring, the finite places correspond to the rational primes, and the two local hypotheses are
supplied by total reality at the archimedean places and by unramifiedness at the finite ones.

A prime of the ring of integers of the rationals is determined by the rational prime it contains,
so a place of an extension whose prime below is not the distinguished one does not contain the
distinguished rational prime, and a field ramified at most at that prime is unramified there.  The
distinguished unit is the one produced by the cyclicity of the residue field, available because the
residue characteristic exceeds the degree.

## Main results

* `InverseGalois.CFT.ratPlace`: the finite place of the rationals attached to a rational prime.
* `InverseGalois.CFT.heightOneSpectrum_rat_eq_of_natCast_mem`: **a finite place of the rationals is
  determined by the rational prime it contains.**
* `InverseGalois.CFT.isUnramifiedAt_of_ramifiedSet_subset_singleton`: a field ramified at most at
  one rational prime is unramified at every place not containing it.
* `InverseGalois.CFT.exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_rat`: **the second cohomology of
  the idele class group of a totally real cyclic extension of the rationals ramified at a single
  prime contains a class annihilated by exactly the multiples of the degree.**

## Tags

number field, idele class group, fundamental class, cyclic extension, totally real
-/

open IsDedekindDomain NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### The ring of integers of the rationals -/

/-- The ring of integers of the rationals has principal ideals, being isomorphic to the
integers. -/
instance : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm
    Rat.ringOfIntegersEquiv.symm.surjective

/-! ### Finite places of the rationals -/

/-- The rational prime attached to a finite place of the rationals is the one the place contains:
the two are prime numbers dividing one another. -/
theorem natGenerator_eq_of_natCast_mem {q : ℕ} (hq : q.Prime) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : Rat.HeightOneSpectrum.natGenerator v = q := by
  have hcast : ((q : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((q : ℕ) : 𝓞 ℚ) :=
    (map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) q).symm
  have hmem : ((q : ℕ) : ℤ) ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    rw [hcast]
    exact Ideal.apply_mem_of_equiv_iff.mpr hv
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hq).mp
    ((Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mpr hmem)

/-- **A finite place of the rationals is determined by the rational prime it contains.** -/
theorem heightOneSpectrum_rat_eq_of_natCast_mem {q : ℕ} (hq : q.Prime)
    {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
    (Subtype.ext ((natGenerator_eq_of_natCast_mem hq hv).trans
      (natGenerator_eq_of_natCast_mem hq hw).symm))

/-- The finite place of the rationals attached to a rational prime. -/
noncomputable def ratPlace (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

/-- The place attached to a rational prime contains that prime. -/
theorem natCast_mem_ratPlace (q : ℕ) (hq : q.Prime) :
    ((q : ℕ) : 𝓞 ℚ) ∈ (ratPlace q hq).asIdeal := by
  have hng : Rat.HeightOneSpectrum.natGenerator (ratPlace q hq) = q :=
    congrArg Subtype.val
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩)
  have hdvd : Rat.HeightOneSpectrum.natGenerator (ratPlace q hq) ∣ q :=
    Dvd.intro 1 (by rw [hng, mul_one])
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((q : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((q : ℕ) : 𝓞 ℚ) from
      (map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) q).symm] at hdvd
  exact Ideal.apply_mem_of_equiv_iff.mp hdvd

/-! ### Unramifiedness away from a single prime -/

/-- A number field ramified at most at one rational prime is unramified at every finite place not
containing that prime: a place with nontrivial inertia is ramified, so the rational prime below it
is the distinguished one, and the place then contains it. -/
theorem isUnramifiedAt_of_ramifiedSet_subset_singleton {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] {q : ℕ} (hq : q.Prime) (hram : ramifiedSet K ⊆ {q})
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((q : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  refine (inertia_eq_bot_iff_isUnramifiedAt_base (k := ℚ) w.asIdeal w.ne_bot).mp ?_
  by_contra hne
  obtain ⟨p, hp, hpu⟩ := exists_prime_under w.asIdeal w.ne_bot
  have hmem := hram (mem_ramifiedSet_of_inertia_ne_bot w.asIdeal w.ne_bot p hp hpu hne)
  rw [Set.mem_singleton_iff] at hmem
  subst hmem
  refine hw ?_
  have h1 : (p : ℤ) ∈ Ideal.under ℤ w.asIdeal := by
    rw [hpu]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.under_def, Ideal.mem_comap] at h1
  simpa using h1

/-! ### The class of the right order -/

section Class

open groupCohomology

variable (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]

/-- **The second cohomology of the idele class group of a totally real cyclic extension of the
rationals ramified at a single prime contains a class annihilated by exactly the multiples of the
degree.**  Total reality makes every local unit at an archimedean place a norm, unramifiedness away
from the distinguished prime makes every local unit there a norm, and the residue field at the
distinguished prime is cyclic of order prime to the degree, so its units are generated modulo
degree-th powers by a single element. -/
theorem exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_rat [IsCyclic Gal(K/ℚ)] [IsTotallyReal K]
    {q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ Nat.card Gal(K/ℚ)) (hram : ramifiedSet K ⊆ {q}) :
    ∃ α : ↥(H2 (ideleClassRep ℚ K)), ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/ℚ) : ℤ) ∣ m := by
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := Gal(K/ℚ))
  obtain ⟨g, hg⟩ := exists_unitGen_pow_mul_pow ℚ (ratPlace q hq) hq (natCast_mem_ratPlace q hq)
    (Nat.card_pos (α := Gal(K/ℚ))).ne' hqn
  refine exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep (k := ℚ) K hgen (ratPlace q hq)
    (fun w b => mem_normSubgroup_infiniteCompletion_of_isReal ℚ w (IsTotallyReal.isReal w) b)
    (fun w hne b hb => ?_) hg
  refine mem_normSubgroup_adicCompletion_of_isUnramifiedAt ℚ w ?_ hb
  refine isUnramifiedAt_of_ramifiedSet_subset_singleton hq hram w fun hmem => hne ?_
  refine heightOneSpectrum_rat_eq_of_natCast_mem hq ?_ (natCast_mem_ratPlace q hq)
  rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact hmem

end Class

end InverseGalois.CFT
