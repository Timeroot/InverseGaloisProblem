/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.PrimeResidueField

/-!
# Every finite place of the rationals has residue degree one

A finite place of a number field lies over the rational prime it contains, because the ideal that
prime generates is maximal and the ideal below the place is proper.  Over the rationals themselves
there is nothing else to say: the residue degree of a place is at most the degree of the field over
the rationals, which is one, and it is positive, so it is one.

That is the hypothesis under which the residue field of a completion is the prime field, and hence
under which the number of residues of the completion is the rational prime itself.

## Main results

* `InverseGalois.CFT.liesOver_span_of_natCast_mem`: **a finite place lies over the rational prime
  it contains.**
* `InverseGalois.CFT.natCast_natGenerator_mem`: a finite place of the rationals contains the
  rational prime attached to it.
* `InverseGalois.CFT.inertiaDeg_rat_eq_one`: **every finite place of the rationals has residue
  degree one.**
* `InverseGalois.CFT.exists_prime_liesOver_inertiaDeg_eq_one_rat`: the three together.

## Tags

number field, finite place, residue degree, rational prime
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Lying over the rational prime a place contains -/

/-- **A finite place lies over the rational prime it contains.**  The ideal that prime generates is
maximal and is contained in the ideal below the place, which is proper. -/
theorem liesOver_span_of_natCast_mem {K : Type*} [Field K] [NumberField K] {q : ℕ} (hq : q.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI := isMaximal_span_prime hq
  have hle : Ideal.span {(q : ℤ)} ≤ Ideal.under ℤ v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hv
  exact ⟨(isMaximal_span_prime hq).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩

/-! ### The finite places of the rationals -/

/-- A finite place of the rationals contains the rational prime attached to it. -/
theorem natCast_natGenerator_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ Rat.HeightOneSpectrum.natGenerator v := dvd_rfl
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
        ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) from
      (map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) _).symm] at hdvd
  exact Ideal.apply_mem_of_equiv_iff.mp hdvd

/-- **Every finite place of the rationals has residue degree one.**  The residue degree of a place
is at most the degree of the field over the rationals and is positive, and here that degree is
one. -/
theorem inertiaDeg_rat_eq_one {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    [v.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] :
    (Ideal.span {(q : ℤ)}).inertiaDeg v.asIdeal = 1 := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI := isMaximal_span_prime hq
  have hp0 : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using Int.natCast_ne_zero.2 hq.ne_zero
  have hle := Ideal.inertiaDeg_le_finrank (R := ℤ) (S := 𝓞 ℚ) (K := ℚ) (L := ℚ)
    (p := Ideal.span {(q : ℤ)}) v.asIdeal hp0
  have hpos := Ideal.inertiaDeg_pos (R := ℤ) (S := 𝓞 ℚ) (Ideal.span {(q : ℤ)}) v.asIdeal
  rw [Module.finrank_self] at hle
  omega

/-- **The local data at a finite place of the rationals**: the rational prime it contains, the fact
that it lies over that prime, and its residue degree. -/
theorem exists_prime_liesOver_inertiaDeg_eq_one_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∧
      ∃ _ : v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}),
        (Ideal.span {(q : ℤ)}).inertiaDeg v.asIdeal = 1 := by
  have hq : (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    Rat.HeightOneSpectrum.prime_natGenerator v
  have hmem := natCast_natGenerator_mem v
  haveI := liesOver_span_of_natCast_mem hq v hmem
  exact ⟨_, hq, hmem, inferInstance, inertiaDeg_rat_eq_one hq v⟩

end InverseGalois.CFT
