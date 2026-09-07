/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.RelativeSplitDensity

/-!
# Almost every prime of a number field has residue degree one over the rationals

The absolute norm of a prime of a number field is a power of its residue characteristic, so a
prime either has absolute norm equal to that characteristic — its residue field is the prime
field — or has absolute norm at least the square of it.  The second kind is rare: the sum
`∑_𝔭 (char 𝔭)^{-2}` over *all* primes converges, because the primes over a given rational prime
are at most `[K : ℚ]` in number and `∑_p p^{-2}` converges.  So the Dirichlet series of the primes
of residue degree greater than one is bounded independently of `s`, and those primes have
Dirichlet density zero.

A set of density zero is as harmless as a finite set when one compares densities, and the
comparison used to produce split primes tolerates one of each.  Intersecting the primes that split
completely in a Galois extension but not in a larger one with the primes of residue degree one
therefore still leaves infinitely many.  That refinement is what makes a Frobenius element
computed over an intermediate field agree with the one computed over the base: for a prime of
residue degree one over the rationals, every field between the rationals and the number field sees
the same decomposition group.

## Main definitions

* `InverseGalois.NumberTheory.degreeOneSet` — the primes of a number field whose absolute norm is
  their residue characteristic.

## Main results

* `InverseGalois.NumberTheory.sq_resChar_le_absNorm` — a prime whose absolute norm is not its
  residue characteristic has absolute norm at least the square of it.
* `InverseGalois.NumberTheory.hasIdealDensity_compl_degreeOneSet` — **the primes of residue degree
  greater than one have Dirichlet density zero.**
* `InverseGalois.NumberTheory.idealDensity_le_of_subset_union₂` — densities are monotone up to a
  finite set together with a set of density zero.
* `InverseGalois.NumberTheory.infinite_setOf_splitsCompletelyIn_not_splitsCompletelyIn_degreeOne`
  — **infinitely many primes of residue degree one split completely in a smaller Galois extension
  but not in a larger one.**

## Tags

Dirichlet density, residue degree, residue characteristic, splitting of primes, number field
-/

open NumberField Ideal Filter Topology IsDedekindDomain

namespace InverseGalois.NumberTheory

section DegreeOne

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The primes of a number field whose absolute norm is their residue characteristic, that is,
whose residue field is the prime field. -/
noncomputable def degreeOneSet : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | absNorm v.asIdeal = resChar v}

/-- **A prime whose absolute norm is not its residue characteristic has absolute norm at least the
square of it**, since the cofactor is itself a divisor of the norm exceeding one and so at least
the least prime factor. -/
theorem sq_resChar_le_absNorm {v : HeightOneSpectrum (𝓞 K)}
    (hv : absNorm v.asIdeal ≠ resChar v) : resChar v ^ 2 ≤ absNorm v.asIdeal := by
  have h2 : 2 ≤ absNorm v.asIdeal := two_le_absNorm v
  have hne : absNorm v.asIdeal ≠ 1 := by omega
  obtain ⟨m, hm⟩ := (absNorm v.asIdeal).minFac_dvd
  have hp : resChar v = (absNorm v.asIdeal).minFac := rfl
  have hm1 : m ≠ 1 := by
    intro h
    rw [h, mul_one] at hm
    exact hv (by rw [hp, ← hm])
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    omega
  have hm2 : 2 ≤ m := by omega
  have hdvd : m ∣ absNorm v.asIdeal := ⟨(absNorm v.asIdeal).minFac, by rw [mul_comm]; exact hm⟩
  have hle : resChar v ≤ m := hp ▸ Nat.minFac_le_of_dvd hm2 hdvd
  calc resChar v ^ 2 = resChar v * resChar v := sq _
    _ ≤ (absNorm v.asIdeal).minFac * m := Nat.mul_le_mul (le_of_eq hp) hle
    _ = absNorm v.asIdeal := hm.symm

/-- **The squares of the residue characteristics of the primes of a number field are summable**,
because at most `[K : ℚ]` primes share a residue characteristic and the squares of the rational
primes are summable. -/
theorem summable_resCharSqInv :
    Summable fun v : HeightOneSpectrum (𝓞 K) => ((resChar v : ℝ)) ^ (-2 : ℝ) := by
  refine summable_of_fiber_bound (fun v => Real.rpow_nonneg (by positivity) _)
    (fun m => (Module.finrank ℚ K : ℝ) * ((m : ℝ) ^ (-2 : ℝ)))
    ((Real.summable_nat_rpow.mpr (by norm_num)).mul_left _) (fun m => ?_)
  refine tsum_fiber_le (fun v : HeightOneSpectrum (𝓞 K) => ((resChar v : ℝ)) ^ (-2 : ℝ)) m
    ((m : ℝ) ^ (-2 : ℝ)) (Real.rpow_nonneg (by positivity) _) (fun v hv => ?_)
  show ((resChar v : ℝ)) ^ (-2 : ℝ) ≤ ((m : ℝ)) ^ (-2 : ℝ)
  rw [hv]

variable (K) in
/-- The sum of the reciprocal squares of the residue characteristics of the primes of a number
field, an absolute constant of the field. -/
noncomputable def resCharSqSum : ℝ :=
  ∑' v : HeightOneSpectrum (𝓞 K), ((resChar v : ℝ)) ^ (-2 : ℝ)

/-- **The Dirichlet series of the primes of residue degree greater than one is bounded by an
absolute constant of the field**, uniformly in the exponent. -/
theorem idealSum_compl_degreeOneSet_le {s : ℝ} (hs : 1 < s) :
    idealSum (degreeOneSet K)ᶜ s ≤ resCharSqSum K := by
  have hbound : ∀ v : ↥(degreeOneSet K)ᶜ, normPow s v.1 ≤ ((resChar v.1 : ℝ)) ^ (-2 : ℝ) := by
    rintro ⟨v, hv⟩
    exact normPow_le_rpow_neg_two_of_sq_le hs.le (resChar_prime v).two_le v
      (sq_resChar_le_absNorm hv)
  calc idealSum (degreeOneSet K)ᶜ s
      ≤ ∑' v : ↥(degreeOneSet K)ᶜ, ((resChar v.1 : ℝ)) ^ (-2 : ℝ) :=
        Summable.tsum_le_tsum hbound (summable_normPow_subtype hs _)
          (summable_resCharSqInv.subtype _)
    _ ≤ resCharSqSum K :=
        Summable.tsum_subtype_le _ _ (fun v => Real.rpow_nonneg (by positivity) _)
          summable_resCharSqInv

/-- **The primes of a number field whose residue field is larger than the prime field have
Dirichlet density zero.** -/
theorem hasIdealDensity_compl_degreeOneSet : HasIdealDensity (degreeOneSet K)ᶜ 0 := by
  have hb : Tendsto (fun s : ℝ => resCharSqSum K / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_logWeight
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hL, abs_of_nonneg (idealSum_nonneg _)]
  gcongr
  exact idealSum_compl_degreeOneSet_le (Set.mem_Ioi.mp hs)

/-- Dirichlet series over the primes are subadditive along a covering of one set by three
others. -/
theorem idealSum_le_of_subset_union₂ {S T₁ T₂ F : Set (HeightOneSpectrum (𝓞 K))}
    (hsub : S ⊆ F ∪ (T₁ ∪ T₂)) {s : ℝ} (hs : 1 < s) :
    idealSum S s ≤ idealSum F s + idealSum T₁ s + idealSum T₂ s := by
  have h1 := idealSum_le_of_subset_union hsub hs
  have h2 := idealSum_le_of_subset_union (S := T₁ ∪ T₂) (F := T₁) (T := T₂) subset_rfl hs
  linarith

/-- **Densities are monotone up to a finite set together with a set of density zero.** -/
theorem idealDensity_le_of_subset_union₂ {S T F F' : Set (HeightOneSpectrum (𝓞 K))}
    (hF : F.Finite) (hF' : HasIdealDensity F' 0) (hsub : S ⊆ F ∪ (F' ∪ T)) {a b : ℝ}
    (hS : HasIdealDensity S a) (hT : HasIdealDensity T b) : a ≤ b := by
  have hsum := ((hasIdealDensity_of_finite hF).add hF').add hT
  rw [zero_add, zero_add] at hsum
  refine le_of_tendsto_of_tendsto hS hsum ?_
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  rw [← add_div, ← add_div]
  gcongr
  exact idealSum_le_of_subset_union₂ hsub (Set.mem_Ioi.mp hs)

end DegreeOne

/-- **The primes of residue degree one over the rationals that split completely in a smaller
Galois extension but not in a larger one are infinite in number.**  Were they finite, the
completely split primes of the smaller extension would be covered by a finite set, the primes of
residue degree greater than one, and the completely split primes of the larger extension; the
middle set has density zero, so comparing densities would give `1/[A : k] ≤ 1/[B : k]`. -/
theorem infinite_setOf_splitsCompletelyIn_not_splitsCompletelyIn_degreeOne
    (k : Type*) [Field k] [NumberField k]
    (A : Type*) [Field A] [NumberField A] [Algebra k A] [IsGalois k A]
    (B : Type*) [Field B] [NumberField B] [Algebra k B] [IsGalois k B]
    (hlt : Module.finrank k A < Module.finrank k B) :
    {v : HeightOneSpectrum (𝓞 k) | SplitsCompletelyIn k A v ∧ ¬ SplitsCompletelyIn k B v ∧
      absNorm v.asIdeal = resChar v}.Infinite := by
  intro hfin
  have hsub : relSplitSet k A ⊆
      {v : HeightOneSpectrum (𝓞 k) | SplitsCompletelyIn k A v ∧ ¬ SplitsCompletelyIn k B v ∧
        absNorm v.asIdeal = resChar v} ∪ ((degreeOneSet k)ᶜ ∪ relSplitSet k B) := by
    intro v hv
    by_cases hd : absNorm v.asIdeal = resChar v
    · by_cases hB : SplitsCompletelyIn k B v
      · exact Or.inr (Or.inr hB)
      · exact Or.inl ⟨hv, hB, hd⟩
    · exact Or.inr (Or.inl hd)
  have hle := idealDensity_le_of_subset_union₂ hfin hasIdealDensity_compl_degreeOneSet hsub
    (hasIdealDensity_relSplitSet (k := k) (L := A)) (hasIdealDensity_relSplitSet (k := k) (L := B))
  have hApos : (0 : ℝ) < (Module.finrank k A : ℝ) := by
    have := Module.finrank_pos (R := k) (M := A)
    positivity
  have hBpos : (0 : ℝ) < (Module.finrank k B : ℝ) := by
    have := Module.finrank_pos (R := k) (M := B)
    positivity
  have hltR : (Module.finrank k A : ℝ) < (Module.finrank k B : ℝ) := by exact_mod_cast hlt
  have hkey : (Module.finrank k B : ℝ) ≤ (Module.finrank k A : ℝ) := by
    by_contra hc
    push_neg at hc
    have hcontra : 1 / (Module.finrank k B : ℝ) < 1 / (Module.finrank k A : ℝ) :=
      one_div_lt_one_div_of_lt hApos hc
    linarith
  linarith

end InverseGalois.NumberTheory
