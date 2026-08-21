/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.IdealEulerProduct
import InverseGalois.NumberTheory.SplitCompletely

/-!
# The Dirichlet density of the completely split primes

A set `S` of rational primes is said to have Dirichlet density `d` when the ratio of
`∑_{p ∈ S} p^{-s}` to `log (1/(s-1))` tends to `d` as `s` decreases to `1` along the reals.  The
denominator is the correct normalisation because `∑_p p^{-s}`, taken over *all* primes, is itself
asymptotic to `log (1/(s-1))`; a density is therefore a proportion, and the whole set of primes
has density one.

For a number field `K` which is Galois over `ℚ` of degree `n`, the primes that split completely
in `K` have density `1/n`.  The proof is the classical one.  Taking the logarithm of the Euler
product for the Dedekind zeta function of `K` expresses `log ζ_K(s)` as a sum of the quantities
`-log (1 - N𝔭^{-s})` over the primes `𝔭` of the ring of integers.  Each such quantity differs
from `N𝔭^{-s}` by at most `2 N𝔭^{-2s}`, and grouping the primes `𝔭` according to the rational
prime `p` they lie above shows that the total contribution of the terms `N𝔭^{-2s}` is bounded
independently of `s`.  Above an unramified rational prime `p` all residue degrees agree, by the
transitivity of the Galois action on the primes over `p`; so either `p` splits completely, and
contributes exactly `n` primes of norm `p`, or every prime above `p` has norm at least `p²` and
the whole fibre is again absorbed into the error.  Only finitely many rational primes ramify, by
the theorem of Kummer and Dedekind, and those are absorbed as well.  What is left is
`log ζ_K(s) = n · ∑_{p split} p^{-s} + O(1)`, and the simple pole of `ζ_K` at `s = 1` turns the
left-hand side into `log (1/(s-1)) + O(1)`.

The Euler product itself is not proved here; it enters as the hypothesis
`InverseGalois.NumberTheory.EulerProductHypothesis`.

A set of primes with positive density is infinite, so the density computation gives a quantitative
form of Chebotarev's theorem for the trivial conjugacy class.  Comparing two Galois number fields
of different degrees yields the statement that motivates all of this: infinitely many rational
primes split completely in the smaller field and fail to split completely in the larger one.

## Main results

* `InverseGalois.NumberTheory.HasDirichletDensity` — the property of a set of natural numbers of
  having a prescribed Dirichlet density.
* `InverseGalois.NumberTheory.infinite_of_hasDirichletDensity_pos` — a set with positive
  Dirichlet density is infinite.
* `InverseGalois.NumberTheory.density_le_of_subset_union` — if `S` is contained in the union of a
  finite set and a set `T`, then the density of `S` is at most the density of `T`.
* `InverseGalois.NumberTheory.finite_ramifiedSet` — only finitely many rational primes ramify in
  a number field.
* `InverseGalois.NumberTheory.hasDirichletDensity_splitSet` — the primes that split completely in
  a Galois number field of degree `n` have Dirichlet density `1/n`.
* `InverseGalois.NumberTheory.infinite_setOf_splitsCompletely_not_splitsCompletely` — for Galois
  number fields `A` and `B` with `[A : ℚ] < [B : ℚ]`, infinitely many rational primes split
  completely in `A` but not in `B`.

The Euler product itself is proved in `InverseGalois.NumberTheory.IdealEulerProduct`.  The
statements above are established first from it as an explicit hypothesis, `EulerProductHypothesis`,
and then discharged.
-/

open NumberField Ideal Filter Topology IsDedekindDomain RingOfIntegers UniqueFactorizationMonoid
open Polynomial
open scoped IntermediateField

namespace InverseGalois.NumberTheory

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-! ### Dirichlet density -/

/-- The Dirichlet series `∑_{p ∈ S} p^{-s}` attached to a set `S` of natural numbers. -/
noncomputable def primeSum (S : Set ℕ) (s : ℝ) : ℝ := ∑' p : S, (p : ℝ) ^ (-s)

/-- A set `S` of natural numbers has **Dirichlet density** `d` when the ratio of the Dirichlet
series `∑_{p ∈ S} p^{-s}` to `log (1/(s-1))` tends to `d` as `s` decreases to `1`. -/
def HasDirichletDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun s : ℝ => primeSum S s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 d)

/-- Each term of a Dirichlet series with positive exponent is at most one. -/
theorem rpow_neg_le_one {p : ℕ} {s : ℝ} (hs : 0 < s) : (p : ℝ) ^ (-s) ≤ 1 := by
  rcases Nat.eq_zero_or_pos p with h | h
  · rw [h]
    simp [Real.zero_rpow (by linarith : -s ≠ 0)]
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h) (by linarith)

/-- A Dirichlet series with non-negative terms is non-negative. -/
theorem primeSum_nonneg (S : Set ℕ) {s : ℝ} : 0 ≤ primeSum S s :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The Dirichlet series of any set of natural numbers converges for `s > 1`. -/
theorem summable_rpow_subtype {s : ℝ} (hs : 1 < s) (S : Set ℕ) :
    Summable (fun p : S => ((p : ℕ) : ℝ) ^ (-s)) :=
  (Real.summable_nat_rpow.mpr (by linarith)).subtype S

/-- The Dirichlet series of a finite set is bounded by its cardinality. -/
theorem primeSum_le_card {S : Set ℕ} (hS : S.Finite) {s : ℝ} (hs : 0 < s) :
    primeSum S s ≤ (Nat.card S : ℝ) := by
  haveI := hS.to_subtype
  calc primeSum S s ≤ ∑' _ : S, (1 : ℝ) :=
        Summable.tsum_le_tsum (fun _ => rpow_neg_le_one hs) Summable.of_finite Summable.of_finite
    _ = (Nat.card S : ℝ) := by rw [tsum_const, nsmul_eq_mul, mul_one]

/-- The normalising weight `log (1/(s-1))` tends to infinity as `s` decreases to one. -/
theorem tendsto_logWeight : Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using sub_pos.mpr (Set.mem_Ioi.mp hs)
  have h2 : Tendsto (fun s : ℝ => 1 / (s - 1)) (𝓝[>] 1) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero.comp h1
  exact Real.tendsto_log_atTop.comp h2

/-- Near `s = 1` from the right the normalising weight is positive. -/
theorem eventually_logWeight_pos : ∀ᶠ s : ℝ in 𝓝[>] 1, 0 < Real.log (1 / (s - 1)) :=
  tendsto_logWeight.eventually (eventually_gt_atTop (0 : ℝ))

/-- **A set of primes of positive Dirichlet density is infinite.**  A finite set has a bounded
Dirichlet series, whose ratio to the unbounded weight `log (1/(s-1))` tends to zero. -/
theorem infinite_of_hasDirichletDensity_pos {S : Set ℕ} {d : ℝ} (hd : 0 < d)
    (h : HasDirichletDensity S d) : S.Infinite := by
  intro hfin
  have hb : Tendsto (fun s : ℝ => (Nat.card S : ℝ) / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_logWeight
  have h0 : Tendsto (fun s : ℝ => primeSum S s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL, abs_of_nonneg (primeSum_nonneg S)]
    gcongr
    exact primeSum_le_card hfin (by simpa using lt_trans zero_lt_one (Set.mem_Ioi.mp hs))
  exact hd.ne' (tendsto_nhds_unique h h0)

/-- The Dirichlet series of a set, written as a sum over all natural numbers of an indicator. -/
theorem tsum_indicator_rpow (S : Set ℕ) (s : ℝ) :
    ∑' m : ℕ, S.indicator (fun m : ℕ => (m : ℝ) ^ (-s)) m = primeSum S s :=
  (tsum_subtype S _).symm

/-- The indicator form of a Dirichlet series is summable for `s > 1`. -/
theorem summable_indicator_rpow (S : Set ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (S.indicator (fun m : ℕ => (m : ℝ) ^ (-s))) :=
  (hasSum_subtype_iff_indicator.mp (summable_rpow_subtype hs S).hasSum).summable

/-- The terms of a Dirichlet series in indicator form are non-negative. -/
theorem indicator_rpow_nonneg (S : Set ℕ) (s : ℝ) (m : ℕ) :
    (0 : ℝ) ≤ S.indicator (fun m : ℕ => (m : ℝ) ^ (-s)) m :=
  Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) m

/-- Dirichlet series are subadditive along a covering of one set by two others. -/
theorem primeSum_le_of_subset_union {S T F : Set ℕ} (hsub : S ⊆ F ∪ T) {s : ℝ} (hs : 1 < s) :
    primeSum S s ≤ primeSum F s + primeSum T s := by
  rw [← tsum_indicator_rpow S s, ← tsum_indicator_rpow F s, ← tsum_indicator_rpow T s,
    ← (summable_indicator_rpow F hs).tsum_add (summable_indicator_rpow T hs)]
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_indicator_rpow S hs)
    ((summable_indicator_rpow F hs).add (summable_indicator_rpow T hs))
  by_cases hm : m ∈ S
  · rw [Set.indicator_of_mem hm]
    rcases hsub hm with h | h
    · rw [Set.indicator_of_mem h]
      have := indicator_rpow_nonneg T s m
      linarith
    · rw [Set.indicator_of_mem h]
      have := indicator_rpow_nonneg F s m
      linarith
  · rw [Set.indicator_of_notMem hm]
    exact add_nonneg (indicator_rpow_nonneg F s m) (indicator_rpow_nonneg T s m)

/-- A finite set of natural numbers has Dirichlet density zero. -/
theorem hasDirichletDensity_of_finite {F : Set ℕ} (hF : F.Finite) : HasDirichletDensity F 0 := by
  have hb : Tendsto (fun s : ℝ => (Nat.card F : ℝ) / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_logWeight
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hL, abs_of_nonneg (primeSum_nonneg F)]
  gcongr
  exact primeSum_le_card hF (by simpa using lt_trans zero_lt_one (Set.mem_Ioi.mp hs))

/-- **Densities are monotone up to finite sets.**  If `S` is covered by a finite set together
with `T`, then the density of `S` does not exceed the density of `T`. -/
theorem density_le_of_subset_union {S T F : Set ℕ} (hF : F.Finite) (hsub : S ⊆ F ∪ T)
    {a b : ℝ} (hS : HasDirichletDensity S a) (hT : HasDirichletDensity T b) : a ≤ b := by
  have hsum := (hasDirichletDensity_of_finite hF).add hT
  rw [zero_add] at hsum
  refine le_of_tendsto_of_tendsto hS hsum ?_
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  rw [← add_div]
  gcongr
  exact primeSum_le_of_subset_union hsub (Set.mem_Ioi.mp hs)

/-! ### The primes of a number field, grouped by residue characteristic -/

section NumberFieldSection

variable {K : Type*} [Field K] [NumberField K]

/-- The ideal generated by a rational prime in `ℤ` is non-zero. -/
theorem span_intCast_ne_bot {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  simp [Ideal.span_singleton_eq_bot, hp.ne_zero]

/-- A prime of the ring of integers has absolute norm at least two. -/
theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ absNorm v.asIdeal := by
  have h0 : absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (absNorm_eq_zero_iff.mp h)
  have h1 : absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (absNorm_eq_one_iff.mp h)
  omega

/-- Every prime of the ring of integers lies over a rational prime. -/
theorem exists_prime_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  classical
  have hq : (Ideal.under ℤ v.asIdeal).IsPrime := inferInstance
  have hmem : ((absNorm v.asIdeal : ℕ) : ℤ) ∈ Ideal.under ℤ v.asIdeal := by
    simpa [Ideal.under_def, Ideal.mem_comap, algebraMap_int_eq] using Ideal.absNorm_mem v.asIdeal
  have hne : Ideal.under ℤ v.asIdeal ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    have h2 := two_le_absNorm v
    have : (absNorm v.asIdeal : ℤ) ≠ 0 := by exact_mod_cast (by omega : absNorm v.asIdeal ≠ 0)
    exact this hmem
  set g := Submodule.IsPrincipal.generator (Ideal.under ℤ v.asIdeal) with hgdef
  have hspan : Ideal.span {g} = Ideal.under ℤ v.asIdeal :=
    Submodule.IsPrincipal.span_singleton_generator _
  have hg0 : g ≠ 0 := by
    intro h
    apply hne
    rw [← hspan, h, Ideal.span_singleton_eq_bot]
  have hgp : Prime g := by
    rw [← Ideal.span_singleton_prime hg0, hspan]
    exact hq
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ⟨?_⟩⟩
  rw [← hspan]
  exact Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs g).symm

/-- The absolute norm of a prime lying over `p` is a power of `p`, so `p` is its least prime
factor. -/
theorem minFac_absNorm_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] : (absNorm v.asIdeal).minFac = p := by
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (p := p) v.asIdeal hp
  have h2 := two_le_absNorm v
  set f := (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal with hf
  have hne1 : p ^ f ≠ 1 := by
    intro hc
    rw [h] at h2
    omega
  have hmp : (p ^ f).minFac.Prime := Nat.minFac_prime hne1
  rw [h]
  exact (Nat.prime_dvd_prime_iff_eq hmp hp).mp (hmp.dvd_of_dvd_pow (Nat.minFac_dvd _))

/-- The residue characteristic of a prime of the ring of integers: the rational prime it lies
over, read off as the least prime factor of its absolute norm. -/
noncomputable def resChar (v : HeightOneSpectrum (𝓞 K)) : ℕ := (absNorm v.asIdeal).minFac

/-- The residue characteristic is a rational prime, and the given prime lies over it. -/
theorem resChar_spec (v : HeightOneSpectrum (𝓞 K)) :
    (resChar v).Prime ∧ v.asIdeal.LiesOver (Ideal.span {((resChar v : ℕ) : ℤ)}) := by
  obtain ⟨p, hp, hlo⟩ := exists_prime_liesOver v
  have hh : resChar v = p := minFac_absNorm_eq hp v
  rw [hh]
  exact ⟨hp, hlo⟩

/-- The residue characteristic is prime. -/
theorem resChar_prime (v : HeightOneSpectrum (𝓞 K)) : (resChar v).Prime := (resChar_spec v).1

/-- A prime lies over its residue characteristic. -/
theorem liesOver_resChar (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.LiesOver (Ideal.span {((resChar v : ℕ) : ℤ)}) := (resChar_spec v).2

/-- A prime with residue characteristic `p` lies over `p`. -/
theorem liesOver_of_resChar {p : ℕ} (v : HeightOneSpectrum (𝓞 K)) (h : resChar v = p) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := h ▸ liesOver_resChar v

/-- A prime lying over `p` has residue characteristic `p`. -/
theorem resChar_eq_of_liesOver {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] : resChar v = p := minFac_absNorm_eq hp v

/-- The residue characteristic of a prime is at most its absolute norm. -/
theorem resChar_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : resChar v ≤ absNorm v.asIdeal :=
  Nat.minFac_le (by have := two_le_absNorm v; omega)

/-- The primes with residue characteristic `p` are exactly the primes over `p`. -/
noncomputable def fiberEquiv {p : ℕ} (hp : p.Prime) :
    ↥(resChar ⁻¹' {p} : Set (HeightOneSpectrum (𝓞 K))) ≃
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) where
  toFun v := ⟨v.1.asIdeal, v.1.isPrime, liesOver_of_resChar v.1 v.2⟩
  invFun P :=
    ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver (span_intCast_ne_bot hp) P.2⟩, by
      haveI : P.1.IsPrime := P.2.1
      haveI : P.1.LiesOver (Ideal.span {(p : ℤ)}) := P.2.2
      exact resChar_eq_of_liesOver hp ⟨P.1, P.2.1, _⟩⟩
  left_inv v := by ext; rfl
  right_inv P := by ext; rfl

/-- Only finitely many primes of the ring of integers have a given residue characteristic. -/
instance finite_fiber (p : ℕ) :
    Finite ↥(resChar ⁻¹' {p} : Set (HeightOneSpectrum (𝓞 K))) := by
  by_cases hp : p.Prime
  · haveI := Fact.mk hp
    haveI : Finite ↥((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :=
      (primesOver_finite _ (𝓞 K)).to_subtype
    exact Finite.of_equiv _ (fiberEquiv (K := K) hp).symm
  · have he : (resChar ⁻¹' {p} : Set (HeightOneSpectrum (𝓞 K))) = ∅ := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hp (h ▸ resChar_prime v)
    rw [he]
    infer_instance

/-- There are at most `[K : ℚ]` primes with a given residue characteristic. -/
theorem card_fiber_le (p : ℕ) :
    Nat.card ↥(resChar ⁻¹' {p} : Set (HeightOneSpectrum (𝓞 K))) ≤ Module.finrank ℚ K := by
  by_cases hp : p.Prime
  · haveI := Fact.mk hp
    rw [Nat.card_congr (fiberEquiv (K := K) hp), Nat.card_coe_set_eq,
      ← coe_primesOverFinset (span_intCast_ne_bot hp) (𝓞 K), Set.ncard_coe_finset]
    exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K (span_intCast_ne_bot hp)
  · have he : (resChar ⁻¹' {p} : Set (HeightOneSpectrum (𝓞 K))) = ∅ := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hp (h ▸ resChar_prime v)
    simp [he]

/-- A completely split rational prime has exactly `[K : ℚ]` primes above it. -/
theorem card_fiber_eq_of_splitsCompletely {p : ℕ} (hp : p.Prime) (hs : SplitsCompletely K p) :
    Nat.card ↥(resChar ⁻¹' {p} : Set (HeightOneSpectrum (𝓞 K))) = Module.finrank ℚ K := by
  haveI := Fact.mk hp
  have hb := span_intCast_ne_bot (p := p) hp
  rw [Nat.card_congr (fiberEquiv (K := K) hp), Nat.card_coe_set_eq,
    ← coe_primesOverFinset hb (𝓞 K), Set.ncard_coe_finset]
  rw [← Ideal.sum_ramification_inertia (𝓞 K) ℚ K hb, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨h1, h2⟩ := hs P ((mem_primesOverFinset_iff hb (𝓞 K)).mp hP)
  rw [h1, h2]

/-- Above a completely split rational prime every prime has absolute norm `p`. -/
theorem absNorm_eq_of_splitsCompletely {p : ℕ} (hp : p.Prime) (hs : SplitsCompletely K p)
    (v : HeightOneSpectrum (𝓞 K)) (hv : resChar v = p) : absNorm v.asIdeal = p := by
  haveI := liesOver_of_resChar v hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg' (p := p) v.asIdeal hp
  have h2 := (hs v.asIdeal ⟨v.isPrime, inferInstance⟩).2
  rw [h, h2, pow_one]

/-- **Above an unramified rational prime that does not split completely every prime has absolute
norm at least `p²`.**  In a Galois extension all the primes above `p` have the same residue
degree; if that degree were one the fundamental identity would force `p` to split completely. -/
theorem sq_le_absNorm_of_not_splitsCompletely [IsGalois ℚ K] {p : ℕ} (hp : p.Prime)
    (hunr : ∀ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P = 1)
    (hns : ¬ SplitsCompletely K p)
    (v : HeightOneSpectrum (𝓞 K)) (hv : resChar v = p) : p ^ 2 ≤ absNorm v.asIdeal := by
  haveI := Fact.mk hp
  haveI := liesOver_of_resChar v hv
  rw [SplitsCompletely] at hns
  push_neg at hns
  obtain ⟨P, hP, hPne⟩ := hns
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (span_intCast_ne_bot hp) hP
  set w : HeightOneSpectrum (𝓞 K) := ⟨P, hP.1, hPbot⟩ with hw
  have hfne : (Ideal.span {(p : ℤ)}).inertiaDeg P ≠ 0 := by
    intro h0
    have h2 := two_le_absNorm w
    have hnn : absNorm w.asIdeal = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg P) :=
      Ideal.absNorm_eq_pow_inertiaDeg' (p := p) P hp
    rw [hnn, h0, pow_zero] at h2
    omega
  have hf2 : 2 ≤ (Ideal.span {(p : ℤ)}).inertiaDeg P := by
    rcases Nat.lt_or_ge ((Ideal.span {(p : ℤ)}).inertiaDeg P) 2 with h | h
    · exact absurd (hunr P hP) (fun hr => hPne hr (by omega))
    · exact h
  have heq : (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal = (Ideal.span {(p : ℤ)}).inertiaDeg P :=
    Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v.asIdeal P (K ≃ₐ[ℚ] K)
  have hnv : absNorm v.asIdeal = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg' (p := p) v.asIdeal hp
  rw [hnv, heq]
  exact Nat.pow_le_pow_right hp.one_lt.le hf2

/-! ### Ramified primes -/

variable (K) in
/-- The set of rational primes that ramify in `K`. -/
def ramifiedSet : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
    Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P ≠ 1}

/-- **Only finitely many rational primes ramify in a number field.**  For a prime `p` that neither
divides the Kummer–Dedekind exponent of a chosen integral generator nor makes the reduction of its
minimal polynomial inseparable, the ramification indices above `p` are the multiplicities of the
irreducible factors of a squarefree polynomial, hence all equal to one. -/
theorem finite_ramifiedSet (K : Type*) [Field K] [NumberField K] : (ramifiedSet K).Finite := by
  classical
  obtain ⟨θ, hθ⟩ := exists_integral_primitive_element K
  have hbad1 : {p : ℕ | p ∣ RingOfIntegers.exponent θ}.Finite := by
    refine Set.Finite.subset ((RingOfIntegers.exponent θ).divisors : Finset ℕ).finite_toSet ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simpa [Nat.mem_divisors] using ⟨hp, exponent_ne_zero θ hθ⟩
  have hbad2 : {p : ℕ | p.Prime ∧
      ¬ Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))}.Finite :=
    finite_setOf_prime_not_squarefree_map (separable_map_minpoly θ)
  refine (hbad1.union hbad2).subset ?_
  rintro p ⟨hp, P, hP, hram⟩
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and] at hc
  obtain ⟨hexp, hsq'⟩ := hc
  have hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
    by_contra h
    exact hsq' hp h
  haveI := Fact.mk hp
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hg0 : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have h₂ := (primesOverSpanEquivMonicFactorsMod hexp ⟨P, ⟨hP.1, hP.2⟩⟩).2
  have hramx := ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at hramx
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg0] at h₂
  exact hram (hramx.trans (multiplicity_eq_one_of_squarefree hsq h₂.1 h₂.2.2))

/-! ### Local factors and their logarithms -/

/-- The local factor `N𝔭^{-s}` of a prime of the ring of integers. -/
noncomputable def normPow (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (absNorm v.asIdeal : ℝ) ^ (-s)

/-- The absolute norm of a prime, as a real number, is at least two. -/
theorem two_le_absNorm_real (v : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ (absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v

/-- Local factors are positive. -/
theorem normPow_pos {s : ℝ} (v : HeightOneSpectrum (𝓞 K)) : 0 < normPow s v :=
  Real.rpow_pos_of_pos (by have := two_le_absNorm_real v; linarith) _

/-- For `s ≥ 1` the local factors are at most `1/2`. -/
theorem normPow_le_half {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    normPow s v ≤ 1 / 2 := by
  have h2 := two_le_absNorm_real v
  have h1 : (2 : ℝ) ≤ (absNorm v.asIdeal : ℝ) ^ s :=
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (2 : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le one_le_two hs
      _ ≤ (absNorm v.asIdeal : ℝ) ^ s := Real.rpow_le_rpow (by norm_num) h2 (by linarith)
  rw [normPow, Real.rpow_neg (by linarith), ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h1

/-- The local factor at `v` is at most the local factor of its residue characteristic. -/
theorem normPow_le_resChar {s : ℝ} (hs : 0 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    normPow s v ≤ ((resChar v : ℝ)) ^ (-s) := by
  have hpos : (0 : ℝ) < (resChar v : ℝ) := by exact_mod_cast (resChar_prime v).pos
  have hle : ((resChar v : ℕ) : ℝ) ≤ (absNorm v.asIdeal : ℝ) := by
    exact_mod_cast resChar_le_absNorm v
  rw [normPow, Real.rpow_neg (by linarith), Real.rpow_neg hpos.le, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos _)
    (Real.rpow_le_rpow hpos.le hle hs)

/-- The real power `m^{-2}` is the inverse of the square. -/
theorem rpow_neg_two (m : ℕ) : (m : ℝ) ^ (-2 : ℝ) = ((m : ℝ) ^ 2)⁻¹ := by
  rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- For `s ≥ 1` the square of a local factor is at most `N𝔭^{-2}`. -/
theorem sq_normPow_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    (normPow s v) ^ 2 ≤ (absNorm v.asIdeal : ℝ) ^ (-2 : ℝ) := by
  have h2 : (2 : ℝ) ≤ (absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v
  rw [normPow, ← Real.rpow_natCast ((absNorm v.asIdeal : ℝ) ^ (-s)) 2,
    ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
  push_cast
  nlinarith

/-- A prime whose absolute norm is at least `p²` has local factor at most `p^{-2}`. -/
theorem normPow_le_rpow_neg_two_of_sq_le {s : ℝ} (hs : 1 ≤ s) {p : ℕ} (hp : 2 ≤ p)
    (v : HeightOneSpectrum (𝓞 K)) (h : p ^ 2 ≤ absNorm v.asIdeal) :
    normPow s v ≤ (p : ℝ) ^ (-2 : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h2 : (2 : ℝ) ≤ (absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v
  have hsq : ((p : ℝ)) ^ 2 ≤ (absNorm v.asIdeal : ℝ) := by exact_mod_cast h
  calc normPow s v = (absNorm v.asIdeal : ℝ) ^ (-s) := rfl
    _ ≤ (absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = ((absNorm v.asIdeal : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ ((p : ℝ) ^ 2)⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le (by positivity) hsq
    _ = (p : ℝ) ^ (-2 : ℝ) := (rpow_neg_two p).symm

/-- The logarithm of the local Euler factor, `-log (1 - N𝔭^{-s})`. -/
noncomputable def localLog (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -Real.log (1 - normPow s v)

/-- The argument of the local logarithm is positive. -/
theorem one_sub_normPow_pos {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    0 < 1 - normPow s v := by
  have := normPow_le_half hs v
  linarith

/-- Local logarithms are non-negative. -/
theorem localLog_nonneg {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ localLog s v := by
  have h1 := normPow_pos (s := s) v
  have h2 := one_sub_normPow_pos hs v
  simp only [localLog, neg_nonneg]
  exact Real.log_nonpos (by linarith) (by linarith)

/-- **The local logarithm differs from the local factor by at most twice its square.** -/
theorem abs_localLog_sub {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    |localLog s v - normPow s v| ≤ 2 * (normPow s v) ^ 2 := by
  set x := normPow (K := K) s v with hx
  have h1 : 0 < x := normPow_pos v
  have h2 : x ≤ 1 / 2 := normPow_le_half hs v
  have habs : |x| = x := abs_of_pos h1
  have hlt : |x| < 1 := by rw [habs]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, habs] at h
  norm_num at h
  have hd : localLog s v - x = -(x + Real.log (1 - x)) := by
    simp [localLog, ← hx]
    ring
  rw [hd, abs_neg]
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg x]

/-- A local logarithm is at most twice the corresponding local factor. -/
theorem localLog_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    localLog s v ≤ 2 * normPow s v := by
  have h := abs_localLog_sub hs v
  have h1 : 0 < normPow (K := K) s v := normPow_pos v
  have h2 : normPow (K := K) s v ≤ 1 / 2 := normPow_le_half hs v
  have h3 := abs_le.mp h
  nlinarith [h3.2]

/-- A local logarithm is at most one. -/
theorem localLog_le_one {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    localLog s v ≤ 1 := by
  have h1 := localLog_le hs v
  have h2 := normPow_le_half hs v
  linarith

/-- Exponentiating a local logarithm returns the local Euler factor. -/
theorem exp_localLog {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    Real.exp (localLog s v) = (1 - normPow s v)⁻¹ := by
  rw [localLog, Real.exp_neg, Real.exp_log (one_sub_normPow_pos hs v)]

/-! ### Summing over the primes of `K` -/

/-- **A function on the primes of `K` is summable as soon as its sums over the fibres of the
residue characteristic are dominated by a summable function of the rational primes.** -/
theorem summable_of_fiber_bound {F : HeightOneSpectrum (𝓞 K) → ℝ} (hF : ∀ v, 0 ≤ F v)
    (G : ℕ → ℝ) (hG : Summable G)
    (hb : ∀ m : ℕ, ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), F v.1 ≤ G m) :
    Summable F := by
  have he := (Equiv.sigmaPreimageEquiv (resChar (K := K))).summable_iff (f := F)
  rw [← he]
  have hnn : ∀ x : (m : ℕ) × ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))),
      0 ≤ (F ∘ (Equiv.sigmaPreimageEquiv (resChar (K := K)))) x := fun x => hF _
  rw [summable_sigma_of_nonneg hnn]
  exact ⟨fun m => Summable.of_finite, hG.of_nonneg_of_le (fun m => tsum_nonneg fun v => hF _) hb⟩

/-- A fibre sum is at most `[K : ℚ]` times a uniform bound on the summand. -/
theorem tsum_fiber_le (F : HeightOneSpectrum (𝓞 K) → ℝ) (m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), resChar v = m → F v ≤ c) :
    ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), F v.1 ≤
      (Module.finrank ℚ K : ℝ) * c := by
  calc ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), F v.1
      ≤ ∑' _ : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), c :=
        Summable.tsum_le_tsum (fun v => h v.1 v.2) Summable.of_finite Summable.of_finite
    _ = (Nat.card ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))) : ℝ) * c := by
        rw [tsum_const, nsmul_eq_mul]
    _ ≤ (Module.finrank ℚ K : ℝ) * c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_fiber_le m) hc

/-- A fibre sum of a function that is constant along the fibre. -/
theorem tsum_fiber_eq (F : HeightOneSpectrum (𝓞 K) → ℝ) (m : ℕ) (c : ℝ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), resChar v = m → F v = c) :
    ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), F v.1 =
      (Nat.card ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))) : ℝ) * c := by
  calc ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), F v.1
      = ∑' _ : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), c :=
        tsum_congr (fun v => h v.1 v.2)
    _ = (Nat.card ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))) : ℝ) * c := by
        rw [tsum_const, nsmul_eq_mul]

/-- The local factors are summable for `s > 1`. -/
theorem summable_normPow {s : ℝ} (hs : 1 < s) : Summable (normPow (K := K) s) := by
  refine summable_of_fiber_bound (fun v => (normPow_pos v).le)
    (fun m => (Module.finrank ℚ K : ℝ) * ((m : ℝ) ^ (-s)))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _) (fun m => ?_)
  refine tsum_fiber_le _ m _ (Real.rpow_nonneg (by positivity) _) (fun v hv => ?_)
  rw [← hv]
  exact normPow_le_resChar (by linarith) v

/-- The local logarithms are summable for `s > 1`. -/
theorem summable_localLog {s : ℝ} (hs : 1 < s) : Summable (localLog (K := K) s) :=
  Summable.of_nonneg_of_le (fun v => localLog_nonneg hs.le v) (fun v => localLog_le hs.le v)
    ((summable_normPow hs).mul_left 2)

/-! ### The Euler product and the logarithm of the zeta function -/

/-- The **Euler product** for the Dedekind zeta function of a number field, taken over the primes
of its ring of integers. -/
def EulerProductHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ {s : ℂ}, 1 < s.re →
    ∏' 𝔭 : HeightOneSpectrum (𝓞 K), (1 - (absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ = dedekindZeta K s

variable (K) in
/-- The logarithm of the Dedekind zeta function, defined directly as the sum of the local
logarithms. -/
noncomputable def logZeta (s : ℝ) : ℝ := ∑' v : HeightOneSpectrum (𝓞 K), localLog s v

/-- **The Dedekind zeta function is the exponential of the sum of the local logarithms.** -/
theorem dedekindZeta_eq_exp (h : EulerProductHypothesis K) {s : ℝ} (hs : 1 < s) :
    dedekindZeta K (s : ℂ) = ((Real.exp (logZeta K s) : ℝ) : ℂ) := by
  have hA : HasSum (localLog (K := K) s) (logZeta K s) := (summable_localLog hs).hasSum
  have hC : HasSum (fun v => ((localLog (K := K) s v : ℝ) : ℂ)) ((logZeta K s : ℝ) : ℂ) :=
    hA.map Complex.ofRealHom Complex.continuous_ofReal
  have hP := hC.cexp
  have hfun : (Complex.exp ∘ fun v => ((localLog (K := K) s v : ℝ) : ℂ)) =
      fun v : HeightOneSpectrum (𝓞 K) => (1 - (absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    funext v
    have h1 : Complex.exp ((localLog (K := K) s v : ℝ) : ℂ)
        = ((Real.exp (localLog (K := K) s v) : ℝ) : ℂ) := (Complex.ofReal_exp _).symm
    have h2 : ((normPow (K := K) s v : ℝ) : ℂ) = (absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) := by
      rw [normPow, Complex.ofReal_cpow (by positivity)]
      push_cast
      rfl
    rw [Function.comp_apply, h1, exp_localLog hs.le v, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, h2]
  rw [hfun] at hP
  have hz := h (s := (s : ℂ)) (by simpa using hs)
  rw [← hz, hP.tprod_eq, ← Complex.ofReal_exp]

/-- The logarithm of the zeta function, plus `log (s - 1)`, converges as `s` decreases to one:
this is the statement that `ζ_K` has a simple pole at `s = 1`. -/
theorem tendsto_logZeta_add (h : EulerProductHypothesis K) :
    Tendsto (fun s : ℝ => Real.log (s - 1) + logZeta K s) (𝓝[>] 1)
      (𝓝 (Real.log (dedekindZeta_residue K))) := by
  have hz := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hre : Tendsto (fun s : ℝ => (((s : ℂ) - 1) * dedekindZeta K (s : ℂ)).re) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
    have h0 := (Complex.continuous_re.tendsto ((dedekindZeta_residue K : ℝ) : ℂ)).comp hz
    rwa [Complex.ofReal_re] at h0
  have heq : (fun s : ℝ => (((s : ℂ) - 1) * dedekindZeta K (s : ℂ)).re) =ᶠ[𝓝[>] 1]
      fun s : ℝ => (s - 1) * Real.exp (logZeta K s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [dedekindZeta_eq_exp h (Set.mem_Ioi.mp hs),
      show ((s : ℂ) - 1) * ((Real.exp (logZeta K s) : ℝ) : ℂ)
        = (((s - 1) * Real.exp (logZeta K s) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have h2 := hre.congr' heq
  have h3 := ((Real.continuousAt_log (dedekindZeta_residue_ne_zero K)).tendsto).comp h2
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (0 : ℝ) < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
  simp only [Function.comp_apply]
  rw [Real.log_mul (ne_of_gt hs1) (Real.exp_ne_zero _), Real.log_exp]

/-- **The logarithm of the zeta function is asymptotic to `log (1/(s-1))`.** -/
theorem tendsto_logZeta_div (h : EulerProductHypothesis K) :
    Tendsto (fun s : ℝ => logZeta K s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
  have hdiv := (tendsto_logZeta_add h).div_atTop tendsto_logWeight
  have h2 := hdiv.add (tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓝[>] (1 : ℝ)))
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_logWeight_pos] with s hL0
  have hlog : Real.log (1 / (s - 1)) = -Real.log (s - 1) := by rw [one_div, Real.log_inv]
  have ht : Real.log (s - 1) ≠ 0 := by
    intro h0
    rw [hlog, h0, neg_zero] at hL0
    exact lt_irrefl 0 hL0
  rw [hlog]
  field_simp
  ring

/-! ### Comparison with the sum over the completely split primes -/

variable (K) in
/-- The set of rational primes that split completely in `K`. -/
def splitSet : Set ℕ := {p : ℕ | p.Prime ∧ SplitsCompletely K p}

variable (K) in
/-- The sum of the local logarithms over the primes of residue characteristic `m`. -/
noncomputable def fiberSum (s : ℝ) (m : ℕ) : ℝ :=
  ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))), localLog s v.1

variable (K) in
/-- The main term attached to a rational prime: `[K : ℚ] · p^{-s}` when `p` splits completely,
and zero otherwise. -/
noncomputable def splitTerm (s : ℝ) (m : ℕ) : ℝ :=
  (splitSet K).indicator (fun m => (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-s)) m

variable (K) in
/-- The bound, independent of `s`, on the discrepancy between the fibre sums and the main terms. -/
noncomputable def errBound (m : ℕ) : ℝ :=
  2 * (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-2 : ℝ)
    + (ramifiedSet K).indicator (fun _ => 2 * (Module.finrank ℚ K : ℝ)) m

/-- The error bound is non-negative. -/
theorem errBound_nonneg (m : ℕ) : 0 ≤ errBound K m :=
  add_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) m)

/-- The error bound is summable. -/
theorem summable_errBound : Summable (errBound K) := by
  have h1 : Summable fun m : ℕ => 2 * (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-2 : ℝ) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  have h2 : Summable ((ramifiedSet K).indicator (fun _ => 2 * (Module.finrank ℚ K : ℝ))) :=
    (hasSum_subtype_iff_indicator.mp (((finite_ramifiedSet K).summable _).hasSum)).summable
  exact h1.add h2

/-- Fibre sums are non-negative. -/
theorem fiberSum_nonneg {s : ℝ} (hs : 1 ≤ s) (m : ℕ) : 0 ≤ fiberSum K s m :=
  tsum_nonneg fun _ => localLog_nonneg hs _

/-- A fibre sum is at most `[K : ℚ]`. -/
theorem fiberSum_le {s : ℝ} (hs : 1 ≤ s) (m : ℕ) :
    fiberSum K s m ≤ (Module.finrank ℚ K : ℝ) := by
  have h := tsum_fiber_le (localLog (K := K) s) m 1 zero_le_one
    (fun v _ => localLog_le_one hs v)
  simpa [fiberSum] using h

/-- The main terms are non-negative. -/
theorem splitTerm_nonneg {s : ℝ} (m : ℕ) : 0 ≤ splitTerm K s m :=
  Set.indicator_nonneg (fun _ _ => by positivity) m

/-- A main term is at most `[K : ℚ]`. -/
theorem splitTerm_le {s : ℝ} (hs : 1 ≤ s) (m : ℕ) :
    splitTerm K s m ≤ (Module.finrank ℚ K : ℝ) := by
  classical
  rw [splitTerm, Set.indicator_apply]
  split_ifs with hm
  · have hp : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1.two_le
    have h1 : (m : ℝ) ^ (-s) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℚ K)]
  · positivity

/-- No prime of the ring of integers has a composite residue characteristic. -/
theorem isEmpty_fiber_of_not_prime {m : ℕ} (hm : ¬ m.Prime) :
    IsEmpty ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))) := by
  constructor
  rintro ⟨v, hv⟩
  exact hm (hv ▸ resChar_prime v)

/-- **The fibre sum over a rational prime agrees with its main term up to the error bound.**
Above a completely split prime the local logarithms differ from the local factors by at most
twice their squares; above an unramified prime that does not split completely every local factor
is itself at most `p^{-2}`; and the finitely many ramified primes are absorbed wholesale. -/
theorem abs_fiberSum_sub [IsGalois ℚ K] {s : ℝ} (hs : 1 ≤ s) (m : ℕ) :
    |fiberSum K s m - splitTerm K s m| ≤ errBound K m := by
  by_cases hm : m.Prime
  · by_cases hram : m ∈ ramifiedSet K
    · have h1 : |fiberSum K s m - splitTerm K s m| ≤ 2 * (Module.finrank ℚ K : ℝ) := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have ha := fiberSum_nonneg (K := K) hs m
          have hb := splitTerm_le (K := K) hs m
          linarith
        · have ha := fiberSum_le (K := K) hs m
          have hb := splitTerm_nonneg (K := K) (s := s) m
          linarith
      refine h1.trans ?_
      rw [errBound, Set.indicator_of_mem hram]
      have : (0 : ℝ) ≤ 2 * (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-2 : ℝ) := by positivity
      linarith
    · have hunr : ∀ P ∈ (Ideal.span {(m : ℤ)}).primesOver (𝓞 K),
          Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(m : ℤ)}) P = 1 := by
        intro P hP
        by_contra hc
        exact hram ⟨hm, P, hP, hc⟩
      have hbase : |fiberSum K s m - splitTerm K s m| ≤
          2 * (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-2 : ℝ) := by
        by_cases hsp : SplitsCompletely K m
        · have hmem : m ∈ splitSet K := ⟨hm, hsp⟩
          have hnorm : ∀ v : HeightOneSpectrum (𝓞 K), resChar v = m →
              normPow s v = (m : ℝ) ^ (-s) := by
            intro v hv
            rw [normPow, absNorm_eq_of_splitsCompletely hm hsp v hv]
          have e2 : ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))),
              normPow s v.1 = (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-s) := by
            rw [tsum_fiber_eq _ m _ hnorm, card_fiber_eq_of_splitsCompletely hm hsp]
          have e1 : fiberSum K s m - splitTerm K s m =
              ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))),
                (localLog s v.1 - normPow s v.1) := by
            rw [Summable.tsum_sub Summable.of_finite Summable.of_finite, e2, splitTerm,
              Set.indicator_of_mem hmem, fiberSum]
          rw [e1]
          calc |∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))),
                  (localLog s v.1 - normPow s v.1)|
              ≤ ∑' v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))),
                  |localLog s v.1 - normPow s v.1| := by
                simpa using norm_tsum_le_tsum_norm
                  (f := fun v : ↥(resChar ⁻¹' {m} : Set (HeightOneSpectrum (𝓞 K))) =>
                    localLog s v.1 - normPow s v.1) Summable.of_finite
            _ ≤ (Module.finrank ℚ K : ℝ) * (2 * (m : ℝ) ^ (-2 : ℝ)) := by
                refine tsum_fiber_le
                  (fun v : HeightOneSpectrum (𝓞 K) => |localLog s v - normPow s v|) m
                  (2 * (m : ℝ) ^ (-2 : ℝ)) (by positivity) (fun v hv => ?_)
                refine (abs_localLog_sub hs v).trans ?_
                have hsq := sq_normPow_le hs v
                rw [absNorm_eq_of_splitsCompletely hm hsp v hv] at hsq
                linarith
            _ = 2 * (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-2 : ℝ) := by ring
        · have hnmem : m ∉ splitSet K := fun h => hsp h.2
          rw [splitTerm, Set.indicator_of_notMem hnmem, sub_zero,
            abs_of_nonneg (fiberSum_nonneg (K := K) hs m)]
          calc fiberSum K s m
              ≤ (Module.finrank ℚ K : ℝ) * (2 * (m : ℝ) ^ (-2 : ℝ)) := by
                refine tsum_fiber_le (localLog (K := K) s) m (2 * (m : ℝ) ^ (-2 : ℝ))
                  (by positivity) (fun v hv => ?_)
                refine (localLog_le hs v).trans ?_
                have hn := normPow_le_rpow_neg_two_of_sq_le hs hm.two_le v
                  (sq_le_absNorm_of_not_splitsCompletely hm hunr hsp v hv)
                linarith
            _ = 2 * (Module.finrank ℚ K : ℝ) * (m : ℝ) ^ (-2 : ℝ) := by ring
      refine hbase.trans ?_
      rw [errBound]
      have : (0 : ℝ) ≤ (ramifiedSet K).indicator (fun _ => 2 * (Module.finrank ℚ K : ℝ)) m :=
        Set.indicator_nonneg (fun _ _ => by positivity) m
      linarith
  · have he := isEmpty_fiber_of_not_prime (K := K) hm
    have h1 : fiberSum K s m = 0 := tsum_empty
    have h2 : splitTerm K s m = 0 := by
      rw [splitTerm, Set.indicator_of_notMem (fun h => hm h.1)]
    rw [h1, h2, sub_zero, abs_zero]
    exact errBound_nonneg m

/-- Grouping the primes of `K` by residue characteristic computes the logarithm of the zeta
function. -/
theorem hasSum_fiberSum {s : ℝ} (hs : 1 < s) : HasSum (fiberSum K s) (logZeta K s) :=
  ((summable_localLog hs).hasSum).tsum_fiberwise resChar

/-- The main terms sum to `[K : ℚ]` times the Dirichlet series of the completely split primes. -/
theorem hasSum_splitTerm {s : ℝ} (hs : 1 < s) :
    HasSum (splitTerm K s) ((Module.finrank ℚ K : ℝ) * primeSum (splitSet K) s) := by
  have h1 : HasSum ((fun m : ℕ => (m : ℝ) ^ (-s)) ∘ (Subtype.val : splitSet K → ℕ))
      (primeSum (splitSet K) s) := (summable_rpow_subtype hs (splitSet K)).hasSum
  have h2 : HasSum ((splitSet K).indicator (fun m : ℕ => (m : ℝ) ^ (-s)))
      (primeSum (splitSet K) s) := hasSum_subtype_iff_indicator.mp h1
  have h3 := h2.mul_left (Module.finrank ℚ K : ℝ)
  have e : splitTerm K s = fun m : ℕ => (Module.finrank ℚ K : ℝ) *
      (splitSet K).indicator (fun m : ℕ => (m : ℝ) ^ (-s)) m := by
    funext m
    rw [splitTerm, Set.indicator_const_mul]
  rw [e]
  exact h3

/-- **The logarithm of the zeta function differs from `[K : ℚ]` times the Dirichlet series of the
completely split primes by a bounded amount.** -/
theorem abs_logZeta_sub [IsGalois ℚ K] {s : ℝ} (hs : 1 < s) :
    |logZeta K s - (Module.finrank ℚ K : ℝ) * primeSum (splitSet K) s| ≤ ∑' m : ℕ, errBound K m := by
  have hsub := (hasSum_fiberSum (K := K) hs).sub (hasSum_splitTerm (K := K) hs)
  have habs : Summable fun m : ℕ => |fiberSum K s m - splitTerm K s m| :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => abs_fiberSum_sub hs.le m)
      summable_errBound
  have hnorm : Summable fun m : ℕ => ‖fiberSum K s m - splitTerm K s m‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have h1 := norm_tsum_le_tsum_norm hnorm
  simp only [Real.norm_eq_abs] at h1
  rw [← hsub.tsum_eq]
  exact h1.trans
    (Summable.tsum_le_tsum (fun m => abs_fiberSum_sub hs.le m) habs summable_errBound)

/-! ### The density theorem -/

/-- **The rational primes that split completely in a Galois number field `K` have Dirichlet
density `1/[K : ℚ]`.** -/
theorem hasDirichletDensity_splitSet_of_eulerProduct [IsGalois ℚ K] (h : EulerProductHypothesis K) :
    HasDirichletDensity (splitSet K) (1 / (Module.finrank ℚ K : ℝ)) := by
  have hn0 : ((Module.finrank ℚ K : ℕ) : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  have hE : Tendsto (fun s : ℝ =>
      (logZeta K s - (Module.finrank ℚ K : ℝ) * primeSum (splitSet K) s)
        / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    have hb : Tendsto (fun s : ℝ => (∑' m : ℕ, errBound K m) / Real.log (1 / (s - 1)))
        (𝓝[>] 1) (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_logWeight
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL0]
    gcongr
    exact abs_logZeta_sub (Set.mem_Ioi.mp hs)
  have hnT : Tendsto (fun s : ℝ =>
      (Module.finrank ℚ K : ℝ) * primeSum (splitSet K) s / Real.log (1 / (s - 1)))
        (𝓝[>] 1) (𝓝 1) := by
    have h4 := (tendsto_logZeta_div h).sub hE
    rw [sub_zero] at h4
    refine h4.congr fun s => ?_
    rw [← sub_div, sub_sub_cancel]
  refine (hnT.div_const ((Module.finrank ℚ K : ℕ) : ℝ)).congr fun s => ?_
  rw [mul_div_assoc, mul_div_cancel_left₀ _ hn0]

/-- **Infinitely many rational primes split completely in a Galois number field**, with the
density `1/[K : ℚ]`. -/
theorem infinite_splitSet_of_eulerProduct [IsGalois ℚ K] (h : EulerProductHypothesis K) :
    (splitSet K).Infinite := by
  refine infinite_of_hasDirichletDensity_pos ?_ (hasDirichletDensity_splitSet_of_eulerProduct h)
  have := Module.finrank_pos (R := ℚ) (M := K)
  positivity

end NumberFieldSection

/-- **The primes that split completely in a smaller Galois number field but not in a larger one
are infinite in number.**  Were they finite, the completely split primes of the smaller field
would be covered by a finite set together with the completely split primes of the larger one, and
comparing densities would give `1/[A : ℚ] ≤ 1/[B : ℚ]`. -/
theorem infinite_setOf_splitsCompletely_not_splitsCompletely_of_eulerProduct
    (A : Type*) [Field A] [NumberField A] [IsGalois ℚ A]
    (B : Type*) [Field B] [NumberField B] [IsGalois ℚ B]
    (hA : EulerProductHypothesis A) (hB : EulerProductHypothesis B)
    (hlt : Module.finrank ℚ A < Module.finrank ℚ B) :
    {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ¬ SplitsCompletely B p}.Infinite := by
  intro hfin
  have hsub : splitSet A ⊆
      {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ¬ SplitsCompletely B p} ∪ splitSet B := by
    rintro p ⟨hp, hsp⟩
    by_cases hB' : SplitsCompletely B p
    · exact Or.inr ⟨hp, hB'⟩
    · exact Or.inl ⟨hp, hsp, hB'⟩
  have hle := density_le_of_subset_union hfin hsub (hasDirichletDensity_splitSet_of_eulerProduct hA)
    (hasDirichletDensity_splitSet_of_eulerProduct hB)
  have hApos : (0 : ℝ) < (Module.finrank ℚ A : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := A)
    positivity
  have hBpos : (0 : ℝ) < (Module.finrank ℚ B : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := B)
    positivity
  have hltR : (Module.finrank ℚ A : ℝ) < (Module.finrank ℚ B : ℝ) := by exact_mod_cast hlt
  have hkey : (Module.finrank ℚ B : ℝ) ≤ (Module.finrank ℚ A : ℝ) := by
    by_contra hc
    push_neg at hc
    have hcontra : 1 / (Module.finrank ℚ B : ℝ) < 1 / (Module.finrank ℚ A : ℝ) :=
      one_div_lt_one_div_of_lt hApos hc
    linarith
  linarith

/-! ## The density theorems, unconditionally -/

/-- **The Dedekind zeta function of a number field is the Euler product over the primes of its
ring of integers.** -/
theorem eulerProductHypothesis (K : Type*) [Field K] [NumberField K] :
    EulerProductHypothesis K :=
  fun hs => dedekindZeta_eulerProduct_primeIdeal K hs

/-- **The primes that split completely in a Galois number field of degree `n` have Dirichlet
density `1/n`.**

Each such prime contributes exactly `n` primes of the ring of integers, all of residue degree one,
and these account for the whole of `log ζ_K(s)` up to a bounded error; the simple pole of `ζ_K` at
`s = 1` then pins the density. -/
theorem hasDirichletDensity_splitSet (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    HasDirichletDensity (splitSet K) (1 / (Module.finrank ℚ K : ℝ)) :=
  hasDirichletDensity_splitSet_of_eulerProduct (eulerProductHypothesis K)

/-- **Infinitely many rational primes split completely in a Galois number field.** -/
theorem infinite_splitSet (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    (splitSet K).Infinite :=
  infinite_splitSet_of_eulerProduct (eulerProductHypothesis K)

/-- **The primes that split completely in a smaller Galois number field but not in a larger one
are infinite in number.**

This is the only consequence of Chebotarev's theorem that the Scholz–Reichardt construction
requires. -/
theorem infinite_setOf_splitsCompletely_not_splitsCompletely
    (A : Type*) [Field A] [NumberField A] [IsGalois ℚ A]
    (B : Type*) [Field B] [NumberField B] [IsGalois ℚ B]
    (hlt : Module.finrank ℚ A < Module.finrank ℚ B) :
    {p : ℕ | p.Prime ∧ SplitsCompletely A p ∧ ¬ SplitsCompletely B p}.Infinite :=
  infinite_setOf_splitsCompletely_not_splitsCompletely_of_eulerProduct A B
    (eulerProductHypothesis A) (eulerProductHypothesis B) hlt

end InverseGalois.NumberTheory
