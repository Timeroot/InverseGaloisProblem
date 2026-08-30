/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.SplitDensity

/-!
# The density of the primes of a number field splitting completely in an extension

A set `S` of primes of a number field `k` is said to have Dirichlet density `d` when the ratio of
`∑_{𝔭 ∈ S} N𝔭^{-s}` to `log (1/(s-1))` tends to `d` as `s` decreases to `1` along the reals, the
norm being the absolute norm of the ideal.  The normalisation is again the right one: the sum over
*all* primes of `k` is itself asymptotic to `log (1/(s-1))`, because it differs from the logarithm
of the Dedekind zeta function of `k` by a bounded amount and that function has a simple pole.

For an extension `L` of `k` which is Galois of degree `n`, the primes of `k` that split completely
in `L` have density `1/n`.  The proof is the classical one, run over the base `k` instead of over
the rationals.  The logarithm of the Euler product for `ζ_L` is a sum of the quantities
`-log (N𝔓^{-s})` over the primes `𝔓` of the ring of integers of `L`; each differs from `N𝔓^{-s}`
by at most `2 N𝔓^{-2s}`, and grouping the primes `𝔓` according to the prime `𝔭` of `k` below them
shows that the total contribution of the terms `N𝔓^{-2s}` is bounded independently of `s`.  Above
an unramified `𝔭` all residue degrees agree, so either `𝔭` splits completely, and contributes
exactly `n` primes of norm `N𝔭`, or every prime above `𝔭` has norm at least `N𝔭²` and the whole
fibre is absorbed into the error.  Only finitely many primes of `k` ramify in `L`, since a prime
of `k` ramifying in `L` lies over a rational prime ramifying in `L`, and those are absorbed as
well.  What is left is `log ζ_L(s) = n · ∑_{𝔭 split} N𝔭^{-s} + O(1)`, and the simple pole of `ζ_L`
at `s = 1` turns the left-hand side into `log (1/(s-1)) + O(1)`.

## Main results

* `InverseGalois.NumberTheory.HasIdealDensity` — the property of a set of primes of a number field
  of having a prescribed Dirichlet density.
* `InverseGalois.NumberTheory.infinite_of_hasIdealDensity_pos` — a set of primes with positive
  density is infinite.
* `InverseGalois.NumberTheory.hasIdealDensity_univ` — the whole set of primes of a number field
  has density one.
* `InverseGalois.NumberTheory.SplitsCompletelyIn` — the property of a prime of the base of being
  unramified with trivial residue extension at every prime above it.
* `InverseGalois.NumberTheory.finite_relRamifiedSet` — only finitely many primes of the base
  ramify in a finite extension.
* `InverseGalois.NumberTheory.hasIdealDensity_relSplitSet` — the primes of `k` that split
  completely in a Galois extension of degree `n` have Dirichlet density `1/n`.
* `InverseGalois.NumberTheory.infinite_setOf_splitsCompletelyIn_not_splitsCompletelyIn` — for
  Galois extensions `A` and `B` of `k` with `[A : k] < [B : k]`, infinitely many primes of `k`
  split completely in `A` but not in `B`.

## Tags

Dirichlet density, Chebotarev, Dedekind zeta function, splitting of primes, number field
-/

open NumberField Ideal Filter Topology IsDedekindDomain

namespace InverseGalois.NumberTheory

/-! ### Dirichlet series over the primes of a number field -/

section Base

variable {k : Type*} [Field k] [NumberField k]

/-- The Dirichlet series `∑_{𝔭 ∈ S} N𝔭^{-s}` attached to a set `S` of primes of a number field. -/
noncomputable def idealSum (S : Set (HeightOneSpectrum (𝓞 k))) (s : ℝ) : ℝ :=
  ∑' v : S, normPow s v.1

/-- A set `S` of primes of a number field has **Dirichlet density** `d` when the ratio of the
Dirichlet series `∑_{𝔭 ∈ S} N𝔭^{-s}` to `log (1/(s-1))` tends to `d` as `s` decreases to `1`. -/
def HasIdealDensity (S : Set (HeightOneSpectrum (𝓞 k))) (d : ℝ) : Prop :=
  Tendsto (fun s : ℝ => idealSum S s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 d)

/-- A Dirichlet series with non-negative terms is non-negative. -/
theorem idealSum_nonneg (S : Set (HeightOneSpectrum (𝓞 k))) {s : ℝ} : 0 ≤ idealSum S s :=
  tsum_nonneg fun v => (normPow_pos v.1).le

/-- The Dirichlet series of any set of primes converges for `s > 1`. -/
theorem summable_normPow_subtype {s : ℝ} (hs : 1 < s) (S : Set (HeightOneSpectrum (𝓞 k))) :
    Summable fun v : S => normPow s v.1 :=
  (summable_normPow hs).subtype S

/-- The Dirichlet series of a finite set of primes is bounded by its cardinality. -/
theorem idealSum_le_card {S : Set (HeightOneSpectrum (𝓞 k))} (hS : S.Finite) {s : ℝ} (hs : 1 ≤ s) :
    idealSum S s ≤ (Nat.card S : ℝ) := by
  haveI := hS.to_subtype
  calc idealSum S s ≤ ∑' _ : S, (1 : ℝ) :=
        Summable.tsum_le_tsum (fun v => (normPow_le_half hs v.1).trans (by norm_num))
          Summable.of_finite Summable.of_finite
    _ = (Nat.card S : ℝ) := by rw [tsum_const, nsmul_eq_mul, mul_one]

/-- The Dirichlet series of a set of primes, written as a sum over all primes of an indicator. -/
theorem tsum_indicator_normPow (S : Set (HeightOneSpectrum (𝓞 k))) (s : ℝ) :
    ∑' v : HeightOneSpectrum (𝓞 k), S.indicator (normPow s) v = idealSum S s :=
  (tsum_subtype S _).symm

/-- The indicator form of a Dirichlet series over the primes is summable for `s > 1`. -/
theorem summable_indicator_normPow (S : Set (HeightOneSpectrum (𝓞 k))) {s : ℝ} (hs : 1 < s) :
    Summable (S.indicator (normPow (K := k) s)) :=
  (hasSum_subtype_iff_indicator.mp (summable_normPow_subtype hs S).hasSum).summable

/-- The terms of a Dirichlet series over the primes in indicator form are non-negative. -/
theorem indicator_normPow_nonneg (S : Set (HeightOneSpectrum (𝓞 k))) (s : ℝ)
    (v : HeightOneSpectrum (𝓞 k)) : (0 : ℝ) ≤ S.indicator (normPow s) v :=
  Set.indicator_nonneg (fun w _ => (normPow_pos w).le) v

/-- Dirichlet series over the primes are subadditive along a covering of one set by two others. -/
theorem idealSum_le_of_subset_union {S T F : Set (HeightOneSpectrum (𝓞 k))} (hsub : S ⊆ F ∪ T)
    {s : ℝ} (hs : 1 < s) : idealSum S s ≤ idealSum F s + idealSum T s := by
  rw [← tsum_indicator_normPow S s, ← tsum_indicator_normPow F s, ← tsum_indicator_normPow T s,
    ← (summable_indicator_normPow F hs).tsum_add (summable_indicator_normPow T hs)]
  refine Summable.tsum_le_tsum (fun v => ?_) (summable_indicator_normPow S hs)
    ((summable_indicator_normPow F hs).add (summable_indicator_normPow T hs))
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv]
    rcases hsub hv with h | h
    · rw [Set.indicator_of_mem h]
      have := indicator_normPow_nonneg T s v
      linarith
    · rw [Set.indicator_of_mem h]
      have := indicator_normPow_nonneg F s v
      linarith
  · rw [Set.indicator_of_notMem hv]
    exact add_nonneg (indicator_normPow_nonneg F s v) (indicator_normPow_nonneg T s v)

/-- **A set of primes of positive Dirichlet density is infinite.** -/
theorem infinite_of_hasIdealDensity_pos {S : Set (HeightOneSpectrum (𝓞 k))} {d : ℝ} (hd : 0 < d)
    (h : HasIdealDensity S d) : S.Infinite := by
  intro hfin
  have hb : Tendsto (fun s : ℝ => (Nat.card S : ℝ) / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_logWeight
  have h0 : Tendsto (fun s : ℝ => idealSum S s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL, abs_of_nonneg (idealSum_nonneg S)]
    gcongr
    exact idealSum_le_card hfin (le_of_lt (Set.mem_Ioi.mp hs))
  exact hd.ne' (tendsto_nhds_unique h h0)

/-- A finite set of primes has Dirichlet density zero. -/
theorem hasIdealDensity_of_finite {F : Set (HeightOneSpectrum (𝓞 k))} (hF : F.Finite) :
    HasIdealDensity F 0 := by
  have hb : Tendsto (fun s : ℝ => (Nat.card F : ℝ) / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_logWeight
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hL, abs_of_nonneg (idealSum_nonneg F)]
  gcongr
  exact idealSum_le_card hF (le_of_lt (Set.mem_Ioi.mp hs))

/-- **Densities are monotone up to finite sets.** -/
theorem idealDensity_le_of_subset_union {S T F : Set (HeightOneSpectrum (𝓞 k))} (hF : F.Finite)
    (hsub : S ⊆ F ∪ T) {a b : ℝ} (hS : HasIdealDensity S a) (hT : HasIdealDensity T b) : a ≤ b := by
  have hsum := (hasIdealDensity_of_finite hF).add hT
  rw [zero_add] at hsum
  refine le_of_tendsto_of_tendsto hS hsum ?_
  filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL
  rw [← add_div]
  gcongr
  exact idealSum_le_of_subset_union hsub (Set.mem_Ioi.mp hs)

/-! ### The sum over all the primes -/

variable (k) in
/-- The sum of the squares of the norms of the primes, an absolute constant of the field. -/
noncomputable def sqNormSum : ℝ := ∑' v : HeightOneSpectrum (𝓞 k), normPow (2 : ℝ) v

/-- The sum of the squares of the norms of the primes converges. -/
theorem summable_sqNormPow : Summable (normPow (K := k) (2 : ℝ)) :=
  summable_normPow (by norm_num)

/-- **The logarithm of the zeta function differs from the Dirichlet series of all the primes by a
bounded amount.**  Each local logarithm differs from the corresponding local factor by at most
twice its square, and the squares are summable uniformly in `s`. -/
theorem abs_logZeta_sub_idealSum_univ {s : ℝ} (hs : 1 < s) :
    |logZeta k s - idealSum (Set.univ : Set (HeightOneSpectrum (𝓞 k))) s| ≤ 2 * sqNormSum k := by
  have hbnd : ∀ v : HeightOneSpectrum (𝓞 k),
      |localLog s v - normPow s v| ≤ 2 * normPow (2 : ℝ) v := by
    intro v
    refine (abs_localLog_sub hs.le v).trans ?_
    have := sq_normPow_le hs.le v
    have h2 : normPow (2 : ℝ) v = (absNorm v.asIdeal : ℝ) ^ (-2 : ℝ) := rfl
    rw [h2]
    linarith
  have habs : Summable fun v : HeightOneSpectrum (𝓞 k) => |localLog s v - normPow s v| :=
    Summable.of_nonneg_of_le (fun v => abs_nonneg _) hbnd (summable_sqNormPow.mul_left 2)
  have huniv : idealSum (Set.univ : Set (HeightOneSpectrum (𝓞 k))) s
      = ∑' v : HeightOneSpectrum (𝓞 k), normPow s v := by
    rw [idealSum, tsum_univ]
  have hdiff : logZeta k s - idealSum (Set.univ : Set (HeightOneSpectrum (𝓞 k))) s
      = ∑' v : HeightOneSpectrum (𝓞 k), (localLog s v - normPow s v) := by
    rw [logZeta, huniv, Summable.tsum_sub (summable_localLog hs) (summable_normPow hs)]
  rw [hdiff]
  have hnorm : Summable fun v : HeightOneSpectrum (𝓞 k) => ‖localLog s v - normPow s v‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have h1 := norm_tsum_le_tsum_norm hnorm
  simp only [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  calc ∑' v : HeightOneSpectrum (𝓞 k), |localLog s v - normPow s v|
      ≤ ∑' v : HeightOneSpectrum (𝓞 k), 2 * normPow (2 : ℝ) v :=
        Summable.tsum_le_tsum hbnd habs (summable_sqNormPow.mul_left 2)
    _ = 2 * sqNormSum k := by rw [sqNormSum]; exact tsum_mul_left

/-- **The whole set of primes of a number field has Dirichlet density one.** -/
theorem hasIdealDensity_univ :
    HasIdealDensity (Set.univ : Set (HeightOneSpectrum (𝓞 k))) 1 := by
  have hE : Tendsto (fun s : ℝ => (logZeta k s
        - idealSum (Set.univ : Set (HeightOneSpectrum (𝓞 k))) s) / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 0) := by
    have hb : Tendsto (fun s : ℝ => (2 * sqNormSum k) / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_logWeight
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL0]
    gcongr
    exact abs_logZeta_sub_idealSum_univ (Set.mem_Ioi.mp hs)
  have h4 := (tendsto_logZeta_div (eulerProductHypothesis k)).sub hE
  rw [sub_zero] at h4
  refine h4.congr fun s => ?_
  rw [← sub_div, sub_sub_cancel]

end Base

/-! ### The primes above a prime of the base -/

section Relative

variable {k L : Type*} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]

omit [NumberField L] in
/-- The ring of integers of an extension is faithful over the ring of integers of the base. -/
scoped instance faithfulSMul_ringOfIntegers : FaithfulSMul (𝓞 k) (𝓞 L) :=
  FaithfulSMul.of_field_isFractionRing (𝓞 k) (𝓞 L) k L

omit [NumberField L] in
/-- The ring of integers of an extension has no zero smul divisors over the ring of integers of
the base. -/
scoped instance noZeroSMulDivisors_ringOfIntegers : NoZeroSMulDivisors (𝓞 k) (𝓞 L) := by
  refine ⟨fun {c x} h => ?_⟩
  rw [Algebra.smul_def, mul_eq_zero] at h
  rcases h with h | h
  · exact Or.inl ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 L))).mp h)
  · exact Or.inr h

variable (k) in
/-- The prime of the base lying below a prime of an extension. -/
def primeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 k) where
  asIdeal := Ideal.under (𝓞 k) w.asIdeal
  isPrime := Ideal.IsPrime.under _ _
  ne_bot := Ideal.under_ne_bot _ w.ne_bot

omit [NumberField k] [NumberField L] in
@[simp]
theorem primeBelow_asIdeal (w : HeightOneSpectrum (𝓞 L)) :
    (primeBelow k w).asIdeal = Ideal.under (𝓞 k) w.asIdeal := rfl

instance liesOver_primeBelow (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (primeBelow k w).asIdeal := ⟨rfl⟩

omit [NumberField k] [NumberField L] in
/-- A prime of the extension lying over a prime of the base has that prime below it. -/
theorem primeBelow_eq_of_liesOver (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] : primeBelow k w = v :=
  HeightOneSpectrum.ext
    (Ideal.LiesOver.over (A := 𝓞 k) (P := w.asIdeal) (p := v.asIdeal)).symm

/-- A prime of the base is maximal in the ring of integers. -/
theorem isMaximal_asIdeal (v : HeightOneSpectrum (𝓞 k)) : v.asIdeal.IsMaximal :=
  v.isPrime.isMaximal v.ne_bot

/-- **The primes of the extension lying above a given prime of the base are exactly the primes
over it.** -/
def relFiberEquiv (v : HeightOneSpectrum (𝓞 k)) :
    ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩
  invFun P :=
    ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot P.2⟩, by
      haveI : P.1.IsPrime := P.2.1
      haveI : P.1.LiesOver v.asIdeal := P.2.2
      exact primeBelow_eq_of_liesOver v ⟨P.1, P.2.1, _⟩⟩
  left_inv w := by ext; rfl
  right_inv P := by ext; rfl

/-- Only finitely many primes of the extension lie above a given prime of the base. -/
instance finite_relFiber (v : HeightOneSpectrum (𝓞 k)) :
    Finite ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) := by
  haveI := isMaximal_asIdeal v
  haveI : Finite ↥(v.asIdeal.primesOver (𝓞 L)) := (primesOver_finite _ (𝓞 L)).to_subtype
  exact Finite.of_equiv _ (relFiberEquiv (L := L) v).symm

variable (L) in
/-- There are at most `[L : k]` primes of the extension above a prime of the base. -/
theorem card_relFiber_le (v : HeightOneSpectrum (𝓞 k)) :
    Nat.card ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) ≤ Module.finrank k L := by
  rw [Nat.card_congr (relFiberEquiv (L := L) v), Nat.card_coe_set_eq,
    ← coe_primesOverFinset v.ne_bot (𝓞 L), Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 L) k L v.ne_bot

variable (k L) in
/-- A prime of the base **splits completely** in an extension when every prime above it is
unramified with trivial residue extension. -/
def SplitsCompletelyIn (v : HeightOneSpectrum (𝓞 k)) : Prop :=
  ∀ P ∈ v.asIdeal.primesOver (𝓞 L),
    Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 L)) v.asIdeal P = 1 ∧
    v.asIdeal.inertiaDeg P = 1

/-- A completely split prime of the base has exactly `[L : k]` primes above it. -/
theorem card_relFiber_eq_of_splitsCompletelyIn {v : HeightOneSpectrum (𝓞 k)}
    (hs : SplitsCompletelyIn k L v) :
    Nat.card ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) = Module.finrank k L := by
  rw [Nat.card_congr (relFiberEquiv (L := L) v), Nat.card_coe_set_eq,
    ← coe_primesOverFinset v.ne_bot (𝓞 L), Set.ncard_coe_finset,
    ← Ideal.sum_ramification_inertia (𝓞 L) k L v.ne_bot, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨h1, h2⟩ := hs P ((mem_primesOverFinset_iff v.ne_bot (𝓞 L)).mp hP)
  rw [h1, h2]

/-- Above a completely split prime of the base every prime has the same absolute norm. -/
theorem absNorm_eq_of_splitsCompletelyIn {v : HeightOneSpectrum (𝓞 k)}
    (hs : SplitsCompletelyIn k L v) (w : HeightOneSpectrum (𝓞 L)) (hw : primeBelow k w = v) :
    absNorm w.asIdeal = absNorm v.asIdeal := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  have h2 := (hs w.asIdeal ⟨w.isPrime, inferInstance⟩).2
  rw [h, h2, pow_one]

/-- **Above an unramified prime of the base that does not split completely every prime has
absolute norm at least the square of the norm below.**  In a Galois extension all the primes above
a given prime share their residue degree; were that degree one the fundamental identity would make
the prime split completely. -/
theorem sq_le_absNorm_of_not_splitsCompletelyIn [IsGalois k L] {v : HeightOneSpectrum (𝓞 k)}
    (hunr : ∀ P ∈ v.asIdeal.primesOver (𝓞 L),
      Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 L)) v.asIdeal P = 1)
    (hns : ¬ SplitsCompletelyIn k L v) (w : HeightOneSpectrum (𝓞 L)) (hw : primeBelow k w = v) :
    absNorm v.asIdeal ^ 2 ≤ absNorm w.asIdeal := by
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩
  rw [SplitsCompletelyIn] at hns
  push_neg at hns
  obtain ⟨P, hP, hPne⟩ := hns
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver v.asIdeal := hP.2
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot hP
  set x : HeightOneSpectrum (𝓞 L) := ⟨P, hP.1, hPbot⟩ with hx
  have hfne : v.asIdeal.inertiaDeg P ≠ 0 := by
    intro h0
    have h2 := two_le_absNorm x
    have hnn : absNorm x.asIdeal = absNorm v.asIdeal ^ (v.asIdeal.inertiaDeg P) :=
      Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P v.asIdeal v.isPrime v.ne_bot
    rw [hnn, h0, pow_zero] at h2
    omega
  have hf2 : 2 ≤ v.asIdeal.inertiaDeg P := by
    rcases Nat.lt_or_ge (v.asIdeal.inertiaDeg P) 2 with h | h
    · exact absurd (hunr P hP) (fun hr => hPne hr (by omega))
    · exact h
  have heq : v.asIdeal.inertiaDeg w.asIdeal = v.asIdeal.inertiaDeg P :=
    Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.asIdeal P (L ≃ₐ[k] L)
  have hnv : absNorm w.asIdeal = absNorm v.asIdeal ^ (v.asIdeal.inertiaDeg w.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [hnv, heq]
  exact Nat.pow_le_pow_right (by have := two_le_absNorm v; omega) hf2

/-! ### The primes of the base that ramify -/

variable (k L) in
/-- The set of primes of the base that ramify in an extension. -/
def relRamifiedSet : Set (HeightOneSpectrum (𝓞 k)) :=
  {v | ∃ P ∈ v.asIdeal.primesOver (𝓞 L),
    Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 L)) v.asIdeal P ≠ 1}

/-- **A prime of the base ramifying in an extension lies over a rational prime that ramifies
there.**  Ramification indices multiply along a tower, so a relative index different from one
forces the absolute one to differ from one as well. -/
theorem resChar_mem_ramifiedSet_of_mem_relRamifiedSet {v : HeightOneSpectrum (𝓞 k)}
    (hv : v ∈ relRamifiedSet k L) : resChar v ∈ ramifiedSet L := by
  obtain ⟨P, hP, hPne⟩ := hv
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver v.asIdeal := hP.2
  haveI := liesOver_resChar v
  set p : ℕ := resChar v with hp
  have hprime : p.Prime := resChar_prime v
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans P v.asIdeal (Ideal.span {(p : ℤ)})
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot hP
  have htower : Ideal.ramificationIdx (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) P
      = Ideal.ramificationIdx (algebraMap ℤ (𝓞 k)) (Ideal.span {(p : ℤ)}) v.asIdeal *
        Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 L)) v.asIdeal P := by
    refine Ideal.ramificationIdx_algebra_tower ?_ ?_ ?_
    · exact fun h => v.ne_bot (by
        rwa [Ideal.map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 L))] at h)
    · exact fun h => span_intCast_ne_bot hprime (by
        rwa [Ideal.map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective ℤ (𝓞 L))] at h)
    · exact Ideal.map_le_of_le_comap
        (le_of_eq (Ideal.LiesOver.over (A := 𝓞 k) (P := P) (p := v.asIdeal)))
  refine ⟨hprime, P, ⟨hP.1, inferInstance⟩, ?_⟩
  rw [htower]
  intro hc
  exact hPne (Nat.eq_one_of_mul_eq_one_left hc)

/-- **Only finitely many primes of the base ramify in a finite extension.**  Each lies over one of
the finitely many rational primes that ramify in the extension, and only finitely many primes of
the base lie over a given rational prime. -/
theorem finite_relRamifiedSet : (relRamifiedSet k L).Finite := by
  have hfin := finite_ramifiedSet L
  have hpre : (resChar ⁻¹' (ramifiedSet L) : Set (HeightOneSpectrum (𝓞 k))).Finite := by
    have hcover : (resChar ⁻¹' (ramifiedSet L) : Set (HeightOneSpectrum (𝓞 k)))
        = ⋃ p ∈ ramifiedSet L, (resChar ⁻¹' {p} : Set (HeightOneSpectrum (𝓞 k))) := by
      ext v
      simp
    rw [hcover]
    exact hfin.biUnion fun p _ => Set.toFinite _
  exact hpre.subset fun v hv => resChar_mem_ramifiedSet_of_mem_relRamifiedSet hv

/-! ### Comparison with the sum over the completely split primes of the base -/

variable (k L) in
/-- The set of primes of the base that split completely in the extension. -/
def relSplitSet : Set (HeightOneSpectrum (𝓞 k)) := {v | SplitsCompletelyIn k L v}

variable (k L) in
/-- The sum of the local logarithms over the primes of the extension above a prime of the base. -/
noncomputable def relFiberSum (s : ℝ) (v : HeightOneSpectrum (𝓞 k)) : ℝ :=
  ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))), localLog s w.1

variable (k L) in
/-- The main term attached to a prime of the base: `[L : k] · N𝔭^{-s}` when the prime splits
completely, and zero otherwise. -/
noncomputable def relSplitTerm (s : ℝ) (v : HeightOneSpectrum (𝓞 k)) : ℝ :=
  (Module.finrank k L : ℝ) * (relSplitSet k L).indicator (normPow s) v

variable (k L) in
/-- The bound, independent of `s`, on the discrepancy between the fibre sums and the main
terms. -/
noncomputable def relErrBound (v : HeightOneSpectrum (𝓞 k)) : ℝ :=
  2 * (Module.finrank k L : ℝ) * normPow (2 : ℝ) v
    + (relRamifiedSet k L).indicator (fun _ => 2 * (Module.finrank k L : ℝ)) v

omit [NumberField L] in
/-- The error bound is non-negative. -/
theorem relErrBound_nonneg (v : HeightOneSpectrum (𝓞 k)) : 0 ≤ relErrBound k L v := by
  have hv := normPow_pos (K := k) (s := (2 : ℝ)) v
  exact add_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) v)

/-- The error bound is summable. -/
theorem summable_relErrBound : Summable (relErrBound k L) := by
  have h1 : Summable fun v : HeightOneSpectrum (𝓞 k) =>
      2 * (Module.finrank k L : ℝ) * normPow (2 : ℝ) v := by
    have := summable_sqNormPow (k := k)
    simpa [mul_assoc] using this.mul_left (2 * (Module.finrank k L : ℝ))
  have h2 : Summable ((relRamifiedSet k L).indicator (fun _ => 2 * (Module.finrank k L : ℝ))) :=
    (hasSum_subtype_iff_indicator.mp
      (((finite_relRamifiedSet (k := k) (L := L)).summable _).hasSum)).summable
  exact h1.add h2

/-- A fibre sum over the primes above a prime of the base is at most `[L : k]` times a uniform
bound on the summand. -/
theorem tsum_relFiber_le (F : HeightOneSpectrum (𝓞 L) → ℝ) (v : HeightOneSpectrum (𝓞 k)) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ w : HeightOneSpectrum (𝓞 L), primeBelow k w = v → F w ≤ c) :
    ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))), F w.1 ≤
      (Module.finrank k L : ℝ) * c := by
  calc ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))), F w.1
      ≤ ∑' _ : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))), c :=
        Summable.tsum_le_tsum (fun w => h w.1 w.2) Summable.of_finite Summable.of_finite
    _ = (Nat.card ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) : ℝ) * c := by
        rw [tsum_const, nsmul_eq_mul]
    _ ≤ (Module.finrank k L : ℝ) * c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_relFiber_le L v) hc

omit [NumberField k] [NumberField L] in
/-- A fibre sum of a function that is constant along the fibre. -/
theorem tsum_relFiber_eq (F : HeightOneSpectrum (𝓞 L) → ℝ) (v : HeightOneSpectrum (𝓞 k)) (c : ℝ)
    (h : ∀ w : HeightOneSpectrum (𝓞 L), primeBelow k w = v → F w = c) :
    ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))), F w.1 =
      (Nat.card ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) : ℝ) * c := by
  calc ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))), F w.1
      = ∑' _ : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))), c :=
        tsum_congr fun w => h w.1 w.2
    _ = (Nat.card ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) : ℝ) * c := by
        rw [tsum_const, nsmul_eq_mul]

omit [NumberField k] in
/-- Fibre sums are non-negative. -/
theorem relFiberSum_nonneg {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 k)) :
    0 ≤ relFiberSum k L s v :=
  tsum_nonneg fun _ => localLog_nonneg hs _

/-- A fibre sum is at most `[L : k]`. -/
theorem relFiberSum_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 k)) :
    relFiberSum k L s v ≤ (Module.finrank k L : ℝ) := by
  have h := tsum_relFiber_le (localLog (K := L) s) v 1 zero_le_one
    (fun w _ => localLog_le_one hs w)
  simpa [relFiberSum] using h

omit [NumberField L] in
/-- The main terms are non-negative. -/
theorem relSplitTerm_nonneg {s : ℝ} (v : HeightOneSpectrum (𝓞 k)) : 0 ≤ relSplitTerm k L s v :=
  mul_nonneg (Nat.cast_nonneg _)
    (Set.indicator_nonneg (fun w _ => (normPow_pos (s := s) w).le) v)

omit [NumberField L] in
/-- A main term is at most `[L : k]`. -/
theorem relSplitTerm_le {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 k)) :
    relSplitTerm k L s v ≤ (Module.finrank k L : ℝ) := by
  classical
  rw [relSplitTerm, Set.indicator_apply]
  have h2 : (0 : ℝ) ≤ (Module.finrank k L : ℝ) := Nat.cast_nonneg _
  split_ifs with hv
  · have h1 : normPow (K := k) s v ≤ 1 / 2 := normPow_le_half hs v
    nlinarith
  · rw [mul_zero]
    exact h2

/-- **The fibre sum over a prime of the base agrees with its main term up to the error bound.**
Above a completely split prime the local logarithms differ from the local factors by at most twice
their squares; above an unramified prime that does not split completely every local factor is
itself at most the square of the factor below; and the finitely many ramified primes are absorbed
wholesale. -/
theorem abs_relFiberSum_sub [IsGalois k L] {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 k)) :
    |relFiberSum k L s v - relSplitTerm k L s v| ≤ relErrBound k L v := by
  by_cases hram : v ∈ relRamifiedSet k L
  · have h1 : |relFiberSum k L s v - relSplitTerm k L s v| ≤ 2 * (Module.finrank k L : ℝ) := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have ha := relFiberSum_nonneg (k := k) (L := L) hs v
        have hb := relSplitTerm_le (k := k) (L := L) hs v
        linarith
      · have ha := relFiberSum_le (k := k) (L := L) hs v
        have hb := relSplitTerm_nonneg (k := k) (L := L) (s := s) v
        linarith
    refine h1.trans ?_
    rw [relErrBound, Set.indicator_of_mem hram]
    have : (0 : ℝ) ≤ 2 * (Module.finrank k L : ℝ) * normPow (K := k) (2 : ℝ) v := by
      have := normPow_pos (K := k) (s := (2 : ℝ)) v
      positivity
    linarith
  · have hunr : ∀ P ∈ v.asIdeal.primesOver (𝓞 L),
        Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 L)) v.asIdeal P = 1 := by
      intro P hP
      by_contra hc
      exact hram ⟨P, hP, hc⟩
    have hbase : |relFiberSum k L s v - relSplitTerm k L s v| ≤
        2 * (Module.finrank k L : ℝ) * normPow (K := k) (2 : ℝ) v := by
      by_cases hsp : SplitsCompletelyIn k L v
      · have hmem : v ∈ relSplitSet k L := hsp
        have hnorm : ∀ w : HeightOneSpectrum (𝓞 L), primeBelow k w = v →
            normPow (K := L) s w = normPow (K := k) s v := by
          intro w hw
          rw [normPow, normPow, absNorm_eq_of_splitsCompletelyIn hsp w hw]
        have e2 : ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))),
            normPow (K := L) s w.1 = (Module.finrank k L : ℝ) * normPow (K := k) s v := by
          rw [tsum_relFiber_eq _ v _ hnorm, card_relFiber_eq_of_splitsCompletelyIn hsp]
        have e1 : relFiberSum k L s v - relSplitTerm k L s v =
            ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))),
              (localLog s w.1 - normPow (K := L) s w.1) := by
          rw [Summable.tsum_sub Summable.of_finite Summable.of_finite, e2, relSplitTerm,
            Set.indicator_of_mem hmem, relFiberSum]
        rw [e1]
        calc |∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))),
                (localLog s w.1 - normPow (K := L) s w.1)|
            ≤ ∑' w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))),
                |localLog s w.1 - normPow (K := L) s w.1| := by
              simpa using norm_tsum_le_tsum_norm
                (f := fun w : ↥(primeBelow k ⁻¹' {v} : Set (HeightOneSpectrum (𝓞 L))) =>
                  localLog s w.1 - normPow (K := L) s w.1) Summable.of_finite
          _ ≤ (Module.finrank k L : ℝ) * (2 * normPow (K := k) (2 : ℝ) v) := by
              refine tsum_relFiber_le
                (fun w : HeightOneSpectrum (𝓞 L) => |localLog s w - normPow (K := L) s w|) v
                (2 * normPow (K := k) (2 : ℝ) v) ?_ (fun w hw => ?_)
              · have := normPow_pos (K := k) (s := (2 : ℝ)) v
                positivity
              · refine (abs_localLog_sub hs w).trans ?_
                have hsq := sq_normPow_le hs w
                rw [absNorm_eq_of_splitsCompletelyIn hsp w hw] at hsq
                have hnp : normPow (K := k) (2 : ℝ) v = (absNorm v.asIdeal : ℝ) ^ (-2 : ℝ) := rfl
                rw [hnp]
                linarith
          _ = 2 * (Module.finrank k L : ℝ) * normPow (K := k) (2 : ℝ) v := by ring
      · have hnmem : v ∉ relSplitSet k L := hsp
        rw [relSplitTerm, Set.indicator_of_notMem hnmem, mul_zero, sub_zero,
          abs_of_nonneg (relFiberSum_nonneg (k := k) (L := L) hs v)]
        calc relFiberSum k L s v
            ≤ (Module.finrank k L : ℝ) * (2 * normPow (K := k) (2 : ℝ) v) := by
              refine tsum_relFiber_le (localLog (K := L) s) v
                (2 * normPow (K := k) (2 : ℝ) v) ?_ (fun w hw => ?_)
              · have := normPow_pos (K := k) (s := (2 : ℝ)) v
                positivity
              · refine (localLog_le hs w).trans ?_
                have hn := normPow_le_rpow_neg_two_of_sq_le hs (two_le_absNorm v) w
                  (sq_le_absNorm_of_not_splitsCompletelyIn hunr hsp w hw)
                have hnp : normPow (K := k) (2 : ℝ) v = (absNorm v.asIdeal : ℝ) ^ (-2 : ℝ) := rfl
                rw [hnp]
                linarith
          _ = 2 * (Module.finrank k L : ℝ) * normPow (K := k) (2 : ℝ) v := by ring
    refine hbase.trans ?_
    rw [relErrBound]
    have : (0 : ℝ) ≤ (relRamifiedSet k L).indicator (fun _ => 2 * (Module.finrank k L : ℝ)) v :=
      Set.indicator_nonneg (fun _ _ => by positivity) v
    linarith

omit [NumberField k] in
/-- Grouping the primes of the extension by the prime of the base below them computes the
logarithm of the zeta function. -/
theorem hasSum_relFiberSum {s : ℝ} (hs : 1 < s) :
    HasSum (relFiberSum k L s) (logZeta L s) :=
  ((summable_localLog hs).hasSum).tsum_fiberwise (primeBelow k)

omit [NumberField L] in
/-- The main terms sum to `[L : k]` times the Dirichlet series of the completely split primes of
the base. -/
theorem hasSum_relSplitTerm {s : ℝ} (hs : 1 < s) :
    HasSum (relSplitTerm k L s)
      ((Module.finrank k L : ℝ) * idealSum (relSplitSet k L) s) :=
  HasSum.mul_left _
    (hasSum_subtype_iff_indicator.mp (summable_normPow_subtype hs (relSplitSet k L)).hasSum)

/-- **The logarithm of the zeta function of the extension differs from `[L : k]` times the
Dirichlet series of the completely split primes of the base by a bounded amount.** -/
theorem abs_logZeta_sub_rel [IsGalois k L] {s : ℝ} (hs : 1 < s) :
    |logZeta L s - (Module.finrank k L : ℝ) * idealSum (relSplitSet k L) s|
      ≤ ∑' v : HeightOneSpectrum (𝓞 k), relErrBound k L v := by
  have hsub := (hasSum_relFiberSum (k := k) (L := L) hs).sub
    (hasSum_relSplitTerm (k := k) (L := L) hs)
  have habs : Summable fun v : HeightOneSpectrum (𝓞 k) =>
      |relFiberSum k L s v - relSplitTerm k L s v| :=
    Summable.of_nonneg_of_le (fun v => abs_nonneg _) (fun v => abs_relFiberSum_sub hs.le v)
      summable_relErrBound
  have hnorm : Summable fun v : HeightOneSpectrum (𝓞 k) =>
      ‖relFiberSum k L s v - relSplitTerm k L s v‖ := by
    simpa only [Real.norm_eq_abs] using habs
  have h1 := norm_tsum_le_tsum_norm hnorm
  simp only [Real.norm_eq_abs] at h1
  rw [← hsub.tsum_eq]
  exact h1.trans
    (Summable.tsum_le_tsum (fun v => abs_relFiberSum_sub hs.le v) habs summable_relErrBound)

/-! ### The relative density theorem -/

/-- **The primes of a number field `k` that split completely in a Galois extension `L` of degree
`n` have Dirichlet density `1/n`.**

Each such prime carries exactly `n` primes of `L`, all of residue degree one, and these account
for the whole of `log ζ_L(s)` up to a bounded error; the simple pole of `ζ_L` at `s = 1` then pins
the density. -/
theorem hasIdealDensity_relSplitSet [IsGalois k L] :
    HasIdealDensity (relSplitSet k L) (1 / (Module.finrank k L : ℝ)) := by
  have hn0 : ((Module.finrank k L : ℕ) : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := k) (M := L)
    positivity
  have hE : Tendsto (fun s : ℝ =>
      (logZeta L s - (Module.finrank k L : ℝ) * idealSum (relSplitSet k L) s)
        / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    have hb : Tendsto
        (fun s : ℝ => (∑' v : HeightOneSpectrum (𝓞 k), relErrBound k L v)
          / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_logWeight
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, eventually_logWeight_pos] with s hs hL0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL0]
    gcongr
    exact abs_logZeta_sub_rel (Set.mem_Ioi.mp hs)
  have hnT : Tendsto (fun s : ℝ =>
      (Module.finrank k L : ℝ) * idealSum (relSplitSet k L) s / Real.log (1 / (s - 1)))
        (𝓝[>] 1) (𝓝 1) := by
    have h4 := (tendsto_logZeta_div (eulerProductHypothesis L)).sub hE
    rw [sub_zero] at h4
    refine h4.congr fun s => ?_
    rw [← sub_div, sub_sub_cancel]
  refine (hnT.div_const ((Module.finrank k L : ℕ) : ℝ)).congr fun s => ?_
  rw [mul_div_assoc, mul_div_cancel_left₀ _ hn0]

/-- **Infinitely many primes of a number field split completely in a Galois extension of it.** -/
theorem infinite_relSplitSet [IsGalois k L] : (relSplitSet k L).Infinite := by
  refine infinite_of_hasIdealDensity_pos ?_ (hasIdealDensity_relSplitSet (k := k) (L := L))
  have := Module.finrank_pos (R := k) (M := L)
  positivity

end Relative

/-- **The primes of a number field that split completely in a smaller Galois extension but not in
a larger one are infinite in number.**  Were they finite, the completely split primes of the
smaller extension would be covered by a finite set together with those of the larger one, and
comparing densities would give `1/[A : k] ≤ 1/[B : k]`. -/
theorem infinite_setOf_splitsCompletelyIn_not_splitsCompletelyIn
    (k : Type*) [Field k] [NumberField k]
    (A : Type*) [Field A] [NumberField A] [Algebra k A] [IsGalois k A]
    (B : Type*) [Field B] [NumberField B] [Algebra k B] [IsGalois k B]
    (hlt : Module.finrank k A < Module.finrank k B) :
    {v : HeightOneSpectrum (𝓞 k) |
      SplitsCompletelyIn k A v ∧ ¬ SplitsCompletelyIn k B v}.Infinite := by
  intro hfin
  have hsub : relSplitSet k A ⊆
      {v : HeightOneSpectrum (𝓞 k) |
        SplitsCompletelyIn k A v ∧ ¬ SplitsCompletelyIn k B v} ∪ relSplitSet k B := by
    intro v hv
    by_cases hB : SplitsCompletelyIn k B v
    · exact Or.inr hB
    · exact Or.inl ⟨hv, hB⟩
  have hle := idealDensity_le_of_subset_union hfin hsub
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
