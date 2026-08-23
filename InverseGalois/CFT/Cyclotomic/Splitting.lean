/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.NumberTheory.SplitCompletely

/-!
# The splitting law for cyclotomic fields

Let `K = ℚ(ζₙ)` be the `n`-th cyclotomic field and let `p` be a rational prime not dividing `n`.
The decomposition of `p` in the ring of integers of `K` is governed entirely by the residue of `p`
modulo `n`: the ramification index of every prime above `p` is `1`, and the common residue degree
is the multiplicative order of `p` in `ZMod n`.  Consequently `p` splits completely in `K` exactly
when that order is `1`, that is, exactly when `p ≡ 1 [MOD n]`.

This is the degree-one case of Artin reciprocity for `ℚ`: the abelian extension `ℚ(ζₙ)/ℚ` is
described by the congruence conditions modulo its conductor, and the primes that split completely
in it are precisely those lying in the trivial residue class.

## Main results

* `InverseGalois.CFT.splitsCompletely_iff_cast_eq_one` — for `p` not dividing `n`, the prime `p`
  splits completely in `ℚ(ζₙ)` if and only if the image of `p` in `ZMod n` is `1`.
* `InverseGalois.CFT.splitsCompletely_iff_modEq` — the same criterion phrased as the congruence
  `p ≡ 1 [MOD n]`.
* `InverseGalois.CFT.splitsCompletely_of_modEq` and
  `InverseGalois.CFT.modEq_of_splitsCompletely` — the two directions, stated separately.
-/

open Ideal NumberField

namespace InverseGalois.CFT

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime]

/-- **A prime not dividing `n` splits completely in `ℚ(ζₙ)` precisely when it is `1` modulo `n`.**
Above such a prime the ramification index is always `1`, so splitting completely amounts to every
residue degree being `1`; that residue degree is the multiplicative order of `p` in `ZMod n`, the
same for every prime above `p`, and an element has order `1` exactly when it is the identity. -/
theorem splitsCompletely_iff_cast_eq_one (hn : ¬ p ∣ n) :
    NumberTheory.SplitsCompletely K p ↔ (p : ZMod n) = 1 := by
  rw [← orderOf_eq_one_iff]
  constructor
  · intro h
    obtain ⟨⟨P, hP⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
    haveI : P.IsPrime := hP.1
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
    have hdeg := (h P hP).2
    rwa [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K P hn] at hdeg
  · intro h P hP
    haveI : P.IsPrime := hP.1
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
    exact ⟨IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hn,
      by rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K P hn, h]⟩

/-- **The cyclotomic splitting law.**  A rational prime `p` not dividing `n` splits completely in
the `n`-th cyclotomic field if and only if `p ≡ 1 [MOD n]`, the congruence being the translation
into arithmetic of the equality of `p` with `1` in `ZMod n`. -/
theorem splitsCompletely_iff_modEq (hn : ¬ p ∣ n) :
    NumberTheory.SplitsCompletely K p ↔ p ≡ 1 [MOD n] := by
  rw [splitsCompletely_iff_cast_eq_one n K p hn, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]

/-- **A prime congruent to `1` modulo `n` splits completely in the `n`-th cyclotomic field.** -/
theorem splitsCompletely_of_modEq (hn : ¬ p ∣ n) (h : p ≡ 1 [MOD n]) :
    NumberTheory.SplitsCompletely K p :=
  (splitsCompletely_iff_modEq n K p hn).mpr h

/-- **A prime splitting completely in the `n`-th cyclotomic field is congruent to `1` modulo
`n`.** -/
theorem modEq_of_splitsCompletely (hn : ¬ p ∣ n) (h : NumberTheory.SplitsCompletely K p) :
    p ≡ 1 [MOD n] :=
  (splitsCompletely_iff_modEq n K p hn).mp h

end InverseGalois.CFT
