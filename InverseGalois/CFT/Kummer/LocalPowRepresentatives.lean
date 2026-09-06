/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Approximation.PowClass
import InverseGalois.CFT.Local.AdicPowIndex
import InverseGalois.CFT.Local.InfinitePowIndex

/-!
# Finitely many global representatives of the local power classes

At a place of a number field the units of the completion modulo their `n`-th powers form a
**finite** group: the index of the `n`-th powers is bounded by the local index formula, which
expresses it in terms of `n`, the absolute value of `n` at the place, and the number of `n`-th roots
of unity of the completion.  Weak approximation makes the units of the field surject onto that finite group, since a
single element of the field can be prescribed at one place up to an `n`-th power.

Consequently there is a **finite set of units of the field** meeting every class: every unit of the
completion is a unit of the field times an `n`-th power of the completion, and the unit of the field
may be taken from a set fixed once and for all, independently of the local unit.

A finite set of representatives is what allows a Kummer argument at a place to be run inside a
single finite level of an infinite extension: the level need only contain an `n`-th root of the
element under study together with `n`-th roots of the finitely many representatives, rather than a
root of an element produced after the level has been chosen.

## Main results

* `InverseGalois.CFT.finiteIndex_range_powMonoidHom_units_adicCompletion`: **the `n`-th powers have
  finite index in the units of the completion at a finite place.**
* `InverseGalois.CFT.finiteIndex_range_powMonoidHom_units_infiniteCompletion`: **the same at an
  archimedean place.**
* `InverseGalois.CFT.exists_finite_pow_representatives_adicCompletion`: **finitely many units of a
  number field represent every power class of the completion at a finite place.**
* `InverseGalois.CFT.exists_finite_pow_representatives_infiniteCompletion`: **the same at an
  archimedean place.**

## Tags

number field, completion, local power class, weak approximation, Kummer theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Finiteness of the group of local power classes -/

/-- **The `n`-th powers have finite index in the units of the completion at a finite place.**  The
local index formula expresses the index in terms of the absolute value of `n` at the place and the
number of `n`-th roots of unity of the completion, both of which are nonzero. -/
theorem finiteIndex_range_powMonoidHom_units_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.FiniteIndex := by
  haveI : NeZero n := ⟨hn⟩
  refine ⟨fun h0 => ?_⟩
  have hidx := index_range_powMonoidHom_units_adicCompletion v hn
  rw [h0] at hidx
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hc : (Nat.card ↥(rootsOfUnity n (v.adicCompletion K)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  refine (mul_ne_zero hn' hc) ?_
  simpa using hidx.symm

omit [NumberField K] in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The `n`-th powers have finite index in the units of the completion at an archimedean
place.** -/
theorem finiteIndex_range_powMonoidHom_units_infiniteCompletion (w : InfinitePlace K)
    {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.FiniteIndex := by
  haveI : NeZero n := ⟨hn⟩
  refine ⟨fun h0 => ?_⟩
  have hidx := index_range_powMonoidHom_units_infinitePlace w hn
  rw [h0, zero_mul] at hidx
  exact (Nat.mul_ne_zero hn Nat.card_pos.ne') hidx.symm

/-! ### Finitely many representatives -/

/-- **Finitely many units of a number field represent every power class of the completion at a
finite place.**  The power classes form a finite group onto which the units of the field surject,
by weak approximation, so a section of that surjection has finite range. -/
theorem exists_finite_pow_representatives_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : n ≠ 0) :
    ∃ T : Set Kˣ, T.Finite ∧ ∀ η : (v.adicCompletion K)ˣ, ∃ a ∈ T,
      ∃ z : (v.adicCompletion K)ˣ,
        η = Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a * z ^ n := by
  haveI := finiteIndex_range_powMonoidHom_units_adicCompletion v hn
  set H := (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range with hH
  have hsurj : Function.Surjective (fun a : Kˣ =>
      (QuotientGroup.mk (Units.map (algebraMap K (v.adicCompletion K) : K →* _) a) :
        (v.adicCompletion K)ˣ ⧸ H)) := by
    intro q
    obtain ⟨η, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb0, -, hbC⟩ := exists_ne_zero_pow_mul_eq_completion (K := K) (Y := Unit)
      (ι := fun _ => v) hn (fun x y _ => Subsingleton.elim x y)
      (fun _ => 1) (fun _ => one_ne_zero) (fun _ => (η : v.adicCompletion K))
      (fun _ => η.ne_zero)
    obtain ⟨z, hz⟩ := hbC ()
    have hbne : algebraMap K (v.adicCompletion K) b ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr hb0
    have hzne : z ≠ 0 := by
      intro h
      rw [h, zero_pow hn, zero_mul] at hz
      exact hbne hz.symm
    have hmul : Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K)
        (Units.mk0 b hb0) = Units.mk0 z hzne ^ n * η := by
      refine Units.ext ?_
      simpa using hz.symm
    refine ⟨Units.mk0 b hb0, ?_⟩
    show (QuotientGroup.mk (Units.map (algebraMap K (v.adicCompletion K) : K →* _)
      (Units.mk0 b hb0)) : (v.adicCompletion K)ˣ ⧸ H) = QuotientGroup.mk η
    refine QuotientGroup.eq.mpr ?_
    have hmem : (Units.mk0 z hzne ^ n)⁻¹ ∈ H := H.inv_mem ⟨Units.mk0 z hzne, rfl⟩
    have heq : (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K)
        (Units.mk0 b hb0))⁻¹ * η = (Units.mk0 z hzne ^ n)⁻¹ := by
      rw [hmul, mul_inv_rev, mul_comm (η⁻¹), mul_assoc, inv_mul_cancel, mul_one]
    rw [heq]
    exact hmem
  refine ⟨Set.range (Function.surjInv hsurj), Set.finite_range _, fun η => ?_⟩
  refine ⟨Function.surjInv hsurj (QuotientGroup.mk η), Set.mem_range_self _, ?_⟩
  have hfa := Function.surjInv_eq hsurj (QuotientGroup.mk η)
  obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hfa
  refine ⟨z, ?_⟩
  have hz' : (z : (v.adicCompletion K)ˣ) ^ n
      = (Units.map (algebraMap K (v.adicCompletion K) : K →* _)
          (Function.surjInv hsurj (QuotientGroup.mk η)))⁻¹ * η := hz
  rw [hz']
  group

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **Finitely many units of a number field represent every power class of the completion at an
archimedean place.** -/
theorem exists_finite_pow_representatives_infiniteCompletion (u : InfinitePlace K)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ T : Set Kˣ, T.Finite ∧ ∀ η : u.Completionˣ, ∃ a ∈ T, ∃ z : u.Completionˣ,
      η = Units.map (algebraMap K u.Completion : K →* u.Completion) a * z ^ n := by
  classical
  haveI := finiteIndex_range_powMonoidHom_units_infiniteCompletion u hn
  set H := (powMonoidHom n : u.Completionˣ →* u.Completionˣ).range with hH
  have hsurj : Function.Surjective (fun a : Kˣ =>
      (QuotientGroup.mk (Units.map (algebraMap K u.Completion : K →* _) a) :
        u.Completionˣ ⧸ H)) := by
    intro q
    obtain ⟨η, rfl⟩ := QuotientGroup.mk_surjective q
    have hane : ∀ w : InfinitePlace K,
        Function.update (fun w : InfinitePlace K => (1 : w.Completion)) u (η : u.Completion) w
          ≠ 0 := by
      intro w
      rcases eq_or_ne w u with rfl | hw
      · rw [Function.update_self]
        exact η.ne_zero
      · rw [Function.update_of_ne hw]
        exact one_ne_zero
    obtain ⟨b, hb0, hbA, -⟩ := exists_ne_zero_pow_mul_eq_completion (K := K) (Y := Empty)
      (ι := fun y => y.elim) hn (fun x => x.elim) _ hane (fun y => y.elim) (fun y => y.elim)
    · obtain ⟨z, hz⟩ := hbA u
      rw [Function.update_self] at hz
      have hbne : algebraMap K u.Completion b ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K u.Completion).injective).mpr hb0
      have hzne : z ≠ 0 := by
        intro h
        rw [h, zero_pow hn, zero_mul] at hz
        exact hbne hz.symm
      have hmul : Units.map (algebraMap K u.Completion : K →* u.Completion) (Units.mk0 b hb0)
          = Units.mk0 z hzne ^ n * η := by
        refine Units.ext ?_
        simpa using hz.symm
      refine ⟨Units.mk0 b hb0, ?_⟩
      show (QuotientGroup.mk (Units.map (algebraMap K u.Completion : K →* _)
        (Units.mk0 b hb0)) : u.Completionˣ ⧸ H) = QuotientGroup.mk η
      refine QuotientGroup.eq.mpr ?_
      have hmem : (Units.mk0 z hzne ^ n)⁻¹ ∈ H := H.inv_mem ⟨Units.mk0 z hzne, rfl⟩
      have heq : (Units.map (algebraMap K u.Completion : K →* u.Completion)
          (Units.mk0 b hb0))⁻¹ * η = (Units.mk0 z hzne ^ n)⁻¹ := by
        rw [hmul, mul_inv_rev, mul_comm (η⁻¹), mul_assoc, inv_mul_cancel, mul_one]
      rw [heq]
      exact hmem
  refine ⟨Set.range (Function.surjInv hsurj), Set.finite_range _, fun η => ?_⟩
  refine ⟨Function.surjInv hsurj (QuotientGroup.mk η), Set.mem_range_self _, ?_⟩
  have hfa := Function.surjInv_eq hsurj (QuotientGroup.mk η)
  obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hfa
  refine ⟨z, ?_⟩
  have hz' : (z : u.Completionˣ) ^ n
      = (Units.map (algebraMap K u.Completion : K →* _)
          (Function.surjInv hsurj (QuotientGroup.mk η)))⁻¹ * η := hz
  rw [hz']
  group

end InverseGalois.CFT
