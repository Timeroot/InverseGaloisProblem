/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.EvenRecursion

/-!
# Three consecutive stages carrying a common invariant

A sequence taking its values in a finite set repeats: below twice the size of the set, some value
is taken three times.  Taking the *first three* occurrences of such a value makes the three gaps
between them as small as they can be: no stage strictly between the first two carries that value,
none strictly between the last two does, and exactly one stage strictly between the first and the
last does, namely the middle one.

That is the pattern a rule alternating with the number of intervening stages of the same invariant
needs: the counter is even for the first gap, even for the second, and odd for the long one.

## Main results

* `InverseGalois.CFT.exists_three_occurrences`: **a sequence into a finite set takes some value
  three times below twice the size of the set, at three consecutive occurrences.**
* `InverseGalois.CFT.exists_three_stages`: the same, read through the counter of the recursion.

## Tags

pigeonhole principle, finite set, recursion, parity
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Three consecutive occurrences of one value -/

open scoped Classical in
/-- **A sequence into a finite set takes some value three times below twice the size of the set,
and the three occurrences can be taken to follow one another**: no member of the sequence strictly
between the first two takes that value, none strictly between the last two does, and exactly one
strictly between the first and the last does. -/
theorem exists_three_occurrences {α : Type*} (t : Finset α) (f : ℕ → α)
    (hf : ∀ m < 2 * t.card + 1, f m ∈ t) :
    ∃ i j N : ℕ, i < j ∧ j < N ∧ N < 2 * t.card + 1 ∧ f j = f i ∧ f N = f i ∧
      ((Finset.Ico (i + 1) j).filter fun l => f l = f i).card = 0 ∧
      ((Finset.Ico (j + 1) N).filter fun l => f l = f j).card = 0 ∧
      ((Finset.Ico (i + 1) N).filter fun l => f l = f i).card = 1 := by
  classical
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.range (2 * t.card + 1)) (t := t) (f := f) (n := 2)
    (fun a ha => hf a (Finset.mem_range.1 ha)) (by rw [Finset.card_range]; omega)
  set F := (Finset.range (2 * t.card + 1)).filter fun x => f x = y with hFdef
  have hFmem : ∀ x, x ∈ F ↔ x < 2 * t.card + 1 ∧ f x = y := by
    intro x
    rw [hFdef, Finset.mem_filter, Finset.mem_range]
  have hFne : F.Nonempty := Finset.card_pos.1 (by omega)
  have hiF : F.min' hFne ∈ F := F.min'_mem hFne
  set i := F.min' hFne with hidef
  set F₁ := F.filter fun x => i < x with hF₁def
  have hF₁mem : ∀ x, x ∈ F₁ ↔ x ∈ F ∧ i < x := by
    intro x
    rw [hF₁def, Finset.mem_filter]
  have hF₁eq : F₁ = F.erase i := by
    ext x
    rw [hF₁mem, Finset.mem_erase]
    exact ⟨fun h => ⟨h.2.ne', h.1⟩,
      fun h => ⟨h.2, lt_of_le_of_ne (F.min'_le x h.2) (Ne.symm h.1)⟩⟩
  have hF₁ne : F₁.Nonempty := by
    refine Finset.card_pos.1 ?_
    rw [hF₁eq, Finset.card_erase_of_mem hiF]
    omega
  have hjF₁ : F₁.min' hF₁ne ∈ F₁ := F₁.min'_mem hF₁ne
  set j := F₁.min' hF₁ne with hjdef
  set F₂ := F₁.filter fun x => j < x with hF₂def
  have hF₂mem : ∀ x, x ∈ F₂ ↔ x ∈ F₁ ∧ j < x := by
    intro x
    rw [hF₂def, Finset.mem_filter]
  have hF₂eq : F₂ = F₁.erase j := by
    ext x
    rw [hF₂mem, Finset.mem_erase]
    exact ⟨fun h => ⟨h.2.ne', h.1⟩,
      fun h => ⟨h.2, lt_of_le_of_ne (F₁.min'_le x h.2) (Ne.symm h.1)⟩⟩
  have hF₂ne : F₂.Nonempty := by
    refine Finset.card_pos.1 ?_
    rw [hF₂eq, Finset.card_erase_of_mem hjF₁]
    rw [hF₁eq, Finset.card_erase_of_mem hiF]
    omega
  have hNF₂ : F₂.min' hF₂ne ∈ F₂ := F₂.min'_mem hF₂ne
  set N := F₂.min' hF₂ne with hNdef
  have hjF : j ∈ F := ((hF₁mem j).1 hjF₁).1
  have hNF₁ : N ∈ F₁ := ((hF₂mem N).1 hNF₂).1
  have hNF : N ∈ F := ((hF₁mem N).1 hNF₁).1
  have hij : i < j := ((hF₁mem j).1 hjF₁).2
  have hjN : j < N := ((hF₂mem N).1 hNF₂).2
  have hNlt : N < 2 * t.card + 1 := ((hFmem N).1 hNF).1
  have hfi : f i = y := ((hFmem i).1 hiF).2
  have hfj : f j = y := ((hFmem j).1 hjF).2
  have hfN : f N = y := ((hFmem N).1 hNF).2
  refine ⟨i, j, N, hij, hjN, hNlt, by rw [hfi, hfj], by rw [hfi, hfN], ?_, ?_, ?_⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro l hl hfl
    rw [Finset.mem_Ico] at hl
    have hlF₁ : l ∈ F₁ :=
      (hF₁mem l).2 ⟨(hFmem l).2 ⟨by omega, by rw [← hfi]; exact hfl⟩, by omega⟩
    exact absurd (F₁.min'_le l hlF₁) (by omega)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro l hl hfl
    rw [Finset.mem_Ico] at hl
    have hlF₁ : l ∈ F₁ :=
      (hF₁mem l).2 ⟨(hFmem l).2 ⟨by omega, by rw [← hfj]; exact hfl⟩, by omega⟩
    have hlF₂ : l ∈ F₂ := (hF₂mem l).2 ⟨hlF₁, by omega⟩
    exact absurd (F₂.min'_le l hlF₂) (by omega)
  · rw [Finset.card_eq_one]
    refine ⟨j, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
    · rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, by omega⟩, by rw [hfi, hfj]⟩
    · intro l hl
      rw [Finset.mem_filter, Finset.mem_Ico] at hl
      by_contra hne
      have hlF₁ : l ∈ F₁ :=
        (hF₁mem l).2 ⟨(hFmem l).2 ⟨by omega, by rw [← hfi]; exact hl.2⟩, by omega⟩
      have hlF₂ : l ∈ F₂ :=
        (hF₂mem l).2 ⟨hlF₁, lt_of_le_of_ne (F₁.min'_le l hlF₁) (Ne.symm hne)⟩
      exact absurd (F₂.min'_le l hlF₂) (by omega)

/-! ### The counter of the recursion at three consecutive stages -/

open scoped Classical in
/-- **Three stages of the recursion carrying a common invariant, with the counter even across the
first gap, even across the second, and odd across the whole span.** -/
theorem exists_three_stages {K : Type} [Field K] [NumberField K] {Φ : Type} (t : Finset Φ)
    (d : EvenRecData K Φ) (hcls : ∀ m < 2 * t.card + 1, d.cls m ∈ t) :
    ∃ i j N : ℕ, i < j ∧ j < N ∧ N < 2 * t.card + 1 ∧ d.cls j = d.cls i ∧ d.cls N = d.cls i ∧
      d.count i j = 0 ∧ d.count j N = 0 ∧ d.count i N = 1 := by
  classical
  obtain ⟨i, j, N, hij, hjN, hNlt, hj, hN, h1, h2, h3⟩ :=
    exists_three_occurrences t d.cls hcls
  exact ⟨i, j, N, hij, hjN, hNlt, hj, hN, h1, h2, h3⟩

end InverseGalois.CFT
