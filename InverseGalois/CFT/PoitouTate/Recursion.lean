/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.GlobalClasses

/-!
# Adding one ramified place at a time

A construction of algebraic numbers with prescribed local behaviour produces, from a finite set of
places carrying a prescription, one further place together with a unit realising the prescription
and ramified exactly at the new place.  Iterating it produces an unlimited supply of such places
and units, and the point of the iteration is that the prescription may be chosen along the way:
at the conjugates of a place already produced one prescribes the inverse of the class of the unit
attached to it, so that every later unit cancels every earlier one at all the nontrivial
conjugates of the earlier place.

This file carries out that iteration abstractly.  The construction which supplies a new place is
taken as a hypothesis, phrased over an abstract predicate on places recording whatever splitting
condition the new place is required to satisfy, so that nothing about the field in which the
places split has to be mentioned.  What is produced is, for every stage, a finite set of places, a
prescription, and sequences of places and units satisfying a list of invariants; those invariants
are exactly what a pigeonhole argument on the sequences needs downstream.

The set of places grows by a whole Galois orbit at each stage, which is what makes the prescription
at the conjugates well posed: the new place is not conjugate to any old one, because it lies
outside a set already stable under the Galois group.

The prescription is allowed to be ramified on a distinguished part of the fixed set, and then so
are the units produced; everywhere else both stay unramified.  Nothing in the iteration is affected
by this, since the distinguished part is fixed once and for all and the places added along the way
lie outside it.

## Main results

* `InverseGalois.CFT.RecData`: the data carried along the recursion.
* `InverseGalois.CFT.RecInv`: the invariants it is required to satisfy.
* `InverseGalois.CFT.exists_recInv_succ`: **one step of the recursion.**
* `InverseGalois.CFT.exists_recInv`: **the recursion runs for arbitrarily many steps.**

## Tags

number field, place, local class, prescription, recursion, Galois orbit
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The data and the invariants -/

/-- The data carried along a recursion which adds one place at a time: a finite set of places
carrying a prescription of local classes, together with the places already chosen and the units
already produced. -/
structure RecData (K : Type) [Field K] [NumberField K] (p : ℕ) where
  /-- the finite set of places at which the local behaviour is prescribed -/
  places : Finset (HeightOneSpectrum (𝓞 K))
  /-- the prescribed local class at each place -/
  pres : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p
  /-- the places chosen so far -/
  chosen : ℕ → HeightOneSpectrum (𝓞 K)
  /-- the units produced so far -/
  unit : ℕ → Kˣ

/-- The invariants maintained by a recursion which adds one place at a time.  The prescription is
unramified away from a distinguished part of the fixed set, agrees with the class of a fixed unit
on the fixed set, and records the inverse of the class of each unit at the nontrivial conjugates of
its own place; the chosen places satisfy the given splitting condition, have trivial decomposition
group, and are pairwise non-conjugate; and each unit is ramified at its own place and, away from
the distinguished part, nowhere else. -/
structure RecInv (k : Type) {K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
    {p : ℕ} [NeZero p] (Spl : HeightOneSpectrum (𝓞 K) → Prop)
    (Tr T S₀ : Finset (HeightOneSpectrum (𝓞 K))) (g : Kˣ) (n : ℕ) (d : RecData K p) : Prop where
  /-- the distinguished part is part of the prescribed set -/
  ramSub : Tr ⊆ T
  /-- the prescribed set of places is part of the initial one -/
  fixed : T ⊆ S₀
  /-- the initial set of places is part of the current one -/
  subset : S₀ ⊆ d.places
  /-- the current set of places is stable under the Galois group -/
  stable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ d.places → σ • v ∈ d.places
  /-- the prescription is unramified away from the distinguished part -/
  unram : ∀ v ∈ d.places, v ∉ Tr → d.pres v ∈ localUnramified v p
  /-- on the fixed set the prescription is the class of the fixed unit -/
  presT : ∀ v ∈ T, d.pres v = localClassHom v p g
  /-- the places added along the way satisfy the splitting condition -/
  split : ∀ v ∈ d.places, v ∉ T → Spl v
  /-- the chosen places belong to the current set -/
  chosenMem : ∀ i < n, d.chosen i ∈ d.places
  /-- the chosen places avoid the fixed set -/
  chosenNotMem : ∀ i < n, d.chosen i ∉ T
  /-- the chosen places have trivial decomposition group -/
  chosenStab : ∀ i < n, stabilizer Gal(K/k) (d.chosen i) = ⊥
  /-- distinct chosen places are not conjugate -/
  chosenNe : ∀ i < n, ∀ j < n, i ≠ j → ∀ σ : Gal(K/k), d.chosen i ≠ σ • d.chosen j
  /-- each unit is unramified away from its own place and the distinguished part -/
  unitUnram : ∀ i < n, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ d.chosen i →
    (p : ℤ) ∣ placeValue v (d.unit i)
  /-- each unit is ramified at its own place -/
  unitRam : ∀ i < n, ¬ (p : ℤ) ∣ placeValue (d.chosen i) (d.unit i)
  /-- on the fixed set each unit has the class of the fixed unit -/
  unitPres : ∀ i < n, ∀ v ∈ T, localClassHom v p (d.unit i) = localClassHom v p g
  /-- at the nontrivial conjugates of a chosen place the prescription inverts its unit -/
  presConj : ∀ i < n, ∀ σ : Gal(K/k), σ ≠ 1 →
    d.pres (σ • d.chosen i) = (localClassHom (σ • d.chosen i) p (d.unit i))⁻¹
  /-- at the nontrivial conjugates of a chosen place every later unit inverts its unit -/
  unitConj : ∀ i < n, ∀ j < n, i < j → ∀ σ : Gal(K/k), σ ≠ 1 →
    localClassHom (σ • d.chosen i) p (d.unit j)
      = (localClassHom (σ • d.chosen i) p (d.unit i))⁻¹

/-! ### The recursion -/

section Recursion

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
  {p : ℕ} [NeZero p] {Spl : HeightOneSpectrum (𝓞 K) → Prop}
  {Tr T S₀ : Finset (HeightOneSpectrum (𝓞 K))} {g : Kˣ}

/-- **One step of the recursion.**  The new place is not conjugate to any place of the current set,
because that set is stable under the Galois group; so the prescription may be extended by the
inverse of the class of the new unit at every nontrivial conjugate of the new place, and by the
trivial class at the new place itself. -/
theorem exists_recInv_succ
    (hSpl : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), Spl v → Spl (σ • v))
    (hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S → σ • v ∈ S) →
      ∀ c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v ∈ S, v ∉ Tr → c v ∈ localUnramified v p) →
        (∀ v ∈ T, c v = localClassHom v p g) →
        (∀ v ∈ S, v ∉ T → Spl v) →
        ∃ Q : HeightOneSpectrum (𝓞 K), Q ∉ S ∧ Spl Q ∧ stabilizer Gal(K/k) Q = ⊥ ∧
          ∃ w : Kˣ, (∀ v ∈ S, localClassHom v p w = c v) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ Q → (p : ℤ) ∣ placeValue v w) ∧
            ¬ (p : ℤ) ∣ placeValue Q w)
    (n : ℕ) (d : RecData K p) (hd : RecInv k Spl Tr T S₀ g n d) :
    ∃ d' : RecData K p, RecInv k Spl Tr T S₀ g (n + 1) d' := by
  classical
  obtain ⟨Q, hQS, hQSpl, hQstab, w, hwS, hwunr, hwram⟩ :=
    hstep d.places hd.subset hd.stable d.pres hd.unram hd.presT hd.split
  -- no conjugate of the new place meets the current set
  have hconj : ∀ σ : Gal(K/k), σ • Q ∉ d.places := fun σ hmem => by
    refine hQS ?_
    have h := hd.stable σ⁻¹ _ hmem
    rwa [inv_smul_smul] at h
  have hQnot : Q ∉ d.places := by simpa using hconj 1
  -- a nontrivial automorphism moves the new place
  have hQmove : ∀ σ : Gal(K/k), σ ≠ 1 → σ • Q ≠ Q := fun σ hσ hfix =>
    hσ ((Subgroup.eq_bot_iff_forall _).1 hQstab σ (mem_stabilizer_iff.2 hfix))
  -- the enlarged set of places
  have hrange : (Set.range fun σ : Gal(K/k) => σ • Q).Finite := Set.finite_range _
  obtain ⟨S', hS'⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ S' ↔ v ∈ d.places ∨ ∃ σ : Gal(K/k), σ • Q = v := by
    refine ⟨d.places ∪ hrange.toFinset, fun v => ?_⟩
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_range]
  -- the enlarged prescription
  obtain ⟨c', hc'old, hc'Q, hc'new⟩ :
      ∃ c' : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v ∈ d.places, c' v = d.pres v) ∧ c' Q = 1 ∧
          ∀ v : HeightOneSpectrum (𝓞 K), v ∉ d.places → v ≠ Q →
            c' v = (localClassHom v p w)⁻¹ := by
    refine ⟨fun v => if v ∈ d.places then d.pres v else if v = Q then 1
      else (localClassHom v p w)⁻¹, fun v hv => if_pos hv, ?_, fun v hv hvQ => ?_⟩
    · dsimp only
      rw [if_neg hQnot, if_pos rfl]
    · dsimp only
      rw [if_neg hv, if_neg hvQ]
  have hc'conj : ∀ σ : Gal(K/k), σ ≠ 1 → c' (σ • Q) = (localClassHom (σ • Q) p w)⁻¹ :=
    fun σ hσ => hc'new _ (hconj σ) (hQmove σ hσ)
  -- the enlarged sequences
  obtain ⟨Pl', hPl'ne, hPl'n⟩ : ∃ Pl' : ℕ → HeightOneSpectrum (𝓞 K),
      (∀ i, i ≠ n → Pl' i = d.chosen i) ∧ Pl' n = Q :=
    ⟨fun i => if i = n then Q else d.chosen i, fun _ hi => if_neg hi, if_pos rfl⟩
  obtain ⟨z', hz'ne, hz'n⟩ : ∃ z' : ℕ → Kˣ, (∀ i, i ≠ n → z' i = d.unit i) ∧ z' n = w :=
    ⟨fun i => if i = n then w else d.unit i, fun _ hi => if_neg hi, if_pos rfl⟩
  -- the invariants, one by one
  have hsub : S₀ ⊆ S' := fun v hv => (hS' v).2 (Or.inl (hd.subset hv))
  have hstab : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S' → σ • v ∈ S' := by
    intro σ v hv
    rcases (hS' v).1 hv with h | ⟨τ, rfl⟩
    · exact (hS' _).2 (Or.inl (hd.stable σ v h))
    · exact (hS' _).2 (Or.inr ⟨σ * τ, mul_smul σ τ Q⟩)
  have hunram : ∀ v ∈ S', v ∉ Tr → c' v ∈ localUnramified v p := by
    intro v _ hvTr
    by_cases hvS : v ∈ d.places
    · rw [hc'old v hvS]
      exact hd.unram v hvS hvTr
    · by_cases hvQ : v = Q
      · subst hvQ
        rw [hc'Q]
        exact one_mem _
      · rw [hc'new v hvS hvQ]
        exact inv_mem ((localClassHom_mem_localUnramified_iff v w).2 (hwunr v hvTr hvQ))
  have hpresT : ∀ v ∈ T, c' v = localClassHom v p g :=
    fun v hv => (hc'old v (hd.subset (hd.fixed hv))).trans (hd.presT v hv)
  have hsplit : ∀ v ∈ S', v ∉ T → Spl v := by
    intro v hv hvT
    rcases (hS' v).1 hv with h | ⟨τ, rfl⟩
    · exact hd.split v h hvT
    · exact hSpl τ Q hQSpl
  have hchosenMem : ∀ i < n + 1, Pl' i ∈ S' := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [hPl'ne i h.ne]
      exact (hS' _).2 (Or.inl (hd.chosenMem i h))
    · rw [hPl'n]
      exact (hS' _).2 (Or.inr ⟨1, one_smul _ _⟩)
  have hchosenNotMem : ∀ i < n + 1, Pl' i ∉ T := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [hPl'ne i h.ne]
      exact hd.chosenNotMem i h
    · rw [hPl'n]
      exact fun hQT => hQnot (hd.subset (hd.fixed hQT))
  have hchosenStab : ∀ i < n + 1, stabilizer Gal(K/k) (Pl' i) = ⊥ := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [hPl'ne i h.ne]
      exact hd.chosenStab i h
    · rw [hPl'n]
      exact hQstab
  have hchosenNe : ∀ i < n + 1, ∀ j < n + 1, i ≠ j → ∀ σ : Gal(K/k), Pl' i ≠ σ • Pl' j := by
    intro i hi j hj hij σ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
      · rw [hPl'ne i h.ne, hPl'ne j h'.ne]
        exact hd.chosenNe i h j h' hij σ
      · rw [hPl'ne i h.ne, hPl'n]
        exact fun heq => hconj σ (heq ▸ hd.chosenMem i h)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
      · rw [hPl'ne j h'.ne, hPl'n]
        exact fun heq => hQnot (heq ▸ hd.stable σ _ (hd.chosenMem j h'))
      · exact absurd rfl hij
  have hunitUnram : ∀ i < n + 1, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ Pl' i →
      (p : ℤ) ∣ placeValue v (z' i) := by
    intro i hi v hvTr hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [hPl'ne i h.ne] at hv
      rw [hz'ne i h.ne]
      exact hd.unitUnram i h v hvTr hv
    · rw [hPl'n] at hv
      rw [hz'n]
      exact hwunr v hvTr hv
  have hunitRam : ∀ i < n + 1, ¬ (p : ℤ) ∣ placeValue (Pl' i) (z' i) := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [hz'ne i h.ne, hPl'ne i h.ne]
      exact hd.unitRam i h
    · rw [hz'n, hPl'n]
      exact hwram
  have hunitPres : ∀ i < n + 1, ∀ v ∈ T, localClassHom v p (z' i) = localClassHom v p g := by
    intro i hi v hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [hz'ne i h.ne]
      exact hd.unitPres i h v hv
    · rw [hz'n, hwS v (hd.subset (hd.fixed hv))]
      exact hd.presT v hv
  have hpresConj : ∀ i < n + 1, ∀ σ : Gal(K/k), σ ≠ 1 →
      c' (σ • Pl' i) = (localClassHom (σ • Pl' i) p (z' i))⁻¹ := by
    intro i hi σ hσ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [hz'ne i h.ne, hPl'ne i h.ne, hc'old _ (hd.stable σ _ (hd.chosenMem i h))]
      exact hd.presConj i h σ hσ
    · rw [hz'n, hPl'n]
      exact hc'conj σ hσ
  have hunitConj : ∀ i < n + 1, ∀ j < n + 1, i < j → ∀ σ : Gal(K/k), σ ≠ 1 →
      localClassHom (σ • Pl' i) p (z' j) = (localClassHom (σ • Pl' i) p (z' i))⁻¹ := by
    intro i _ j hj hij σ hσ
    have h : i < n := lt_of_lt_of_le hij (Nat.lt_succ_iff.1 hj)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
    · rw [hz'ne i h.ne, hz'ne j h'.ne, hPl'ne i h.ne]
      exact hd.unitConj i h j h' hij σ hσ
    · rw [hz'ne i h.ne, hz'n, hPl'ne i h.ne, hwS _ (hd.stable σ _ (hd.chosenMem i h))]
      exact hd.presConj i h σ hσ
  exact ⟨⟨S', c', Pl', z'⟩, hd.ramSub, hd.fixed, hsub, hstab, hunram, hpresT, hsplit, hchosenMem,
    hchosenNotMem, hchosenStab, hchosenNe, hunitUnram, hunitRam, hunitPres, hpresConj, hunitConj⟩

/-- **The recursion runs for arbitrarily many steps.**  The initial data prescribes the class of
the fixed unit on the prescribed set and the trivial class on the rest of the initial set; a single
run of the construction supplies a place and a unit to start the sequences with. -/
theorem exists_recInv
    (hSpl : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), Spl v → Spl (σ • v))
    (hTrT : Tr ⊆ T) (hTS : T ⊆ S₀)
    (hSstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S₀ → σ • v ∈ S₀)
    (hSsplit : ∀ v ∈ S₀, v ∉ T → Spl v)
    (hgunr : ∀ v ∈ T, v ∉ Tr → localClassHom v p g ∈ localUnramified v p)
    (hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S → σ • v ∈ S) →
      ∀ c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v ∈ S, v ∉ Tr → c v ∈ localUnramified v p) →
        (∀ v ∈ T, c v = localClassHom v p g) →
        (∀ v ∈ S, v ∉ T → Spl v) →
        ∃ Q : HeightOneSpectrum (𝓞 K), Q ∉ S ∧ Spl Q ∧ stabilizer Gal(K/k) Q = ⊥ ∧
          ∃ w : Kˣ, (∀ v ∈ S, localClassHom v p w = c v) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ Q → (p : ℤ) ∣ placeValue v w) ∧
            ¬ (p : ℤ) ∣ placeValue Q w)
    (n : ℕ) : ∃ d : RecData K p, RecInv k Spl Tr T S₀ g n d := by
  classical
  induction n with
  | zero =>
    obtain ⟨c₀, hc₀T, hc₀not⟩ : ∃ c₀ : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v ∈ T, c₀ v = localClassHom v p g) ∧ ∀ v ∉ T, c₀ v = 1 :=
      ⟨fun v => if v ∈ T then localClassHom v p g else 1, fun _ hv => if_pos hv,
        fun _ hv => if_neg hv⟩
    have hc₀unr : ∀ v ∈ S₀, v ∉ Tr → c₀ v ∈ localUnramified v p := by
      intro v _ hvTr
      by_cases hvT : v ∈ T
      · rw [hc₀T v hvT]
        exact hgunr v hvT hvTr
      · rw [hc₀not v hvT]
        exact one_mem _
    obtain ⟨Q, -, -, -, -⟩ := hstep S₀ subset_rfl hSstable c₀ hc₀unr hc₀T hSsplit
    refine ⟨⟨S₀, c₀, fun _ => Q, fun _ => 1⟩, hTrT, hTS, subset_rfl, hSstable, hc₀unr, hc₀T,
      hSsplit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals exact fun i hi => absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    obtain ⟨d, hd⟩ := ih
    exact exists_recInv_succ hSpl hstep m d hd

end Recursion

end InverseGalois.CFT
