/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SymbolReciprocity
import InverseGalois.CFT.PoitouTate.GlobalClasses

/-!
# Adding one ramified place at a time, with a prescription depending on the stage

The recursion of `InverseGalois.CFT.RecInv` prescribes, at a nontrivial conjugate of a place it has
already chosen, one local class shared by every later stage.  A product of two stages is then
trivial there, and a product of three stages is not: the shared prescription contributes its square
and what is left is the class of the earliest stage.

This file runs the same recursion with a prescription which is allowed to depend on the stage.  At
the nontrivial conjugates of an earlier place each later stage is prescribed either the class of
the earlier unit or the trivial class, according to a rule which reads two things: a fixed subset
of the Galois group meeting each pair of distinct mutually inverse automorphisms once, and the
number of intervening stages carrying the same invariant as the earlier one.  The rule alternates
with that number, so that among three stages carrying a common invariant and following one another
the first two cancel at the conjugates of the first place while the third does not, and the pattern
repeats at the conjugates of the second place.  That is exactly what a product of three stages
needs.

The invariant read by the rule is carried along as part of the data, and is tied to the values of
the units by one of the invariants of the recursion; it is what the pigeonhole principle
downstream matches.

## Main results

* `InverseGalois.CFT.exists_half_set`: **a subset of a group meeting each pair of distinct mutually
  inverse elements exactly once.**
* `InverseGalois.CFT.EvenRecData`: the data carried along the recursion.
* `InverseGalois.CFT.EvenRecInv`: the invariants it is required to satisfy.
* `InverseGalois.CFT.exists_evenRecInv_succ`: **one step of the recursion.**
* `InverseGalois.CFT.exists_evenRecInv`: **the recursion runs for arbitrarily many steps.**

## Tags

number field, place, local class, prescription, recursion, Galois orbit, parity
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Half of a group -/

/-- **A subset of a group meeting each pair of distinct mutually inverse elements exactly once**,
and containing no element which is its own inverse. -/
theorem exists_half_set (G : Type*) [Group G] :
    ∃ L : Set G, (∀ σ : G, σ = σ⁻¹ → σ ∉ L) ∧ ∀ σ : G, σ ≠ σ⁻¹ → (σ ∈ L ↔ σ⁻¹ ∉ L) := by
  obtain ⟨_, -⟩ := exists_wellOrder G
  refine ⟨{σ : G | σ < σ⁻¹}, fun σ h hm => ?_, fun σ h => ?_⟩
  · rw [Set.mem_setOf_eq, ← h] at hm
    exact lt_irrefl σ hm
  · simp only [Set.mem_setOf_eq, inv_inv]
    exact ⟨fun h1 h2 => absurd (h1.trans h2) (lt_irrefl σ),
      fun h1 => lt_of_le_of_ne (not_lt.1 h1) h⟩

/-- **The rule read by the prescription**: an automorphism is prescribed the class of the earlier
unit when it belongs to the chosen half of the Galois group, and its inverse is read instead as
soon as an odd number of stages carrying the same invariant has intervened. -/
def EvenFlag {G : Type*} [Group G] (L : Set G) (m : ℕ) (σ : G) : Prop :=
  if Even m then σ ∈ L else σ⁻¹ ∈ L

/-- At a stage separated from the earlier one by no intervening stage the rule is membership of the
chosen half. -/
theorem evenFlag_zero {G : Type*} [Group G] (L : Set G) (σ : G) :
    EvenFlag L 0 σ ↔ σ ∈ L := by
  rw [EvenFlag, if_pos (by decide : Even 0)]

/-- At a stage separated from the earlier one by one intervening stage the rule is membership of
the chosen half by the inverse. -/
theorem evenFlag_one {G : Type*} [Group G] (L : Set G) (σ : G) :
    EvenFlag L 1 σ ↔ σ⁻¹ ∈ L := by
  rw [EvenFlag, if_neg (by decide)]

/-! ### The data and the invariants -/

/-- The data carried along a recursion which adds one place at a time with a prescription depending
on the stage: a finite set of places, the places already chosen, the units already produced, and
the invariant of each stage which the prescription reads. -/
structure EvenRecData (K : Type) [Field K] [NumberField K] (Φ : Type) where
  /-- the finite set of places at which the local behaviour is prescribed -/
  places : Finset (HeightOneSpectrum (𝓞 K))
  /-- the places chosen so far -/
  chosen : ℕ → HeightOneSpectrum (𝓞 K)
  /-- the units produced so far -/
  unit : ℕ → Kˣ
  /-- the invariant of each stage -/
  cls : ℕ → Φ

open scoped Classical in
/-- The number of stages strictly between two given ones carrying the same invariant as the
earlier one. -/
noncomputable def EvenRecData.count {K : Type} [Field K] [NumberField K] {Φ : Type}
    (d : EvenRecData K Φ) (i j : ℕ) : ℕ :=
  ((Finset.Ico (i + 1) j).filter fun l => d.cls l = d.cls i).card

open scoped Classical in
/-- The prescription used at a given stage: the class of the fixed unit on the fixed set, the class
of an earlier unit at those nontrivial conjugates of its own place which the rule selects, and the
trivial class everywhere else. -/
noncomputable def evenPres {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
    {Φ : Type} (L : Set Gal(K/k)) (p : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K))) (g : Kˣ)
    (d : EvenRecData K Φ) (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : localClasses v p :=
  (if v ∈ T then localClassHom v p g else 1) *
    ∏ i ∈ Finset.range n,
      (if ∃ σ : Gal(K/k), σ ≠ 1 ∧ EvenFlag L (d.count i n) σ ∧ σ • d.chosen i = v then
        localClassHom v p (d.unit i) else 1)

/-- The invariants maintained by a recursion which adds one place at a time with a prescription
depending on the stage.  The chosen places satisfy the given splitting condition, have trivial
decomposition group, and are pairwise non-conjugate; each unit is a local power at every infinite
place, has the class of the fixed unit on the fixed set, is ramified at its own place and nowhere
else, and is a unit away from the initial set of places and its own place; the invariant recorded
for each stage is the pair formed by its values at the Frobenius automorphisms of the conjugates of
its own place and by its value at its own place read modulo the exponent; and at the nontrivial
conjugates of the place of an earlier stage each later unit has, according to the rule, either the
class of the earlier unit or the trivial class. -/
structure EvenRecInv (k : Type) {K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
    {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (L : Set Gal(K/k))
    (Spl : HeightOneSpectrum (𝓞 K) → Prop) (T S₀ : Finset (HeightOneSpectrum (𝓞 K))) (g : Kˣ)
    (n : ℕ) (d : EvenRecData K ((Gal(K/k) → Multiplicative QModZ) × ZMod p)) : Prop where
  /-- the prescribed set of places is part of the initial one -/
  fixed : T ⊆ S₀
  /-- the initial set of places is part of the current one -/
  subset : S₀ ⊆ d.places
  /-- the current set of places is stable under the Galois group -/
  stable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ d.places → σ • v ∈ d.places
  /-- the places added along the way satisfy the splitting condition -/
  split : ∀ v ∈ d.places, v ∉ T → Spl v
  /-- the chosen places belong to the current set -/
  chosenMem : ∀ i < n, d.chosen i ∈ d.places
  /-- the chosen places avoid the initial set -/
  chosenNotMem : ∀ i < n, d.chosen i ∉ S₀
  /-- the chosen places have trivial decomposition group -/
  chosenStab : ∀ i < n, stabilizer Gal(K/k) (d.chosen i) = ⊥
  /-- distinct chosen places are not conjugate -/
  chosenNe : ∀ i < n, ∀ j < n, i ≠ j → ∀ σ : Gal(K/k), d.chosen i ≠ σ • d.chosen j
  /-- each unit is unramified away from its own place -/
  unitUnram : ∀ i < n, ∀ v : HeightOneSpectrum (𝓞 K), v ≠ d.chosen i →
    (p : ℤ) ∣ placeValue v (d.unit i)
  /-- each unit is ramified at its own place -/
  unitRam : ∀ i < n, ¬ (p : ℤ) ∣ placeValue (d.chosen i) (d.unit i)
  /-- each unit is a unit away from the initial set of places and its own place -/
  unitZero : ∀ i < n, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ → v ≠ d.chosen i →
    placeValue v (d.unit i) = 0
  /-- each unit is a local power at every infinite place -/
  unitInf : ∀ i < n, ∀ w : InfinitePlace K, infClassHom w p (d.unit i) = 1
  /-- on the fixed set each unit has the class of the fixed unit -/
  unitPres : ∀ i < n, ∀ v ∈ T, localClassHom v p (d.unit i) = localClassHom v p g
  /-- the invariant recorded for each stage is the one read by the pigeonhole principle -/
  clsSpec : ∀ i < n, d.cls i =
    ((fun σ : Gal(K/k) => placeFrobValue hres hζ (σ • d.chosen i) (d.unit i)),
      ((placeValue (d.chosen i) (d.unit i) : ℤ) : ZMod p))
  /-- at the nontrivial conjugates of a chosen place every later unit follows the rule -/
  unitConj : ∀ i < n, ∀ j < n, i < j → ∀ σ : Gal(K/k), σ ≠ 1 →
    (EvenFlag L (d.count i j) σ → localClassHom (σ • d.chosen i) p (d.unit j) =
      localClassHom (σ • d.chosen i) p (d.unit i)) ∧
    (¬ EvenFlag L (d.count i j) σ → localClassHom (σ • d.chosen i) p (d.unit j) = 1)


/-! ### The prescription -/

section Pres

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] {Φ : Type}
  {p : ℕ} [NeZero p] {L : Set Gal(K/k)} {T : Finset (HeightOneSpectrum (𝓞 K))} {g : Kˣ}
  {d : EvenRecData K Φ} {n : ℕ}

/-- The count of intervening stages only reads the invariants of the stages already passed. -/
theorem EvenRecData.count_congr {d' : EvenRecData K Φ} {i j : ℕ} (hij : i < j)
    (h : ∀ l < j, d'.cls l = d.cls l) : d'.count i j = d.count i j := by
  classical
  refine congrArg Finset.card (Finset.filter_congr fun l hl => ?_)
  rw [h l (Finset.mem_Ico.1 hl).2, h i hij]

omit [NeZero p] in
/-- On the fixed set the prescription is the class of the fixed unit. -/
theorem evenPres_of_mem (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
    v ∈ T → σ • v ∈ T) (hchosen : ∀ i < n, d.chosen i ∉ T)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) :
    evenPres L p T g d n v = localClassHom v p g := by
  classical
  rw [evenPres, if_pos hv, Finset.prod_eq_one, mul_one]
  intro i hi
  refine if_neg ?_
  rintro ⟨σ, -, -, hσ⟩
  refine hchosen i (Finset.mem_range.1 hi) ?_
  have h := hTstable σ⁻¹ v hv
  rwa [← hσ, inv_smul_smul] at h

/-- The prescription is unramified at every place. -/
theorem evenPres_mem_localUnramified
    (hgunr : ∀ v ∈ T, localClassHom v p g ∈ localUnramified v p)
    (hstab : ∀ i < n, stabilizer Gal(K/k) (d.chosen i) = ⊥)
    (hunram : ∀ i < n, ∀ v : HeightOneSpectrum (𝓞 K), v ≠ d.chosen i →
      (p : ℤ) ∣ placeValue v (d.unit i))
    (v : HeightOneSpectrum (𝓞 K)) : evenPres L p T g d n v ∈ localUnramified v p := by
  classical
  refine mul_mem ?_ (prod_mem fun i hi => ?_)
  · by_cases hv : v ∈ T
    · rw [if_pos hv]
      exact hgunr v hv
    · rw [if_neg hv]
      exact one_mem _
  · by_cases hc : ∃ σ : Gal(K/k), σ ≠ 1 ∧ EvenFlag L (d.count i n) σ ∧ σ • d.chosen i = v
    · rw [if_pos hc]
      obtain ⟨σ, hσ, -, hσv⟩ := hc
      refine (localClassHom_mem_localUnramified_iff v _).2
        (hunram i (Finset.mem_range.1 hi) v fun hvQ => hσ ?_)
      refine (Subgroup.eq_bot_iff_forall _).1 (hstab i (Finset.mem_range.1 hi)) σ ?_
      rw [mem_stabilizer_iff, hσv]
      exact hvQ
    · rw [if_neg hc]
      exact one_mem _

end Pres

section Conj

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] {Φ : Type}
  {p : ℕ} {L : Set Gal(K/k)} {T : Finset (HeightOneSpectrum (𝓞 K))} {g : Kˣ}
  {d : EvenRecData K Φ} {n : ℕ}
  (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
  (hchosen : ∀ i < n, d.chosen i ∉ T)
  (hne : ∀ i < n, ∀ j < n, i ≠ j → ∀ σ : Gal(K/k), d.chosen i ≠ σ • d.chosen j)
  (hstab : ∀ i < n, stabilizer Gal(K/k) (d.chosen i) = ⊥)

include hTstable hchosen in
/-- A nontrivial conjugate of a chosen place lies outside the fixed set. -/
theorem smul_chosen_notMem {j : ℕ} (hj : j < n) (τ : Gal(K/k)) : τ • d.chosen j ∉ T :=
  fun hmem => hchosen j hj (by
    have h := hTstable τ⁻¹ _ hmem
    rwa [inv_smul_smul] at h)

include hTstable hchosen hne in
/-- At a nontrivial conjugate of a chosen place selected by the rule, the prescription is the class
of the unit attached to that place. -/
theorem evenPres_smul_chosen_of_flag {j : ℕ} (hj : j < n) {τ : Gal(K/k)} (hτ : τ ≠ 1)
    (hflag : EvenFlag L (d.count j n) τ) :
    evenPres L p T g d n (τ • d.chosen j) = localClassHom (τ • d.chosen j) p (d.unit j) := by
  classical
  rw [evenPres, if_neg (smul_chosen_notMem hTstable hchosen hj τ)]
  refine (one_mul (_ : localClasses (τ • d.chosen j) p)).trans ?_
  rw [Finset.prod_eq_single j]
  · exact if_pos ⟨τ, hτ, hflag, rfl⟩
  · intro i hi hij
    refine if_neg ?_
    rintro ⟨σ, -, -, hσ⟩
    exact hne j hj i (Finset.mem_range.1 hi) (Ne.symm hij) (τ⁻¹ * σ)
      (by rw [mul_smul, hσ, inv_smul_smul])
  · exact fun hjn => absurd (Finset.mem_range.2 hj) hjn

include hTstable hchosen hne hstab in
/-- At a nontrivial conjugate of a chosen place not selected by the rule, the prescription is
trivial. -/
theorem evenPres_smul_chosen_of_not_flag {j : ℕ} (hj : j < n) {τ : Gal(K/k)}
    (hflag : ¬ EvenFlag L (d.count j n) τ) : evenPres L p T g d n (τ • d.chosen j) = 1 := by
  classical
  rw [evenPres, if_neg (smul_chosen_notMem hTstable hchosen hj τ)]
  refine (one_mul (_ : localClasses (τ • d.chosen j) p)).trans ?_
  refine Finset.prod_eq_one fun i hi => ?_
  refine if_neg ?_
  rintro ⟨σ, -, hσf, hσ⟩
  by_cases hij : i = j
  · subst hij
    refine hflag ?_
    have hst : τ⁻¹ * σ = 1 := (Subgroup.eq_bot_iff_forall _).1 (hstab i (Finset.mem_range.1 hi)) _
      (mem_stabilizer_iff.2 (by rw [mul_smul, hσ, inv_smul_smul]))
    rwa [inv_mul_eq_one.1 hst]
  · exact hne j hj i (Finset.mem_range.1 hi) (Ne.symm hij) (τ⁻¹ * σ)
      (by rw [mul_smul, hσ, inv_smul_smul])

end Conj

/-! ### The recursion -/

section Step

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}
  {hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v)}
  {ζ : K} {hζ : IsPrimitiveRoot ζ p} {L : Set Gal(K/k)}
  {Spl : HeightOneSpectrum (𝓞 K) → Prop} {T S₀ : Finset (HeightOneSpectrum (𝓞 K))} {g : Kˣ}

open scoped Classical in
/-- **One step of the recursion.**  Given the invariants at a stage, a further place and a further
unit produce the invariants at the next stage. -/
theorem exists_evenRecInv_succ
    (hSpl : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), Spl v → Spl (σ • v))
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hgunr : ∀ v ∈ T, localClassHom v p g ∈ localUnramified v p)
    (hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S → σ • v ∈ S) →
      ∀ c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v : HeightOneSpectrum (𝓞 K), c v ∈ localUnramified v p) →
        (∀ v ∈ T, c v = localClassHom v p g) →
        (∀ v ∈ S, v ∉ T → Spl v) →
        ∃ Q : HeightOneSpectrum (𝓞 K), Q ∉ S ∧ Spl Q ∧ stabilizer Gal(K/k) Q = ⊥ ∧
          ∃ w : Kˣ, (∀ v ∈ S, localClassHom v p w = c v) ∧
            (∀ y : InfinitePlace K, infClassHom y p w = 1) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → (p : ℤ) ∣ placeValue v w) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ → v ≠ Q → placeValue v w = 0) ∧
            ¬ (p : ℤ) ∣ placeValue Q w)
    (n : ℕ) (d : EvenRecData K ((Gal(K/k) → Multiplicative QModZ) × ZMod p))
    (hd : EvenRecInv k hres hζ L Spl T S₀ g n d) :
    ∃ d' : EvenRecData K ((Gal(K/k) → Multiplicative QModZ) × ZMod p),
      EvenRecInv k hres hζ L Spl T S₀ g (n + 1) d' := by
  have hchosenT : ∀ i < n, d.chosen i ∉ T := fun i hi hmem => hd.chosenNotMem i hi (hd.fixed hmem)
  obtain ⟨Q, hQS, hQSpl, hQstab, w, hwS, hwinf, hwunr, hwzero, hwram⟩ :=
    hstep d.places hd.subset hd.stable (evenPres L p T g d n)
      (evenPres_mem_localUnramified hgunr hd.chosenStab hd.unitUnram)
      (evenPres_of_mem hTstable hchosenT) hd.split
  have hconj : ∀ σ : Gal(K/k), σ • Q ∉ d.places := by
    intro σ hmem
    refine hQS ?_
    have h := hd.stable σ⁻¹ _ hmem
    rwa [inv_smul_smul] at h
  have hrange : (Set.range fun σ : Gal(K/k) => σ • Q).Finite := Set.finite_range _
  obtain ⟨S', hS'⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ S' ↔ v ∈ d.places ∨ ∃ σ : Gal(K/k), σ • Q = v := by
    refine ⟨d.places ∪ hrange.toFinset, fun v => ?_⟩
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_range]
  obtain ⟨Pl', hPl'ne, hPl'n⟩ : ∃ Pl' : ℕ → HeightOneSpectrum (𝓞 K),
      (∀ i, i ≠ n → Pl' i = d.chosen i) ∧ Pl' n = Q :=
    ⟨fun i => if i = n then Q else d.chosen i, fun _ hi => if_neg hi, if_pos rfl⟩
  obtain ⟨z', hz'ne, hz'n⟩ : ∃ z' : ℕ → Kˣ, (∀ i, i ≠ n → z' i = d.unit i) ∧ z' n = w :=
    ⟨fun i => if i = n then w else d.unit i, fun _ hi => if_neg hi, if_pos rfl⟩
  obtain ⟨cl', hcl'ne, hcl'n⟩ : ∃ cl' : ℕ → (Gal(K/k) → Multiplicative QModZ) × ZMod p,
      (∀ i, i ≠ n → cl' i = d.cls i) ∧ cl' n =
        ((fun σ : Gal(K/k) => placeFrobValue hres hζ (σ • Q) w),
          ((placeValue Q w : ℤ) : ZMod p)) :=
    ⟨fun i => if i = n then ((fun σ : Gal(K/k) => placeFrobValue hres hζ (σ • Q) w),
      ((placeValue Q w : ℤ) : ZMod p)) else d.cls i, fun _ hi => if_neg hi, if_pos rfl⟩
  refine ⟨⟨S', Pl', z', cl'⟩, hd.fixed, fun v hv => (hS' v).2 (Or.inl (hd.subset hv)), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    intro σ v hv
    rcases (hS' v).1 hv with h | ⟨τ, rfl⟩
    · exact (hS' _).2 (Or.inl (hd.stable σ v h))
    · exact (hS' _).2 (Or.inr ⟨σ * τ, mul_smul σ τ Q⟩)
  · dsimp only
    intro v hv hvT
    rcases (hS' v).1 hv with h | ⟨τ, rfl⟩
    · exact hd.split v h hvT
    · exact hSpl τ Q hQSpl
  · dsimp only
    intro i hi
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · rw [show Pl' i = Q from h ▸ hPl'n]
      exact (hS' _).2 (Or.inr ⟨1, one_smul _ _⟩)
    · rw [hPl'ne i h.ne]
      exact (hS' _).2 (Or.inl (hd.chosenMem i h))
  · dsimp only
    intro i hi
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · rw [show Pl' i = Q from h ▸ hPl'n]
      exact fun hmem => hQS (hd.subset hmem)
    · rw [hPl'ne i h.ne]
      exact hd.chosenNotMem i h
  · dsimp only
    intro i hi
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · rw [show Pl' i = Q from h ▸ hPl'n]
      exact hQstab
    · rw [hPl'ne i h.ne]
      exact hd.chosenStab i h
  · dsimp only
    intro i hi j hj hij σ
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · subst h
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hj) with h' | h'
      · exact absurd h'.symm hij
      · rw [hPl'n, hPl'ne j h'.ne]
        exact fun hQeq => hconj 1 (by
          rw [one_smul, hQeq]
          exact hd.stable σ _ (hd.chosenMem j h'))
    · rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hj) with h' | h'
      · subst h'
        rw [hPl'ne i h.ne, hPl'n]
        exact fun hQeq => hconj σ (hQeq ▸ hd.chosenMem i h)
      · rw [hPl'ne i h.ne, hPl'ne j h'.ne]
        exact hd.chosenNe i h j h' hij σ
  · dsimp only
    intro i hi v hv
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · subst h
      rw [hz'n]
      rw [hPl'n] at hv
      exact hwunr v hv
    · rw [hz'ne i h.ne]
      rw [hPl'ne i h.ne] at hv
      exact hd.unitUnram i h v hv
  · dsimp only
    intro i hi
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · subst h
      rw [hz'n, hPl'n]
      exact hwram
    · rw [hz'ne i h.ne, hPl'ne i h.ne]
      exact hd.unitRam i h
  · dsimp only
    intro i hi v hv hvne
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · subst h
      rw [hz'n]
      rw [hPl'n] at hvne
      exact hwzero v hv hvne
    · rw [hz'ne i h.ne]
      rw [hPl'ne i h.ne] at hvne
      exact hd.unitZero i h v hv hvne
  · dsimp only
    intro i hi y
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · subst h
      rw [hz'n]
      exact hwinf y
    · rw [hz'ne i h.ne]
      exact hd.unitInf i h y
  · dsimp only
    intro i hi v hv
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · subst h
      rw [hz'n, hwS v (hd.subset (hd.fixed hv))]
      exact evenPres_of_mem hTstable hchosenT v hv
    · rw [hz'ne i h.ne]
      exact hd.unitPres i h v hv
  · dsimp only
    intro i hi
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with h | h
    · subst h
      rw [hz'n, hPl'n]
      exact hcl'n
    · rw [hcl'ne i h.ne, hz'ne i h.ne, hPl'ne i h.ne]
      exact hd.clsSpec i h
  · show ∀ i < n + 1, ∀ j < n + 1, i < j → ∀ σ : Gal(K/k), σ ≠ 1 →
      (EvenFlag L ((EvenRecData.mk S' Pl' z' cl').count i j) σ →
        localClassHom (σ • Pl' i) p (z' j) = localClassHom (σ • Pl' i) p (z' i)) ∧
      (¬ EvenFlag L ((EvenRecData.mk S' Pl' z' cl').count i j) σ →
        localClassHom (σ • Pl' i) p (z' j) = 1)
    intro i hi j hj hij σ hσ
    have hcount : ∀ m, m ≤ n → i < m →
        (EvenRecData.mk S' Pl' z' cl').count i m = d.count i m := by
      intro m hm him
      exact EvenRecData.count_congr him fun l hl => hcl'ne l (by omega)
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hj) with h' | h'
    · subst h'
      have hin : i < j := hij
      rw [hcount j le_rfl hin, hPl'ne i hin.ne, hz'n, hz'ne i hin.ne,
        hwS _ (hd.stable σ _ (hd.chosenMem i hin))]
      refine ⟨fun hf => evenPres_smul_chosen_of_flag hTstable hchosenT hd.chosenNe hin hσ hf,
        fun hf => evenPres_smul_chosen_of_not_flag hTstable hchosenT hd.chosenNe hd.chosenStab
          hin hf⟩
    · have hin : i < n := lt_trans hij h'
      rw [hcount j (le_of_lt h') hij, hPl'ne i hin.ne, hz'ne j h'.ne, hz'ne i hin.ne]
      exact hd.unitConj i hin j h' hij σ hσ

/-- **The recursion runs for arbitrarily many steps.** -/
theorem exists_evenRecInv
    (hSpl : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), Spl v → Spl (σ • v))
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hTS : T ⊆ S₀)
    (hSstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S₀ → σ • v ∈ S₀)
    (hSsplit : ∀ v ∈ S₀, v ∉ T → Spl v)
    (hgunr : ∀ v ∈ T, localClassHom v p g ∈ localUnramified v p)
    (hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S → σ • v ∈ S) →
      ∀ c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v : HeightOneSpectrum (𝓞 K), c v ∈ localUnramified v p) →
        (∀ v ∈ T, c v = localClassHom v p g) →
        (∀ v ∈ S, v ∉ T → Spl v) →
        ∃ Q : HeightOneSpectrum (𝓞 K), Q ∉ S ∧ Spl Q ∧ stabilizer Gal(K/k) Q = ⊥ ∧
          ∃ w : Kˣ, (∀ v ∈ S, localClassHom v p w = c v) ∧
            (∀ y : InfinitePlace K, infClassHom y p w = 1) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → (p : ℤ) ∣ placeValue v w) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₀ → v ≠ Q → placeValue v w = 0) ∧
            ¬ (p : ℤ) ∣ placeValue Q w)
    (n : ℕ) : ∃ d : EvenRecData K ((Gal(K/k) → Multiplicative QModZ) × ZMod p),
      EvenRecInv k hres hζ L Spl T S₀ g n d := by
  classical
  induction n with
  | zero =>
    obtain ⟨c₀, hc₀T, hc₀not⟩ : ∃ c₀ : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p,
        (∀ v ∈ T, c₀ v = localClassHom v p g) ∧ ∀ v ∉ T, c₀ v = 1 :=
      ⟨fun v => if v ∈ T then localClassHom v p g else 1, fun _ hv => if_pos hv,
        fun _ hv => if_neg hv⟩
    have hc₀unr : ∀ v : HeightOneSpectrum (𝓞 K), c₀ v ∈ localUnramified v p := by
      intro v
      by_cases hvT : v ∈ T
      · rw [hc₀T v hvT]
        exact hgunr v hvT
      · rw [hc₀not v hvT]
        exact one_mem _
    obtain ⟨Q, -, -, -, -⟩ := hstep S₀ subset_rfl hSstable c₀ hc₀unr hc₀T hSsplit
    refine ⟨⟨S₀, fun _ => Q, fun _ => 1, fun _ => (1, 0)⟩, hTS, subset_rfl, hSstable, hSsplit,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals exact fun i hi => absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    obtain ⟨d, hd⟩ := ih
    exact exists_evenRecInv_succ hSpl hTstable hgunr hstep m d hd

end Step

end InverseGalois.CFT
