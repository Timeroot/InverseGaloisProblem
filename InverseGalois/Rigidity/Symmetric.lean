/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.Rigidity

/-!
# The symmetric groups are rigid

This file proves the classical first application of the rigidity method: for every `n ≥ 3` the
symmetric group `Sₙ` carries a **rigidity certificate**, built from the triple of conjugacy classes

* a transposition,
* an `(n-1)`-cycle,
* an `n`-cycle,

and therefore `Sₙ` is an inverse Galois group over `ℚ`.

Everything is proved by hand, uniformly in `n`; nothing is decided by computation.

The rigid triples are completely classified.  Writing `ρ` for the inverse of the last entry — an
`n`-cycle, so a cycle moving every letter — the product-one relation forces the middle entry to be
`s · ρ` with `s` the first entry, a transposition.  Cutting a letter out of a full cycle is exactly
what produces an `(n-1)`-cycle: `s · ρ` has one fixed point `y`, and `s` must then be the
transposition `(y, ρ y)`.  So the triples are precisely the

```
stdTriple ρ y = ((y, ρ y), (y, ρ y) · ρ, ρ⁻¹)
```

for a full cycle `ρ` and a letter `y`.  Any two of these are simultaneously conjugate — conjugate
the two full cycles, then move the marked letter by a power of the target cycle, which centralizes
it — so the triples form a single orbit and the structure constant is `1`
(`Rigidity.rigid_card_iff_single_orbit` turns that into the certificate's counting field).  The
remaining certificate fields are the triviality of the center of `Sₙ` for `n ≥ 3` and the
rationality of the three classes, which holds because a coprime power of a cycle is a cycle with
the same support.

## Main definitions

* `Rigidity.IsFullCycle` — a cycle moving every letter, i.e. an `n`-cycle on `n` letters.
* `Rigidity.stdTriple` — the standard rigid triple attached to a full cycle and a letter.
* `Rigidity.permCert`, `Rigidity.snCert` — the rigidity certificate of a symmetric group.

## Main results

* `Rigidity.center_perm_eq_bot` — a symmetric group on at least three letters is centerless.
* `Rigidity.cycleType_pow_coprime` — a coprime power of a permutation has the same cycle type.
* `Rigidity.isRationalClass_mk`, `Rigidity.isRationalClass_perm` — every conjugacy class of a
  symmetric group is rational, i.e. a symmetric group is a rational group.
* `Rigidity.exists_eq_stdTriple` — classification of the rigid triples.
* `Rigidity.single_orbit`, `Rigidity.card_rigidTuples` — the structure constant is `1`.
* `Rigidity.sn_isInverseGalois` — `Sₙ` is an inverse Galois group over `ℚ` for every `n ≥ 3`.
-/

open Equiv Equiv.Perm Finset

namespace Rigidity

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
/-- The center of a symmetric group on at least three letters is trivial. -/
theorem center_perm_eq_bot (h3 : 3 ≤ Fintype.card α) :
    Subgroup.center (Perm α) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a : α, g a ≠ a := by
    by_contra hall
    push_neg at hall
    exact hne (Equiv.ext hall)
  obtain ⟨c, hc⟩ : ∃ c : α, c ∉ ({a, g a} : Finset α) := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset α) ⊆ {a, g a} := fun x _ => hall x
    have h1 := Finset.card_le_card hsub
    simp only [Finset.card_univ] at h1
    have h2 : ({a, g a} : Finset α).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have key := hg (Equiv.swap (g a) c)
  have h1 : (Equiv.swap (g a) c * g) a = c := by simp [Equiv.swap_apply_left]
  have h2 : (g * Equiv.swap (g a) c) a = g a := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hc.1)]
  rw [← key] at h2
  exact hc.2 (h1.symm.trans h2)

/-- **A coprime power has the same cycle type.**  Stated with a common multiple `n` of the order so
that the induction over disjoint cycles goes through: the hypothesis then descends unchanged to
each factor. -/
theorem cycleType_pow_of_dvd {k n : ℕ} (hk : Nat.Coprime k n) {g : Perm α}
    (hn : orderOf g ∣ n) : (g ^ k).cycleType = g.cycleType := by
  induction g using Equiv.Perm.cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ =>
      have hco : Nat.Coprime k (orderOf σ) := Nat.Coprime.coprime_dvd_right hn hk
      rw [(hσ.pow_iff.mpr hco).cycleType, hσ.cycleType, support_pow_coprime hco]
  | induction_disjoint σ τ hd hσ ih1 ih2 =>
      rw [hd.orderOf] at hn
      rw [hd.commute.mul_pow, (hd.pow_disjoint_pow k k).cycleType_mul, hd.cycleType_mul,
        ih1 ((Nat.dvd_lcm_left _ _).trans hn), ih2 ((Nat.dvd_lcm_right _ _).trans hn)]

/-- Raising a permutation to a power coprime to its order does not change its cycle type: each
cycle of length `ℓ` is sent to a cycle of the same length, because `k` is coprime to `ℓ` too. -/
theorem cycleType_pow_coprime {g : Perm α} {k : ℕ} (hk : Nat.Coprime k (orderOf g)) :
    (g ^ k).cycleType = g.cycleType :=
  cycleType_pow_of_dvd hk dvd_rfl

/-- **Every conjugacy class of a symmetric group is rational**, i.e. a symmetric group is a
*rational group*: conjugacy is measured by the cycle type, which a coprime power preserves. -/
theorem isRationalClass_mk (g : Perm α) : IsRationalClass (ConjClasses.mk g) := by
  intro h hh k hk
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hh ⊢
  exact isConj_iff_cycleType_eq.mpr
    ((cycleType_pow_coprime hk).trans (isConj_iff_cycleType_eq.mp hh))

/-- The rationality of every class of a symmetric group, stated for the class itself. -/
theorem isRationalClass_perm (c : ConjClasses (Perm α)) : IsRationalClass c :=
  ConjClasses.mk_surjective.forall.mpr isRationalClass_mk c

/-- A **full cycle** on `α`: a cycle moving every letter, i.e. an `n`-cycle on `n` letters. -/
structure IsFullCycle (ρ : Perm α) : Prop where
  /-- it is a cycle -/
  isCycle : ρ.IsCycle
  /-- it moves every letter -/
  support_eq : ρ.support = Finset.univ

namespace IsFullCycle

theorem apply_ne {ρ : Perm α} (hρ : IsFullCycle ρ) (x : α) : ρ x ≠ x := by
  have : x ∈ ρ.support := by rw [hρ.support_eq]; exact Finset.mem_univ x
  exact Equiv.Perm.mem_support.mp this

theorem cycleType {ρ : Perm α} (hρ : IsFullCycle ρ) :
    ρ.cycleType = {Fintype.card α} := by
  rw [hρ.isCycle.cycleType, hρ.support_eq, Finset.card_univ]

theorem inv {ρ : Perm α} (hρ : IsFullCycle ρ) : IsFullCycle ρ⁻¹ :=
  ⟨hρ.isCycle.inv, by rw [Equiv.Perm.support_inv]; exact hρ.support_eq⟩

/-- On at least three letters a full cycle has no orbit of length two. -/
theorem apply_apply_ne {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (x : α) :
    ρ (ρ x) ≠ x := by
  intro h
  have hne : x ≠ ρ x := (hρ.apply_ne x).symm
  have hswap : ρ = Equiv.swap x (ρ x) :=
    hρ.isCycle.eq_swap_of_apply_apply_eq_self (hρ.apply_ne x) h
  have hsupp : (Equiv.swap x (ρ x)).support = Finset.univ := hswap ▸ hρ.support_eq
  rw [Equiv.Perm.support_swap hne] at hsupp
  have h2 := congrArg Finset.card hsupp
  rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton,
    Finset.card_univ] at h2
  omega

end IsFullCycle

/-- The **standard rigid triple** attached to a full cycle `ρ` and a letter `y`: the transposition
`(y, ρ y)`, the `(n-1)`-cycle obtained by cutting `y` out of `ρ`, and the inverse cycle. -/
def stdTriple (ρ : Perm α) (y : α) : Fin 3 → Perm α :=
  ![Equiv.swap y (ρ y), Equiv.swap y (ρ y) * ρ, ρ⁻¹]

/-- The three conjugacy classes of the standard rigid triple: a transposition, an `(n-1)`-cycle and
an `n`-cycle. -/
def rigidClasses (ρ : Perm α) (y : α) : Fin 3 → ConjClasses (Perm α) :=
  fun i => ConjClasses.mk (stdTriple ρ y i)

/-- The middle entry of the standard triple is a cycle: cutting one letter out of a full cycle
leaves a cycle. -/
theorem isCycle_cut {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (y : α) :
    (Equiv.swap y (ρ y) * ρ).IsCycle :=
  hρ.isCycle.swap_mul (hρ.apply_ne y) (hρ.apply_apply_ne h3 y)

theorem support_cut {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (y : α) :
    (Equiv.swap y (ρ y) * ρ).support = Finset.univ \ {y} := by
  rw [Equiv.Perm.support_swap_mul_eq _ _ (hρ.apply_apply_ne h3 y), hρ.support_eq]

theorem cycleType_cut {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (y : α) :
    (Equiv.swap y (ρ y) * ρ).cycleType = {Fintype.card α - 1} := by
  rw [(isCycle_cut hρ h3 y).cycleType, support_cut hρ h3 y, Finset.card_sdiff_of_subset (by simp),
    Finset.card_singleton, Finset.card_univ]

omit [Fintype α] in
/-- A transposition sending `u` to a different letter `v` is the transposition of `u` and `v`. -/
theorem eq_swap_of_isSwap {s : Perm α} (hs : s.IsSwap) {u v : α} (huv : u ≠ v) (h : s u = v) :
    s = Equiv.swap u v := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  by_cases hua : u = a
  · subst hua
    rw [Equiv.swap_apply_left] at h
    rw [← h]
  · by_cases hub : u = b
    · subst hub
      rw [Equiv.swap_apply_right] at h
      rw [← h, Equiv.swap_comm]
    · rw [Equiv.swap_apply_of_ne_of_ne hua hub] at h
      exact absurd h huv

/-! ### The rigid triple -/

omit [Fintype α] in
theorem prod_stdTriple (ρ : Perm α) (y : α) : (List.ofFn (stdTriple ρ y)).prod = 1 := by
  show Equiv.swap y (ρ y) * (Equiv.swap y (ρ y) * ρ * (ρ⁻¹ * 1)) = 1
  group
  exact Equiv.swap_mul_self _ _

theorem gen_stdTriple {ρ : Perm α} (hρ : IsFullCycle ρ) (y : α) :
    Subgroup.closure (Set.range (stdTriple ρ y)) = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_cycle_adjacent_swap hρ.isCycle hρ.support_eq y,
    Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz
  · have hmem : ρ⁻¹ ∈ Subgroup.closure (Set.range (stdTriple ρ y)) :=
      Subgroup.subset_closure ⟨2, rfl⟩
    rw [hz]
    simpa using inv_mem hmem
  · rw [hz]
    exact Subgroup.subset_closure ⟨0, rfl⟩

theorem stdTriple_mem_rigidTuples {ρ : Perm α} (hρ : IsFullCycle ρ) (y : α) :
    stdTriple ρ y ∈ rigidTuples (rigidClasses ρ y) :=
  ⟨fun _ => rfl, prod_stdTriple ρ y, gen_stdTriple hρ y⟩

omit [Fintype α] in
theorem conj_stdTriple (c ρ : Perm α) (y : α) (i : Fin 3) :
    c * stdTriple ρ y i * c⁻¹ = stdTriple (c * ρ * c⁻¹) (c y) i := by
  have happ : (c * ρ * c⁻¹) (c y) = c (ρ y) := by simp
  fin_cases i
  · show c * Equiv.swap y (ρ y) * c⁻¹ = Equiv.swap (c y) ((c * ρ * c⁻¹) (c y))
    rw [happ, ← Equiv.swap_apply_apply]
  · show c * (Equiv.swap y (ρ y) * ρ) * c⁻¹
        = Equiv.swap (c y) ((c * ρ * c⁻¹) (c y)) * (c * ρ * c⁻¹)
    rw [happ, Equiv.swap_apply_apply]
    group
  · show c * ρ⁻¹ * c⁻¹ = (c * ρ * c⁻¹)⁻¹
    group

/-- **Classification of the rigid triples.**  Every generating product-one triple in the three
prescribed classes is the standard triple of some full cycle and some letter: the last entry is the
inverse of a full cycle `ρ'`, the middle entry fixes a unique letter `y'`, and the transposition is
forced to be `(y', ρ' y')`. -/
theorem exists_eq_stdTriple {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (y : α)
    {g : Fin 3 → Perm α} (hg : g ∈ rigidTuples (rigidClasses ρ y)) :
    ∃ (ρ' : Perm α) (y' : α), IsFullCycle ρ' ∧ g = stdTriple ρ' y' := by
  obtain ⟨hclass, hprod, -⟩ := hg
  have hct : ∀ i, (g i).cycleType = (stdTriple ρ y i).cycleType := fun i =>
    isConj_iff_cycleType_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hclass i))
  -- the last entry is a full cycle
  have hct2 : (g 2).cycleType = {Fintype.card α} := by
    rw [hct 2]; show (ρ⁻¹).cycleType = _; exact hρ.inv.cycleType
  have hcyc2 : (g 2).IsCycle := by
    rw [← card_cycleType_eq_one, hct2, Multiset.card_singleton]
  have hsupp2 : (g 2).support = Finset.univ := by
    have hs : #(g 2).support = Fintype.card α :=
      Multiset.singleton_inj.mp (hcyc2.cycleType.symm.trans hct2)
    exact Finset.eq_univ_of_card _ hs
  set ρ' : Perm α := (g 2)⁻¹ with hρ'def
  have hρ' : IsFullCycle ρ' := (IsFullCycle.mk hcyc2 hsupp2).inv
  -- the first entry is a transposition
  have hswap0 : (g 0).IsSwap := by
    refine isSwap_iff_cycleType.mpr ?_
    rw [hct 0]
    show (Equiv.swap y (ρ y)).cycleType = {2}
    exact isSwap_iff_cycleType.mp ⟨y, ρ y, (hρ.apply_ne y).symm, rfl⟩
  -- the middle entry fixes a letter
  have hct1 : (g 1).cycleType = {Fintype.card α - 1} := by
    rw [hct 1]; show (Equiv.swap y (ρ y) * ρ).cycleType = _; exact cycleType_cut hρ h3 y
  have hcyc1 : (g 1).IsCycle := by
    rw [← card_cycleType_eq_one, hct1, Multiset.card_singleton]
  have hcard1 : #(g 1).support = Fintype.card α - 1 :=
    Multiset.singleton_inj.mp (hcyc1.cycleType.symm.trans hct1)
  obtain ⟨y', hy'⟩ : ∃ y' : α, g 1 y' = y' := by
    by_contra hall
    push_neg at hall
    have huniv : (g 1).support = Finset.univ :=
      Finset.eq_univ_of_forall fun x => Equiv.Perm.mem_support.mpr (hall x)
    rw [huniv, Finset.card_univ] at hcard1
    omega
  -- the product relation determines the middle entry
  have hprod' : g 0 * (g 1 * (g 2 * 1)) = 1 := hprod
  have hg1 : g 1 = (g 0)⁻¹ * ρ' := by
    have h := hprod'
    rw [mul_one] at h
    have h2 := congrArg (fun z => (g 0)⁻¹ * z * (g 2)⁻¹) h
    simpa [mul_assoc] using h2
  have hg0inv : (g 0)⁻¹ = g 0 := by
    obtain ⟨a, b, -, hab⟩ := hswap0
    rw [hab, Equiv.swap_inv]
  rw [hg0inv] at hg1
  have hfix : g 0 (ρ' y') = y' := by
    have h := hy'
    rw [hg1] at h
    simpa using h
  have hg0 : g 0 = Equiv.swap y' (ρ' y') :=
    (eq_swap_of_isSwap hswap0 (hρ'.apply_ne y') hfix).trans (Equiv.swap_comm _ _)
  refine ⟨ρ', y', hρ', funext fun i => ?_⟩
  fin_cases i
  · exact hg0
  · show g 1 = Equiv.swap y' (ρ' y') * ρ'
    rw [hg1, hg0]
  · show g 2 = ρ'⁻¹
    rw [hρ'def, inv_inv]

/-- Two full cycles are conjugate by a permutation carrying any prescribed letter to any other:
conjugate the cycles first, then adjust by a power of the target cycle. -/
theorem exists_conj_of_isFullCycle {ρ₁ ρ₂ : Perm α} (h1 : IsFullCycle ρ₁) (h2 : IsFullCycle ρ₂)
    (y₁ y₂ : α) : ∃ c : Perm α, c * ρ₁ * c⁻¹ = ρ₂ ∧ c y₁ = y₂ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp
    ((isConj_iff_cycleType_eq (σ := ρ₁) (τ := ρ₂)).mpr
      (h1.cycleType.trans h2.cycleType.symm))
  obtain ⟨j, hj⟩ := h2.isCycle.exists_pow_eq (h2.apply_ne (c y₁)) (h2.apply_ne y₂)
  refine ⟨ρ₂ ^ j * c, ?_, ?_⟩
  · have hrw : ρ₂ ^ j * c * ρ₁ * (ρ₂ ^ j * c)⁻¹ = ρ₂ ^ j * (c * ρ₁ * c⁻¹) * (ρ₂ ^ j)⁻¹ := by group
    rw [hrw, hc]; group
  · simpa using hj

/-- **The rigid triples form a single simultaneous-conjugacy orbit.** -/
theorem single_orbit {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (y : α) :
    ∀ g₁ ∈ rigidTuples (rigidClasses ρ y), ∀ g₂ ∈ rigidTuples (rigidClasses ρ y),
      ∃ x : ConjAct (Perm α), x • g₁ = g₂ := by
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨ρ₁, y₁, hρ₁, rfl⟩ := exists_eq_stdTriple hρ h3 y hg₁
  obtain ⟨ρ₂, y₂, hρ₂, rfl⟩ := exists_eq_stdTriple hρ h3 y hg₂
  obtain ⟨c, hcρ, hcy⟩ := exists_conj_of_isFullCycle hρ₁ hρ₂ y₁ y₂
  refine ⟨ConjAct.toConjAct c, funext fun i => ?_⟩
  rw [Pi.smul_apply, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, conj_stdTriple, hcρ, hcy]

/-- **The structure constant is one**: there are exactly `|Sₙ|` generating product-one triples in
the three prescribed classes. -/
theorem card_rigidTuples {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (y : α) :
    Nat.card (rigidTuples (rigidClasses ρ y)) = Nat.card (Perm α) :=
  (rigid_card_iff_single_orbit (center_perm_eq_bot h3)
    ⟨_, stdTriple_mem_rigidTuples hρ y⟩).mpr (single_orbit hρ h3 y)

/-! ### The certificate -/

/-- **The rigidity certificate of a symmetric group on at least three letters**: the classical
rigid triple consisting of a transposition, an `(n-1)`-cycle and an `n`-cycle. -/
def permCert {ρ : Perm α} (hρ : IsFullCycle ρ) (h3 : 3 ≤ Fintype.card α) (y : α) :
    RigidityCertificate (Perm α) where
  r := 3
  C := rigidClasses ρ y
  center_triv := fun g hg => by rwa [center_perm_eq_bot h3, Subgroup.mem_bot] at hg
  rational := fun i => isRationalClass_perm _
  gen := ⟨_, stdTriple_mem_rigidTuples hρ y⟩
  rigid := card_rigidTuples hρ h3 y

/-- The rotation of `Fin n` is a full cycle. -/
theorem isFullCycle_finRotate {n : ℕ} (h : 2 ≤ n) : IsFullCycle (finRotate n) :=
  ⟨isCycle_finRotate_of_le h, support_finRotate_of_le h⟩

/-- **The rigidity certificate of `Sₙ` for every `n ≥ 3`.** -/
def snCert (n : ℕ) (h3 : 3 ≤ n) : RigidityCertificate (Perm (Fin n)) :=
  permCert (isFullCycle_finRotate (by omega)) (by simpa using h3) ⟨0, by omega⟩

/-- **The symmetric group on `n ≥ 3` letters is an inverse Galois group over `ℚ`**, by the rigidity
criterion applied to the certificate `snCert`. -/
theorem sn_isInverseGalois (n : ℕ) (h3 : 3 ≤ n) : IsInverseGalois (Perm (Fin n)) :=
  rigidity_realizable (snCert n h3)

end Rigidity
