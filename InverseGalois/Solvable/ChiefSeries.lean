/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic

/-!
# Elementary abelian layers of a finite solvable group

Shafarevich's theorem — every finite solvable group is a Galois group over `ℚ` — is proved by
peeling a solvable group apart one layer at a time, each layer being an elementary abelian
`p`-group, and solving the resulting embedding problems.  This file supplies the group theory
that organizes that induction, with no arithmetic input whatsoever.

The starting point is the classical fact that a *minimal* nontrivial normal subgroup `N` of a
finite solvable group `G` is elementary abelian.  Minimality is used twice.  First, the
commutator `⁅N, N⁆` is a normal subgroup of `G` that is strictly smaller than `N` because `N` is
solvable and nontrivial, so it must be trivial and `N` is abelian.  Second, for a prime `p`
dividing the order of `N`, the elements of `N` killed by `p` form a normal subgroup of `G` —
normality is immediate from `(g x g⁻¹) ^ p = g x ^ p g⁻¹` — and it is nontrivial by Cauchy's
theorem, so it is all of `N`.

Iterating this along the quotients `G ⧸ N` gives an induction principle for finite solvable
groups whose single inductive step adds an elementary abelian normal subgroup, and hence an
unconditional reduction of the inverse Galois problem for solvable groups to embedding problems
with elementary abelian kernel.

## Main results

* `exists_normal_elementaryAbelian`: a nontrivial finite solvable group has a nontrivial normal
  subgroup that is an elementary abelian `p`-group for some prime `p`.
* `induction_on_elementaryAbelian`: to prove a property of all finite solvable groups it suffices
  to prove it for the trivial group and to propagate it from `G ⧸ N` to `G` along an elementary
  abelian normal subgroup `N ≠ ⊥`.
* `isInverseGalois_of_isSolvable_of_embeddingProblems`: if every embedding problem with
  elementary abelian kernel can be solved, then every finite solvable group is a Galois group
  over `ℚ`.
-/

/-- The elements of a subgroup `N` that are killed by `p`, as a subgroup of the ambient group.
The hypothesis `hcomm` says that the elements of `N` commute with one another, which is what
makes this set closed under multiplication. -/
private def pTorsionOfComm {G : Type*} [Group G] (N : Subgroup G) (p : ℕ)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : Subgroup G where
  carrier := {g | g ∈ N ∧ g ^ p = 1}
  one_mem' := ⟨one_mem N, one_pow p⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by
      have hab : Commute a b := hcomm a ha.1 b hb.1
      rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

private lemma mem_pTorsionOfComm {G : Type*} [Group G] {N : Subgroup G} {p : ℕ}
    {hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a} {g : G} :
    g ∈ pTorsionOfComm N p hcomm ↔ g ∈ N ∧ g ^ p = 1 := Iff.rfl

/-- A nontrivial finite solvable group has a nontrivial **elementary abelian** normal subgroup:
a normal subgroup `N ≠ ⊥` together with a prime `p` such that every element of `N` satisfies
`x ^ p = 1` and any two elements of `N` commute.

Such an `N` is obtained as a minimal element of the (finite, nonempty) collection of nontrivial
normal subgroups of `G`. -/
theorem exists_normal_elementaryAbelian {G : Type*} [Group G] [Finite G] [IsSolvable G]
    (hG : Nontrivial G) :
    ∃ (N : Subgroup G) (_ : N.Normal), N ≠ ⊥ ∧
      ∃ p : ℕ, p.Prime ∧ (∀ x : N, x ^ p = 1) ∧ ∀ x y : N, x * y = y * x := by
  haveI := hG
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  -- A minimal element of the set of nontrivial normal subgroups of `G`.
  obtain ⟨N, ⟨hN, hNbot⟩, hNmin⟩ :=
    wellFounded_lt.has_min {H : Subgroup G | H.Normal ∧ H ≠ ⊥}
      ⟨⊤, inferInstance, Ne.symm bot_ne_top⟩
  haveI := hN
  -- Minimality, in the form in which it gets used.
  have key : ∀ K : Subgroup G, K.Normal → K ≤ N → K ≠ ⊥ → K = N := fun K hK hKN hKbot => by
    by_contra h
    exact hNmin K ⟨hK, hKbot⟩ (lt_of_le_of_ne hKN h)
  -- Step 1: `N` is abelian, because `⁅N, N⁆` is a normal subgroup strictly below `N`.
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    have hlt : ⁅N, N⁆ < N := IsSolvable.commutator_lt_of_ne_bot hNbot
    have hbot : ⁅N, N⁆ = ⊥ := by
      by_contra h
      exact hlt.ne (key _ (Subgroup.commutator_normal N N) hlt.le h)
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot ha) b hb).symm
  -- Step 2: a prime `p` dividing the order of `N`, and an element of `N` of order `p`.
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := N)).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpdvd
  -- Step 3: the `p`-torsion of `N` is a nontrivial normal subgroup of `G` inside `N`.
  set K : Subgroup G := pTorsionOfComm N p hcomm
  have hKle : K ≤ N := fun g hg => (mem_pTorsionOfComm.mp hg).1
  have hKnormal : K.Normal :=
    ⟨fun a ha g => mem_pTorsionOfComm.mpr
      ⟨hN.conj_mem a (mem_pTorsionOfComm.mp ha).1 g, by
        rw [conj_pow, (mem_pTorsionOfComm.mp ha).2, mul_one, mul_inv_cancel]⟩⟩
  have hxK : (x : G) ∈ K := mem_pTorsionOfComm.mpr ⟨x.2, by
    have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    simpa using congrArg (Subgroup.subtype N) hxp⟩
  have hKbot : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxK
    have hx1 : x = 1 := Subtype.ext hxK
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hKN : K = N := key K hKnormal hKle hKbot
  refine ⟨N, hN, hNbot, p, hp, fun y => ?_, fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩
  have hy : (y : G) ∈ K := by rw [hKN]; exact y.2
  exact Subtype.ext (by simpa using (mem_pTorsionOfComm.mp hy).2)

/-- Induction on a finite solvable group along its elementary abelian layers.

To prove a property `P` of all finite solvable groups it suffices to prove it for trivial groups
and to show that it passes from a quotient `G ⧸ N` to `G` whenever `N` is a nontrivial elementary
abelian normal subgroup of the finite solvable group `G`. -/
theorem induction_on_elementaryAbelian
    {P : ∀ (G : Type) [Group G] [Finite G], Prop}
    (htriv : ∀ (G : Type) [Group G] [Finite G], Subsingleton G → P G)
    (hstep : ∀ (G : Type) [Group G] [Finite G] [IsSolvable G] (N : Subgroup G) [N.Normal],
      N ≠ ⊥ → (∃ p : ℕ, p.Prime ∧ ∀ x : N, x ^ p = 1) → (∀ x y : N, x * y = y * x) →
      P (G ⧸ N) → P G)
    (G : Type) [Group G] [Finite G] [IsSolvable G] : P G := by
  suffices H : ∀ (n : ℕ) (G : Type) [Group G] [Finite G] [IsSolvable G], Nat.card G ≤ n → P G by
    exact H (Nat.card G) G le_rfl
  intro n
  induction n with
  | zero => exact fun G _ _ _ h => absurd h (not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard
    rcases subsingleton_or_nontrivial G with hs | hs
    · exact htriv G hs
    · obtain ⟨N, hN, hNbot, p, hp, hpow, hcomm⟩ := exists_normal_elementaryAbelian hs
      haveI := hN
      have hcardN : 1 < Nat.card N := by
        haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
        exact Finite.one_lt_card
      have hq : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      have hlt : Nat.card (G ⧸ N) < Nat.card G := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
        exact (Nat.lt_mul_iff_one_lt_right hq).mpr hcardN
      exact hstep G N hNbot ⟨p, hp, hpow⟩ hcomm (ih (G ⧸ N) (by omega))

/-- Shafarevich's theorem, modulo its arithmetic input.

If every embedding problem with elementary abelian kernel can be solved — that is, if for every
finite solvable group `G` with a nontrivial elementary abelian normal subgroup `N` the group `G`
is a Galois group over `ℚ` as soon as `G ⧸ N` is — then every finite solvable group is a Galois
group over `ℚ`. -/
theorem isInverseGalois_of_isSolvable_of_embeddingProblems
    (hstep : ∀ (G : Type) [Group G] [Finite G] [IsSolvable G] (N : Subgroup G) [N.Normal],
      N ≠ ⊥ → (∃ p : ℕ, p.Prime ∧ ∀ x : N, x ^ p = 1) → (∀ x y : N, x * y = y * x) →
      IsInverseGalois (G ⧸ N) → IsInverseGalois G)
    (G : Type) [Group G] [Finite G] [IsSolvable G] : IsInverseGalois G :=
  induction_on_elementaryAbelian (P := fun G _ _ => IsInverseGalois G)
    (fun G _ _ hs => by
      haveI := hs
      haveI : Unique G := uniqueOfSubsingleton 1
      exact IsInverseGalois.unit.of_mulEquiv MulEquiv.ofUnique)
    hstep G
