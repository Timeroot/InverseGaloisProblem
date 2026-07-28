/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Inertia generators of prescribed cycle type (rigidity-ready)

This module generalizes the *local-monodromy* / inertia machinery underlying the `Sₙ` Morse
computation (`Mathlib.RingTheory.Polynomial.Morse`,
`Polynomial.Splits.toPermHom_apply_eq_one_or_isSwap_of_ncard_le_of_mem_inertia`, and its use in
`InverseGalois.Hilbert.Analytic.MorseSwap.swap_input_final`) so that it can read off cycle types
*other than transpositions* from ramification/collision data.  It is designed to be **family
agnostic** — the reusable core needed by the rigidity method, which computes geometric monodromy
from local inertia generators around branch points.

## The picture

Let `G` act on a domain `S` (a `MulSemiringAction`), let `f : R[X]` split in `S`, and let
`p : Ideal S` be a prime lying over a branch point.  An element `g` of the **inertia subgroup**
`p.inertia G` fixes every element of `S` modulo `p` (`AddSubgroup.mem_inertia`), so the induced
permutation `MulAction.toPermHom G (f.rootSet S) g` of the roots **preserves the reduction map**
`x ↦ x mod p`.  Consequently:

* its support is contained in the *collision locus* — the set of roots that share their reduction
  with some other root (`support_toPermHom_inertia_subset`); and
* its cycle type is constrained by the size of that locus.

The Morse lemma is the case where every collision has size `2` (ramification index `≤ 2`), forcing a
transposition.  Here:

* `support_toPermHom_inertia_subset` is the general combinatorial core (any ramification index): the
  inertia permutation lives on the collision locus and pointwise fixes everything else.
* `isThreeCycle_of_mem_alternating_of_ncard_le_three` is the `Aₙ` analogue of the Morse swap lemma:
  a **nontrivial even** inertia generator sitting over a branch point with a single collision of
  `≤ 3` sheets is a **3-cycle**.  "Even" is exactly the square-discriminant hypothesis that puts the
  whole monodromy inside `Aₙ`; it is what upgrades "`1` or swap or 3-cycle" to "3-cycle".
* `isCycle_of_isCycleOn_of_ne_one` packages the general *totally-ramified, tame* case: if the
  inertia generator acts as a single cycle on the collision locus (the analytic Puiseux/tameness
  input: a single place of ramification index `e` over the branch point), it is an `e`-cycle.

`isThreeCycle_of_mem_alternating_of_ncard_le_three` needs **no** tameness input — it trades the
analytic transitivity hypothesis for the cheap group-theoretic parity constraint, which is why it is
the cleanest formalizable route to a 3-cycle whenever a branch point has a collision of exactly
three sheets.
-/

open Polynomial Equiv
open scoped Classical

namespace InertiaCycle

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] {f : R[X]}
  [DecidableEq (f.rootSet S)]

omit [DecidableEq (f.rootSet S)] in
/-- **Inertia preserves the reduction of the roots.**  If `g` lies in the inertia subgroup of a
prime `p`, then the permutation it induces on the roots of `f` in `S` sends every root to a root
with the *same* image modulo `p`.  This is the single algebraic fact powering every cycle-type
computation below; it holds for arbitrary ramification index.  (Generalizes the `hπ` step in the
Morse proof.) -/
theorem toPermHom_inertia_reduction_eq (p : Ideal S) {g : G} (hg : g ∈ p.inertia G)
    (x : f.rootSet S) :
    Ideal.Quotient.mk p ((MulAction.toPermHom G (f.rootSet S) g x : f.rootSet S) : S)
      = Ideal.Quotient.mk p (x : S) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    rootSet.coe_smul]
  exact hg (x : S)

/-- The **collision locus**: the set of roots of `f` in `S` that reduce, modulo `p`, to the same
element of `S ⧸ p` as some *other* root.  Roots outside this set have a distinct reduction, hence are
fixed by every inertia generator.  Its cardinality is `∑ (ramification data)` over the primes above
the branch point; a single collision of size `e` corresponds to a locus of size `e`. -/
def collisionLocus (p : Ideal S) : Set (f.rootSet S) :=
  {x | ∃ y : f.rootSet S, y ≠ x ∧ Ideal.Quotient.mk p (y : S) = Ideal.Quotient.mk p (x : S)}

omit [DecidableEq (f.rootSet S)] in
@[simp] theorem mem_collisionLocus {p : Ideal S} {x : f.rootSet S} :
    x ∈ collisionLocus (f := f) p ↔
      ∃ y : f.rootSet S, y ≠ x ∧ Ideal.Quotient.mk p (y : S) = Ideal.Quotient.mk p (x : S) :=
  Iff.rfl

/-- **The inertia permutation is supported on the collision locus** (arbitrary ramification index).
Every root moved by an inertia generator collides, modulo `p`, with its (distinct) image.  This is
the exact generalization of the Morse "`1` or swap" dichotomy: there the locus has size `≤ 2`, here
it may have any size.  Combined with a bound on the locus it pins down the cycle type. -/
theorem support_toPermHom_inertia_subset (p : Ideal S) {g : G} (hg : g ∈ p.inertia G) :
    ((MulAction.toPermHom G (f.rootSet S) g).support : Set (f.rootSet S))
      ⊆ collisionLocus (f := f) p := by
  intro x hx
  rw [Finset.mem_coe, Equiv.Perm.mem_support] at hx
  exact ⟨MulAction.toPermHom G (f.rootSet S) g x, hx, toPermHom_inertia_reduction_eq p hg x⟩

/-- Cardinality bound: the support of an inertia generator has at most `#(collision locus)`
elements. -/
theorem card_support_toPermHom_inertia_le (p : Ideal S) {g : G} (hg : g ∈ p.inertia G)
    {k : ℕ} (hk : (collisionLocus (f := f) p).ncard ≤ k) :
    (MulAction.toPermHom G (f.rootSet S) g).support.card ≤ k := by
  have hfin : (collisionLocus (f := f) p).Finite := Set.toFinite _
  calc (MulAction.toPermHom G (f.rootSet S) g).support.card
      = ((MulAction.toPermHom G (f.rootSet S) g).support : Set (f.rootSet S)).ncard := by
        rw [Set.ncard_coe_finset]
    _ ≤ (collisionLocus (f := f) p).ncard :=
        Set.ncard_le_ncard (support_toPermHom_inertia_subset p hg) hfin
    _ ≤ k := hk

/-- **The `Aₙ` analogue of the Morse swap lemma.**  A **nontrivial, even** inertia generator lying
over a branch point whose collision locus has at most three sheets acts on the roots as a
**3-cycle**.

Structure of the proof (parallel to the Morse `1`-or-swap dichotomy, but using parity instead of a
size-`2` bound):
* the support is contained in the collision locus, so `#support ≤ 3`;
* nontriviality gives `#support ≥ 2`;
* evenness (membership in the alternating group, i.e. `sign = 1`) rules out `#support = 2`, since a
  permutation with two-element support is a transposition (`sign = -1`);
* hence `#support = 3`, which characterizes a 3-cycle.

"Even" is precisely the square-discriminant condition of the Serre/Mestre `Aₙ` construction. -/
theorem isThreeCycle_of_mem_alternating_of_ncard_le_three (p : Ideal S) {g : G}
    (hg : g ∈ p.inertia G) (hloc : (collisionLocus (f := f) p).ncard ≤ 3)
    (hne : MulAction.toPermHom G (f.rootSet S) g ≠ 1)
    (heven : MulAction.toPermHom G (f.rootSet S) g ∈ alternatingGroup (f.rootSet S)) :
    (MulAction.toPermHom G (f.rootSet S) g).IsThreeCycle := by
  set σ := MulAction.toPermHom G (f.rootSet S) g with hσ
  have hle3 : σ.support.card ≤ 3 := card_support_toPermHom_inertia_le p hg hloc
  have hge2 : 2 ≤ σ.support.card := Equiv.Perm.two_le_card_support_of_ne_one hne
  have hsign : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.mp heven
  have hne2 : σ.support.card ≠ 2 := by
    intro h2
    have hswap : σ.IsSwap := Equiv.Perm.card_support_eq_two.mp h2
    rw [hswap.sign_eq] at hsign
    exact absurd hsign (by decide)
  have h3 : σ.support.card = 3 := by omega
  exact card_support_eq_three_iff.mp h3

/-- **General totally-ramified tame case: an `e`-cycle on the ramified sheets.**  If an inertia
generator acts as a *single cycle* on the collision locus — the analytic content of a **single place
of ramification index `e`** over the branch point (tame Puiseux data) — then it is a genuine cycle
whose length equals the size of the collision locus.

This is the honest general "index `e` ⟹ `e`-cycle" statement: the transitivity hypothesis
`IsCycleOn` is exactly the ramification-theoretic input the rigidity method must supply (a single
totally-ramified prime, tame residue), and everything else is packaged here.  Combined with
`support_toPermHom_inertia_subset`, `Equiv.Perm.IsCycle.card_support`-style facts read off the
length. -/
theorem isCycle_of_isCycleOn_of_ne_one (p : Ideal S) {g : G} (hg : g ∈ p.inertia G)
    (hcyc : (MulAction.toPermHom G (f.rootSet S) g).IsCycleOn (collisionLocus (f := f) p))
    (hne : MulAction.toPermHom G (f.rootSet S) g ≠ 1) :
    (MulAction.toPermHom G (f.rootSet S) g).IsCycle := by
  set σ := MulAction.toPermHom G (f.rootSet S) g with hσ
  have hsub : (σ.support : Set (f.rootSet S)) ⊆ collisionLocus (f := f) p :=
    support_toPermHom_inertia_subset p hg
  obtain ⟨x, hx⟩ : σ.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hne (Equiv.Perm.support_eq_empty_iff.mp h))
  refine ⟨x, Equiv.Perm.mem_support.mp hx, fun y hy => ?_⟩
  have hxloc : x ∈ collisionLocus (f := f) p := hsub (Finset.mem_coe.mpr hx)
  have hyloc : y ∈ collisionLocus (f := f) p :=
    hsub (Finset.mem_coe.mpr (Equiv.Perm.mem_support.mpr hy))
  exact hcyc.2 hxloc hyloc

/-- **Reading off the cycle length in the totally-ramified tame case.**  Combining
`isCycle_of_isCycleOn_of_ne_one` with the collision-locus support bound: a nontrivial inertia
generator that is a single cycle on a collision locus of size `e` is an `e`-cycle
(`#support = e`).  This is the general "index `e` ⟹ `e`-cycle on the ramified sheets" conclusion,
with the tameness/single-place hypothesis supplied as `IsCycleOn`. -/
theorem card_support_eq_of_isCycleOn (p : Ideal S) {g : G} (hg : g ∈ p.inertia G)
    (hcyc : (MulAction.toPermHom G (f.rootSet S) g).IsCycleOn (collisionLocus (f := f) p))
    (hne : MulAction.toPermHom G (f.rootSet S) g ≠ 1)
    {e : ℕ} (he : (collisionLocus (f := f) p).ncard = e) :
    (MulAction.toPermHom G (f.rootSet S) g).support.card = e := by
  set σ := MulAction.toPermHom G (f.rootSet S) g with hσ
  have hsub : (σ.support : Set (f.rootSet S)) ⊆ collisionLocus (f := f) p :=
    support_toPermHom_inertia_subset p hg
  -- The locus is nontrivial: a moved root collides with a distinct partner, both in the locus.
  have hnt : (collisionLocus (f := f) p).Nontrivial := by
    obtain ⟨x, hx⟩ : σ.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (fun h => hne (Equiv.Perm.support_eq_empty_iff.mp h))
    have hxloc : x ∈ collisionLocus (f := f) p := hsub (Finset.mem_coe.mpr hx)
    obtain ⟨y, hyx, hmk⟩ := mem_collisionLocus.mp hxloc
    exact ⟨x, hxloc, y, mem_collisionLocus.mpr ⟨x, hyx.symm, hmk.symm⟩, hyx.symm⟩
  -- `IsCycleOn` (nontrivial) moves every point of the locus, so the locus is contained in the
  -- support; combined with `hsub` this makes support = locus.
  have hsupp : (σ.support : Set (f.rootSet S)) = collisionLocus (f := f) p :=
    Set.Subset.antisymm hsub (fun a ha =>
      Finset.mem_coe.mpr (Equiv.Perm.mem_support.mpr (hcyc.apply_ne hnt ha)))
  rw [← Set.ncard_coe_finset, hsupp, he]

end InertiaCycle
