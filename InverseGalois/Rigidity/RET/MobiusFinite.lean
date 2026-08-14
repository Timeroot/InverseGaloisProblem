/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.AnharmonicS3
import InverseGalois.Rigidity.RET.MobiusDihedral
import InverseGalois.Rigidity.RET.RegularCubic
import InverseGalois.Rigidity.RET.RegularQuadratic

/-!
# The finite groups of fractional linear substitutions over the rationals

A finite group of fractional linear substitutions of `ℚ(u)` acts faithfully on `ℚ(u)` fixing the
constants, so Artin's theorem and Lüroth's theorem make it a regular inverse Galois group.  This
file collects the groups that arise, which up to isomorphism are the cyclic groups of order `1`,
`2`, `3`, `4` and `6` and the dihedral groups of order `2`, `4`, `6`, `8` and `12` — the finite
subgroups of the projective linear group over the rationals.

The dihedral ones come from a rotation together with an inverting involution.  The cyclic ones
come from the rotation alone: the powers of a single substitution of exact order `n` form a cyclic
group of order `n` inside the ring automorphisms of `ℚ(u)`, and any abstract cyclic group of that
order is isomorphic to it.  The rotations already exhibited therefore supply the cyclic groups too,
the substitutions `u ↦ -u`, `u ↦ (u - 1)/(u + 1)` and `u ↦ (2u - 1)/(u + 1)` having orders two,
four and six.

## Main results

* `Rigidity.RET.isRegularInverseGalois_of_isCyclic` — the cyclic criterion: a substitution whose
  exact order is the cardinality of a finite cyclic group realizes that group regularly.
* `Rigidity.RET.isRegularInverseGalois_of_isCyclic_card_mem` — every cyclic group whose order is
  one of `1`, `2`, `3`, `4`, `6` is a regular inverse Galois group.
* `Rigidity.RET.isRegularInverseGalois_dihedralGroup_mem` — every dihedral group of order
  `2`, `4`, `6`, `8` or `12` is a regular inverse Galois group.
* `Rigidity.RET.isRegularInverseGalois_of_isMobius` and
  `Rigidity.RET.isInverseGalois_of_isMobius` — the two lists together.
-/

noncomputable section

namespace Rigidity.RET

/-! ## The cyclic criterion -/

/-- The powers of a substitution of finite order form a finite group. -/
theorem finite_zpowers_of_isOfFinOrder {ρ : RingAut (RatFunc ℚ)} (hρ : IsOfFinOrder ρ) :
    Finite (Subgroup.zpowers ρ) :=
  Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact hρ.orderOf_pos.ne')

/-- **The powers of a substitution of finite order are a regular inverse Galois group**, being a
finite group of ring automorphisms of `ℚ(u)` and hence a faithful one. -/
theorem isRegularInverseGalois_zpowers {ρ : RingAut (RatFunc ℚ)} (hρ : IsOfFinOrder ρ) :
    IsRegularInverseGalois (Subgroup.zpowers ρ) :=
  haveI := finite_zpowers_of_isOfFinOrder hρ
  IsRegularInverseGalois.of_injective_ringAut _ (Subgroup.subtype _) Subtype.val_injective

/-- **A substitution of the right exact order realizes a cyclic group.**  Two cyclic groups of the
same cardinality are isomorphic, so the powers of `ρ` are a copy of `G`. -/
theorem isRegularInverseGalois_of_isCyclic {G : Type} [Group G] [Finite G] [IsCyclic G]
    {ρ : RingAut (RatFunc ℚ)} (hord : orderOf ρ = Nat.card G) : IsRegularInverseGalois G := by
  have hpos : 0 < orderOf ρ := by rw [hord]; exact Nat.card_pos
  refine (isRegularInverseGalois_zpowers (orderOf_pos_iff.mp hpos)).of_mulEquiv ?_
  exact mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, hord])

/-! ## The individual cyclic groups -/

/-- **A group of order one is a regular inverse Galois group**, realized by `ℚ(T)` over itself. -/
theorem isRegularInverseGalois_of_card_eq_one {G : Type} [Group G] (hG : Nat.card G = 1) :
    IsRegularInverseGalois G :=
  haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG).1
  IsRegularInverseGalois.of_subsingleton

/-- **A cyclic group of order four is a regular inverse Galois group**, realized by the powers of
`u ↦ (u - 1)/(u + 1)`. -/
theorem isRegularInverseGalois_of_isCyclic_card_eq_four {G : Type} [Group G] [IsCyclic G]
    (hG : Nat.card G = 4) : IsRegularInverseGalois G := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  exact isRegularInverseGalois_of_isCyclic (ρ := squareRot) (by rw [orderOf_squareRot, hG])

/-- **A cyclic group of order six is a regular inverse Galois group**, realized by the powers of
`u ↦ (2u - 1)/(u + 1)`. -/
theorem isRegularInverseGalois_of_isCyclic_card_eq_six {G : Type} [Group G] [IsCyclic G]
    (hG : Nat.card G = 6) : IsRegularInverseGalois G := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  exact isRegularInverseGalois_of_isCyclic (ρ := hexRot) (by rw [orderOf_hexRot, hG])

/-- **Every cyclic group whose order occurs among the substitutions of `ℚ(u)`** — that is, one of
`1`, `2`, `3`, `4`, `6` — **is a regular inverse Galois group.** -/
theorem isRegularInverseGalois_of_isCyclic_card_mem {G : Type} [Group G] [IsCyclic G]
    (hG : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 ∨ Nat.card G = 6) :
    IsRegularInverseGalois G := by
  rcases hG with h | h | h | h | h
  · exact isRegularInverseGalois_of_card_eq_one h
  · exact isRegularInverseGalois_of_card_eq_two h
  · exact isRegularInverseGalois_of_card_eq_three h
  · exact isRegularInverseGalois_of_isCyclic_card_eq_four h
  · exact isRegularInverseGalois_of_isCyclic_card_eq_six h

/-- A group whose cardinality is one of the five listed numbers is finite. -/
theorem finite_of_card_mem {G : Type} [Group G]
    (hG : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 ∨ Nat.card G = 6) :
    Finite G := by
  rcases hG with h | h | h | h | h <;>
    exact Nat.finite_of_card_ne_zero (by rw [h]; norm_num)

/-- **Every such cyclic group is a Galois group over the rationals.** -/
theorem isInverseGalois_of_isCyclic_card_mem {G : Type} [Group G] [IsCyclic G]
    (hG : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 ∨ Nat.card G = 6) :
    IsInverseGalois G :=
  haveI := finite_of_card_mem hG
  (isRegularInverseGalois_of_isCyclic_card_mem hG).isInverseGalois

/-! ## The dihedral list -/

/-- **Every dihedral group of order `2`, `4`, `6`, `8` or `12` is a regular inverse Galois
group.**  The first is cyclic of order two; the others come from a rotation of order `2`, `3`, `4`
or `6` together with the inverting involution `u ↦ 1/u`. -/
theorem isRegularInverseGalois_dihedralGroup_mem {n : ℕ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) : IsRegularInverseGalois (DihedralGroup n) := by
  rcases hn with h | h | h | h | h <;> subst h
  · exact isRegularInverseGalois_of_card_eq_two (by rw [DihedralGroup.nat_card])
  · exact isRegularInverseGalois_dihedralGroup_two
  · exact isRegularInverseGalois_dihedralGroup_three
  · exact isRegularInverseGalois_dihedralGroup_four
  · exact isRegularInverseGalois_dihedralGroup_six

/-- **Every such dihedral group is a Galois group over the rationals.** -/
theorem isInverseGalois_dihedralGroup_mem {n : ℕ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) : IsInverseGalois (DihedralGroup n) := by
  have hreg := isRegularInverseGalois_dihedralGroup_mem hn
  rcases hn with h | h | h | h | h <;> subst h <;> exact hreg.isInverseGalois

/-! ## The two lists together -/

/-- **Being one of the finite subgroups of the projective linear group over the rationals**: cyclic
of order `1`, `2`, `3`, `4` or `6`, or dihedral of order `2`, `4`, `6`, `8` or `12`. -/
def IsMobiusGroup (G : Type) [Group G] : Prop :=
  (IsCyclic G ∧
      (Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 ∨ Nat.card G = 6)) ∨
    ∃ n : ℕ, (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) ∧ Nonempty (G ≃* DihedralGroup n)

/-- **Every finite subgroup of the projective linear group over the rationals is a regular inverse
Galois group.**  Each one is a group of fractional linear substitutions of `ℚ(u)`, so Artin's
theorem and Lüroth's theorem realize it over a rational base with no new constants. -/
theorem isRegularInverseGalois_of_isMobius {G : Type} [Group G] (hG : IsMobiusGroup G) :
    IsRegularInverseGalois G := by
  rcases hG with ⟨hcyc, hcard⟩ | ⟨n, hn, ⟨e⟩⟩
  · haveI := hcyc
    exact isRegularInverseGalois_of_isCyclic_card_mem hcard
  · exact (isRegularInverseGalois_dihedralGroup_mem hn).of_mulEquiv e.symm

/-- Every group on the list is finite. -/
theorem finite_of_isMobius {G : Type} [Group G] (hG : IsMobiusGroup G) : Finite G := by
  rcases hG with ⟨_, hcard⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact finite_of_card_mem hcard
  · rcases hn with h | h | h | h | h <;> subst h <;> exact Finite.of_equiv _ e.toEquiv.symm

/-- **Every finite subgroup of the projective linear group over the rationals is a Galois group
over the rationals.** -/
theorem isInverseGalois_of_isMobius {G : Type} [Group G] (hG : IsMobiusGroup G) :
    IsInverseGalois G :=
  haveI := finite_of_isMobius hG
  (isRegularInverseGalois_of_isMobius hG).isInverseGalois

end Rigidity.RET
