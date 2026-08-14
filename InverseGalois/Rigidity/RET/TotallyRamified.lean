/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeomFundamental
import InverseGalois.Rigidity.RET.InertiaGen
import InverseGalois.Rigidity.RET.Unramified

/-!
# The fibre of a cover is the coset space of an inertia group

The fundamental identity over an algebraically closed constant field says that the number of points
of a cover above a point of the line, times the order of the inertia group there, is the degree of
the cover.  Read as a statement about subgroups it says that the fibre has as many points as the
inertia group has cosets — the deck group is transitive on the fibre and the inertia group is the
stabilizer of a point of it.

Both extremes of that identity are meaningful.  A point above which the cover has a *single* point
is one where the inertia group is everything; since inertia at a geometric place is cyclic, a cover
with such a point has a cyclic deck group, and contrapositively a cover whose deck group is not
cyclic has at least two points above *every* point of the line.  At the other extreme a point above
which the cover has the full complement of `deg` points is exactly an unbranched one.

## Main results

* `Rigidity.RET.ncard_primesOver_eq_index` — the points of a cover above a point of the line are
  the cosets of an inertia group there.
* `Rigidity.RET.geomInertia_eq_top_iff` — the inertia group is the whole deck group exactly when
  the cover has a single point above the point of the line.
* `Rigidity.RET.isCyclic_deck_of_ncard_primesOver_eq_one` — a cover with a single point above some
  point of the line has a cyclic deck group.
* `Rigidity.RET.one_lt_ncard_primesOver_of_not_isCyclic` — a cover whose deck group is not cyclic
  has at least two points above every point of the line.
* `Rigidity.RET.ncard_primesOver_eq_card_deck_iff_isUnramifiedAt` — the cover has as many points
  above a point of the line as its degree exactly when it is unbranched there.
-/

open Polynomial IsDedekindDomain Pointwise

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

/-! ### The fibre as a coset space -/

/-- **The points of a cover above a point of the line are the cosets of an inertia group there.**
This is the fundamental identity rewritten with the index of a subgroup in place of a quotient of
cardinalities. -/
theorem ncard_primesOver_eq_index (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] :
    ((placeP t).primesOver (Bring L.M)).ncard = (geomInertia L.M Q).index := by
  refine Nat.eq_of_mul_eq_mul_right (m := Nat.card (geomInertia L.M Q)) Nat.card_pos ?_
  rw [ncard_primesOver_mul_card_geomInertia L t Q, Subgroup.index_mul_card]

/-- **A cover has a single point above a point of the line exactly when the inertia group there is
the whole deck group.** -/
theorem geomInertia_eq_top_iff (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] :
    geomInertia L.M Q = ⊤ ↔ ((placeP t).primesOver (Bring L.M)).ncard = 1 := by
  rw [← card_geomInertia_eq_card_deck_iff L t Q, Subgroup.card_eq_iff_eq_top]

/-- **A cover has as many points above a point of the line as its degree exactly when the inertia
group there is trivial.** -/
theorem geomInertia_eq_bot_iff (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] :
    geomInertia L.M Q = ⊥ ↔
      ((placeP t).primesOver (Bring L.M)).ncard = Nat.card L.deck := by
  rw [← card_geomInertia_eq_one_iff L t Q, Subgroup.card_eq_one]

/-! ### A single point above a point of the line forces a cyclic deck group -/

/-- **A cover with a single point above some point of the line has a cyclic deck group.**  The
inertia group there is the whole deck group, and inertia at a geometric place is cyclic. -/
theorem isCyclic_deck_of_ncard_primesOver_eq_one (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)]
    (h : ((placeP t).primesOver (Bring L.M)).ncard = 1) : IsCyclic L.deck := by
  haveI : IsCyclic (geomInertia L.M Q) := isCyclic_geomInertia L.M t Q
  have htop : geomInertia L.M Q = ⊤ := (geomInertia_eq_top_iff L t Q).mpr h
  exact isCyclic_of_surjective (geomInertia L.M Q).subtype
    fun g => ⟨⟨g, by rw [htop]; exact Subgroup.mem_top g⟩, rfl⟩

/-- A cover has at least one point above every point of the line. -/
theorem ncard_primesOver_pos (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] : 0 < ((placeP t).primesOver (Bring L.M)).ncard := by
  rcases Nat.eq_zero_or_pos ((placeP t).primesOver (Bring L.M)).ncard with h0 | h
  · have hid := ncard_primesOver_mul_card_geomInertia L t Q
    rw [h0, zero_mul] at hid
    exact absurd hid.symm (Nat.card_pos (α := L.deck)).ne'
  · exact h

/-- **A cover whose deck group is not cyclic has at least two points above every point of the
line.** -/
theorem one_lt_ncard_primesOver_of_not_isCyclic (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] (h : ¬ IsCyclic L.deck) :
    1 < ((placeP t).primesOver (Bring L.M)).ncard := by
  refine lt_of_le_of_ne (ncard_primesOver_pos L t Q) fun hone => ?_
  exact h (isCyclic_deck_of_ncard_primesOver_eq_one L t Q hone.symm)

/-! ### The unbranched points -/

/-- The inertia group at a place above an unbranched point of the line is trivial. -/
theorem geomInertia_eq_bot_of_isUnramifiedAt (L : LineCover) {t : k}
    (h : ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] : geomInertia L.M Q = ⊥ := by
  rw [eq_bot_iff]
  exact fun σ hσ => Subgroup.mem_bot.mpr (h σ ⟨Q, ‹Q.IsMaximal›, ‹Q.LiesOver (placeP t)›, hσ⟩)

/-- **A cover is unbranched over a point of the line exactly when it has as many points above it as
its degree.**  In one direction the inertia group at any place above the point is trivial, and the
fundamental identity converts that into the count; in the other the count makes the inertia group at
one place trivial, and the deck group is transitive on the places, so all of them are. -/
theorem ncard_primesOver_eq_card_deck_iff_isUnramifiedAt (L : LineCover) (t : k)
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    ((placeP t).primesOver (Bring L.M)).ncard = Nat.card L.deck ↔
      ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1 := by
  refine ⟨fun h σ hσ => ?_, fun h => (geomInertia_eq_bot_iff L t Q).mp
    (geomInertia_eq_bot_of_isUnramifiedAt L h Q)⟩
  have hbot : geomInertia L.M Q = ⊥ := (geomInertia_eq_bot_iff L t Q).mpr h
  obtain ⟨Q', hQ'max, hQ'over, hQ'in⟩ := hσ
  haveI := hQ'max
  haveI : Q'.IsPrime := hQ'max.isPrime
  haveI := hQ'over
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  obtain ⟨g, hg⟩ := exists_smul_eq_of_liesOver (Ω := L.M) t Q Q'
  rw [hg, geomInertia_smul, hbot, Subgroup.map_bot] at hQ'in
  exact Subgroup.mem_bot.mp hQ'in

/-- **A cover unramified outside `S` has the full complement of points above every point outside
`S`.** -/
theorem ncard_primesOver_eq_card_deck_of_isUnramifiedOutside (L : LineCover) {S : Set k}
    (h : L.IsUnramifiedOutside S) {t : k} (ht : t ∉ S) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] :
    ((placeP t).primesOver (Bring L.M)).ncard = Nat.card L.deck :=
  (ncard_primesOver_eq_card_deck_iff_isUnramifiedAt L t Q).mpr (h t ht)

end Rigidity.RET

end
