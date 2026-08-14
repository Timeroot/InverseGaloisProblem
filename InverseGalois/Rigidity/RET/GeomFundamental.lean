/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.TamePi1

/-!
# The fundamental identity for a cover of the line

Over an algebraically closed constant field the points of a cover carry no residue extension: the
residue field at a place of the cover is again the constant field.  The fundamental identity of
ramification theory therefore loses one of its three factors, and what remains is a bare count —
the number of points of the cover above a point of the line, times the order of the inertia group
at any one of them, is the degree of the cover.

Everything about how a cover sits over one point of the line is contained in that single equation.
A point is unbranched exactly when it carries the full complement of points of the cover; it is
totally ramified exactly when it carries one; and in between the order of the inertia group always
divides the degree.

## Main results

* `Rigidity.RET.finrank_residue_eq_one` — the residue field at a place of a cover is the constant
  field.
* `Rigidity.RET.card_geomInertia_eq_ramificationIdxIn` — the order of the inertia group at a place
  is the winding number of the cover there.
* `Rigidity.RET.ncard_primesOver_mul_card_geomInertia` — the fundamental identity.
* `Rigidity.RET.card_geomInertia_eq_card_deck_iff` — total ramification is a single point above.
-/

open Polynomial IsDedekindDomain Pointwise

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

/-! ### No residue extension over an algebraically closed constant field -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The residue field at a place of a cover is the constant field.**  It is algebraic over the
residue field of the point of the line below, which is the constant field itself, and the constant
field is algebraically closed. -/
theorem finrank_residue_eq_one (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] :
    Module.finrank (Polynomial k ⧸ placeP t) (Bring L.M ⧸ Q) = 1 := by
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  haveI : Algebra.IsIntegral (Polynomial k ⧸ placeP t) (Bring L.M ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := Polynomial k)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := Polynomial k ⧸ placeP t) (K := Bring L.M ⧸ Q)
  have hequiv : (Polynomial k ⧸ placeP t) ≃ₐ[Polynomial k ⧸ placeP t] (Bring L.M ⧸ Q) :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  rw [← hequiv.toLinearEquiv.finrank_eq, Module.finrank_self]

/-! ### The order of the inertia group is the winding number -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **The order of the inertia group at a place of a cover is the winding number there.**  The
residue extension is separable because the base residue field has characteristic zero, and in a
Galois extension of Dedekind domains the inertia group has the ramification index for its
order. -/
theorem card_geomInertia_eq_ramificationIdxIn (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    Nat.card (geomInertia L.M Q) = Ideal.ramificationIdxIn (placeP t) (Bring L.M) := by
  haveI := residue_isSeparable L.M t Q
  exact Ideal.card_inertia_eq_ramificationIdxIn (G := L.deck) (placeP t) (placeP_ne_bot t) Q

set_option synthInstance.maxHeartbeats 400000 in
/-- **The order of the inertia group at a place of a cover is the ramification index there.** -/
theorem card_geomInertia_eq_ramificationIdx (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    Nat.card (geomInertia L.M Q)
      = Ideal.ramificationIdx (algebraMap (Polynomial k) (Bring L.M)) (placeP t) Q := by
  rw [card_geomInertia_eq_ramificationIdxIn L t Q]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx (placeP t) Q L.deck

/-- **All the places of a cover above one point of the line ramify equally.** -/
theorem card_geomInertia_eq_card_geomInertia (L : LineCover) (t : k) (Q Q' : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] [Q'.IsMaximal] [Q'.LiesOver (placeP t)] :
    Nat.card (geomInertia L.M Q) = Nat.card (geomInertia L.M Q') := by
  rw [card_geomInertia_eq_ramificationIdxIn L t Q, card_geomInertia_eq_ramificationIdxIn L t Q']

/-! ### The fundamental identity -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **The fundamental identity for a cover of the line**: the number of points of the cover above a
point of the line, times the order of the inertia group at any one of them, is the degree of the
cover.  The third factor of the classical identity, the residue degree, is one because the constant
field is algebraically closed. -/
theorem ncard_primesOver_mul_card_geomInertia (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    ((placeP t).primesOver (Bring L.M)).ncard * Nat.card (geomInertia L.M Q)
      = Nat.card L.deck := by
  haveI := residue_isSeparable L.M t Q
  have h := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := L.deck) (placeP t) Q
  rwa [finrank_residue_eq_one L t Q, mul_one] at h

/-- **The order of an inertia group divides the degree of the cover.** -/
theorem card_geomInertia_dvd_card_deck (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    Nat.card (geomInertia L.M Q) ∣ Nat.card L.deck :=
  ⟨((placeP t).primesOver (Bring L.M)).ncard,
    by rw [← ncard_primesOver_mul_card_geomInertia L t Q, mul_comm]⟩

/-- **A cover is totally ramified over a point exactly when it has a single point above it.** -/
theorem card_geomInertia_eq_card_deck_iff (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    Nat.card (geomInertia L.M Q) = Nat.card L.deck ↔
      ((placeP t).primesOver (Bring L.M)).ncard = 1 := by
  have h := ncard_primesOver_mul_card_geomInertia L t Q
  have hpos : 0 < Nat.card L.deck := Nat.card_pos
  constructor
  · intro hc
    rw [hc] at h
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, one_mul])
  · intro hc
    rw [hc, one_mul] at h
    exact h

/-- **A cover is unbranched over a point exactly when it has as many points above it as its
degree.** -/
theorem card_geomInertia_eq_one_iff (L : LineCover) (t : k) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    Nat.card (geomInertia L.M Q) = 1 ↔
      ((placeP t).primesOver (Bring L.M)).ncard = Nat.card L.deck := by
  have h := ncard_primesOver_mul_card_geomInertia L t Q
  have hpos : 0 < Nat.card L.deck := Nat.card_pos
  constructor
  · intro hc
    rw [hc, mul_one] at h
    exact h
  · intro hc
    rw [hc] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact h)

end Rigidity.RET

end
