/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.InertiaSub
import InverseGalois.Rigidity.RET.Infinity

/-!
# Unramifiedness passes to Galois subcovers

`RET/Unramified.lean` and `RET/Infinity.lean` propagate unramifiedness *upwards*: a compositum of
subcovers unramified outside `S` is unramified outside `S`.  This file supplies the opposite,
and easier, direction — a **Galois subcover of a cover unramified outside `S` is unramified
outside `S`** — which is what lets a cover with a prescribed deck group be cut out of a larger,
more symmetric cover that is easier to build by hand.

The argument is the inertia dictionary of `RET/InertiaSub.lean` plus transitivity of the deck group
on places.  Inertia at the contraction of a place `Q` of the big cover is the image of inertia at
`Q` (`geomInertia_comap_eq_map`), hence trivial; and every place of the subcover above the point is
a deck translate of such a contraction (`exists_smul_eq_of_liesOver`), so its inertia group is a
conjugate of the trivial group.

## Main results

* `Rigidity.RET.LineCover.exists_place` — a cover has a place above every point of the line.
* `Rigidity.RET.LineCover.IsUnramifiedOutside.sub` — unramifiedness outside `S` passes to a Galois
  subcover.
* `Rigidity.RET.LineCover.IsUnramifiedAtInfinity.sub` — unramifiedness at infinity passes to a
  Galois subcover.
-/

open Polynomial
open scoped Pointwise

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

namespace LineCover

attribute [local instance] sub_isGalois

/-- **A cover of the line has a place above every point of the line.**  The integral model is
integral over `ℚ̄[X]` and the structure map is injective, so lying over applies. -/
theorem exists_place (L : LineCover) (t : k) :
    ∃ Q : Ideal (Bring L.M), Q.IsMaximal ∧ Q.LiesOver (placeP t) :=
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral (placeP t)

/-- **Unramifiedness outside `S` passes to a Galois subcover.** -/
theorem IsUnramifiedOutside.sub {L : LineCover} {S : Set k} (h : L.IsUnramifiedOutside S)
    (E : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) E] :
    (L.sub E).IsUnramifiedOutside S := by
  haveI := isScalarTower_poly_sub (E : Type) L.M
  intro t ht τ hτ
  obtain ⟨Q', hQ'max, hQ'over, hQ'in⟩ := hτ
  obtain ⟨Q, hQmax, hQover⟩ := L.exists_place t
  haveI := hQmax
  haveI : Q.IsPrime := hQmax.isPrime
  haveI := hQover
  -- inertia upstairs is trivial, so inertia at the contracted place is trivial
  have hbot : geomInertia L.M Q = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    exact Subgroup.mem_bot.mpr (h t ht σ ⟨Q, hQmax, hQover, hσ⟩)
  have hQ'in' : τ ∈ geomInertia (E : Type) Q' := hQ'in
  have hcomap : geomInertia (E : Type)
      (Q.comap (subInclusion (E := (E : Type)) (M := L.M))) = ⊥ := by
    rw [geomInertia_comap_eq_map (E := (E : Type)) (M := L.M) (L.subHom E) (L.subHom_commutes E)
      t Q (L.subHom_surjective E), hbot, Subgroup.map_bot]
  -- every place of the subcover above `t` is a deck translate of the contracted place
  haveI := hQ'max
  haveI : Q'.IsPrime := hQ'max.isPrime
  haveI := hQ'over
  haveI hcm : (Q.comap (subInclusion (E := (E : Type)) (M := L.M))).IsMaximal :=
    isMaximal_comap_subInclusion (E := (E : Type)) t Q
  haveI : (Q.comap (subInclusion (E := (E : Type)) (M := L.M))).IsPrime := hcm.isPrime
  haveI := liesOver_comap_subInclusion (E := (E : Type)) (M := L.M) t Q
  obtain ⟨g, hg⟩ := exists_smul_eq_of_liesOver (Ω := (E : Type)) t
    (Q.comap (subInclusion (E := (E : Type)) (M := L.M))) Q'
  rw [hg, geomInertia_smul, hcomap, Subgroup.map_bot] at hQ'in'
  exact Subgroup.mem_bot.mp hQ'in'

/-- **Unramifiedness at infinity passes to a Galois subcover.** -/
theorem IsUnramifiedAtInfinity.sub {L : LineCover} (h : L.IsUnramifiedAtInfinity)
    (E : IntermediateField (RatFunc k) L.M) [hnorm : Normal (RatFunc k) E] :
    (L.sub E).IsUnramifiedAtInfinity := by
  haveI hnorm' :
      Normal (RatFunc k) (Twist.subField (φ := invSubst.toRingEquiv) (M := L.M) E) :=
    Normal.of_algEquiv (F := RatFunc k) (E := Twist invSubst.toRingEquiv ((E : Type)))
      (Twist.subFieldEquiv E)
  rw [isUnramifiedAtInfinity_iff] at h ⊢
  refine IsUnramifiedOutside.transport
    (L := @LineCover.sub (L.twist invSubst.toRingEquiv)
      (Twist.subField (φ := invSubst.toRingEquiv) (M := L.M) E) hnorm')
    (L' := (L.sub E).twist invSubst.toRingEquiv)
    (Twist.subFieldEquiv (φ := invSubst.toRingEquiv) (M := L.M) E).symm ?_
  exact @IsUnramifiedOutside.sub (L.twist invSubst.toRingEquiv) {(0 : k)}ᶜ h
    (Twist.subField (φ := invSubst.toRingEquiv) (M := L.M) E) hnorm'

end LineCover

end Rigidity.RET
