/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Coeff

/-!
# The connecting step between the first and the second cohomology of a topological group

Take a short exact sequence of coefficients for a topological group: a submodule, the module, and
the quotient, with the two maps commuting with the actions.  A cochain with values in the quotient
can be lifted term by term to the module, because the projection is onto.  The lift is no longer a
cocycle, but the failure is measured by its coboundary, and that coboundary is killed by the
projection, so it takes its values in the submodule.  This is the classical passage from a class of
the first cohomology of the quotient to a class of the second cohomology of the submodule, written
here entirely in terms of explicit cochains.

The passage is exact in the middle.  On one side, a class of the second cohomology of the submodule
that is obtained this way dies in the second cohomology of the module, since there its cocycle is
visibly the coboundary of the lift.  On the other side, a class that dies in the second cohomology
of the module is the coboundary of some cochain, and the projection of that cochain is then a
cocycle for the quotient which the passage carries back to the class one started with.  The class
produced does not depend on the choice of lift: two lifts of the same quotient cochain differ by a
cochain with values in the submodule, and their coboundaries therefore differ by a coboundary.

Everything is done for smooth cochains, so the lifts and the differences are checked to be constant
on the cosets of an open normal subgroup, an intersection of two such subgroups being open and
normal again.  The section is stated for a general topological group and general coefficients; the
use in view is a Galois group of a number field, where the passage lowers a question about the
second cohomology to a question about the first, in which the reciprocity law is available.

## Main results

* `InverseGalois.CFT.isMulCocycle₁_iff_coboundary₂_eq_one`: a cochain in degree one is a cocycle
  exactly when its coboundary is trivial.
* `InverseGalois.CFT.exists_lift_of_isMulCocycle₁`: **a smooth cocycle for the quotient lifts to a
  smooth cochain for the module whose coboundary is a smooth cocycle for the submodule.**
* `InverseGalois.CFT.coeffH2_eq_one_of_lift`: a class of the second cohomology of the submodule
  whose cocycle is the coboundary of a smooth cochain for the module dies in the second cohomology
  of the module.
* `InverseGalois.CFT.exists_lift_of_coeffH2_eq_one`: **a class of the second cohomology of the
  submodule that dies in the second cohomology of the module comes from a smooth cocycle for the
  quotient.**
* `InverseGalois.CFT.smoothH2Mk_eq_of_lift`: two lifts of the same cochain for the quotient give the
  same class of the second cohomology of the submodule.

## Tags

group cohomology, profinite group, connecting homomorphism, dimension shifting, cocycle
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Cocycles in degree one and the coboundary in degree two -/

section Cocycle

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- A cochain in degree one is a cocycle exactly when the coboundary it defines in degree two is
trivial. -/
theorem isMulCocycle₁_iff_coboundary₂_eq_one (u : G → M) :
    IsMulCocycle₁ u ↔ coboundary₂ u = 1 := by
  constructor
  · intro hu
    funext p
    show p.1 • u p.2 / u (p.1 * p.2) * u p.1 = 1
    rw [hu p.1 p.2, div_mul_eq_div_div, div_self', one_div, inv_mul_cancel]
  · intro h g j
    have h2 : g • u j / u (g * j) * u g = 1 := congrFun h (g, j)
    rw [div_mul_eq_mul_div, div_eq_one] at h2
    exact h2.symm

end Cocycle

/-! ### Lifting a cocycle of the quotient -/

section Connecting

variable {G E M Q : Type*} [Group G] [TopologicalSpace G]
  [CommGroup E] [CommGroup M] [CommGroup Q]
  [MulDistribMulAction G E] [MulDistribMulAction G M] [MulDistribMulAction G Q]
  [IsSmoothAction G M]
  (ι : E →* M) (hιe : ∀ (g : G) (e : E), ι (g • e) = g • ι e) (hιinj : Function.Injective ι)
  (π : M →* Q) (hπe : ∀ (g : G) (m : M), π (g • m) = g • π m)
  (hcomp : ∀ e : E, π (ι e) = 1)
  (hex : ∀ m : M, π m = 1 → ∃ e : E, ι e = m)

include hιe hιinj hπe hex in
/-- **A smooth cocycle for the quotient lifts to a smooth cochain for the module, and the coboundary
of that lift is a smooth cocycle with values in the submodule.**  This is the passage from the first
cohomology of the quotient to the second cohomology of the submodule. -/
theorem exists_lift_of_isMulCocycle₁ (hsurj : Function.Surjective π)
    {u : G → Q} (hu : IsMulCocycle₁ u) (hus : IsSmooth₁ u) :
    ∃ (v : G → M) (a : G × G → E), IsSmooth₁ v ∧ (∀ g, π (v g) = u g) ∧
      IsMulCocycle₂ a ∧ IsSmooth₂ a ∧ coboundary₂ v = coeffMap₂ ι a := by
  obtain ⟨s, hs⟩ := hsurj.hasRightInverse
  set v : G → M := fun g => s (u g) with hvdef
  have hvs : IsSmooth₁ v := by
    obtain ⟨N, hN, h⟩ := hus
    exact ⟨N, hN, fun x n hn => congrArg s (h x n hn)⟩
  have hv : ∀ g, π (v g) = u g := fun g => hs (u g)
  have hcob : coeffMap₂ π (coboundary₂ v) = 1 := by
    rw [← coboundary₂_coeffMap₁ π hπe v]
    have hpv : coeffMap₁ π v = u := funext hv
    rw [hpv]
    exact (isMulCocycle₁_iff_coboundary₂_eq_one u).1 hu
  have hker : ∀ p : G × G, ∃ e : E, ι e = coboundary₂ v p := fun p => hex _ (congrFun hcob p)
  choose a ha using hker
  have hacoc : IsMulCocycle₂ a := by
    intro g h j
    apply hιinj
    simp only [map_mul, hιe, ha]
    exact isMulCocycle₂_coboundary₂ v g h j
  have hasm : IsSmooth₂ a := by
    obtain ⟨N, hN, hsm⟩ := hvs.coboundary₂
    exact ⟨N, hN, fun x y n hn m hm => hιinj (by rw [ha, ha]; exact hsm x y n hn m hm)⟩
  exact ⟨v, a, hvs, hv, hacoc, hasm, funext fun p => (ha p).symm⟩

omit [IsSmoothAction G M] in
include hιe in
/-- A class of the second cohomology of the submodule whose cocycle is the coboundary of a smooth
cochain for the module dies in the second cohomology of the module. -/
theorem coeffH2_eq_one_of_lift {a : G × G → E} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    {v : G → M} (hvs : IsSmooth₁ v) (hv : coboundary₂ v = coeffMap₂ ι a) :
    coeffH2 ι hιe (smoothH2Mk a ha has) = 1 := by
  rw [coeffH2_smoothH2Mk]
  exact (smoothH2Mk_eq_one_iff _ _).2 ⟨v, hvs, hv⟩

omit [IsSmoothAction G M] in
include hιe hπe hcomp in
/-- **A class of the second cohomology of the submodule that dies in the second cohomology of the
module comes from a smooth cocycle for the quotient**: its cocycle is the coboundary of a smooth
cochain, and the projection of that cochain is a smooth cocycle for the quotient. -/
theorem exists_lift_of_coeffH2_eq_one
    {a : G × G → E} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a)
    (h : coeffH2 ι hιe (smoothH2Mk a ha has) = 1) :
    ∃ v : G → M, IsSmooth₁ v ∧ coboundary₂ v = coeffMap₂ ι a ∧
      IsMulCocycle₁ (coeffMap₁ π v) ∧ IsSmooth₁ (coeffMap₁ π v) := by
  rw [coeffH2_smoothH2Mk] at h
  obtain ⟨v, hvs, hv⟩ := (smoothH2Mk_eq_one_iff _ _).1 h
  refine ⟨v, hvs, hv, ?_, hvs.coeffMap₁ π⟩
  rw [isMulCocycle₁_iff_coboundary₂_eq_one, coboundary₂_coeffMap₁ π hπe, hv]
  funext p
  exact hcomp (a p)

omit [MulDistribMulAction G Q] [IsSmoothAction G M] in
include hιe hιinj hex in
/-- Two smooth lifts of the same cochain for the quotient give the same class of the second
cohomology of the submodule: they differ by a smooth cochain with values in the submodule, so their
coboundaries differ by a coboundary. -/
theorem smoothH2Mk_eq_of_lift
    {v v' : G → M} (hvs : IsSmooth₁ v) (hvs' : IsSmooth₁ v')
    (hvv : ∀ g, π (v g) = π (v' g))
    {a a' : G × G → E} (hacoc : IsMulCocycle₂ a) (hasm : IsSmooth₂ a)
    (hacoc' : IsMulCocycle₂ a') (hasm' : IsSmooth₂ a')
    (hva : coboundary₂ v = coeffMap₂ ι a) (hva' : coboundary₂ v' = coeffMap₂ ι a') :
    smoothH2Mk a hacoc hasm = smoothH2Mk a' hacoc' hasm' := by
  have hker : ∀ g : G, ∃ e : E, ι e = v' g / v g := by
    intro g
    refine hex _ ?_
    rw [map_div, hvv g, div_self']
  choose c hc using hker
  have hcs : IsSmooth₁ c := by
    obtain ⟨N, hN, h⟩ := hvs
    obtain ⟨N', hN', h'⟩ := hvs'
    refine ⟨N ⊓ N', hN.inf hN', fun x n hn => hιinj ?_⟩
    rw [hc, hc, h x n hn.1, h' x n hn.2]
  have hprod : v' = v * coeffMap₁ ι c := by
    funext g
    show v' g = v g * ι (c g)
    rw [hc g, div_eq_mul_inv, mul_comm (v' g) (v g)⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hcbd : coboundary₂ v' = coboundary₂ v * coeffMap₂ ι (coboundary₂ c) := by
    rw [hprod, coboundary₂_mul, coboundary₂_coeffMap₁ ι hιe]
  have hfin : ∀ p, a' p = a p * coboundary₂ c p := by
    intro p
    apply hιinj
    rw [map_mul]
    have h1 : ι (a' p) = coboundary₂ v' p := congrFun hva'.symm p
    have h2 : ι (a p) = coboundary₂ v p := congrFun hva.symm p
    rw [h1, h2, congrFun hcbd p]
    rfl
  rw [smoothH2Mk_eq_iff]
  refine ⟨c⁻¹, hcs.inv, ?_⟩
  rw [coboundary₂_inv]
  funext p
  show (coboundary₂ c p)⁻¹ = a p / a' p
  rw [hfin p, div_mul_eq_div_div, div_self', one_div]

end Connecting

end InverseGalois.CFT
