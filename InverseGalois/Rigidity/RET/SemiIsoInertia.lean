/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Semilinear
import InverseGalois.Rigidity.RET.InertiaGen

/-!
# Branch cycles travel along a semilinear isomorphism

A semilinear isomorphism of covers carries inertia to inertia
(`Rigidity.RET.LineCover.IsInertiaAt.semiIso`).  This file upgrades that statement from inertia
*elements* to inertia *generators*, by computing the whole inertia group of the moved place: it is
the image of the original one under the induced isomorphism of deck groups.  A *system of
distinguished branch cycles* is therefore carried to a system of distinguished branch cycles over
the moved points.

The consequence is that both halves of the Riemann existence correspondence only depend on the
tuple of branch points through the coordinate change: if they hold over one tuple, they hold over
any tuple reached from it by a change of coordinate which preserves the integral model.

## Main results

* `Rigidity.RET.LineCover.SemiIso.geomInertia_map` — the inertia group of the moved place is the
  image of the inertia group.
* `Rigidity.RET.LineCover.IsInertiaGenAt.semiIso` — distinguished inertia generators travel.
* `Rigidity.RET.LineCover.IsBranchCycleGenSystem.semiIso` — systems of distinguished branch cycles
  travel.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

namespace LineCover

variable {φ : RatFunc k ≃+* RatFunc k} {ψ : Polynomial k ≃+* Polynomial k}

namespace SemiIso

variable {L L' : LineCover}

/-- **The inertia group of a moved place is the image of the inertia group.** -/
theorem geomInertia_map (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (Q : Ideal (Bring L.M)) :
    geomInertia L'.M (Ideal.map (e.bring h) Q)
      = Subgroup.map (e.deckEquiv : L.deck →* L'.deck) (geomInertia L.M Q) := by
  ext τ
  constructor
  · intro hτ
    refine ⟨e.symm.conj τ, ?_, e.conj_conj_symm τ⟩
    have hmem := e.symm.mem_inertia_map h.symm hτ
    rwa [← e.bring_symm h, map_symm_map] at hmem
  · rintro ⟨σ, hσ, rfl⟩
    exact e.mem_inertia_map h hσ

end SemiIso

/-- **Distinguished inertia generators travel along a semilinear isomorphism**, with the point
moved along. -/
theorem IsInertiaGenAt.semiIso {L L' : LineCover} (e : SemiIso L L' φ) (h : PolyPreserving φ ψ)
    {t t' : k} (hmove : Ideal.map ψ (placeP t) = placeP t') {σ : L.deck}
    (hσ : L.IsInertiaGenAt t σ) : L'.IsInertiaGenAt t' (e.conj σ) := by
  obtain ⟨Q, hQmax, hQover, hI⟩ := hσ
  haveI := hQmax
  haveI := hQover
  refine ⟨Ideal.map (e.bring h) Q, e.isMaximal_map h Q, ?_, ?_⟩
  · have hover := e.liesOver_map h Q (placeP t)
    rwa [hmove] at hover
  · rw [e.geomInertia_map h Q, hI, MonoidHom.map_zpowers]
    rfl

/-- **Systems of distinguished branch cycles travel along a semilinear isomorphism**, with the
points moved along. -/
theorem IsBranchCycleGenSystem.semiIso {L L' : LineCover} (e : SemiIso L L' φ)
    (h : PolyPreserving φ ψ) {r : ℕ} {t t' : Fin r → k}
    (hmove : ∀ i, Ideal.map ψ (placeP (t i)) = placeP (t' i)) {g : Fin r → L.deck}
    (hg : L.IsBranchCycleGenSystem t g) :
    L'.IsBranchCycleGenSystem t' (fun i => e.conj (g i)) where
  inertia i := IsInertiaGenAt.semiIso e h (hmove i) (hg.inertia i)
  top := by
    have hrange : Set.range (fun i => e.conj (g i))
        = (e.deckEquiv : L.deck →* L'.deck) '' Set.range g := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← MonoidHom.map_closure, hg.top,
      Subgroup.map_top_of_surjective _ (MulEquiv.surjective e.deckEquiv)]
  prod := by
    have hlist : (List.ofFn fun i => e.conj (g i))
        = (List.ofFn g).map (e.deckEquiv : L.deck →* L'.deck) := by
      rw [List.map_ofFn]
      rfl
    rw [hlist, List.prod_hom, hg.prod, map_one]

end LineCover

end Rigidity.RET
