/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Transport and dévissage for the first cohomology

Two ways of deducing the vanishing of the first cohomology of a representation from the vanishing
of the first cohomology of another one.

The first is transport along an isomorphism: an isomorphism of the acting groups together with a
linear isomorphism of the modules intertwining the two actions carries cocycles to cocycles and
coboundaries to coboundaries, so the two cohomology groups vanish together.

The second is dévissage along a quotient.  Let `π : G → G'` be a surjection, and suppose the module
of a representation of `G'` embeds in the module of a representation of `G` as the part fixed by
the kernel of `π`, compatibly with the two actions.  A `1`-cocycle of `G` that vanishes on the
kernel is constant on the fibres of `π`, and each of its values is fixed by the kernel, so it comes
from a `1`-cocycle of `G'`; if that one is a coboundary then so is the original.  Correcting a
general cocycle by a coboundary to make it vanish on the kernel is the hypothesis `hres`, which in
applications is the vanishing of the first cohomology of the kernel.

## Main results

* `InverseGalois.CFT.eq_zero_H1_of_mulEquiv`: **the first cohomology is transported along an
  isomorphism of groups compatible with a linear isomorphism of the modules.**
* `InverseGalois.CFT.eq_zero_H1_of_devissage`: **the first cohomology of `G` vanishes when the
  first cohomology of a quotient `G'` vanishes and every `1`-cocycle of `G` restricts to a
  coboundary on the kernel.**

## Tags

group cohomology, first cohomology, inflation, restriction, dévissage
-/

universe u

open groupCohomology

namespace InverseGalois.CFT

variable {k : Type u} [CommRing k] {G G' : Type u} [Group G] [Group G']
  {A : Rep k G} {B : Rep k G'}

/-! ### Transport along an isomorphism -/

section Transport

/-- **Transport of the vanishing of the first cohomology** along an isomorphism of groups compatible
with a linear isomorphism of the modules. -/
theorem eq_zero_H1_of_mulEquiv (e : G ≃* G') (φ : A ≃ₗ[k] B)
    (hφ : ∀ (g : G) (a : A), φ (A.ρ g a) = B.ρ (e g) (φ a))
    (hB : ∀ y : groupCohomology B 1, y = 0)
    (z : groupCohomology A 1) : z = 0 := by
  induction z using H1_induction_on with
  | h x =>
    have hmem : (fun q : G' => φ ((x : G → A) (e.symm q))) ∈ cocycles₁ B := by
      rw [mem_cocycles₁_iff]
      intro q r
      rw [map_mul, (mem_cocycles₁_iff (x : G → A)).1 x.2, map_add, hφ, MulEquiv.apply_symm_apply]
    obtain ⟨c, hc⟩ := (H1π_eq_zero_iff _).1 (hB (H1π B ⟨_, hmem⟩))
    refine (H1π_eq_zero_iff _).2 ⟨φ.symm c, funext fun g => ?_⟩
    have hcg : B.ρ (e g) c - c = φ ((x : G → A) (e.symm (e g))) := congrFun hc (e g)
    rw [MulEquiv.symm_apply_apply] at hcg
    show A.ρ g (φ.symm c) - φ.symm c = (x : G → A) g
    refine φ.injective ?_
    rw [map_sub, hφ, LinearEquiv.apply_symm_apply]
    exact hcg

end Transport

/-! ### Dévissage along a quotient -/

section Devissage

/-- **Dévissage for the first cohomology.**  Let `π : G → G'` be a surjection and let the module of
a representation of `G'` sit inside the module of a representation of `G` as the part fixed by the
kernel, compatibly with the actions.  If every `1`-cocycle of `G` becomes a coboundary on the
kernel, and the first cohomology of `G'` vanishes, then the first cohomology of `G` vanishes. -/
theorem eq_zero_H1_of_devissage (π : G →* G') (hπ : Function.Surjective π) (φ : B →ₗ[k] A)
    (hφinj : Function.Injective φ)
    (hφeq : ∀ (g : G) (b : B), φ (B.ρ (π g) b) = A.ρ g (φ b))
    (hφrange : ∀ a : A, (∀ s : G, π s = 1 → A.ρ s a = a) → ∃ b : B, φ b = a)
    (hres : ∀ x : cocycles₁ A, ∃ b : A, ∀ s : G, π s = 1 → (x : G → A) s = A.ρ s b - b)
    (hB : ∀ y : groupCohomology B 1, y = 0)
    (z : groupCohomology A 1) : z = 0 := by
  induction z using H1_induction_on with
  | h x =>
    obtain ⟨b, hb⟩ := hres x
    set x0 : G → A := fun g => (x : G → A) g - (A.ρ g b - b) with hx0def
    have hcoc : ∀ g h : G, x0 (g * h) = A.ρ g (x0 h) + x0 g := by
      intro g h
      have hx := (mem_cocycles₁_iff (x : G → A)).1 x.2 g h
      simp only [hx0def, hx, map_mul, Module.End.mul_apply, map_sub]
      abel
    have hzero : ∀ s : G, π s = 1 → x0 s = 0 := by
      intro s hs
      simp only [hx0def, hb s hs, sub_self]
    have hconst : ∀ g g' : G, π g = π g' → x0 g = x0 g' := by
      intro g g' h
      have hs : π (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
      have hgg := hcoc g (g⁻¹ * g')
      rw [mul_inv_cancel_left, hzero _ hs, map_zero, zero_add] at hgg
      exact hgg.symm
    have hfix : ∀ (g s : G), π s = 1 → A.ρ s (x0 g) = x0 g := by
      intro g s hs
      have h1 := hcoc s g
      rw [hzero s hs, add_zero] at h1
      rw [← h1]
      exact hconst _ _ (by rw [map_mul, hs, one_mul])
    have hlift : ∀ g : G, ∃ c : B, φ c = x0 g := fun g => hφrange _ (fun s hs => hfix g s hs)
    choose y hy using hlift
    set sec : G' → G := Function.surjInv hπ with hsecdef
    have hsec : ∀ q : G', π (sec q) = q := Function.surjInv_eq hπ
    set w : G' → B := fun q => y (sec q) with hwdef
    have hwv : ∀ q : G', φ (w q) = x0 (sec q) := fun q => hy (sec q)
    have hw : ∀ g : G, φ (w (π g)) = x0 g := by
      intro g
      rw [hwv]
      exact hconst _ _ (hsec (π g))
    have hmem : w ∈ cocycles₁ B := by
      rw [mem_cocycles₁_iff]
      intro q r
      refine hφinj ?_
      have h1 : φ (B.ρ q (w r)) = A.ρ (sec q) (x0 (sec r)) := by
        have h2 := hφeq (sec q) (w r)
        rw [hsec, hwv] at h2
        exact h2
      have h3 : x0 (sec (q * r)) = x0 (sec q * sec r) :=
        hconst _ _ (by rw [hsec, map_mul, hsec, hsec])
      rw [map_add, hwv, hwv, h1, h3, hcoc]
    obtain ⟨c, hc⟩ := (H1π_eq_zero_iff _).1 (hB (H1π B ⟨w, hmem⟩))
    refine (H1π_eq_zero_iff _).2 ⟨φ c + b, funext fun g => ?_⟩
    have hcg : B.ρ (π g) c - c = w (π g) := congrFun hc (π g)
    have hxg : x0 g = A.ρ g (φ c) - φ c := by
      rw [← hw g, ← hcg, map_sub, hφeq]
    have hxx : (x : G → A) g = x0 g + (A.ρ g b - b) := by simp [hx0def]
    show A.ρ g (φ c + b) - (φ c + b) = (x : G → A) g
    rw [hxx, hxg, map_add]
    abel

end Devissage

end InverseGalois.CFT
