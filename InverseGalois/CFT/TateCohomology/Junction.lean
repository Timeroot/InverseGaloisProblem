/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Norm

/-!
# Passing from degree zero to degree one

For a finite group the complete cohomology in degree zero is the invariants modulo the norms, while
in positive degrees it is the ordinary cohomology.  A short exact sequence of representations has a
connecting map out of the ordinary cohomology in degree zero, and that map kills the norms: the
norm of a vector upstairs is invariant and lifts the norm of its image, so the cochain measuring
the failure of the lift to be invariant can be taken to be zero.  The connecting map therefore
descends to the invariants modulo the norms.

The three term sequence obtained in this way is exact at both of its inner spots, which is what
attaches the complete cohomology in degree zero to the ordinary cohomology in degree one.

## Main definitions

* `InverseGalois.CFT.Tate.H0toH1`: the connecting map from the Tate group in degree zero of the
  quotient to the first cohomology of the sub.

## Main results

* `InverseGalois.CFT.Tate.exact_H0_H0toH1`: exactness at the Tate group in degree zero.
* `InverseGalois.CFT.Tate.exact_H0toH1_H1`: exactness at the first cohomology.

## Tags

Tate cohomology, connecting homomorphism, long exact sequence
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-! ### Comparison with the invariants functor -/

omit [Fintype G] in
/-- **A morphism of representations commutes with the action.** -/
theorem hom_equivariant {A B : Rep k G} (φ : A ⟶ B) (g : G) :
    φ.hom.hom ∘ₗ A.ρ g = B.ρ g ∘ₗ φ.hom.hom :=
  LinearMap.ext fun x => Rep.hom_comm_apply φ g x

omit [Fintype G] in
/-- The invariants functor agrees with the map induced on invariants by an equivariant map. -/
theorem invariantsFunctor_map_apply {A B : Rep k G} (φ : A ⟶ B) (x : A.ρ.invariants) :
    (Rep.invariantsFunctor k G).map φ x = invariantsMap φ.hom.hom (hom_equivariant φ) x := rfl

omit [Fintype G] in
/-- **The isomorphism between the cohomology in degree zero and the invariants is natural.** -/
theorem map_H0Iso_inv {A B : Rep k G} (φ : A ⟶ B) (y : A.ρ.invariants) :
    groupCohomology.map (MonoidHom.id G) φ 0 ((groupCohomology.H0Iso A).inv y)
      = (groupCohomology.H0Iso B).inv (invariantsMap φ.hom.hom (hom_equivariant φ) y) := by
  have h := congrArg (fun m : groupCohomology A 0 ⟶ ModuleCat.of k B.ρ.invariants =>
    m ((groupCohomology.H0Iso A).inv y)) (groupCohomology.map_id_comp_H0Iso_hom φ)
  simp only [CategoryTheory.comp_apply, Iso.inv_hom_id_apply] at h
  have h2 := congrArg (fun t => (groupCohomology.H0Iso B).inv t) h
  simp only [Iso.hom_inv_id_apply] at h2
  exact h2

/-! ### The connecting map out of degree zero -/

section Junction

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

/-- **The connecting map annihilates the norms.** -/
theorem delta_zero_normMap (c : X.X₃) :
    groupCohomology.δ hX 0 1 rfl ((groupCohomology.H0Iso X.X₃).inv
      ⟨normMap X.X₃.ρ c, normMap_mem_invariants _ _⟩) = 0 := by
  obtain ⟨b, hb⟩ := (Rep.epi_iff_surjective X.g).1 hX.epi_g c
  have hy : X.g.hom (normMap X.X₂.ρ b) = normMap X.X₃.ρ c := by
    rw [← hb]
    exact map_normMap X.g.hom.hom (hom_equivariant X.g) b
  have hx : X.f.hom ∘ (0 : G → X.X₁) = groupCohomology.d₀₁ X.X₂ (normMap X.X₂.ρ b) := by
    funext g
    simp [apply_normMap]
  rw [groupCohomology.δ₀_apply hX ⟨normMap X.X₃.ρ c, normMap_mem_invariants _ _⟩
    (normMap X.X₂.ρ b) hy 0 hx]
  exact (groupCohomology.H1π_eq_zero_iff _).mpr (zero_mem _)

/-- **The connecting map from the Tate group in degree zero of the quotient to the first
cohomology of the sub.** -/
def H0toH1 : H0 X.X₃.ρ →ₗ[k] groupCohomology X.X₁ 1 :=
  Submodule.liftQ _
    ((groupCohomology.δ hX 0 1 rfl).hom ∘ₗ (groupCohomology.H0Iso X.X₃).inv.hom) <| by
      rintro _ ⟨u, rfl⟩
      obtain ⟨c, rfl⟩ := Coinvariants.mk_surjective X.X₃.ρ u
      have hc : coinvariantsNorm X.X₃.ρ (Coinvariants.mk X.X₃.ρ c)
          = ⟨normMap X.X₃.ρ c, normMap_mem_invariants _ _⟩ :=
        Subtype.ext (coinvariantsNorm_mk _ _)
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hc]
      exact delta_zero_normMap hX c

theorem H0toH1_H0mk (z : X.X₃.ρ.invariants) :
    H0toH1 hX (H0mk X.X₃.ρ z)
      = groupCohomology.δ hX 0 1 rfl ((groupCohomology.H0Iso X.X₃).inv z) := rfl

/-! ### Exactness -/

theorem H0toH1_H0map (v : H0 X.X₂.ρ) :
    H0toH1 hX (H0map X.g.hom.hom (hom_equivariant X.g) v) = 0 := by
  have hrk := (groupCohomology.mapShortComplex₃_exact hX (i := 0) (j := 1)
    rfl).moduleCat_range_eq_ker
  obtain ⟨y, rfl⟩ := H0mk_surjective X.X₂.ρ v
  rw [H0map_H0mk, H0toH1_H0mk, ← map_H0Iso_inv X.g y]
  have h1 : groupCohomology.map (MonoidHom.id G) X.g 0 ((groupCohomology.H0Iso X.X₂).inv y) ∈
      LinearMap.range (groupCohomology.mapShortComplex₃ hX (i := 0) (j := 1) rfl).f.hom :=
    ⟨_, rfl⟩
  rw [hrk] at h1
  exact h1

/-- **The three term sequence is exact at the Tate group in degree zero.** -/
theorem exact_H0_H0toH1 :
    Function.Exact (H0map X.g.hom.hom (hom_equivariant X.g)) (H0toH1 hX) := by
  have hrk := (groupCohomology.mapShortComplex₃_exact hX (i := 0) (j := 1)
    rfl).moduleCat_range_eq_ker
  intro w
  constructor
  · intro hw
    obtain ⟨z, rfl⟩ := H0mk_surjective X.X₃.ρ w
    rw [H0toH1_H0mk] at hw
    obtain ⟨u, hu⟩ : (groupCohomology.H0Iso X.X₃).inv z ∈
        LinearMap.range (groupCohomology.mapShortComplex₃ hX (i := 0) (j := 1) rfl).f.hom := by
      rw [hrk]
      exact hw
    have hu' : groupCohomology.map (MonoidHom.id G) X.g 0 u
        = (groupCohomology.H0Iso X.X₃).inv z := hu
    have hmap := map_H0Iso_inv X.g ((groupCohomology.H0Iso X.X₂).hom u)
    rw [Iso.hom_inv_id_apply] at hmap
    rw [hmap] at hu'
    have hz : invariantsMap X.g.hom.hom (hom_equivariant X.g)
        ((groupCohomology.H0Iso X.X₂).hom u) = z := by
      simpa using congrArg (fun t => (groupCohomology.H0Iso X.X₃).hom t) hu'
    exact ⟨H0mk X.X₂.ρ ((groupCohomology.H0Iso X.X₂).hom u), by rw [H0map_H0mk, hz]⟩
  · rintro ⟨v, rfl⟩
    exact H0toH1_H0map hX v

/-- **The three term sequence is exact at the first cohomology.** -/
theorem exact_H0toH1_H1 :
    Function.Exact (H0toH1 hX) (groupCohomology.map (MonoidHom.id G) X.f 1).hom := by
  have hrk := (groupCohomology.mapShortComplex₁_exact hX (i := 0) (j := 1)
    rfl).moduleCat_range_eq_ker
  intro v
  constructor
  · intro hv
    obtain ⟨t, ht⟩ : v ∈ LinearMap.range
        (groupCohomology.mapShortComplex₁ hX (i := 0) (j := 1) rfl).f.hom := by
      rw [hrk]
      exact hv
    refine ⟨H0mk X.X₃.ρ ((groupCohomology.H0Iso X.X₃).hom t), ?_⟩
    rw [H0toH1_H0mk, Iso.hom_inv_id_apply]
    exact ht
  · rintro ⟨u, rfl⟩
    obtain ⟨z, rfl⟩ := H0mk_surjective X.X₃.ρ u
    rw [H0toH1_H0mk]
    have h1 : groupCohomology.δ hX 0 1 rfl ((groupCohomology.H0Iso X.X₃).inv z) ∈
        LinearMap.range (groupCohomology.mapShortComplex₁ hX (i := 0) (j := 1) rfl).f.hom :=
      ⟨_, rfl⟩
    rw [hrk] at h1
    exact h1

end Junction

end

end InverseGalois.CFT.Tate
