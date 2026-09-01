/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CyclicRestrict
import InverseGalois.CFT.GroupCohomology.InfResTwo

/-!
# The comparison map of a cyclic group is natural

The fixed points of a generator of a finite cyclic group map to the second cohomology of that
group, and the map is given by an explicit two-cocycle: the one whose value is the point itself
exactly when the discrete logarithms of the two arguments add up to at least the order of the
group.  Writing that cocycle additively identifies the comparison map with the class of an
explicit element of the group of two-cocycles.

The explicit description makes the comparison map natural.  A homomorphism of finite cyclic groups
of the same order carrying one generator to the other multiplies discrete logarithms by one, so
pulling the explicit cocycle back along it, and pushing the values forward along a compatible
morphism of representations, returns the explicit cocycle of the image point.  Consequently the
functorial map on second cohomology carries the class of a fixed point to the class of its image.

This is the compatibility that lets a class constructed on a quotient be recognised, after
inflation and restriction to a complementary subgroup, as the class constructed directly on that
subgroup.

## Main definitions

* `InverseGalois.CFT.addCyclicCocycle`: the explicit two-cocycle attached to a generator and a
  fixed point, written additively.

## Main results

* `InverseGalois.CFT.tateH0ToH2_eq_H2π`: **the comparison map is the class of the explicit
  two-cocycle.**
* `InverseGalois.CFT.map_tateH0ToH2`: **the comparison map is natural along a homomorphism of
  cyclic groups of the same order carrying a generator to a generator.**

## Tags

group cohomology, cyclic group, two-cocycle, Tate cohomology, naturality
-/

namespace InverseGalois.CFT

open CategoryTheory groupCohomology CyclicH2

noncomputable section

attribute [local instance] repMulDistribMulAction

variable {G : Type} [Group G] [Fintype G] {A : Rep ℤ G} {g : G} {σ : ↥A.V ≃+ ↥A.V}

/-! ### The explicit two-cocycle, written additively -/

omit [Fintype G] in
/-- The explicit two-cocycle attached to a generator `g` of a finite cyclic group and to a point
`a` of a representation over the integers: it takes the value `a` exactly when the discrete
logarithms of the two arguments add up to at least the order of the group. -/
def addCyclicCocycle (g : G) (a : ↥A.V) : G × G → ↥A.V :=
  fun p => if (dlog g p.1).val + (dlog g p.2).val < Nat.card G then 0 else a

omit [Fintype G] in
/-- The additive explicit two-cocycle is the multiplicative one. -/
theorem ofAdd_addCyclicCocycle (g : G) (a : ↥A.V) (p : G × G) :
    Multiplicative.ofAdd (addCyclicCocycle (A := A) g a p)
      = cyclicCocycle g (Multiplicative.ofAdd a) p := by
  simp only [addCyclicCocycle, cyclicCocycle]
  split <;> rfl

/-- The explicit two-cocycle attached to a fixed point of a generator is a two-cocycle. -/
theorem mem_cocycles₂_addCyclicCocycle (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hσ : ∀ x, σ x = A.ρ g x) {a : ↥A.V} (ha : σ a = a) :
    addCyclicCocycle (A := A) g a ∈ cocycles₂ A := by
  refine mem_cocycles₂_of_isMulCocycle₂ ?_
  have h := isMulCocycle₂_cyclicCocycle (M := Multiplicative ↥A.V) hg
    ((mem_invariantsSubgroup_ofAdd_iff hg hσ a).2 ha)
  intro x y z
  simpa only [ofAdd_addCyclicCocycle] using h x y z

/-- **The map from the fixed points of a generator to the second cohomology is the class of the
explicit two-cocycle.** -/
theorem tateH0ToH2_eq_H2π (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hσ : ∀ x, σ x = A.ρ g x)
    (x : ↥(sigmaSubOne σ).ker) :
    tateH0ToH2 hg hσ x
      = H2π A ⟨addCyclicCocycle g (x : ↥A.V), mem_cocycles₂_addCyclicCocycle hg hσ
          ((mem_ker_sigmaSubOne_iff σ _).1 x.2)⟩ := by
  have h1 : tateH0ToH2 hg hσ x
      = (groupCohomology.map (MonoidHom.id G) (repIso A).hom 2).hom
          (H2π (Rep.ofMulDistribMulAction G (Multiplicative ↥A.V))
            (cocyclesOfIsMulCocycle₂ (isMulCocycle₂_cyclicCocycle hg
              ((mem_invariantsSubgroup_ofAdd_iff hg hσ (x : ↥A.V)).2
                ((mem_ker_sigmaSubOne_iff σ _).1 x.2))))) := rfl
  rw [h1, H2π_comp_map_apply]
  congr 1

/-! ### Naturality along an isomorphism of cyclic groups -/

section Map

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂]
  {A : Rep ℤ G₂} {B : Rep ℤ G₁}

/-- **The map from the fixed points of a generator to the second cohomology is natural** along a
homomorphism of finite cyclic groups of the same order carrying a generator to a generator, and a
compatible morphism of representations: the homomorphism preserves discrete logarithms, so it
pulls the explicit two-cocycle back to the explicit two-cocycle of the image point. -/
theorem map_tateH0ToH2 (f : G₁ →* G₂) (φ : (Action.res _ f).obj A ⟶ B)
    (hcard : Nat.card G₁ = Nat.card G₂) {g₁ : G₁} (hg₁ : ∀ x : G₁, x ∈ Subgroup.zpowers g₁)
    (hg₂ : ∀ x : G₂, x ∈ Subgroup.zpowers (f g₁)) {σA : ↥A.V ≃+ ↥A.V}
    (hσA : ∀ x, σA x = A.ρ (f g₁) x) {σB : ↥B.V ≃+ ↥B.V} (hσB : ∀ x, σB x = B.ρ g₁ x)
    (x : ↥(sigmaSubOne σA).ker) (y : ↥(sigmaSubOne σB).ker)
    (hxy : (y : ↥B.V) = φ.hom (x : ↥A.V)) :
    (groupCohomology.map f φ 2).hom (tateH0ToH2 hg₂ hσA x) = tateH0ToH2 hg₁ hσB y := by
  have hdl : ∀ s : G₁, (dlog (f g₁) (f s)).val = (dlog g₁ s).val := fun s => by
    rw [val_dlog_map f hg₂ hg₁ (d := 1) (pow_one (f g₁)).symm (by rw [one_mul, hcard]) s,
      one_mul]
  rw [tateH0ToH2_eq_H2π, tateH0ToH2_eq_H2π, H2π_comp_map_apply]
  congr 1
  refine cocycles₂_ext fun q r => ?_
  show φ.hom (addCyclicCocycle (A := A) (f g₁) (x : ↥A.V) (f q, f r))
      = addCyclicCocycle (A := B) g₁ (y : ↥B.V) (q, r)
  simp only [addCyclicCocycle, hdl, hcard]
  split
  · simp
  · exact hxy.symm

end Map

end

end InverseGalois.CFT
