/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.TateCohomology.NakayamaRestrict
import InverseGalois.CFT.TateCohomology.RestrictShiftBridge

/-!
# The comparison of Tate and Nakayama on a subgroup is the comparison of the subgroup

The comparison of Tate and Nakayama attached to a class in degree two was defined on a subgroup by
restricting the ingredients built on the whole group: the cocycle of the shift is restricted, and
the identification raising the degree is the one obtained from the restricted sequence.  The
subgroup also has a comparison of its own, built from the representation read on the subgroup and
from the restriction of the class, with no reference to the group it sits in.

The two are the same map.  The cocycle of the shift read on the subgroup and the cocycle chosen on
the subgroup both have, as their class, the restriction of the prescribed class in degree two; they
are therefore cohomologous once the first is pushed along the comparison of the two shifts, and a
map of representations carrying one cocycle to a cohomologous one carries the connecting map of one
tensored extension to the connecting map of the other.  What remains is the compatibility of that
comparison with the passage of the shift through a tensor product, which holds on the nose.

The consequence is a local-to-global statement.  Suppose a representation of the subgroup maps to
the representation of the group read on the subgroup, and carries a class in degree two of its own
to the restriction of the prescribed class — as the units of a completion map to the idele classes
and carry the fundamental class localised at a place to the restriction of the fundamental class.
Then everything the comparison of Tate and Nakayama produces on the subgroup already comes from
that representation: the global obstruction, read on the subgroup, is a local obstruction.

## Main results

* `InverseGalois.CFT.Tate.resHom_tensorHomLeft`: reading a map tensored on the left with a fixed
  representation on a subgroup is tensoring the map read on the subgroup.
* `InverseGalois.CFT.Tate.tateNakayamaTwoMap_res` and
  `InverseGalois.CFT.Tate.resTateNakayamaTwoMap_eq`: **the comparison of Tate and Nakayama on a
  subgroup is the comparison of the subgroup for the restricted representation and the restricted
  class.**
* `InverseGalois.CFT.Tate.tateMap_tensorHomLeft_tateNakayamaTwoMap`: **the comparison of Tate and
  Nakayama on a subgroup is computed by any representation of the subgroup carrying a class in
  degree two to the restricted class.**
* `InverseGalois.CFT.Tate.range_resTateNakayamaTwoMap_le`: **what the comparison of Tate and
  Nakayama produces on a subgroup already comes from such a representation.**

## Tags

Tate cohomology, Tate-Nakayama, restriction, subgroup, fundamental class, localisation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### Cohomologous cocycles -/

section Cohomologous

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G}

/-- **Two cocycles with the same class in degree one differ by the failure of a vector to be
invariant**, one of them being pushed forward along a map of representations. -/
theorem exists_cohomologous_of_H1π_eq (φ : A ⟶ B) (b : groupCohomology.cocycles₁ A)
    (c : groupCohomology.cocycles₁ B)
    (h : groupCohomology.H1π B (homCocycles₁ φ b) = groupCohomology.H1π B c) :
    ∃ y : ↥B.V, ∀ τ : G, φ.hom.hom (b τ) = c τ + (B.ρ τ y - y) := by
  obtain ⟨y, hy⟩ := (groupCohomology.H1π_eq_iff _ _).1 h
  refine ⟨y, fun τ => ?_⟩
  have hτ := congrFun hy τ
  simp only [groupCohomology.d₀₁_hom_apply, Pi.sub_apply] at hτ
  rw [hτ, homCocycles₁_apply]
  abel

end Cohomologous

/-! ### Restricting a map tensored on the left -/

section Tensor

variable {k G : Type u} [CommRing k] [Group G]

/-- Reading a map tensored on the left with a fixed representation on a subgroup is tensoring the
map read on the subgroup with the fixed representation read on the subgroup. -/
theorem resHom_tensorHomLeft (H : Subgroup G) (M : Rep k G) {A B : Rep k G} (ψ : A ⟶ B) :
    resHom H (tensorHomLeft M ψ) = tensorHomLeft (resObj H M) (resHom H ψ) :=
  rfl

end Tensor

/-! ### The comparison of Tate and Nakayama -/

section Subgroup

variable {G : Type} [Group G] [Finite G] (H : Subgroup G) {A : Rep ℤ G} (α : tateModule A 2)
  (M : Rep ℤ G)

/-- **The cocycle of the shift read on a subgroup and the cocycle chosen on the subgroup are
cohomologous**, once the first is pushed along the comparison of the two shifts: both have, as their
class, the restriction of the prescribed class in degree two. -/
theorem exists_resShiftHom_tateTwoCocycle :
    ∃ y : ↥(shiftObj (resObj H A)).V, ∀ τ : ↥H,
      (resShiftHom H A).hom.hom (resCocycles₁ H (shiftObj A) (tateTwoCocycle A α) τ)
        = tateTwoCocycle (resObj H A) (tateRes H A 2 α) τ
          + ((shiftObj (resObj H A)).ρ τ y - y) := by
  refine exists_cohomologous_of_H1π_eq _ _ _ ?_
  refine (tateShiftEquiv (resObj H A) 1).injective ?_
  rw [tateTwoCocycle_spec, ← tateMap_one_H1π, ← resShiftEquiv_eq_tateShiftEquiv,
    resShiftEquiv_H1π_resCocycles₁, tateTwoCocycle_spec]

/-- **The comparison of Tate and Nakayama on a subgroup is the comparison of the subgroup** for the
representation read on the subgroup and the restriction of the prescribed class. -/
theorem tateNakayamaTwoMap_res (n : ℤ) (x : ↥(tateModule (resObj H M) n)) :
    tateNakayamaTwoMap (resObj H A) (tateRes H A 2 α) (resObj H M) n x
      = resTateNakayamaTwoMap H A α M n x := by
  obtain ⟨y, hy⟩ := exists_resShiftHom_tateTwoCocycle H α
  have hδ := tateδ_cocycleTensorSeq_naturality (resShiftHom H A)
    (resCocycles₁ H (shiftObj A) (tateTwoCocycle A α))
    (tateTwoCocycle (resObj H A) (tateRes H A 2 α)) y (resObj H M) hy n x
  show tateShiftEquiv (tensorObj (resObj H A) (resObj H M)) (n + 1)
      (tateMap (shiftTensorIso (resObj H A) (resObj H M)).hom (n + 1)
        (tateδ (cocycleTensorSeq_shortExact (shiftObj (resObj H A))
          (tateTwoCocycle (resObj H A) (tateRes H A 2 α)) (resObj H M)) n x))
    = resShiftEquiv H (tensorObj A M) (n + 1)
      (tateMap (resHom H (shiftTensorIso A M).hom) (n + 1)
        (tateδ (cocycleTensorSeq_shortExact (resObj H (shiftObj A))
          (resCocycles₁ H (shiftObj A) (tateTwoCocycle A α)) (resObj H M)) n x))
  rw [← hδ, resShiftEquiv_eq_tateShiftEquiv,
    tateMap_comp_apply (resHom H (shiftTensorIso A M).hom) (resShiftHom H (tensorObj A M)),
    resShiftHom_shiftTensorIso]
  exact congrArg (fun z => tateShiftEquiv (tensorObj (resObj H A) (resObj H M)) (n + 1) z)
    (tateMap_comp_apply (tensorHomLeft (resObj H M) (resShiftHom H A))
      (shiftTensorIso (resObj H A) (resObj H M)).hom (n + 1) _)

/-- **The comparison of Tate and Nakayama on a subgroup is the comparison of the subgroup**, as
linear maps. -/
theorem resTateNakayamaTwoMap_eq (n : ℤ) :
    resTateNakayamaTwoMap H A α M n
      = tateNakayamaTwoMap (resObj H A) (tateRes H A 2 α) (resObj H M) n :=
  LinearMap.ext fun x => (tateNakayamaTwoMap_res H α M n x).symm

/-- **The comparison of Tate and Nakayama on a subgroup is computed by any representation of the
subgroup carrying a class in degree two to the restriction of the prescribed class.** -/
theorem tateMap_tensorHomLeft_tateNakayamaTwoMap {A' : Rep ℤ ↥H} (φ : A' ⟶ resObj H A)
    (β : tateModule A' 2) (hβ : tateMap φ 2 β = tateRes H A 2 α) (n : ℤ)
    (x : ↥(tateModule (resObj H M) n)) :
    tateMap (tensorHomLeft (resObj H M) φ) (n + 1 + 1)
        (tateNakayamaTwoMap A' β (resObj H M) n x)
      = resTateNakayamaTwoMap H A α M n x := by
  rw [tateNakayamaTwoMap_naturality φ β (resObj H M) n x, hβ, tateNakayamaTwoMap_res]

/-- **What the comparison of Tate and Nakayama produces on a subgroup already comes from any
representation of the subgroup carrying a class in degree two to the restriction of the prescribed
class.** -/
theorem range_resTateNakayamaTwoMap_le {A' : Rep ℤ ↥H} (φ : A' ⟶ resObj H A)
    (β : tateModule A' 2) (hβ : tateMap φ 2 β = tateRes H A 2 α) (n : ℤ) :
    LinearMap.range (resTateNakayamaTwoMap H A α M n)
      ≤ LinearMap.range (tateMap (tensorHomLeft (resObj H M) φ) (n + 1 + 1)).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨tateNakayamaTwoMap A' β (resObj H M) n x,
    tateMap_tensorHomLeft_tateNakayamaTwoMap H α M φ β hβ n x⟩

end Subgroup

end

end InverseGalois.CFT.Tate
