/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaSubgroupError

/-!
# What the obstruction of Tate and Nakayama at a prime produces

The comparison of Tate and Nakayama for a class in degree two sits, for coefficients killed by a
prime, inside a four term exact sequence whose outer terms are the vectors of the representation
killed by the prime, tensored with the coefficients.  That sequence is a window on the long exact
sequence of the extension attached to the class, and the window can be widened by one place: the
long exact sequence is also exact at the term the obstruction lands in.

Widening it names the image of the obstruction.  The obstruction is, up to the identification of the
complete cohomology of the tensored extension with that of the vectors killed by the prime three
degrees higher, the map induced by the inclusion of the tensor product into the extension, and the
map that follows it in the long exact sequence is the one induced by the projection of the extension
onto the coefficients -- which is, up to the same identification, the map entering the comparison
one degree higher.  So **what the obstruction of Tate and Nakayama at a prime produces in a degree
is exactly what the map entering the comparison one degree higher kills**, and the four term
sequence extends to a long exact sequence alternating between the coefficients, their tensor product
with the representation, and the vectors of the representation killed by the prime tensored with the
coefficients.

That turns a statement about the image of the obstruction into a statement about the kernel of an
explicit map, which is the form a duality theorem for the everywhere locally trivial classes takes.

## Main results

* `InverseGalois.CFT.Tate.range_tateNakayamaNextMap`: the values of the map leaving the comparison
  of Tate and Nakayama are exactly what the projection of the tensored extension onto the
  coefficients kills, one degree higher.
* `InverseGalois.CFT.Tate.range_tateNakayamaPTorsionErrorRight`: **what the obstruction of Tate and
  Nakayama at a prime produces is exactly what the map entering the comparison one degree higher
  kills**, so the four term exact sequence extends past the obstruction.
* `InverseGalois.CFT.Tate.range_resTateNakayamaPTorsionErrorRight`: the same over a subgroup of the
  group.

## Tags

Tate-Nakayama, Tate cohomology, torsion, long exact sequence, fundamental class, tensor product
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### The image of the map leaving the comparison -/

section Nakayama

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ (shiftObj A)) (M : Rep k G)

/-- **The values of the map leaving the comparison of Tate and Nakayama are exactly what the map
induced by the projection of the tensored extension onto the coefficients kills**, one degree
higher, because the long exact sequence of the tensored extension is exact at its middle term. -/
theorem range_tateNakayamaNextMap (n : ℤ) :
    LinearMap.range (tateNakayamaNextMap A b M n)
      = LinearMap.ker (tateMap (cocycleTensorSeq (shiftObj A) b M).g (n + 1)).hom := by
  show LinearMap.range ((tateMap (cocycleTensorSeq (shiftObj A) b M).f (n + 1)).hom ∘ₗ
    (tateNakayamaIso A M n).symm.toLinearMap) = _
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  exact (tateExact_map_map (cocycleTensorSeq_shortExact (shiftObj A) b M) (n + 1) x).symm

end Nakayama

/-! ### A class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G] (A : Rep ℤ G) (α : tateModule A 2) (M : Rep ℤ G)

/-- **The values of the map leaving the comparison** for the cocycle attached to a prescribed class
in degree two are exactly what the projection of the tensored extension onto the coefficients kills,
one degree higher. -/
theorem range_tateNakayamaTwoNextMap (n : ℤ) :
    LinearMap.range (tateNakayamaTwoNextMap A α M n)
      = LinearMap.ker
        (tateMap (cocycleTensorSeq (shiftObj A) (tateTwoCocycle A α) M).g (n + 1)).hom :=
  range_tateNakayamaNextMap A (tateTwoCocycle A α) M n

end DegreeTwo

/-! ### The long exact sequence at a prime -/

section Error

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (A : Rep ℤ G)
  (α : tateModule A 2) (W : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)
  (hT : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, IsTateClassTwo (P : Subgroup G) A α)

/-- **What the obstruction of Tate and Nakayama at a prime produces is exactly what the map entering
the comparison one degree higher kills**: both are read off the same term of the long exact sequence
of the tensored extension, which is exact there. -/
theorem range_tateNakayamaPTorsionErrorRight (n : ℤ) :
    LinearMap.range (tateNakayamaPTorsionErrorRight A α W hW hT n)
      = LinearMap.ker (tateNakayamaPTorsionErrorLeft A α W hW hT (n + 1)) := by
  show LinearMap.range ((cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).toLinearMap ∘ₗ
      tateNakayamaTwoNextMap A α W n)
    = LinearMap.ker ((tateMap (cocycleTensorSeq (shiftObj A) (tateTwoCocycle A α) W).g
      (n + 1)).hom ∘ₗ (cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).symm.toLinearMap)
  rw [LinearMap.range_comp, range_tateNakayamaTwoNextMap, LinearMap.ker_comp]
  exact Submodule.map_equiv_eq_comap_symm _ _

/-- **The four term exact sequence measuring the failure of Tate and Nakayama at a prime extends
past the obstruction**: what the obstruction produces in a degree is what the map entering the
comparison one degree higher kills. -/
theorem exact_tateNakayamaPTorsionErrorRightLeft (n : ℤ) :
    Function.Exact (tateNakayamaPTorsionErrorRight A α W hW hT n)
      (tateNakayamaPTorsionErrorLeft A α W hW hT (n + 1)) :=
  LinearMap.exact_iff.2 (range_tateNakayamaPTorsionErrorRight A α W hW hT n).symm

end Error

/-! ### The long exact sequence over a subgroup -/

section Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (A : Rep ℤ G)
  (α : tateModule A 2)
  (h1 : ∀ S : Subgroup G, Limits.IsZero (tateModule (resObj S A) 1))
  (hfin : ∀ S : Subgroup G, Finite ↥(tateModule (resObj S A) 2))
  (hcard : ∀ S : Subgroup G, Nat.card ↥(tateModule (resObj S A) 2) ≤ Nat.card ↥S)
  (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m)
  (H : Subgroup G) (W : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)

/-- **What the obstruction of Tate and Nakayama at a prime produces over a subgroup is exactly what
the map entering the comparison there one degree higher kills.** -/
theorem range_resTateNakayamaPTorsionErrorRight (n : ℤ) :
    LinearMap.range (resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n)
      = LinearMap.ker (resTateNakayamaPTorsionErrorLeft A α h1 hfin hcard hα H W hW (n + 1)) :=
  range_tateNakayamaPTorsionErrorRight (resObj H A) (tateRes H A 2 α) (resObj H W) hW
    (isTateClassTwo_sylow_resObj A α h1 hfin hcard hα H) n

/-- **The four term exact sequence over a subgroup extends past the obstruction.** -/
theorem exact_resTateNakayamaPTorsionErrorRightLeft (n : ℤ) :
    Function.Exact (resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n)
      (resTateNakayamaPTorsionErrorLeft A α h1 hfin hcard hα H W hW (n + 1)) :=
  LinearMap.exact_iff.2 (range_resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n).symm

end Subgroup

end

end InverseGalois.CFT.Tate
