/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.NakayamaSubgroup
import InverseGalois.CFT.TateCohomology.RestrictTrans
import InverseGalois.CFT.TateCohomology.TensorTorsionError

/-!
# The failure of Tate and Nakayama at a prime, read on a subgroup

The comparison of Tate and Nakayama for a class in degree two sits, for coefficients killed by a
prime, inside a four term exact sequence whose two outer terms are the vectors of the representation
killed by the prime, tensored with the coefficients.  That sequence was built for a group carrying a
class satisfying the classical hypotheses of Tate's theorem on every Sylow subgroup, and it is the
exact measure of what the comparison misses.

A subgroup carries the restricted class, and the count that produces Tate's hypotheses on the
subgroups of the group produces them on the subgroups of a subgroup as well.  So the same four term
exact sequence exists over a subgroup, with the representation and the coefficients read there.  Its
comparison map is the comparison of Tate and Nakayama on the subgroup, which was already known to be
the restriction of the comparison over the whole group.

The upshot is a local form of the obstruction: **what the comparison of Tate and Nakayama produces
over a subgroup is exactly what the obstruction map of the subgroup kills**, so a spanning condition
over the subgroup, of the kind the everywhere locally trivial classes of a number field call for,
becomes a statement about a single linear map over that subgroup.

## Main definitions

* `InverseGalois.CFT.Tate.resTateNakayamaPTorsionErrorLeft`,
  `InverseGalois.CFT.Tate.resTateNakayamaPTorsionErrorRight`: the two maps surrounding the
  comparison of Tate and Nakayama over a subgroup, with the vectors of the representation killed by
  the prime at both ends.

## Main results

* `InverseGalois.CFT.Tate.isTateClassTwo_sylow_resObj`: the restricted class satisfies the classical
  hypotheses of Tate's theorem on every Sylow subgroup of a subgroup.
* `InverseGalois.CFT.Tate.range_resTateNakayamaPTorsionErrorLeft`,
  `InverseGalois.CFT.Tate.ker_resTateNakayamaPTorsionErrorRight`: **the four term exact sequence
  measuring the failure of Tate and Nakayama at a prime over a subgroup**, whose middle map is the
  comparison of the whole group read on that subgroup.
* `InverseGalois.CFT.Tate.exact_resTateNakayamaPTorsionErrorLeft`,
  `InverseGalois.CFT.Tate.exact_resTateNakayamaPTorsionErrorRight`: the same, as exactness.

## Tags

Tate-Nakayama, Tate cohomology, subgroup, restriction, torsion, fundamental class
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

section Error

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (A : Rep ℤ G)
  (α : tateModule A 2)
  (h1 : ∀ S : Subgroup G, Limits.IsZero (tateModule (resObj S A) 1))
  (hfin : ∀ S : Subgroup G, Finite ↥(tateModule (resObj S A) 2))
  (hcard : ∀ S : Subgroup G, Nat.card ↥(tateModule (resObj S A) 2) ≤ Nat.card ↥S)
  (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m)
  (H : Subgroup G) (W : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)

include h1 hfin hcard hα in
/-- The restriction of a class annihilated by exactly the multiples of the order of the group
satisfies the classical hypotheses of Tate's theorem on every Sylow subgroup of a subgroup, as soon
as the complete cohomology of the representation satisfies the count on every subgroup. -/
theorem isTateClassTwo_sylow_resObj : ∀ q : ℕ, q.Prime → ∀ P : Sylow q ↥H,
    IsTateClassTwo (P : Subgroup ↥H) (resObj H A) (tateRes H A 2 α) :=
  fun _ _ P => isTateClassTwo_resObj_of_card h1 hfin hcard hα H (P : Subgroup ↥H)

/-- **The map entering the comparison of Tate and Nakayama at a prime over a subgroup**: the vectors
of the representation killed by the prime, read on the subgroup and tensored with the coefficients
read there, three degrees above the lower of the two degrees. -/
def resTateNakayamaPTorsionErrorLeft (n : ℤ) :
    ↥(tateModule (tensorObj (nsmulTorsion (resObj H A) p) (resObj H W)) (n + 1 + 1 + 1)) →ₗ[ℤ]
      ↥(tateModule (resObj H W) n) :=
  tateNakayamaPTorsionErrorLeft (resObj H A) (tateRes H A 2 α) (resObj H W) hW
    (isTateClassTwo_sylow_resObj A α h1 hfin hcard hα H) n

/-- **The map leaving the comparison of Tate and Nakayama at a prime over a subgroup**: the tensor
product read on the subgroup, two degrees above the lower of the two degrees, mapping to the vectors
killed by the prime four degrees above it. -/
def resTateNakayamaPTorsionErrorRight (n : ℤ) :
    ↥(tateModule (tensorObj (resObj H A) (resObj H W)) (n + 1 + 1)) →ₗ[ℤ]
      ↥(tateModule (tensorObj (nsmulTorsion (resObj H A) p) (resObj H W)) (n + 1 + 1 + 1 + 1)) :=
  tateNakayamaPTorsionErrorRight (resObj H A) (tateRes H A 2 α) (resObj H W) hW
    (isTateClassTwo_sylow_resObj A α h1 hfin hcard hα H) n

/-- **What the comparison of Tate and Nakayama over a subgroup kills is exactly what the vectors of
the representation killed by the prime produce**, three degrees above the lower of the two
degrees. -/
theorem range_resTateNakayamaPTorsionErrorLeft (n : ℤ) :
    LinearMap.range (resTateNakayamaPTorsionErrorLeft A α h1 hfin hcard hα H W hW n)
      = LinearMap.ker (resTateNakayamaTwoMap H A α W n) := by
  rw [resTateNakayamaTwoMap_eq]
  exact range_tateNakayamaPTorsionErrorLeft (resObj H A) (tateRes H A 2 α) (resObj H W) hW
    (isTateClassTwo_sylow_resObj A α h1 hfin hcard hα H) n

/-- **What the comparison of Tate and Nakayama produces over a subgroup is exactly what the
obstruction map of that subgroup kills.** -/
theorem ker_resTateNakayamaPTorsionErrorRight (n : ℤ) :
    LinearMap.ker (resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n)
      = LinearMap.range (resTateNakayamaTwoMap H A α W n) := by
  rw [resTateNakayamaTwoMap_eq]
  exact ker_tateNakayamaPTorsionErrorRight (resObj H A) (tateRes H A 2 α) (resObj H W) hW
    (isTateClassTwo_sylow_resObj A α h1 hfin hcard hα H) n

/-- **The four term exact sequence over a subgroup is exact at the coefficients.** -/
theorem exact_resTateNakayamaPTorsionErrorLeft (n : ℤ) :
    Function.Exact (resTateNakayamaPTorsionErrorLeft A α h1 hfin hcard hα H W hW n)
      (resTateNakayamaTwoMap H A α W n) :=
  LinearMap.exact_iff.2 (range_resTateNakayamaPTorsionErrorLeft A α h1 hfin hcard hα H W hW n).symm

/-- **The four term exact sequence over a subgroup is exact at the tensor product.** -/
theorem exact_resTateNakayamaPTorsionErrorRight (n : ℤ) :
    Function.Exact (resTateNakayamaTwoMap H A α W n)
      (resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n) :=
  LinearMap.exact_iff.2 (ker_resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n)

end Error

end

end InverseGalois.CFT.Tate
