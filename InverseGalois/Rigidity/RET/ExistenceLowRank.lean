/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.KummerCover
import InverseGalois.Rigidity.RET.Pi1.Topological.SphereBaseCase

/-!
# The existence direction of the covers correspondence, for at most two branch points

`riemann_existence_cover_mpr` (`RET.Existence`) asserts that a surjection `Γ_r ↠ G` from a sphere
group — a monodromy representation with `r` prescribed branch points — is realized by a finite
Galois extension of `ℚ̄(T)` with group `G`.  For `r ≤ 2` that assertion is a **theorem**, with no
geometric input at all, and this file proves it.

The reason is that the sphere groups of rank at most two are cyclic: `Γ_0` and `Γ_1` are trivial
(`sphereGroup_zero_subsingleton`, `sphereGroup_one_subsingleton`) and `Γ_2 ≅ ℤ`
(`sphereGroup_two_mulEquiv_int`), so a quotient of one of them is a finite cyclic group — and the
finite cyclic groups are realized explicitly by the Kummer covers `yⁿ = T`
(`isGeometricGaloisCover_of_isCyclic`).  Geometrically this is the classical picture: a cover of the
line branched over at most two points is, after a Möbius change of coordinate, `y ↦ yⁿ`.

The bound is sharp in the sense that it is exactly the range in which the group theory forces the
answer: `Γ_r` is free of rank `r - 1` (`sphereGroup_mulEquiv_free`), so from `r = 3` on its finite
quotients are all the two-generated finite groups, and no explicit construction covers them.

## Main results

* `Rigidity.RET.isGeometricGaloisCover_of_sphereGroup_surjective_of_le_two` — a monodromy
  representation with at most two branch points is realized by a geometric Galois cover.
-/

namespace Rigidity.RET

/-- **A sphere group with at most two punctures is cyclic.**  `Γ_0` and `Γ_1` are trivial, and
`Γ_2 ≅ ℤ` is the fundamental group of the twice-punctured sphere `ℂˣ`. -/
theorem isCyclic_sphereGroup_of_le_two {r : ℕ} (hr : r ≤ 2) : IsCyclic (SphereGroup r) := by
  interval_cases r
  · infer_instance
  · infer_instance
  · exact isCyclic_of_surjective sphereGroup_two_mulEquiv_int.symm
      sphereGroup_two_mulEquiv_int.symm.surjective

/-- **The existence direction of the covers correspondence, for at most two branch points.**

A surjection `Γ_r ↠ G` with `r ≤ 2` is realized by a finite Galois extension of `ℚ̄(T)` with group
`G`: such a `G` is a finite cyclic group, hence the group of a Kummer cover `yⁿ = T`.  This is the
special case of `riemann_existence_cover_mpr` in which the branch data is small enough that the
geometry is forced — the general statement needs the Riemann Existence Theorem. -/
theorem isGeometricGaloisCover_of_sphereGroup_surjective_of_le_two {G : Type} [Group G] [Finite G]
    {r : ℕ} (hr : r ≤ 2) (φ : SphereGroup r →* G) (hφ : Function.Surjective φ) :
    IsGeometricGaloisCover G := by
  haveI := isCyclic_sphereGroup_of_le_two hr
  haveI : IsCyclic G := isCyclic_of_surjective φ hφ
  exact isGeometricGaloisCover_of_isCyclic G

end Rigidity.RET
