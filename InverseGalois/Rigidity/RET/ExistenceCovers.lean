/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Existence
import InverseGalois.Rigidity.RET.CoverExistence

/-!
# The covers correspondence

The two directions of the covers form of the Riemann Existence Theorem are assembled here into the
biconditional `riemann_existence_cover`, and applied to a rigidity certificate.  The `→` direction
is group theory and lives with the statement (`RET.Existence`); the `←` direction is the one that
constructs a cover, and it is the existence half of the Riemann Existence Theorem
(`Rigidity.RET.exists_lineCover_of_prodOne`) with its branch points forgotten.

## Main results

* `riemann_existence_cover_mpr` — a surjection from a sphere group is realized by a geometric
  Galois cover.
* `riemann_existence_cover` — the covers correspondence, as a biconditional.
* `RigidityCertificate.isGeometricGaloisCover` — a rigidity certificate realizes its group as a
  geometric Galois cover.
* `isGeometricGaloisCover_of_finite` — every finite group is realized by a geometric Galois cover:
  the inverse Galois problem over `ℚ̄(T)`.
-/

open Polynomial

/-- **Riemann Existence Theorem, the existence direction** (`←` of the covers correspondence
`(2) ↔ (3)`, algebraic incarnation over `ℚ̄`, stated through explicit maps rather than categories).

> A monodromy representation `φ : SphereGroup r ↠ G` — a surjection from the sphere group
> `SphereGroup r ≅ π₁(ℙ¹(ℂ) ∖ S)`, `|S| = r` — is realized by an actual finite Galois extension of
> `ℚ̄(T)` with group `G`.

A surjection out of `Γ_r` is the same thing as a generating product-one tuple in `G`
(`Rigidity.RET.prod_apply_sphereGroup_of`, `Rigidity.RET.closure_range_apply_sphereGroup_of`), and
such a tuple is realized as the branch cycles of a cover of the line over any prescribed `r`
distinct points — here the rational points `0, 1, …, r-1` — by
`Rigidity.RET.exists_lineCover_of_prodOne`.  Forgetting the branch points leaves exactly this
statement.

The images `φ (xᵢ)` are the branch-cycle / inertia generators over the `r` branch points; that they
are inertia at prescribed points is what the sharper `lineCover_exists_of_branchCycles`
(`RET.UniversalTuple`) records and what the branch-cycle descent (`Descent.Tower`) consumes.  See Völklein, *Groups as Galois Groups*,
Thm 2.13 and §4; Serre, *Topics in Galois Theory*, §6. -/
theorem riemann_existence_cover_mpr {G : Type} [Group G] [Finite G]
    (h : ∃ (r : ℕ) (φ : Rigidity.RET.SphereGroup r →* G), Function.Surjective φ) :
    IsGeometricGaloisCover G := by
  classical
  obtain ⟨r, φ, hφ⟩ := h
  have hinj : Function.Injective fun i : Fin r => algebraMap ℚ GeomAKLB.k (i.val : ℚ) := by
    intro i j hij
    have h1 : ((i.val : ℚ)) = ((j.val : ℚ)) := (algebraMap ℚ GeomAKLB.k).injective hij
    exact Fin.val_injective (Nat.cast_injective h1)
  obtain ⟨L, ⟨e⟩, -, -⟩ := Rigidity.RET.exists_lineCover_of_prodOne hinj
    (fun i => φ (PresentedGroup.of i)) (Rigidity.RET.prod_apply_sphereGroup_of φ)
    (Rigidity.RET.closure_range_apply_sphereGroup_of φ hφ)
  exact ⟨L.M, L.field, L.alg, L.findim, L.isGalois, ⟨e⟩⟩

/-- **The covers correspondence `(2) ↔ (3)`**, assembled from its two directions: a finite group is
realized by a geometric Galois cover of `ℙ¹_{ℚ̄}` iff it is a quotient of some sphere group.  All of
the content is in `riemann_existence_cover_mpr`; `riemann_existence_cover_mp` is unconditional. -/
theorem riemann_existence_cover {G : Type} [Group G] [Finite G] :
    IsGeometricGaloisCover G ↔
      ∃ (r : ℕ) (φ : Rigidity.RET.SphereGroup r →* G), Function.Surjective φ :=
  ⟨riemann_existence_cover_mp, riemann_existence_cover_mpr⟩

/-- A rigidity certificate's generating product-one tuple realizes `G` as a geometric Galois cover.

The certificate's `gen` field supplies a product-one tuple `g : Fin r → G` generating `G`; via the
presentation layer this is a surjection `SphereGroup r ↠ G` (`sphereHom` +
`sphereHom_surjective_iff`), which the `←` direction of the Riemann Existence Theorem turns into a
Galois extension of `ℚ̄(T)` with group `G`.  This is the first step of the rigidity method: the
*existence* of the cover over `ℚ̄`, before any descent to `ℚ`. -/
theorem RigidityCertificate.isGeometricGaloisCover {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) : IsGeometricGaloisCover G := by
  obtain ⟨g, _hclass, hprod, hgen⟩ := cert.gen
  exact riemann_existence_cover_mpr
    ⟨cert.r, Rigidity.RET.sphereHom g hprod,
      (Rigidity.RET.sphereHom_surjective_iff g hprod).2 hgen⟩

/-- **The geometric inverse Galois problem over `ℚ̄(T)`: every finite group is the Galois group of
a finite Galois extension of `ℚ̄(T)`.**

The two sides of the covers correspondence pull in opposite directions here, and the correspondence
being a theorem is what makes the statement one.  Its right-hand side asks for a surjection onto `G`
from some sphere group, and that costs nothing — `Γ_r` is free of rank `r - 1`, so a large enough
`r` works for any finite group.  Its left-hand side is the cover, and producing one is the whole
analytic content of the Riemann Existence Theorem.  Over the algebraically closed constant field
there is no arithmetic left to obstruct anything, which is why the geometric problem is settled
while the problem over `ℚ` is not: `IsRegularInverseGalois`, the same statement with `ℚ̄` replaced
by `ℚ`, is open in general and is what a rigidity certificate buys. -/
theorem isGeometricGaloisCover_of_finite {G : Type} [Group G] [Finite G] :
    IsGeometricGaloisCover G :=
  riemann_existence_cover_mpr Rigidity.RET.exists_sphereGroup_surjective
