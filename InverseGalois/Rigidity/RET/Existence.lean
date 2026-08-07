/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Presentation
import InverseGalois.Rigidity.RET.GeomRET
import InverseGalois.Rigidity.Certificate

/-!
# The Riemann Existence Theorem, in its covers form

This file states the **Riemann Existence Theorem** as the single geometric input of the
development, in the *covers* form, and in its algebraic (Grothendieck) incarnation over `ℚ̄`.
Everything downstream — the branch-cycle descent to `ℚ(T)` and the Hilbert specialization to `ℚ` —
is then *derived* from it, rather than from an over-specified bundle handing over the whole
`of_regular_family` hypothesis list in one gulp.

## The precise theorem being isolated

In full, RET is the statement: *let `X` be a compact connected Riemann surface, `S ⊆ X` finite, and
`X° = X ∖ S`; then three categories are equivalent* —

1. finite **branched covers** of `X` unramified outside `S` (non-constant holomorphic
   `φ : Y → X` with `Y` a compact Riemann surface, restricting to a topological cover over `X°`);
2. finite **covering spaces** of `X°` — equivalently, finite `π₁(X°, x₀)`-sets;
3. finite **field extensions** `L / ℳ(X)` unramified outside `S` (contravariantly), `ℳ(X)` the
   function field.

The analytic teeth are the passage `(1) ↔ (2)`: a topological cover of the punctured curve is
automatically holomorphic/algebraic (Grauert–Remmert / GAGA).  That passage involves Riemann
surfaces and analytification, which Mathlib cannot express; it is isolated, for the line, in
`Rigidity.RET.lineCover_exists_of_branchCycles` (`RET.GeomRET`).  The algebraic passage `(2) ↔ (3)`
is what the rigidity method consumes, and what we state here — *without categories* (Mathlib has no category of field extensions), as an
equivalence phrased through explicit maps.

## Specialising to `X = ℙ¹`

Take `X = ℙ¹`, `S = {p₁,…,p_r}`.  Then `π₁(ℙ¹(ℂ) ∖ S) ≅ ⟨x₁,…,x_r ∣ x₁⋯x_r = 1⟩ =
Rigidity.RET.SphereGroup r`.  A finite `π₁(X°)`-set is a finite set with a `SphereGroup r`-action;
the **connected** ones with automorphism group `G` are the transitive faithful ones, i.e. the
**surjections** `SphereGroup r ↠ G`.  Under `(2) ↔ (3)` these correspond to the finite **Galois**
extensions of `ℳ(ℙ¹) = ℚ̄(T)` with group `G`, unramified outside `S`.  Passing `ℂ ⇝ ℚ̄`
(Grothendieck's comparison; `ℚ̄` is algebraically closed) keeps the same finite covers.

So the category-free shadow of `(2) ↔ (3)`, for a finite group `G`, is the biconditional

> `G` is the group of a finite Galois extension of `ℚ̄(T)`  ↔  `G` is a quotient of some sphere
> group `SphereGroup r`,

which is `riemann_existence_cover` below.  Its `←` direction is the existence teeth of RET (a
monodromy representation `SphereGroup r ↠ G` is realized by an actual extension); its `→` direction
says every finite cover of `ℙ¹_{ℚ̄}` has a finite monodromy representation (is branched over
finitely many points).  The `→` direction turns out to need no geometry: since `Γ_r` is free of rank
`r - 1`, *every* finite group admits a surjection from some sphere group
(`Rigidity.RET.exists_sphereGroup_surjective`), so the biconditional's whole content is `←`, the
geometric inverse Galois problem over `ℚ̄(T)`.  Over the algebraically closed constant field `ℚ̄`, "connected" is automatic
(a *field* extension of `ℚ̄(T)` is a connected cover, and its field of constants is a finite
extension of `ℚ̄`, hence `ℚ̄` itself); regularity is the *arithmetic* content of the descent to
`ℚ(T)`, not of RET.

## Main definitions

* `IsGeometricGaloisCover G` — there is a finite Galois extension `L / ℚ̄(T)` with
  `Gal(L / ℚ̄(T)) ≃* G`; this is side `(3)` (a connected Galois cover of `ℙ¹_{ℚ̄}`), phrased through
  the explicit maps `algebraMap ℚ̄(T) L` and `L ≃ₐ[ℚ̄(T)] L ≃* G`.

## Main results

* `riemann_existence_cover_mpr` — the covers correspondence's **existence** direction (`←`): a
  surjection `SphereGroup r ↠ G` is realized by a geometric Galois cover.  It is the shadow, with
  the branch points and the inertia forgotten, of `Rigidity.RET.lineCover_exists_of_branchCycles`
  (`RET.TamePi1`), where the analytic teeth of the correspondence live.
* `riemann_existence_cover_mp` — the **finiteness-of-monodromy** direction (`→`), proven
  unconditionally: it is pure group theory, since `Γ_r` is free of rank `r - 1`.
* `riemann_existence_cover` — the two directions assembled into the biconditional.
* `RigidityCertificate.isGeometricGaloisCover` — a rigidity certificate's generating product-one
  tuple is a surjection `SphereGroup r ↠ G`, so by RET it is realized by a geometric cover.
-/

open Polynomial

/-- `ℚ̄(T)`, the rational function field over the algebraic closure of `ℚ`: the function field
`ℳ(ℙ¹)` of `ℙ¹` over `ℚ̄`, base field of the geometric covers produced by the Riemann Existence
Theorem. -/
abbrev GeomFunctionField : Type := RatFunc (AlgebraicClosure ℚ)

/-- A group `G` is realized by a **geometric Galois cover** if there is a finite Galois extension
`L / ℚ̄(T)` with `Gal(L / ℚ̄(T)) ≃* G`.

This is side `(3)` of the Riemann Existence Theorem in its covers form: a connected Galois cover of
`ℙ¹` over the algebraically closed field `ℚ̄`, phrased algebraically as a Galois extension of the
function field `ℚ̄(T)` — through the explicit structure maps (`Algebra ℚ̄(T) L` and the group
isomorphism `(L ≃ₐ[ℚ̄(T)] L) ≃* G`), not through any category.  Connectedness is automatic (`L` is a
field) and over the algebraically closed constant field `ℚ̄` there is no further regularity
condition; the regularity / field-of-constants content is the arithmetic of the descent to `ℚ(T)`
(`IsRegularInverseGalois`), not of RET itself. -/
def IsGeometricGaloisCover (G : Type*) [Group G] : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra GeomFunctionField L)
    (_ : FiniteDimensional GeomFunctionField L) (_ : IsGalois GeomFunctionField L),
    Nonempty ((L ≃ₐ[GeomFunctionField] L) ≃* G)

/-- **Riemann Existence Theorem, the existence direction** (`←` of the covers correspondence
`(2) ↔ (3)`, algebraic incarnation over `ℚ̄`, stated through explicit maps rather than categories).

> A monodromy representation `φ : SphereGroup r ↠ G` — a surjection from the sphere group
> `SphereGroup r ≅ π₁(ℙ¹(ℂ) ∖ S)`, `|S| = r` — is realized by an actual finite Galois extension of
> `ℚ̄(T)` with group `G`.

A surjection out of `Γ_r` is the same thing as a generating product-one tuple in `G`
(`Rigidity.RET.prod_apply_sphereGroup_of`, `Rigidity.RET.closure_range_apply_sphereGroup_of`), and
such a tuple is realized as the branch cycles of a cover of the line over any prescribed `r`
distinct points — here the rational points `0, 1, …, r-1` — by
`Rigidity.RET.lineCover_exists_of_branchCycles`.  Forgetting the branch points and the inertia
leaves exactly this statement.

The images `φ (xᵢ)` are the branch-cycle / inertia generators over the `r` branch points; that they
are inertia at prescribed points is what the sharper `lineCover_exists_of_branchCycles` records and
what the branch-cycle descent (`Descent.Tower`) consumes.  See Völklein, *Groups as Galois Groups*,
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
  obtain ⟨L, e, -⟩ := Rigidity.RET.lineCover_exists_of_branchCycles _ hinj
    (fun i => φ (PresentedGroup.of i)) (Rigidity.RET.prod_apply_sphereGroup_of φ)
    (Rigidity.RET.closure_range_apply_sphereGroup_of φ hφ)
  exact ⟨L.M, L.field, L.alg, L.findim, L.isGalois, ⟨e⟩⟩

/-- The `→` direction of the covers correspondence: **every** finite Galois extension of `ℚ̄(T)`
carries a surjection from some sphere group.

Classically this is read geometrically — a finite cover of `ℙ¹` is branched over finitely many
points, so its monodromy factors through `π₁` of the complement.  Group-theoretically, however, it
needs no geometry at all: `Γ_r` is free of rank `r - 1` (`sphereGroup_mulEquiv_free`), and every
finite group is a quotient of a free group of large enough rank
(`Rigidity.RET.exists_sphereGroup_surjective`).  The hypothesis is therefore not used.

The honest consequence, recorded here rather than hidden: the right-hand side of
`riemann_existence_cover` holds for *every* finite group, so that biconditional carries exactly the
content of its `←` direction — the geometric inverse Galois problem over `ℚ̄(T)`. -/
theorem riemann_existence_cover_mp {G : Type} [Group G] [Finite G]
    (_h : IsGeometricGaloisCover G) :
    ∃ (r : ℕ) (φ : Rigidity.RET.SphereGroup r →* G), Function.Surjective φ :=
  Rigidity.RET.exists_sphereGroup_surjective

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
