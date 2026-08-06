/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.AbsoluteGaloisQuotient

/-!
# Artin's theorem as a supplier of Galois groups

Artin's theorem says that a faithful action of a finite group `G` on a field `L` makes `L` a Galois
extension of its fixed field `L^G`, with Galois group exactly `G`.  Read as a statement about the
predicate `IsGaloisGroupOver`, it turns *any* faithful finite action on a field into a realization
of that group as a Galois group — the group is prescribed and the base field is whatever the
invariants turn out to be.

This is the engine behind every "explicit cover" construction: to realize `G` as a geometric Galois
cover of the line one exhibits `G` acting faithfully on `ℚ̄(u)` — a group of Möbius transformations,
say — and then identifies the field of invariants with `ℚ̄(T)`.  The identification of the
invariants is the whole difficulty; Artin's theorem supplies everything else, in particular the
inequality `[L : L^G] = |G|` that pins the degree.

Mathlib's `Mathlib/FieldTheory/Fixed.lean` proves the hard parts: `FixedPoints.normal`,
`FixedPoints.isSeparable`, the finite-dimensionality of `L` over `L^G`, and the isomorphism
`FixedPoints.toAlgAutMulEquiv : G ≃* (L ≃ₐ[L^G] L)`.  This file packages them in the shape the
Riemann Existence workstream consumes.

## Main results

* `Rigidity.RET.isGaloisGroupOver_fixedPoints` — a faithful action of a finite group `G` on a field
  `L` realizes `G` as a Galois group over the fixed field `L^G`.
* `Rigidity.RET.isGaloisGroupOver_of_fixedPoints_ringEquiv` — the same, transported along an
  identification of the fixed field with a given base field.
* `Rigidity.RET.isGeometricGaloisCover_of_fixedPoints` — the geometric case: a faithful action on a
  field whose invariants are `ℚ̄(T)` exhibits `G` as a geometric Galois cover of the line.
* `Rigidity.RET.finrank_fixedPoints_eq_card` — `[L : L^G] = |G|`.
* `Rigidity.RET.fixedPoints_eq_of_finrank_le` — a subfield of the invariants over which the degree
  is at most `|G|` is the whole field of invariants.
* `Rigidity.RET.isGeometricGaloisCover_of_invariant_subfield` — the two combined: a faithful action,
  an invariant subfield isomorphic to `ℚ̄(T)`, and the degree bound give a geometric Galois cover.
-/

namespace Rigidity.RET

/-- **Artin's theorem: a faithful finite action realizes its group over the invariants.**

If a finite group `G` acts faithfully by ring automorphisms on a field `L`, then `L` is a finite
Galois extension of the subfield `L^G` of invariants and its Galois group is `G` itself. -/
theorem isGaloisGroupOver_fixedPoints (G : Type) [Group G] [Finite G] (L : Type) [Field L]
    [MulSemiringAction G L] [FaithfulSMul G L] :
    IsGaloisGroupOver (FixedPoints.subfield G L) G :=
  ⟨L, inferInstance, inferInstance, inferInstance, ⟨⟩,
    ⟨(FixedPoints.toAlgAutMulEquiv G L).symm⟩⟩

/-- **Artin's theorem over a prescribed base field.**

An identification `e : L^G ≃+* K` of the invariants of a faithful finite action with a field `K`
realizes the acting group as a Galois group over `K`. -/
theorem isGaloisGroupOver_of_fixedPoints_ringEquiv {G : Type} [Group G] [Finite G] (L : Type)
    [Field L] [MulSemiringAction G L] [FaithfulSMul G L] {K : Type} [Field K]
    (e : FixedPoints.subfield G L ≃+* K) :
    IsGaloisGroupOver K G :=
  IsGaloisGroupOver.of_ringEquiv e (isGaloisGroupOver_fixedPoints G L)

/-- **Explicit geometric covers from invariant theory.**

A finite group acting faithfully on a field whose invariants are the geometric function field
`ℚ̄(T)` is realized by a geometric Galois cover of the line: the cover is the field itself, and the
covering group is the acting group.  This is how one produces covers by hand — the group of
automorphisms of the parameter is prescribed and the base is recovered as the field of invariant
functions. -/
theorem isGeometricGaloisCover_of_fixedPoints {G : Type} [Group G] [Finite G] (L : Type) [Field L]
    [MulSemiringAction G L] [FaithfulSMul G L]
    (e : FixedPoints.subfield G L ≃+* GeomFunctionField) :
    IsGeometricGaloisCover G :=
  isGaloisGroupOver_of_fixedPoints_ringEquiv L e

/-! ## Pinning the field of invariants by a degree bound -/

section Pinning

variable {G : Type} [Group G] [Finite G] {L : Type} [Field L] [MulSemiringAction G L]
  [FaithfulSMul G L]

/-- **The degree of a field over the invariants of a faithful finite action is the order of the
group** (Artin).  Restatement of `FixedPoints.finrank_eq_card` with `Nat.card`. -/
theorem finrank_fixedPoints_eq_card (G : Type) [Group G] [Finite G] (L : Type) [Field L]
    [MulSemiringAction G L] [FaithfulSMul G L] :
    Module.finrank (FixedPoints.subfield G L) L = Nat.card G := by
  haveI := Fintype.ofFinite G
  rw [FixedPoints.finrank_eq_card G L, Nat.card_eq_fintype_card]

/-- **A subfield of the invariants over which the degree is at most `|G|` *is* the invariants.**

This is the practical form of Artin's theorem for identifying a field of invariants: one exhibits
a subfield `K` of invariant elements — typically generated by one explicit invariant function —
and bounds `[L : K]` by `|G|`, usually by writing down a polynomial of that degree over `K` with
`L = K(u)` as a root.  Since `[L : L^G] = |G|` exactly, the bound leaves no room and `K` is the
whole field of invariants. -/
theorem fixedPoints_eq_of_finrank_le (K : Subfield L) (hK : K ≤ FixedPoints.subfield G L)
    [FiniteDimensional K L] (h : Module.finrank K L ≤ Nat.card G) :
    K = FixedPoints.subfield G L := by
  set F := FixedPoints.subfield G L with hFdef
  letI : Algebra K F := (Subfield.inclusion hK).toAlgebra
  haveI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K F := Module.Finite.left K F L
  have hcard : 0 < Nat.card G := Nat.card_pos
  have htower : Module.finrank K F * Module.finrank F L = Module.finrank K L :=
    Module.finrank_mul_finrank ↥K ↥F L
  have hFL : Module.finrank F L = Nat.card G := finrank_fixedPoints_eq_card G L
  have hle : Module.finrank K F * Nat.card G ≤ 1 * Nat.card G := by
    have heq : Module.finrank K F * Nat.card G = Module.finrank K L := by rw [← hFL, htower]
    rw [heq, one_mul]; exact h
  have h1 : Module.finrank K F = 1 :=
    le_antisymm (Nat.le_of_mul_le_mul_right hle hcard) Module.finrank_pos
  refine le_antisymm hK fun y hy => ?_
  obtain ⟨c, hc⟩ := (_root_.finrank_eq_one_iff_of_nonzero' (1 : F) one_ne_zero).mp h1 ⟨y, hy⟩
  have hcv : ((c : L)) = y := by
    have hval := congrArg (Subtype.val) hc
    simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Subfield.inclusion,
      RingHom.codRestrict] using hval
  exact hcv ▸ c.2

/-- **Explicit geometric covers, in the form a construction actually produces them.**

To exhibit a finite group `G` as a geometric Galois cover of the line it suffices to give: a
faithful action of `G` on a field `L`, a subfield `K` of invariant elements which is isomorphic to
`ℚ̄(T)`, and a bound `[L : K] ≤ |G|`.  The bound forces `K` to be *all* the invariants, and Artin's
theorem does the rest.  In practice `K` is generated by one invariant function `w` and the bound
comes from an explicit degree-`|G|` polynomial over `K` satisfied by a generator of `L`. -/
theorem isGeometricGaloisCover_of_invariant_subfield (K : Subfield L)
    (hK : K ≤ FixedPoints.subfield G L) [FiniteDimensional K L]
    (h : Module.finrank K L ≤ Nat.card G) (e : K ≃+* GeomFunctionField) :
    IsGeometricGaloisCover G :=
  isGeometricGaloisCover_of_fixedPoints L (fixedPoints_eq_of_finrank_le K hK h ▸ e)

end Pinning

end Rigidity.RET
