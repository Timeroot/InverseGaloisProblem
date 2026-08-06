/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.AbsoluteGaloisQuotient
import InverseGalois.Rigidity.RET.KummerCover
import InverseGalois.Hilbert.AlternatingFamilyMonodromy
import InverseGalois.Hilbert.AlternatingFamilyOddDescentGeom

/-!
# The alternating and symmetric groups are geometric Galois covers

The Riemann Existence Theorem is the *general* supplier of geometric Galois covers of `ℙ¹_{ℚ̄}`:
given a surjection from a sphere group it produces a Galois extension of `ℚ̄(T)` with the
prescribed group.  For particular groups one can sometimes do better and exhibit the cover by hand,
with no analysis at all.  For the finite **abelian** groups this is the Kummer construction
(`RET.KummerAbelian`).  This file records the first **nonabelian** families: for every `n ≥ 3` both
the alternating group `Aₙ` and the symmetric group `Sₙ` are Galois groups of explicit finite
extensions of `ℚ̄(T)`.

Both extensions are already in the library, as by-products of the inverse Galois problem for `Aₙ`
over `ℚ`.  Serre's family `serreAnFamily n` has geometric monodromy exactly `Aₙ`:
`an_geometric_galois_alternating` (even `n`) and `an_geometric_galois_alternating_odd` (odd `n`)
compute the image of the permutation representation of the Galois group of the family over the
geometric base field to be the alternating group on the roots.  The shared base cover
`serreBaseGeomPoly n` that both of those descend from — the linear cover in which the parameter
enters linearly, so that Lüroth applies — has *full* symmetric monodromy
(`serreBaseGeomPoly_galActionHom_surjective`).  Since the permutation representation of a Galois
group on the roots is faithful, in each case the Galois group *is* the computed image, and the
splitting field is a geometric Galois cover.

Two pieces of plumbing carry that computation to the definition of `IsGeometricGaloisCover`.

* The geometric base field of the `Aₙ` family is `Frac(ℚ̄[X])`, whereas `GeomFunctionField` is
  `RatFunc ℚ̄`; the two are canonically isomorphic but not definitionally equal.
  `IsGaloisGroupOver.of_ringEquiv` (`Pi1/AbsoluteGaloisQuotient.lean`) transports the predicate
  along any isomorphism of base fields.
* The group of the root set has to be matched with the group of `Fin n`, which is
  `Equiv.altCongrHom` (resp. `Equiv.permCongrHom`) applied to a numbering of the `n` roots (there
  are `n` of them: the polynomials are separable of degree `n`).

## Main results

* `Rigidity.RET.isGeometricGaloisCover_alternatingGroup` — for `n ≥ 3`, `Aₙ` is realized by a
  geometric Galois cover of the line, unconditionally.
* `Rigidity.RET.isGeometricGaloisCover_perm` — the same for `Sₙ`.
* `Rigidity.RET.isGeometricGaloisCover_alternatingGroup'`,
  `Rigidity.RET.isGeometricGaloisCover_perm'` — the same statements for every `n`, the small cases
  being cyclic and so covered by the Kummer construction.
-/

open Polynomial AlternatingFamily SerreBaseCover

open scoped Classical

namespace Rigidity.RET

/-! ## The alternating groups -/

/-- `Fact` instance: any polynomial splits in its own splitting field.  Re-declared `local` (as in
the `Aₙ`-family files) so that `galActionHom` statements over the splitting field typecheck. -/
local instance splitsInSplittingField (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

/-- The geometric base field of the `Aₙ` family, `Frac(ℚ̄[X])`, is `ℚ̄(T)`. -/
noncomputable def geomFracEquiv :
    FractionRing (Polynomial (AlgebraicClosure ℚ)) ≃+* GeomFunctionField :=
  (FractionRing.algEquiv (Polynomial (AlgebraicClosure ℚ))
    (RatFunc (AlgebraicClosure ℚ))).toRingEquiv

/-- **A separable degree-`n` polynomial with alternating monodromy has Galois group `Aₙ`.**

The permutation representation of the Galois group on the roots is faithful, so the group is
isomorphic to its image, which is assumed to be the alternating group on the root set; and the root
set has `n` elements, the polynomial being separable of degree `n`. -/
theorem isGaloisGroupOver_alternating_of_range
    (p : Polynomial (FractionRing (Polynomial (AlgebraicClosure ℚ)))) (n : ℕ)
    (hsep : p.Separable) (hdeg : p.natDegree = n)
    (hrange : (Gal.galActionHom p p.SplittingField).range
      = alternatingGroup (p.rootSet p.SplittingField)) :
    IsGaloisGroupOver (FractionRing (Polynomial (AlgebraicClosure ℚ)))
      (alternatingGroup (Fin n)) := by
  haveI : IsGalois (FractionRing (Polynomial (AlgebraicClosure ℚ))) p.SplittingField :=
    IsGalois.of_separable_splitting_field (p := p) hsep
  have hcard : Fintype.card (p.rootSet p.SplittingField) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits p), hdeg]
  exact ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨((MonoidHom.ofInjective (Gal.galActionHom_injective p p.SplittingField)).trans
        (MulEquiv.subgroupCongr hrange)).trans
      (Fintype.equivFinOfCardEq hcard).altCongrHom⟩⟩

/-- **A separable degree-`n` polynomial with full monodromy has Galois group `Sₙ`.**

The permutation representation of the Galois group on the roots is faithful, so the group is
isomorphic to its image, which is assumed to be all of the permutations of the root set; and the
root set has `n` elements, the polynomial being separable of degree `n`. -/
theorem isGaloisGroupOver_perm_of_surjective
    (p : Polynomial (FractionRing (Polynomial (AlgebraicClosure ℚ)))) (n : ℕ)
    (hsep : p.Separable) (hdeg : p.natDegree = n)
    (hsurj : Function.Surjective (Gal.galActionHom p p.SplittingField)) :
    IsGaloisGroupOver (FractionRing (Polynomial (AlgebraicClosure ℚ)))
      (Equiv.Perm (Fin n)) := by
  haveI : IsGalois (FractionRing (Polynomial (AlgebraicClosure ℚ))) p.SplittingField :=
    IsGalois.of_separable_splitting_field (p := p) hsep
  have hcard : Fintype.card (p.rootSet p.SplittingField) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits p), hdeg]
  exact ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(MulEquiv.ofBijective (Gal.galActionHom p p.SplittingField)
        ⟨Gal.galActionHom_injective p p.SplittingField, hsurj⟩).trans
      (Fintype.equivFinOfCardEq hcard).permCongrHom⟩⟩

/-- **The alternating groups are geometric Galois covers**, unconditionally.

For every `n ≥ 3` the alternating group `Aₙ` is the Galois group of a finite extension of `ℚ̄(T)`:
Serre's family `serreAnFamily n` has geometric monodromy exactly `Aₙ`
(`an_geometric_galois_alternating` for even `n`, `an_geometric_galois_alternating_odd` for odd `n`),
so its splitting field over the geometric base field is such an extension.  Together with the
Kummer construction for abelian groups (`isGeometricGaloisCover_of_commGroup`) and with
`isGeometricGaloisCover_perm` this is one of the first nonabelian families of geometric covers
built without the Riemann Existence Theorem. -/
theorem isGeometricGaloisCover_alternatingGroup (n : ℕ) (hn : 3 ≤ n) :
    IsGeometricGaloisCover (alternatingGroup (Fin n)) := by
  refine (isGeometricGaloisCover_iff_isGaloisGroupOver _).mpr
    (IsGaloisGroupOver.of_ringEquiv geomFracEquiv ?_)
  rcases Nat.even_or_odd n with heven | hodd
  · exact isGaloisGroupOver_alternating_of_range (serreAnOverFrac n) n
      (serreAnOverFrac_separable n (by omega) heven) (serreAnOverFrac_natDegree n (by omega))
      (an_geometric_galois_alternating n hn heven)
  · exact isGaloisGroupOver_alternating_of_range (serreAnOverFracOdd n) n
      (serreAnOverFracOdd_separable n (by omega) hodd) (serreAnOverFracOdd_natDegree n (by omega))
      (an_geometric_galois_alternating_odd n hn hodd)

/-- **The symmetric groups are geometric Galois covers**, unconditionally.

For every `n ≥ 3` the symmetric group `Sₙ` is the Galois group of a finite extension of `ℚ̄(T)`:
the shared base cover `serreBaseGeomPoly n` of the `Aₙ`-family construction — the linear cover
attached to `serreBaseP n`, in which the parameter enters linearly — has *full* geometric monodromy
(`serreBaseGeomPoly_galActionHom_surjective`), so its splitting field over the geometric base field
is such an extension. -/
theorem isGeometricGaloisCover_perm (n : ℕ) (hn : 3 ≤ n) :
    IsGeometricGaloisCover (Equiv.Perm (Fin n)) :=
  (isGeometricGaloisCover_iff_isGaloisGroupOver _).mpr
    (IsGaloisGroupOver.of_ringEquiv geomFracEquiv
      (isGaloisGroupOver_perm_of_surjective (serreBaseGeomPoly n) n
        (serreBaseGeomPoly_separable n (by omega)) (serreBaseGeomPoly_natDegree n (by omega))
        (serreBaseGeomPoly_galActionHom_surjective n hn)))

/-! ## The small cases, and the statements for every `n` -/

/-- **The symmetric group on at most two letters is cyclic.**  It is trivial for `n ≤ 1` and of
order two for `n = 2`. -/
theorem isCyclic_perm_of_le_two {n : ℕ} (hn : n ≤ 2) : IsCyclic (Equiv.Perm (Fin n)) := by
  interval_cases n
  · infer_instance
  · infer_instance
  · exact isCyclic_of_prime_card (p := 2) (by simp [Fintype.card_perm])

/-- **The symmetric groups are geometric Galois covers, for every `n`.**

For `n ≥ 3` this is the Serre base cover; for `n ≤ 2` the group is cyclic and the cover is a Kummer
cover. -/
theorem isGeometricGaloisCover_perm' (n : ℕ) : IsGeometricGaloisCover (Equiv.Perm (Fin n)) := by
  rcases le_or_gt 3 n with hn | hn
  · exact isGeometricGaloisCover_perm n hn
  · haveI := isCyclic_perm_of_le_two (n := n) (by omega)
    exact isGeometricGaloisCover_of_isCyclic _

/-- **The alternating groups are geometric Galois covers, for every `n`.**

For `n ≥ 3` this is Serre's family; for `n ≤ 2` the alternating group is a subgroup of a cyclic
group, hence cyclic, and the cover is a Kummer cover. -/
theorem isGeometricGaloisCover_alternatingGroup' (n : ℕ) :
    IsGeometricGaloisCover (alternatingGroup (Fin n)) := by
  rcases le_or_gt 3 n with hn | hn
  · exact isGeometricGaloisCover_alternatingGroup n hn
  · haveI := isCyclic_perm_of_le_two (n := n) (by omega)
    haveI : IsCyclic (alternatingGroup (Fin n)) := inferInstance
    exact isGeometricGaloisCover_of_isCyclic _

end Rigidity.RET
