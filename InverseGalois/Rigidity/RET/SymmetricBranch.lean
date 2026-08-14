/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.ThreePointEquation
import InverseGalois.Rigidity.RET.SerreCovers

/-!
# The symmetric groups branch over three points

The cover of the line attached to the equation `g₀(X) = T` branches exactly where the fibre
degenerates, and for `g₀ = X^{n-1}(X - c)` there are only two such parameters
(`RET.ThreePointEquation`).  Serre's base cover is of that shape, and its geometric monodromy is
the *full* symmetric group (`serreBaseGeomPoly_galActionHom_surjective`).  Combining the two
computations exhibits `Sₙ` as the deck group of a cover of the line with at most two branch points
on the affine line — three on the projective line, counting infinity.

The two computations are made over base fields which are canonically isomorphic but not
definitionally equal (`Frac(ℚ̄[T])` for the monodromy, `ℚ̄(T)` for the covers), so the first half of
the file transports the Galois group of a polynomial along an isomorphism of base fields: reading
the splitting field of the transported polynomial as an extension of the old base field exhibits it
as a splitting field there too, and automorphisms cannot tell the two base fields apart.

## Main results

* `Rigidity.RET.nonempty_gal_mulEquiv_map` — the Galois group of a polynomial only depends on the
  polynomial up to an isomorphism of the base field.
* `Rigidity.RET.nonempty_gal_serreBaseGeomPoly` — the Galois group of Serre's base cover is `Sₙ`.
* `Rigidity.RET.isAffineDeckGroup_two_perm` — `Sₙ` occurs as a deck group with at most two branch
  points on the affine line, for every `n`.
-/

open Polynomial SerreBaseCover

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ### Changing the base field of a polynomial -/

section GalTransport

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra K L]

/-- **A splitting field of the renamed polynomial computes the Galois group of the original.**

If `e : F ≃+* K` and `L` splits `q.map e` over `K`, then `L` splits `q` over `F` as well, once `F`
acts on it through `e`: the two polynomials have the same image in `L`, hence the same roots there,
and the `K`-subalgebra they generate is the `F`-subalgebra they generate because `e` is onto.  An
automorphism of `L` fixing `K` pointwise fixes `F` pointwise, and conversely, so the two Galois
groups agree. -/
theorem nonempty_gal_mulEquiv_of_isSplittingField (e : F ≃+* K) (q : Polynomial F)
    [Polynomial.IsSplittingField K L (q.map (e : F →+* K))] :
    Nonempty (q.Gal ≃* (L ≃ₐ[K] L)) := by
  letI algFK : Algebra F K := (e : F →+* K).toAlgebra
  letI algFL : Algebra F L := ((algebraMap K L).comp (e : F →+* K)).toAlgebra
  haveI tower : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsurj : Function.Surjective (algebraMap F K) := e.surjective
  have hmap : q.map (algebraMap F L) = (q.map (e : F →+* K)).map (algebraMap K L) := by
    rw [Polynomial.map_map]; rfl
  have hroot : q.rootSet L = (q.map (e : F →+* K)).rootSet L := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hmap]
  have key : ∀ x ∈ Algebra.adjoin K ((q.map (e : F →+* K)).rootSet L),
      x ∈ Algebra.adjoin F ((q.map (e : F →+* K)).rootSet L) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem s hs => exact Algebra.subset_adjoin hs
    | algebraMap y =>
        obtain ⟨z, rfl⟩ := e.surjective y
        exact Subalgebra.algebraMap_mem _ z
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  haveI hsf : Polynomial.IsSplittingField F L q := by
    constructor
    · rw [hmap]; exact Polynomial.IsSplittingField.splits L (q.map (e : F →+* K))
    · rw [hroot]
      refine top_unique fun x _ => key x ?_
      rw [Polynomial.IsSplittingField.adjoin_rootSet]
      trivial
  exact ⟨((autCongrOfSurjective (K₁ := F) (K₂ := K) (L := L) hsurj).trans
    (AlgEquiv.autCongr (Polynomial.IsSplittingField.algEquiv (L := L) q))).symm⟩

/-- **The Galois group of a polynomial does not change when the base field is renamed.** -/
theorem nonempty_gal_mulEquiv_map (e : F ≃+* K) (q : Polynomial F) :
    Nonempty (q.Gal ≃* (q.map (e : F →+* K)).Gal) :=
  nonempty_gal_mulEquiv_of_isSplittingField (L := (q.map (e : F →+* K)).SplittingField) e q

end GalTransport

/-! ### Serre's base cover has symmetric deck group -/

/-- `Fact` instance: any polynomial splits in its own splitting field.  Re-declared `local` (as in
the `Aₙ`-family files) so that `galActionHom` statements over the splitting field typecheck. -/
local instance splitsInOwnSplittingField (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

/-- **The generic fibre of Serre's base family is its geometric model**, read over `ℚ̄(T)` instead
of `Frac(ℚ̄[T])`.  The isomorphism between those two fields is the identity on `ℚ̄[T]`. -/
theorem genericPoly_serreBaseC (n : ℕ) :
    genericPoly (serreBaseC n)
      = (serreBaseGeomPoly n).map (geomFracEquiv : GeomBase →+* RatFunc k) := by
  have hcomp : (geomFracEquiv : GeomBase →+* RatFunc k).comp
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase)
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) :=
    RingHom.ext fun x =>
      (FractionRing.algEquiv (Polynomial (AlgebraicClosure ℚ))
        (RatFunc (AlgebraicClosure ℚ))).commutes x
  rw [serreBaseGeomPoly, linearCoverGeom, Polynomial.map_map, hcomp]
  rfl

/-- **The Galois group of Serre's base cover is the full symmetric group.**  Its geometric
monodromy is onto (`serreBaseGeomPoly_galActionHom_surjective`), the permutation representation of
a Galois group on the roots is faithful, and there are `n` roots. -/
theorem nonempty_gal_serreBaseGeomPoly (n : ℕ) (hn : 3 ≤ n) :
    Nonempty ((serreBaseGeomPoly n).Gal ≃* Equiv.Perm (Fin n)) := by
  have hsep := serreBaseGeomPoly_separable n (by omega)
  have hcard : Fintype.card
      ((serreBaseGeomPoly n).rootSet (serreBaseGeomPoly n).SplittingField) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits _),
      serreBaseGeomPoly_natDegree n (by omega)]
  exact ⟨(MulEquiv.ofBijective (Gal.galActionHom (serreBaseGeomPoly n) _)
      ⟨Gal.galActionHom_injective _ _, serreBaseGeomPoly_galActionHom_surjective n hn⟩).trans
    (Fintype.equivFinOfCardEq hcard).permCongrHom⟩

/-- **The cover of the line defined by `serreBaseP n (X) = T` has symmetric deck group.** -/
theorem nonempty_deck_serreBaseCover (n : ℕ) (hn : 3 ≤ n) :
    Nonempty ((serreBaseCover n (by omega : 2 ≤ n)).deck ≃* Equiv.Perm (Fin n)) := by
  obtain ⟨e₁⟩ := nonempty_gal_mulEquiv_map (geomFracEquiv) (serreBaseGeomPoly n)
  obtain ⟨e₂⟩ := nonempty_gal_serreBaseGeomPoly n hn
  rw [← genericPoly_serreBaseC n] at e₁
  exact ⟨e₁.symm.trans e₂⟩

/-- **The symmetric group occurs with two branch points on the affine line**, for every `n`.

For `n ≥ 3` the cover is Serre's base cover, the splitting field of `X^{n-1}(X - c) = T`: its
fibre degenerates only at the two critical values of `X^{n-1}(X - c)`, whatever `n` is.  Counting
the point at infinity this is the classical statement that `Sₙ` is the monodromy group of a cover
of the projective line branched over three points.  For `n ≤ 2` the group is cyclic and one branch
point suffices. -/
theorem isAffineDeckGroup_two_perm (n : ℕ) : IsAffineDeckGroup 2 (Equiv.Perm (Fin n)) := by
  rcases le_or_gt 3 n with hn | hn
  · obtain ⟨e⟩ := nonempty_deck_serreBaseCover n hn
    exact (isAffineDeckGroup_serreBaseCover n (by omega)).congr e
  · exact (isAffineDeckGroup_one_iff.mpr (isCyclic_perm_of_le_two (n := n) (by omega))).mono
      (by norm_num)

end Rigidity.RET

end
