/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Resolvent.ResolventFamily
import InverseGalois.Rigidity.RET.RegularResolvent
import InverseGalois.Rigidity.RET.Specialization

/-!
# The symmetric groups are regular inverse Galois groups

The Morse family `Xⁿ − X − T` has generic Galois group the full symmetric group on `n` letters,
and the resolvent machinery of `InverseGalois.Resolvent` already produces the certificate for it:
a monic `G ∈ ℚ[T][Y]` of degree `n!` which is the generic linear resolvent of `Xⁿ − X − T` and
which stays irreducible after base change to `ℚ̄(T)`.  Specializing that certificate at rational
parameters is how the symmetric groups were realized over `ℚ`; read over `ℚ(T)` instead, it
realizes them *regularly*.

Two things have to be produced over the generic point.  The first is a root of the resolvent in
the splitting field of the family over `ℚ(T)`: the defining property of a generic linear resolvent
is a descent identity valid for *every* field into which the family splits, so it applies verbatim
to the generic splitting field, and the resolvent becomes the product of the linear forms
`∑ᵢ i·x_{σ i}` over all permutations `σ` — each of which is a root.  The second is the landing
certificate, and here nothing has to be computed at all: the Galois group of the splitting field
of a degree-`n` polynomial permutes its `n` roots faithfully.

## Main results

* `Rigidity.RET.generic_resolvent_root` — a generic linear resolvent has a root in the splitting
  field of its family over `ℚ(T)`.
* `Rigidity.RET.isRegularInverseGalois_perm_fin` — the symmetric group on `n` letters is a regular
  inverse Galois group, for every `n`.
* `Rigidity.RET.isInverseGalois_perm_fin` — and hence a Galois group over `ℚ`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-- The geometric base field `ℚ̄(T)`, as the fraction field of the polynomial ring over the
algebraic closure of the rationals. -/
local notation "ℚ̄T" => FractionRing (Polynomial (AlgebraicClosure ℚ))

/-! ## The generic root of a resolvent -/

/-- **A generic linear resolvent has a root over the generic point.**

The descent identity defining a generic linear resolvent holds for every field in which the
family splits, so in particular for the splitting field of the family over `ℚ(T)`.  There the
resolvent factors into the linear forms attached to the permutations of the roots, and the form
attached to the identity permutation is a root of it. -/
theorem generic_resolvent_root (F G : ℚ[X][X]) (hF : F.Monic) (n : ℕ) (hFdeg : F.natDegree = n)
    (hG : ResolventFamily.IsFullResolvent n F G) :
    ∃ α : (F.map (algebraMap ℚ[X] (RatFunc ℚ))).SplittingField,
      (aeval α) (G.map (algebraMap ℚ[X] (RatFunc ℚ))) = 0 := by
  classical
  set f : (RatFunc ℚ)[X] := F.map (algebraMap ℚ[X] (RatFunc ℚ)) with hf
  set L := f.SplittingField with hL
  set ev : ℚ[X] →+* L := (algebraMap (RatFunc ℚ) L).comp (algebraMap ℚ[X] (RatFunc ℚ)) with hev
  have hmapev : F.map ev = f.map (algebraMap (RatFunc ℚ) L) := (Polynomial.map_map _ _ _).symm
  have hsplit : (f.map (algebraMap (RatFunc ℚ) L)).Splits := SplittingField.splits f
  have hdeg : (F.map ev).natDegree = n := by rw [hF.natDegree_map, hFdeg]
  have hcard : (F.map ev).roots.card = n := by
    rw [hmapev, Polynomial.splits_iff_card_roots.mp hsplit, ← hmapev, hdeg]
  obtain ⟨x, hx⟩ := ResolventConstruction.exists_fin_map_eq (F.map ev).roots n hcard
  have hGmap : G.map ev = ResolventFamily.fullResolventProduct n x := hG ev x hdeg hx.symm
  refine ⟨ResolventFamily.genForm n x 1, ?_⟩
  have h0 : Polynomial.eval (ResolventFamily.genForm n x 1)
      (ResolventFamily.fullResolventProduct n x) = 0 := by
    rw [ResolventFamily.fullResolventProduct,
      Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
    simp
  calc (aeval (ResolventFamily.genForm n x 1)) (G.map (algebraMap ℚ[X] (RatFunc ℚ)))
      = Polynomial.eval (ResolventFamily.genForm n x 1) (G.map ev) := by
        rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map]
    _ = 0 := by rw [hGmap]; exact h0

/-! ## The landing certificate -/

/-- **The Galois group of a splitting field embeds in the permutations of `Fin n`** when the
polynomial is separable of degree `n`: it permutes the root set faithfully, and the root set has
exactly `n` elements. -/
theorem exists_injective_galActionHom {p : (RatFunc ℚ)[X]} (hsep : p.Separable) {n : ℕ}
    (hdeg : p.natDegree = n) :
    ∃ φ : (p.SplittingField ≃ₐ[RatFunc ℚ] p.SplittingField) →* Equiv.Perm (Fin n),
      Function.Injective φ := by
  classical
  haveI : Fact ((p.map (algebraMap (RatFunc ℚ) p.SplittingField)).Splits) :=
    ⟨SplittingField.splits p⟩
  have hcard : Fintype.card (p.rootSet p.SplittingField) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits p), hdeg]
  let e : (p.rootSet p.SplittingField) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨(Equiv.permCongrHom e).toMonoidHom.comp (Gal.galActionHom p p.SplittingField), ?_⟩
  exact (Equiv.permCongrHom e).injective.comp (Gal.galActionHom_injective p p.SplittingField)

/-! ## The symmetric groups -/

/-- The two descriptions of the geometric base change of `ℚ[T]` agree. -/
theorem toClosureFrac_eq : ResolventFamily.toClosureFrac = toClosureFrac := rfl

/-- **The symmetric group on `n ≥ 2` letters is a regular inverse Galois group**, realized by the
splitting field of the Morse family `Xⁿ − X − T` over `ℚ(T)`. -/
theorem isRegularInverseGalois_perm_fin_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    IsRegularInverseGalois (Equiv.Perm (Fin n)) := by
  classical
  obtain ⟨G, hGmonic, hGdeg, hGfr, -⟩ := ResolventFamily.exists_fullResolvent n hn
  have hFmonic : (ResolventFamily.genPoly n).Monic := ResolventFamily.genPoly_monic n hn
  have hFdeg : (ResolventFamily.genPoly n).natDegree = n := ResolventFamily.genPoly_natDegree n hn
  set f : (RatFunc ℚ)[X] := (ResolventFamily.genPoly n).map (algebraMap ℚ[X] (RatFunc ℚ)) with hf
  -- the geometric base change of `ℚ(T)` restricts to the geometric base change of `ℚ[T]`
  have hcomp : (algebraMap (RatFunc ℚ) ℚ̄T).comp (algebraMap ℚ[X] (RatFunc ℚ)) = toClosureFrac :=
    RingHom.ext algebraMap_ratFunc_geom_comp
  -- the family is irreducible over `ℚ(T)`, hence separable
  have hfirr : Irreducible f :=
    Monic.irreducible_of_irreducible_map (algebraMap (RatFunc ℚ) ℚ̄T) f (hFmonic.map _)
      (by
        rw [hf, Polynomial.map_map, hcomp, ← toClosureFrac_eq]
        exact ResolventFamily.morseOverFrac_irreducible n hn)
  have hfsep : f.Separable := hfirr.separable
  haveI : IsGalois (RatFunc ℚ) f.SplittingField := IsGalois.of_separable_splitting_field hfsep
  -- the landing certificate
  obtain ⟨φ, hφ⟩ := exists_injective_galActionHom hfsep (n := n) (by rw [hf, hFmonic.natDegree_map,
    hFdeg])
  -- the resolvent is absolutely irreducible over the geometric base field
  have hGabs : Irreducible (G.map toClosureFrac) := by
    have habs : Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :=
      ResolventFamily.fullResolvent_abs_irreducible n hn G hGmonic hGfr
    have hmap := (hGmonic.map
      (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).irreducible_iff_irreducible_map_fraction_map
      (K := ℚ̄T) |>.mp habs
    rwa [Polynomial.map_map] at hmap
  -- the generic root
  obtain ⟨α, hα⟩ := generic_resolvent_root (ResolventFamily.genPoly n) G hFmonic n hFdeg hGfr
  refine IsRegularInverseGalois.of_embeds_and_root f.SplittingField G hGmonic ?_ hGabs α hα φ hφ
  rw [hGdeg, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- **The symmetric group on `n` letters is a regular inverse Galois group**, for every `n`.  For
`n ≤ 1` the group is trivial; otherwise the Morse family `Xⁿ − X − T` realizes it over `ℚ(T)`. -/
theorem isRegularInverseGalois_perm_fin (n : ℕ) : IsRegularInverseGalois (Equiv.Perm (Fin n)) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · haveI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    exact IsRegularInverseGalois.of_subsingleton
  · exact isRegularInverseGalois_perm_fin_of_two_le n h

/-- **The symmetric group on `n` letters is a Galois group over the rationals**, for every `n`. -/
theorem isInverseGalois_perm_fin (n : ℕ) : IsInverseGalois (Equiv.Perm (Fin n)) :=
  (isRegularInverseGalois_perm_fin n).isInverseGalois

end Rigidity.RET
