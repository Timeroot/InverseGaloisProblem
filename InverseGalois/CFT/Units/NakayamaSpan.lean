/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.BaseTateSylow
import InverseGalois.CFT.Units.IdeleClassTorsionSubgroup
import InverseGalois.CFT.Units.NsmulTorsionRep

/-!
# When the comparison of Tate and Nakayama, together with the ideles, spans

The everywhere locally trivial classes of the units of a Galois extension of number fields,
tensored with coefficients killed by a prime, are exactly the classes the comparison of Tate and
Nakayama produces from the coefficients three degrees lower, as soon as one span holds: over a
Sylow subgroup for the prime, the classes the comparison produces together with the classes coming
from the ideles fill the complete cohomology of the idele classes tensored with the coefficients.

That span is a statement about the extension, not about the coefficients: it says that the failure
of the comparison to be surjective is entirely accounted for by the places.  For coefficients that
are free as abelian groups the comparison is surjective outright and the span is automatic, which
is why the statement for a lattice needs no hypothesis at all.  For coefficients killed by a prime
the comparison acquires an error term, and the span is the assertion that the places already carry
that error.

This file names the span and records the statement it yields.  Naming it separates the part of the
theory that the general machinery of a class formation supplies from the part that is genuinely
about the arithmetic of the extension, and lets the statement be used wherever it is needed without
carrying a Sylow subgroup and a choice of coefficients through every intermediate result.

## Main definitions

* `InverseGalois.CFT.HasIdeleClassNakayamaSpanAt`: **the comparison of Tate and Nakayama over a
  Sylow subgroup, together with the classes coming from the ideles, spans the complete cohomology
  of the idele classes tensored with one fixed choice of coefficients, in one fixed degree.**  This
  is the form in which the span is used, and the form in which it is a statement about a single
  extension and a single module.
* `InverseGalois.CFT.HasIdeleClassNakayamaSpan`: the same, asked of every degree and of every
  coefficient module killed by the prime at once.

## Main results

* `InverseGalois.CFT.hasIdeleClassNakayamaSpan_of_not_dvd`: **the span holds whenever the prime
  does not divide the degree of the extension.**
* `InverseGalois.CFT.hasIdeleClassNakayamaSpan_of_isZero`: **the span holds whenever the idele
  classes killed by the prime, tensored with the coefficients, have no complete cohomology over a
  Sylow subgroup** in the degree the obstruction lands in.
* `InverseGalois.CFT.hasIdeleClassNakayamaSpan_of_isZero_idele`: **the span holds whenever the
  ideles killed by the prime and the roots of unity of the extension, each tensored with the
  coefficients, have no complete cohomology over a Sylow subgroup** in the two relevant degrees.
  The first of these two conditions is a statement about the places one at a time, so this reduces
  the span to conditions that can be read off the local extensions.
* `InverseGalois.CFT.hasIdeleClassNakayamaSpan_of_next`: **the span holds whenever the map leaving
  the comparison of Tate and Nakayama over a Sylow subgroup takes, on the classes coming from the
  ideles, every value it takes at all.**  This is the form of the span in which only a map natural
  in the coefficients appears, so the form in which the places can be brought to bear.
* `InverseGalois.CFT.range_shaTorusPTorsionMap_of_spanAt`: **the everywhere locally trivial classes
  of the units tensored with coefficients killed by a prime are exactly the classes the comparison
  of Tate and Nakayama produces**, whenever the span holds for those coefficients in that degree;
  and `InverseGalois.CFT.range_shaTorusPTorsionMap_of_span` for the span asked of everything.
* `InverseGalois.CFT.exists_shaTorusPTorsionMap_of_spanAt`: the same read as **surjectivity onto the
  everywhere locally trivial classes**; and `InverseGalois.CFT.exists_shaTorusPTorsionMap_of_span`.
* `InverseGalois.CFT.exists_shaTorusPTorsionMap_one_of_spanAt`: that surjectivity in the degree an
  embedding problem uses, from the complete cohomology of the coefficients in degree minus two onto
  the first cohomology of the units tensored with them, cut down by the local conditions; and
  `InverseGalois.CFT.exists_shaTorusPTorsionMap_one_of_span`.

## Tags

number field, idele class group, Tate-Nakayama, Sylow subgroup, locally trivial
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (p : ℕ) [Fact p.Prime]

/-- **The comparison of Tate and Nakayama for the idele class group and the fundamental class, read
over a Sylow subgroup for a prime, together with the classes coming from the ideles, spans the
complete cohomology of the idele classes tensored with one fixed choice of coefficients, in one
fixed degree.**  The comparison is surjective on coefficients that are free as abelian groups; on
coefficients killed by a prime it need not be, and the span says the shortfall comes from the
places.  Whether it does is a joint condition on the extension, the coefficients and the degree:
for coefficients on which the Galois group acts trivially the comparison factors through the
ideles and the span reduces to a statement about the extension alone. -/
def HasIdeleClassNakayamaSpanAt (W : Rep ℤ Gal(K/k)) (n : ℤ) : Prop :=
  ∀ P : Sylow p Gal(K/k),
    LinearMap.range (resTateNakayamaTwoMap (P : Subgroup Gal(K/k)) (ideleClassRep k K)
        (baseFundamentalClass k K) W n)
      ⊔ LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
        (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom = ⊤

/-- **The comparison of Tate and Nakayama over a Sylow subgroup for a prime, together with the
classes coming from the ideles, spans the complete cohomology of the idele classes tensored with
any coefficients killed by that prime, in every degree.**  This is the span asked of everything at
once; the statements that use it use it at a single module and a single degree, for which
`HasIdeleClassNakayamaSpanAt` is the right shape. -/
def HasIdeleClassNakayamaSpan : Prop :=
  ∀ W : Rep ℤ Gal(K/k), (∀ w : ↥W.V, p • w = 0) → ∀ n : ℤ,
    HasIdeleClassNakayamaSpanAt k K p W n

variable {k K p}

/-- **The span holds whenever the prime does not divide the degree of the extension.**  A Sylow
subgroup for a prime that does not divide the order of the group is trivial, and the order of a
group annihilates its complete cohomology, so every module read over that subgroup vanishes and
there is nothing left to span. -/
theorem hasIdeleClassNakayamaSpan_of_not_dvd (hp : ¬ p ∣ Nat.card Gal(K/k)) :
    HasIdeleClassNakayamaSpan k K p := by
  intro W _ n P
  have hdvd : Nat.card ↥(P : Subgroup Gal(K/k)) ∣ Nat.card Gal(K/k) :=
    Subgroup.card_subgroup_dvd_card _
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have hcard : Nat.card ↥(P : Subgroup Gal(K/k)) = 1 := by
    rcases m with _ | m
    · simpa using hm
    · exact absurd (dvd_trans (dvd_pow_self p (Nat.succ_ne_zero m)) (hm ▸ hdvd)) hp
  refine Submodule.eq_top_iff'.2 fun x => ?_
  have hx : x = 0 := by
    have hz := card_nsmul_eq_zero_tateModule _ _ x
    rwa [hcard, one_nsmul] at hz
  subst hx
  exact Submodule.zero_mem _

/-- **The span holds whenever the idele classes killed by the prime, tensored with the
coefficients, have no complete cohomology over a Sylow subgroup for the prime** in the degree the
obstruction of Tate and Nakayama lands in.  There the obstruction is the zero map, so the
comparison of Tate and Nakayama is already surjective and the ideles are not needed at all. -/
theorem hasIdeleClassNakayamaSpan_of_isZero
    (h : ∀ W : Rep ℤ Gal(K/k), (∀ w : ↥W.V, p • w = 0) → ∀ (P : Sylow p Gal(K/k)) (n : ℤ),
      Limits.IsZero (tateModule (resObj (P : Subgroup Gal(K/k))
        (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W)) (n + 1 + 1 + 1 + 1))) :
    HasIdeleClassNakayamaSpan k K p := by
  intro W hW n P
  have hz : Limits.IsZero (tateModule (tensorObj
      (nsmulTorsion (resObj (P : Subgroup Gal(K/k)) (ideleClassRep k K)) p)
      (resObj (P : Subgroup Gal(K/k)) W)) (n + 1 + 1 + 1 + 1)) :=
    isZero_tateModule_tensorObj_nsmulTorsion_repOfAddAut
      ((ideleClassAutHom k K).comp (P : Subgroup Gal(K/k)).subtype) p
      (resObj (P : Subgroup Gal(K/k)) W) (n + 1 + 1 + 1 + 1) (h W hW P n)
  have hker : LinearMap.ker
      (resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n) = ⊤ :=
    Submodule.eq_top_iff'.2 fun x => LinearMap.mem_ker.2 (eq_zero_of_isZero hz _)
  rw [← ker_resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n, hker, top_sup_eq]

/-- **The span holds whenever the ideles killed by the prime and the roots of unity of the
extension, each tensored with the coefficients, have no complete cohomology over a Sylow subgroup
for the prime** in the two relevant degrees.  The idele classes killed by the prime sit between
those two groups, so their complete cohomology is squeezed to nothing, and the obstruction of Tate
and Nakayama has nowhere to go.  The condition on the ideles is a condition on the places one at a
time, so this reduces the span to data read off the local extensions. -/
theorem hasIdeleClassNakayamaSpan_of_isZero_idele
    (hI : ∀ W : Rep ℤ Gal(K/k), (∀ w : ↥W.V, p • w = 0) → ∀ (P : Sylow p Gal(K/k)) (n : ℤ),
      Limits.IsZero (tateModule (resObj (P : Subgroup Gal(K/k))
        (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W)) (n + 1 + 1 + 1 + 1)))
    (hU : ∀ W : Rep ℤ Gal(K/k), (∀ w : ↥W.V, p • w = 0) → ∀ (P : Sylow p Gal(K/k)) (n : ℤ),
      Limits.IsZero (tateModule (resObj (P : Subgroup Gal(K/k))
        (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W))
          (n + 1 + 1 + 1 + 1 + 1))) :
    HasIdeleClassNakayamaSpan k K p :=
  hasIdeleClassNakayamaSpan_of_isZero fun W hW P n =>
    isZero_tateModule_tensor_ideleClassTorsionRes (Fact.out : p.Prime) W
      (P : Subgroup Gal(K/k)) (n + 1 + 1 + 1 + 1) (hI W hW P n) (hU W hW P n)

/-- **The span holds whenever the map leaving the comparison of Tate and Nakayama over a Sylow
subgroup for the prime takes, on the classes coming from the ideles, every value it takes at all.**
The classes the comparison produces are exactly those the map leaving it kills, so a spanning
statement about the comparison is a statement about the values of that map; and the map leaving the
comparison is natural in the representation, so unlike the comparison itself its values can be
compared with local ones. -/
theorem hasIdeleClassNakayamaSpan_of_next
    (h : ∀ W : Rep ℤ Gal(K/k), (∀ w : ↥W.V, p • w = 0) → ∀ (P : Sylow p Gal(K/k)) (n : ℤ),
      Submodule.map
          (tateNakayamaTwoNextMap (resObj (P : Subgroup Gal(K/k)) (ideleClassRep k K))
            (tateRes (P : Subgroup Gal(K/k)) (ideleClassRep k K) 2 (baseFundamentalClass k K))
            (resObj (P : Subgroup Gal(K/k)) W) n)
          (LinearMap.range (tateMap (resHom (P : Subgroup Gal(K/k))
            (tensorHomLeft W (ideleToIdeleClass k K))) (n + 1 + 1)).hom)
        = LinearMap.range
          (tateNakayamaTwoNextMap (resObj (P : Subgroup Gal(K/k)) (ideleClassRep k K))
            (tateRes (P : Subgroup Gal(K/k)) (ideleClassRep k K) 2 (baseFundamentalClass k K))
            (resObj (P : Subgroup Gal(K/k)) W) n)) :
    HasIdeleClassNakayamaSpan k K p := by
  intro W hW n P
  rw [← ker_resBaseTateNakayamaPTorsionRight k K W hW (P : Subgroup Gal(K/k)) n, sup_comm]
  exact (map_eq_range_iff_sup_ker_eq_top _ _).1
    ((map_resBaseTateNakayamaPTorsionRight_eq_range_iff k K W hW (P : Subgroup Gal(K/k)) n _).2
      (h W hW P n))

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**,
whenever the comparison of Tate and Nakayama over a Sylow subgroup for the prime spans, for those
coefficients and in that degree, together with the classes coming from the ideles.  A Sylow
subgroup exists because the Galois group is finite, so the span may be applied to any one of
them. -/
theorem range_shaTorusPTorsionMap_of_spanAt (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)
    (n : ℤ) (h : HasIdeleClassNakayamaSpanAt k K p W n) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom := by
  obtain ⟨P⟩ : Nonempty (Sylow p Gal(K/k)) := inferInstance
  exact range_shaTorusPTorsionMap_of_sylow_nakayama k K W hW P n (h P)

/-- **The everywhere locally trivial classes of the units tensored with coefficients killed by a
prime are exactly the image of the complete cohomology of the coefficients three degrees lower**,
whenever the span holds for every choice of coefficients and every degree. -/
theorem range_shaTorusPTorsionMap_of_span (h : HasIdeleClassNakayamaSpan k K p)
    (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0) (n : ℤ) :
    LinearMap.range (shaTorusPTorsionMap k K W hW n)
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1)).hom :=
  range_shaTorusPTorsionMap_of_spanAt W hW n (h W hW n)

/-- **Every everywhere locally trivial class of the units tensored with coefficients killed by a
prime comes from the complete cohomology of the coefficients three degrees lower**, whenever the
span holds for those coefficients in that degree.  This is the surjectivity the statement is used
for. -/
theorem exists_shaTorusPTorsionMap_of_spanAt (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)
    (n : ℤ) (h : HasIdeleClassNakayamaSpanAt k K p W n)
    (x : ↥(tateModule (tensorObj (globalUnitsRep k K) W) (n + 1 + 1 + 1)))
    (hx : tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1) x = 0) :
    ∃ y : ↥(tateModule W n), shaTorusPTorsionMap k K W hW n y = x := by
  have hmem : x ∈ LinearMap.range (shaTorusPTorsionMap k K W hW n) := by
    rw [range_shaTorusPTorsionMap_of_spanAt W hW n h]
    exact hx
  exact hmem

/-- **Every everywhere locally trivial class of the units tensored with coefficients killed by a
prime comes from the complete cohomology of the coefficients three degrees lower**, whenever the
span holds for every choice of coefficients and every degree. -/
theorem exists_shaTorusPTorsionMap_of_span (h : HasIdeleClassNakayamaSpan k K p)
    (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0) (n : ℤ)
    (x : ↥(tateModule (tensorObj (globalUnitsRep k K) W) (n + 1 + 1 + 1)))
    (hx : tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1 + 1 + 1) x = 0) :
    ∃ y : ↥(tateModule W n), shaTorusPTorsionMap k K W hW n y = x :=
  exists_shaTorusPTorsionMap_of_spanAt W hW n (h W hW n) x hx

/-- **Every class of the units tensored with coefficients killed by a prime which is trivial in the
ideles comes from the complete cohomology of the coefficients in degree minus two**, whenever the
span holds for those coefficients in degree minus two.  This is the reading of the statement in the
degree in which an embedding problem uses it: the first cohomology of the units tensored with the
coefficients, cut down by the local conditions, is reached from two degrees below zero. -/
theorem exists_shaTorusPTorsionMap_one_of_spanAt (W : Rep ℤ Gal(K/k))
    (hW : ∀ w : ↥W.V, p • w = 0) (h : HasIdeleClassNakayamaSpanAt k K p W (-2))
    (x : ↥(tateModule (tensorObj (globalUnitsRep k K) W) 1))
    (hx : tateMap (tensorHomLeft W (globalUnitsToIdele k K)) 1 x = 0) :
    ∃ y : ↥(tateModule W (-2)), shaTorusPTorsionMap k K W hW (-2) y = x := by
  refine exists_shaTorusPTorsionMap_of_spanAt W hW (-2) h ?_ ?_
  exact hx

/-- **Every class of the units tensored with coefficients killed by a prime which is trivial in the
ideles comes from the complete cohomology of the coefficients in degree minus two**, whenever the
span holds for every choice of coefficients and every degree. -/
theorem exists_shaTorusPTorsionMap_one_of_span (h : HasIdeleClassNakayamaSpan k K p)
    (W : Rep ℤ Gal(K/k)) (hW : ∀ w : ↥W.V, p • w = 0)
    (x : ↥(tateModule (tensorObj (globalUnitsRep k K) W) 1))
    (hx : tateMap (tensorHomLeft W (globalUnitsToIdele k K)) 1 x = 0) :
    ∃ y : ↥(tateModule W (-2)), shaTorusPTorsionMap k K W hW (-2) y = x :=
  exists_shaTorusPTorsionMap_one_of_spanAt W hW (h W hW (-2)) x hx

end

end InverseGalois.CFT
