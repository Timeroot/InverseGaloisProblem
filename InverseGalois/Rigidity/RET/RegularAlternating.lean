/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Hilbert.Alternating
import InverseGalois.Rigidity.RET.MobiusFinite
import InverseGalois.Rigidity.RET.RegularResolvent
import InverseGalois.Rigidity.RET.RegularSymmetric

/-!
# The alternating groups are regular inverse Galois groups

Serre's square-discriminant families (`AlternatingFamily.serreAnFamily` for even `n`, the conic
family `AlternatingFamily.serreAnFamilyOdd` for odd `n`) were built to realize `Aₙ` over `ℚ` by
specializing the parameter.  Read over the generic point `ℚ(T)` instead, the very same data
realizes `Aₙ` *regularly*, through the resolvent criterion
`IsRegularInverseGalois.of_embeds_and_root`.

Three ingredients are needed over `ℚ(T)`, and each is already available in a form general enough
to be read there rather than at a rational parameter.

* The **landing certificate** `Gal(f) ↪ Aₙ` comes from the discriminant being a square: the
  identity `discSq x = ev(Δ)²` holds for *every* evaluation of the coefficient ring into a field
  in which the family splits, so it holds at the generic splitting field, with
  `Δ = serreAnDeltaPoly n` (resp. `serreAnDeltaPolyOdd n`) read in `ℚ(T)`.

* The **root of the resolvent** comes from the descent identity `IsAltResolvent`, which is also
  quantified over all such evaluations: at the generic splitting field the resolvent becomes the
  product of the linear forms attached to the *even* permutations of the roots, and the form
  attached to the identity is a root of it.

* The **absolute irreducibility** of the resolvent over `ℚ̄(T)` is the geometric monodromy
  computation `AlternatingFamily.anResolvent_abs_irreducible`, transported from `ℚ̄[T]` to `ℚ̄(T)`
  by Gauss' lemma.

## Main results

* `Rigidity.RET.generic_alt_resolvent_root` — an alternating-orbit resolvent has a root in the
  splitting field of its family over `ℚ(T)`.
* `Rigidity.RET.isRegularInverseGalois_alternating_of_family` — the assembled criterion, taking a
  square-discriminant family together with its resolvent.
* `Rigidity.RET.isRegularInverseGalois_alternatingGroup` — the alternating group on `n` letters is
  a regular inverse Galois group, for every `n`.
* `Rigidity.RET.isInverseGalois_alternatingGroup` — and hence a Galois group over `ℚ`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-- The geometric base field `ℚ̄(T)`, as the fraction field of the polynomial ring over the
algebraic closure of the rationals. -/
local notation "ℚ̄T" => FractionRing (Polynomial (AlgebraicClosure ℚ))

/-! ## Enumerating the roots over the splitting field -/

/-- **A root-set equivalence enumerates the root multiset.**  For a separable polynomial the roots
in the splitting field are distinct, so the multiset of roots is exactly the image of a bijection
`Fin n ≃ rootSet`. -/
theorem roots_eq_map_rootSetEquiv {K : Type*} [Field K] {f : K[X]} (hsep : f.Separable)
    {n : ℕ} (v : Fin n ≃ f.rootSet f.SplittingField) :
    (f.map (algebraMap K f.SplittingField)).roots
      = Finset.univ.val.map (fun i ↦ (v i : f.SplittingField)) := by
  classical
  have hnd : (f.map (algebraMap K f.SplittingField)).roots.Nodup := nodup_roots hsep.map
  have hnd2 : (Finset.univ.val.map (fun i ↦ (v i : f.SplittingField))).Nodup :=
    Multiset.Nodup.map (fun i j h ↦ v.injective (Subtype.ext h)) Finset.univ.nodup
  refine (Multiset.Nodup.ext hnd hnd2).mpr fun a ↦ ?_
  have hmem : a ∈ (f.map (algebraMap K f.SplittingField)).roots
      ↔ a ∈ f.rootSet f.SplittingField := by
    simp only [mem_rootSet', mem_roots', IsRoot.def, aeval_def, eval_map]
  rw [hmem]
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := v.surjective ⟨a, ha⟩
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), by rw [hi]⟩
  · intro ha
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp ha
    exact hi ▸ (v i).2

/-! ## The generic root of an alternating-orbit resolvent -/

/-- **An alternating-orbit resolvent has a root over the generic point.**

The descent identity defining such a resolvent holds for every field in which the family splits,
so in particular for the splitting field of the family over `ℚ(T)`.  There the resolvent factors
into the linear forms attached to the even permutations of the roots, and the form attached to the
identity permutation is a root of it. -/
theorem generic_alt_resolvent_root (F G : ℚ[X][X]) (hF : F.Monic) (n : ℕ) (hFdeg : F.natDegree = n)
    (hG : AlternatingFamily.IsAltResolvent n F G) :
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
  obtain ⟨x', -, hGmap⟩ := hG ev x hdeg hx.symm
  refine ⟨ResolventFamily.genForm n x' 1, ?_⟩
  calc (aeval (ResolventFamily.genForm n x' 1)) (G.map (algebraMap ℚ[X] (RatFunc ℚ)))
      = Polynomial.eval (ResolventFamily.genForm n x' 1) (G.map ev) := by
        rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map]
    _ = 0 := by
        rw [hGmap]
        exact AlternatingResolvent.altResolventProduct_isRoot_genForm_one n x'

/-! ## The criterion -/

/-- **A square-discriminant family with an absolutely irreducible orbit resolvent realizes `Aₙ`
regularly.**

The hypotheses are exactly the generic reading of the data that
`IsInverseGalois.of_regular_family` consumes at a rational parameter: `F` is a monic degree-`n`
family whose base change to `ℚ(T)` is separable and whose discriminant is identically the square
of `Δ ∈ ℚ[T]`, and `G` is its monic degree-`n!/2` alternating-orbit resolvent, absolutely
irreducible over `ℚ̄(T)`. -/
theorem isRegularInverseGalois_alternating_of_family (n : ℕ) (hn : 2 ≤ n)
    (F G : ℚ[X][X]) (hFmonic : F.Monic) (hFdeg : F.natDegree = n)
    (hsep : (F.map (algebraMap ℚ[X] (RatFunc ℚ))).Separable) (Δ : ℚ[X])
    (hdisc : ∀ {A : Type} [Field A] (ev : ℚ[X] →+* A) (x : Fin n → A),
      (F.map ev).natDegree = n → (F.map ev).roots = Finset.univ.val.map x →
      discSq x = (ev Δ) ^ 2)
    (hGmonic : G.Monic) (hGdeg : G.natDegree = n.factorial / 2)
    (hGabs : Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
    (hGres : AlternatingFamily.IsAltResolvent n F G) :
    IsRegularInverseGalois (alternatingGroup (Fin n)) := by
  classical
  haveI hntriv : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  set f : (RatFunc ℚ)[X] := F.map (algebraMap ℚ[X] (RatFunc ℚ)) with hf
  have hfdeg : f.natDegree = n := by rw [hf, hFmonic.natDegree_map, hFdeg]
  haveI : IsGalois (RatFunc ℚ) f.SplittingField := IsGalois.of_separable_splitting_field hsep
  -- a root enumeration over the generic splitting field
  have hcardrs : Fintype.card (f.rootSet f.SplittingField) = n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits f), hfdeg]
  set v : Fin n ≃ f.rootSet f.SplittingField := (Fintype.equivFinOfCardEq hcardrs).symm with hv
  set w : Fin n → f.SplittingField := fun i ↦ (v i : f.SplittingField) with hw
  set ev : ℚ[X] →+* f.SplittingField :=
    (algebraMap (RatFunc ℚ) f.SplittingField).comp (algebraMap ℚ[X] (RatFunc ℚ)) with hev
  have hmapev : F.map ev = f.map (algebraMap (RatFunc ℚ) f.SplittingField) :=
    (Polynomial.map_map _ _ _).symm
  have hevdeg : (F.map ev).natDegree = n := by rw [hFmonic.natDegree_map, hFdeg]
  have hevroots : (F.map ev).roots = Finset.univ.val.map w := by
    rw [hmapev]
    exact roots_eq_map_rootSetEquiv hsep v
  -- the landing certificate: the discriminant is a square in `ℚ(T)`
  have hd : discSq w = (algebraMap (RatFunc ℚ) f.SplittingField
      (algebraMap ℚ[X] (RatFunc ℚ) Δ)) ^ 2 := hdisc ev w hevdeg hevroots
  have h_ne : discElem w ≠ 0 := by
    unfold discElem
    rw [← Matrix.det_vandermonde, Ne, Matrix.det_vandermonde_eq_zero_iff]
    push_neg
    exact fun i j h ↦ v.injective (Subtype.ext h)
  obtain ⟨φ, hφ⟩ := exists_gal_embeds_alternating f hsep.ne_zero v ⟨_, hd⟩ h_ne
  -- the resolvent is absolutely irreducible over the geometric base field
  have hGabsFrac : Irreducible (G.map toClosureFrac) := by
    have hmap := (hGmonic.map
      (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).irreducible_iff_irreducible_map_fraction_map
      (K := ℚ̄T) |>.mp hGabs
    rwa [Polynomial.map_map] at hmap
  -- the generic root of the resolvent
  obtain ⟨α, hα⟩ := generic_alt_resolvent_root F G hFmonic n hFdeg hGres
  have halt : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact IsRegularInverseGalois.of_embeds_and_root f.SplittingField G hGmonic
    (hGdeg.trans halt.symm) hGabsFrac α hα φ hφ

/-! ## Serre's two families read over the generic point -/

/-- The geometric base change of `ℚ(T)` restricts to the geometric base change of `ℚ[T]`. -/
theorem algebraMap_comp_eq_toClosureFrac :
    (algebraMap (RatFunc ℚ) ℚ̄T).comp (algebraMap ℚ[X] (RatFunc ℚ)) = toClosureFrac :=
  RingHom.ext algebraMap_ratFunc_geom_comp

/-- Separability over `ℚ(T)` descends from separability over `ℚ̄(T)`. -/
theorem separable_ratFunc_of_separable_closureFrac {F : ℚ[X][X]}
    (h : (F.map ResolventFamily.toClosureFrac).Separable) :
    (F.map (algebraMap ℚ[X] (RatFunc ℚ))).Separable := by
  rw [toClosureFrac_eq, ← algebraMap_comp_eq_toClosureFrac, ← Polynomial.map_map] at h
  exact (Polynomial.separable_map (algebraMap (RatFunc ℚ) ℚ̄T)).mp h

/-- **The alternating group on an even number `n ≥ 4` of letters is a regular inverse Galois
group**, realized by the splitting field of Serre's substituted family over `ℚ(T)`. -/
theorem isRegularInverseGalois_alternatingGroup_even (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    IsRegularInverseGalois (alternatingGroup (Fin n)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨G, hGmonic, hGdeg, hGres, -⟩ := AlternatingFamily.exists_altResolvent n hn2 heven
  refine isRegularInverseGalois_alternating_of_family n hn2 (AlternatingFamily.serreAnFamily n) G
    (AlternatingFamily.serreAnFamily_monic n hn2) (AlternatingFamily.serreAnFamily_natDegree n hn2)
    (separable_ratFunc_of_separable_closureFrac
      (AlternatingFamily.serreAnOverFrac_separable n hn2 heven))
    (AlternatingFamily.serreAnDeltaPoly n) ?_ hGmonic hGdeg
    (AlternatingFamily.anResolvent_abs_irreducible n hn heven G hGmonic hGres) hGres
  intro A _ ev x hdeg hroots
  rw [discSq, AlternatingFamily.serreAnFamily_discSq_general n hn2 ev x hdeg hroots,
    ← AlternatingFamily.serreAnDeltaPoly_sq n heven, map_pow]

/-- **The alternating group on an odd number `n ≥ 3` of letters is a regular inverse Galois
group**, realized by the splitting field of Serre's conic family over `ℚ(T)`. -/
theorem isRegularInverseGalois_alternatingGroup_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    IsRegularInverseGalois (alternatingGroup (Fin n)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨G, hGmonic, hGdeg, hGres, -⟩ := AlternatingFamily.exists_altResolvent_odd n hn2 hodd
  refine isRegularInverseGalois_alternating_of_family n hn2 (AlternatingFamily.serreAnFamilyOdd n) G
    (AlternatingFamily.serreAnFamilyOdd_monic n hn2)
    (AlternatingFamily.serreAnFamilyOdd_natDegree n hn2)
    (separable_ratFunc_of_separable_closureFrac
      (AlternatingFamily.serreAnOverFracOdd_separable n hn2 hodd))
    (AlternatingFamily.serreAnDeltaPolyOdd n) ?_ hGmonic hGdeg
    (AlternatingFamily.anResolvent_abs_irreducible_odd n hn2 hodd G hGmonic hGres) hGres
  intro A _ ev x hdeg hroots
  rw [discSq, AlternatingFamily.serreAnFamilyOdd_discSq_general n hn2 hodd ev x hdeg hroots,
    ← AlternatingFamily.serreAnDeltaPolyOdd_sq n hn2 hodd, map_pow]

/-! ## The alternating groups -/

/-- **The alternating group on `n` letters is a regular inverse Galois group**, for every `n`.

For `n ≤ 2` the group is trivial and for `n = 3` it is cyclic of order three, realized by the
rotation `u ↦ (u − 1)/u` of `ℚ(u)`.  For `n ≥ 4` Serre's square-discriminant family realizes it
over `ℚ(T)`, with the constant field `ℚ` because its orbit resolvent stays irreducible over
`ℚ̄(T)`. -/
theorem isRegularInverseGalois_alternatingGroup (n : ℕ) :
    IsRegularInverseGalois (alternatingGroup (Fin n)) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · -- `A₀`, `A₁`, `A₂` are trivial
    interval_cases n
    · haveI : Subsingleton (alternatingGroup (Fin 0)) :=
        ⟨fun a b ↦ Subtype.ext (Equiv.ext fun x ↦ x.elim0)⟩
      exact IsRegularInverseGalois.of_subsingleton
    · haveI : Subsingleton (alternatingGroup (Fin 1)) :=
        ⟨fun a b ↦ Subtype.ext (Equiv.ext fun x ↦ Subsingleton.elim _ _)⟩
      exact IsRegularInverseGalois.of_subsingleton
    · have hcard : Nat.card (alternatingGroup (Fin 2)) = 1 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      exact isRegularInverseGalois_of_card_eq_one hcard
  · rcases Nat.even_or_odd n with heven | hodd
    · exact isRegularInverseGalois_alternatingGroup_even n h heven
    · exact isRegularInverseGalois_alternatingGroup_odd n h hodd

/-- **The alternating group on `n` letters is a Galois group over the rationals**, for every `n`. -/
theorem isInverseGalois_alternatingGroup (n : ℕ) :
    IsInverseGalois (alternatingGroup (Fin n)) :=
  (isRegularInverseGalois_alternatingGroup n).isInverseGalois

end Rigidity.RET
