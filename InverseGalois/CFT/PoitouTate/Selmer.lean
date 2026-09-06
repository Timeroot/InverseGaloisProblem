/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.SymbolProduct
import InverseGalois.CFT.Kummer.PowerCriterion
import InverseGalois.CFT.PoitouTate.Unramified
import InverseGalois.CFT.Units.SUnitIndex
import InverseGalois.CFT.Units.SUnitValuation

/-!
# The `S`-units are a maximal isotropic subgroup of the local classes

Fix a number field `K` containing a primitive `n`-th root of unity for an odd prime `n`, and a
finite set `S` of finite places carrying every prime above `n` and large enough that every divisor
supported outside `S` is principal.  Each `S`-unit has a class in the units of the completion at
each place of `S`, modulo `n`-th powers, and the resulting map is the object of study here.

The **kernel** of that map is exactly the `n`-th powers among the `S`-units: an `S`-unit which is
an `n`-th power locally at every place of `S` is an `n`-th power at every infinite place too — the
field is totally complex, because it carries a root of unity of order bigger than two — and is a
unit outside `S`, so the criterion for a radical to be trivial applies.  Counting with the index of
the `n`-th powers in the `S`-units, the image therefore has order `n` raised to the number of
places of `S`, the infinite ones included.

The **product of the local class groups** over the places of `S` has order `n` raised to twice that
number: the local index formula multiplies the local indices to `n` raised to twice the number of
places of `S`, and every infinite index is one because the field is totally complex.  So the image
of the `S`-units is exactly a square root of the whole.

Finally the image **pairs trivially with itself** under the product of the norm residue symbols:
that is the product formula, once one knows that the symbols at the places outside `S` are trivial,
which they are because there both arguments are units of the valuation ring and the residue
characteristic does not divide `n`.  The counting lemma for a perfect self-pairing then turns the
inclusion into an equality: **the classes of the `S`-units are precisely their own orthogonal
complement.**  This is the global half of the local-global duality that cuts out a Selmer group.

## Main results

* `InverseGalois.CFT.ker_sUnitClassHom`: the classes of the `S`-units in the local classes at the
  places of `S` are faithful, the kernel being exactly the `n`-th powers.
* `InverseGalois.CFT.card_selmerGroup`: there are `n` raised to the number of places of `S` of
  them.
* `InverseGalois.CFT.card_pi_localClasses`: there are `n` raised to twice that number of local
  classes.
* `InverseGalois.CFT.selmerGroup_le_perpSubgroup`: the classes of the `S`-units pair trivially with
  themselves.
* `InverseGalois.CFT.perpSubgroup_selmerGroup`: **the classes of the `S`-units are precisely their
  own orthogonal complement** under the product of the norm residue symbols.

## Tags

number field, `S`-unit, norm residue symbol, product formula, maximal isotropic, Selmer group,
Poitou-Tate duality, class field theory
-/


set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Valued

/-! ### Places away from the exponent -/

section Bridge

variable {K : Type} [Field K] [NumberField K] {p e n : ℕ}

/-- **A prime not lying above the exponent has residue characteristic prime to it.** -/
theorem not_dvd_of_finitePlace_natCast_eq_one {v : HeightOneSpectrum (𝓞 K)}
    (hres : HasResidueChar (v.adicCompletion K) p e)
    (hv : FinitePlace.mk v ((n : ℕ) : K) = 1) : ¬ p ∣ n := by
  have h : Valued.v ((n : ℕ) : v.adicCompletion K) = 1 :=
    (valued_natCast_eq_one_iff K v n).mpr ((finitePlace_natCast_eq_one_iff v n).mp hv)
  have h' : Valued.v (((n : ℤ) : v.adicCompletion K)) = 1 := by
    rwa [Int.cast_natCast]
  have := (valued_intCast_eq_one_iff_not_dvd hres (m := (n : ℤ))).mp h'
  exact fun hd => this (Int.natCast_dvd_natCast.mpr hd)

omit [NumberField K] in
/-- The `n`-th powers exhaust the units of a complex completion. -/
theorem index_range_powMonoidHom_units_isComplex (hn : n ≠ 0) {w : InfinitePlace K}
    (hw : w.IsComplex) :
    (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index = 1 := by
  rw [index_range_powMonoidHom_units_congr
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) n,
    index_range_powMonoidHom_units_complex hn]

/-- **The product of the local indices over the finite places of a totally complex field.** -/
theorem prod_index_range_powMonoidHom_units_finite_of_isTotallyComplex [NeZero n]
    [IsTotallyComplex K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v, FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ T) :
    (∏ v ∈ T, (powMonoidHom n :
        (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index)
      = n ^ (2 * (Fintype.card (InfinitePlace K) + T.card)) := by
  have hinf : (∏ w : InfinitePlace K,
      (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index) = 1 :=
    Finset.prod_eq_one fun w _ =>
      index_range_powMonoidHom_units_isComplex (NeZero.ne n) (IsTotallyComplex.isComplex w)
  have h := prod_index_range_powMonoidHom_units_of_isPrimitiveRoot hζ T hT
  rwa [hinf, one_mul] at h

end Bridge

/-! ### The classes of the `S`-units at the places of `S` -/

section Selmer

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {Y : Type*} [Fintype Y]

/-- Every class modulo `n`-th powers is killed by `n`. -/
theorem pow_eq_one_of_quotient_range_powMonoidHom {A : Type*} [CommGroup A] (n : ℕ)
    (x : A ⧸ (powMonoidHom n : A →* A).range) : x ^ n = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩

/-- The units of the completion of a number field at a finite place, modulo `n`-th powers. -/
abbrev localClasses (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) : Type :=
  (v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range

/-- The class of an element of a number field in the units of a completion modulo `n`-th powers. -/
noncomputable def localClassHom (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Kˣ →* localClasses v n :=
  (QuotientGroup.mk' _).comp (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom)

/-- The classes of the `S`-units in the units of the completions at the finite places of `S`,
modulo `n`-th powers. -/
noncomputable def sUnitClassHom (ι : Y → HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ↥(sUnits K (Set.range ι)) →* ((y : Y) → localClasses (ι y) n) :=
  Pi.monoidHom fun y => (localClassHom (ι y) n).comp (Subgroup.subtype _)

omit [Fintype Y] in
theorem sUnitClassHom_apply (ι : Y → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : ↥(sUnits K (Set.range ι))) (y : Y) :
    sUnitClassHom ι n a y = localClassHom (ι y) n (a : Kˣ) := rfl

/-- The classes of the `S`-units, read inside the local classes at the finite places of `S`. -/
noncomputable def selmerGroup (ι : Y → HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup ((y : Y) → localClasses (ι y) n) :=
  MonoidHom.range (N := (y : Y) → localClasses (ι y) n) (sUnitClassHom ι n)

omit [Fintype Y] in
theorem mem_selmerGroup {ι : Y → HeightOneSpectrum (𝓞 K)} {m : ℕ}
    {x : (y : Y) → localClasses (ι y) m} :
    x ∈ selmerGroup ι m ↔ ∃ a : ↥(sUnits K (Set.range ι)), sUnitClassHom ι m a = x := Iff.rfl

omit [NumberField K] [NeZero n] [Fintype Y] in
/-- Every element of a complex completion is an `n`-th power. -/
theorem exists_pow_eq_completion_of_isComplex (hn : n ≠ 0) {w : InfinitePlace K}
    (hw : w.IsComplex) (x : w.Completion) : ∃ c : w.Completion, c ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) (Nat.pos_of_ne_zero hn)
  refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z, ?_⟩
  rw [← map_pow, hz, RingEquiv.symm_apply_apply]

omit [NeZero n] in
/-- **The classes of the `S`-units inject into the local classes at the finite places of `S`**,
when `S` carries every prime above the exponent and every divisor supported outside `S` is
principal. -/
theorem ker_sUnitClassHom [IsTotallyComplex K] (hn : n.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hpι : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v) :
    (sUnitClassHom ι n).ker
      = (powMonoidHom n : ↥(sUnits K (Set.range ι)) →* ↥(sUnits K (Set.range ι))).range := by
  refine le_antisymm (fun a ha => ?_) ?_
  · have hbS : ∀ v ∈ Set.range ι,
        ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) ((a : Kˣ) : K) := by
      rintro v ⟨y, rfl⟩
      have h := congrFun (MonoidHom.mem_ker.mp ha) y
      rw [Pi.one_apply, sUnitClassHom_apply, localClassHom, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨(z : (ι y).adicCompletion K), by
        rw [← Units.val_pow_eq_pow_val, show z ^ n = powMonoidHom n z from rfl, hz]; rfl⟩
    obtain ⟨y, hy⟩ := exists_pow_eq_of_forall_localPow hn hζ (Set.finite_range ι)
      Set.finite_empty (fun v hv => absurd hv (Set.notMem_empty v)) hpι hrepr
      (fun _ _ => ⟨1, one_mem _, fun v hv => absurd hv (Set.notMem_empty v)⟩)
      (fun w => exists_pow_eq_completion_of_isComplex hn.ne_zero (IsTotallyComplex.isComplex w) _)
      hbS
      (fun v hvS _ => valuation_eq_one_of_mem_sUnits a.2 hvS)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne_zero] at hy
      exact (a : Kˣ).ne_zero hy.symm
    have hmem : Units.mk0 y hy0 ∈ sUnits K (Set.range ι) := by
      refine mem_sUnits.mpr fun v hv => ?_
      have h := Rigidity.RET.ord_pow (K := K) v hy0 (n := n)
      rw [hy, mem_sUnits.mp a.2 v hv] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (Int.natCast_ne_zero.mpr hn.ne_zero)
    exact ⟨⟨Units.mk0 y hy0, hmem⟩, Subtype.ext (Units.ext hy)⟩
  · rintro _ ⟨c, rfl⟩
    refine MonoidHom.mem_ker.mpr (funext fun v => ?_)
    rw [Pi.one_apply, show powMonoidHom n c = c ^ n from rfl, _root_.map_pow, Pi.pow_apply]
    exact pow_eq_one_of_quotient_range_powMonoidHom n _

omit [NeZero n] [Fintype Y] in
/-- An `S`-unit is a unit of the valuation ring of every completion outside `S`. -/
theorem valued_map_eq_one_of_mem_sUnits {X : Set (HeightOneSpectrum (𝓞 K))} {u : Kˣ}
    (hu : u ∈ sUnits K X) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ X) :
    Valued.v ((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  have hmap : ((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) = (((u : K)) : v.adicCompletion K) := rfl
  rw [hmap, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)]
  exact valuation_eq_one_of_mem_sUnits hu hv

end Selmer

/-! ### The `S`-units are a maximal isotropic subgroup -/

section Maximal

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {Y : Type*} [Fintype Y]

/-- The pairing of the local classes at the finite places of `S` whose value is the product of the
norm residue symbols. -/
noncomputable def localSymbolPiPairing
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (ι : Y → HeightOneSpectrum (𝓞 K)) :
    ((y : Y) → localClasses (ι y) n) →*
      ((y : Y) → localClasses (ι y) n) →* Multiplicative QModZ :=
  piPairing (A := fun y => localClasses (ι y) n) fun y => localSymbolQuotDual (hres (ι y))
    (isUnitValGen_one (valued_adicCompletion_surjective (ι y)))
    (hζ.map_of_injective (algebraMap K ((ι y).adicCompletion K)).injective)

/-- **The local classes at the finite places of `S` number the exponent to twice the number of
places of `S`**, for a totally complex field carrying the roots of unity. -/
theorem card_pi_localClasses [IsTotallyComplex K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {ι : Y → HeightOneSpectrum (𝓞 K)} (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι) :
    Nat.card ((y : Y) → localClasses (ι y) n)
      = n ^ (2 * (Fintype.card (InfinitePlace K) + Fintype.card Y)) := by
  classical
  have hTmem : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 →
      v ∈ Finset.univ.image ι := by
    intro v hv
    obtain ⟨y, rfl⟩ := hnι v hv
    exact Finset.mem_image_of_mem ι (Finset.mem_univ y)
  have hcard : (Finset.univ.image ι).card = Fintype.card Y := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hprod : (∏ v ∈ Finset.univ.image ι, (powMonoidHom n :
      (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index)
      = ∏ y : Y, (powMonoidHom n :
        ((ι y).adicCompletion K)ˣ →* ((ι y).adicCompletion K)ˣ).range.index :=
    Finset.prod_image fun x _ y _ h => hinj h
  have hpt : ∀ y : Y, Nat.card (localClasses (ι y) n)
      = (powMonoidHom n :
        ((ι y).adicCompletion K)ˣ →* ((ι y).adicCompletion K)ˣ).range.index := fun _ => rfl
  rw [Nat.card_pi]
  simp only [hpt]
  rw [← hprod,
    prod_index_range_powMonoidHom_units_finite_of_isTotallyComplex hζ (Finset.univ.image ι) hTmem,
    hcard]

/-- **The classes of the `S`-units number the exponent to the number of places of `S`.** -/
theorem card_selmerGroup [IsTotallyComplex K] (hn : n.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)} (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v) :
    Nat.card ↥(selmerGroup ι n)
      = n ^ (Fintype.card (InfinitePlace K) + Fintype.card Y) := by
  haveI : HasEnoughRootsOfUnity K n := ⟨⟨ζ, hζ⟩, rootsOfUnity.isCyclic K n⟩
  have hpι : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ Set.range ι := by
    intro v hv
    exact hnι v fun h => (finitePlace_natCast_eq_one_iff v n).mp h hv
  rw [selmerGroup, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (H := (y : Y) → localClasses (ι y) n) (sUnitClassHom ι n)).toEquiv,
    show Nat.card (↥(sUnits K (Set.range ι)) ⧸ (sUnitClassHom ι n).ker)
      = (sUnitClassHom ι n).ker.index from rfl,
    ker_sUnitClassHom hn hζ hpι hrepr, index_range_powMonoidHom_sUnits n hinj]

/-- **The classes of the `S`-units pair trivially with themselves**: the product formula for the
norm residue symbol, since the symbols away from `S` are symbols of two units of a valuation ring
whose residue characteristic does not divide the exponent. -/
theorem selmerGroup_le_perpSubgroup (hn : n.Prime) (hodd : 2 < n)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι) :
    selmerGroup ι n ≤ perpSubgroup (A := (y : Y) → localClasses (ι y) n)
      (localSymbolPiPairing hres hζ ι) (selmerGroup ι n) := by
  classical
  haveI := isTotallyComplex_of_isPrimitiveRoot hodd hζ
  rintro _ ⟨b, rfl⟩
  rw [mem_perpSubgroup]
  rintro _ ⟨a, rfl⟩
  have hprod := prod_localSymbol_eq_one hn hres hζ (b : Kˣ) (a : Kˣ) (Finset.univ.image ι) ?_
  · rw [Finset.prod_image fun x _ y _ h => hinj h] at hprod
    rw [localSymbolPiPairing, piPairing_apply]
    simpa only [sUnitClassHom_apply, localClassHom, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, localSymbolQuotDual_mk] using hprod
  · intro v hvT
    have hv : v ∉ Set.range ι := by
      rintro ⟨y, rfl⟩
      exact hvT (Finset.mem_image_of_mem ι (Finset.mem_univ y))
    have hnv : FinitePlace.mk v ((n : ℕ) : K) = 1 := by
      by_contra hc
      exact hv (hnι v hc)
    exact localSymbol_eq_one_of_valued_eq_one (hres v) _ _ hn
      (not_dvd_of_finitePlace_natCast_eq_one (hres v) hnv)
      (valued_map_eq_one_of_mem_sUnits b.2 hv) (valued_map_eq_one_of_mem_sUnits a.2 hv)

/-- **The classes of the `S`-units are precisely their own orthogonal complement in the local
classes at the finite places of `S`**, under the product of the norm residue symbols.  They pair
trivially with themselves by the product formula, and there are exactly as many of them as the
square root of the number of local classes, so the counting lemma for a perfect self-pairing turns
the inclusion into an equality. -/
theorem perpSubgroup_selmerGroup (hn : n.Prime) (hodd : 2 < n)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v) :
    perpSubgroup (A := (y : Y) → localClasses (ι y) n)
        (localSymbolPiPairing hres hζ ι) (selmerGroup ι n) = selmerGroup ι n := by
  classical
  haveI := isTotallyComplex_of_isPrimitiveRoot hodd hζ
  haveI : ∀ y : Y, Finite (localClasses (ι y) n) := by
    intro y
    haveI := finiteIndex_range_powMonoidHom_units_adicCompletion (ι y) (NeZero.ne n)
    infer_instance
  haveI : Finite ((y : Y) → localClasses (ι y) n) := Pi.finite
  refine perpSubgroup_eq_self ?_
    (selmerGroup_le_perpSubgroup hn hodd hres hζ hinj hnι) ?_
  · exact injective_flip_piPairing fun y => injective_flip_localSymbolQuotDual _ _ _
  · rw [card_selmerGroup hn hζ hinj hnι hrepr, card_pi_localClasses hζ hinj hnι,
      ← pow_add, two_mul]

end Maximal

end InverseGalois.CFT
