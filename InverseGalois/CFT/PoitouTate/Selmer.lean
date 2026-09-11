/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealSymbol
import InverseGalois.CFT.Brauer.SymbolProduct
import InverseGalois.CFT.Kummer.PowerCriterion
import InverseGalois.CFT.PoitouTate.InfiniteClasses
import InverseGalois.CFT.PoitouTate.Unramified
import InverseGalois.CFT.Units.SUnitIndex
import InverseGalois.CFT.Units.SUnitValuation

/-!
# The `S`-units are a maximal isotropic subgroup of the local classes

Fix a number field `K` containing a primitive `n`-th root of unity for a prime `n`, and a finite
set `S` of finite places carrying every prime above `n` and large enough that every divisor
supported outside `S` is principal.  Each `S`-unit has a class in the units of the completion at
each place of `S` and at each infinite place, modulo `n`-th powers, and the resulting map is the
object of study here.

The **kernel** of that map is exactly the `n`-th powers among the `S`-units: an `S`-unit which is
an `n`-th power locally at every place of `S` and at every infinite place is a unit outside `S`,
so the criterion for a radical to be trivial applies.  Counting with the index of the `n`-th powers
in the `S`-units, the image therefore has order `n` raised to the number of places of `S`, the
infinite ones included.

The **product of the local class groups** over the places of `S` and the infinite places has order
`n` raised to twice that number, by the local index formula.  So the image of the `S`-units is
exactly a square root of the whole.

Finally the image **pairs trivially with itself** under the product of the norm residue symbols at
the finite places and of the symbols at the infinite ones: that is the product formula over all the
places, once one knows that the symbols at the finite places outside `S` are trivial, which they
are because there both arguments are units of the valuation ring and the residue characteristic
does not divide `n`.  The counting lemma for a perfect self-pairing then turns the inclusion into
an equality: **the classes of the `S`-units are precisely their own orthogonal complement.**  This
is the global half of the local-global duality that cuts out a Selmer group.

## Main results

* `InverseGalois.CFT.ker_fullClassHom`: the classes of the `S`-units at the places of `S` and at
  the infinite places are faithful, the kernel being exactly the `n`-th powers.
* `InverseGalois.CFT.card_selmerGroupFull`: there are `n` raised to the number of places of `S` of
  them.
* `InverseGalois.CFT.card_prod_classes`: there are `n` raised to twice that number of local
  classes.
* `InverseGalois.CFT.selmerGroupFull_le_perpSubgroup`: the classes of the `S`-units pair trivially
  with themselves.
* `InverseGalois.CFT.perpSubgroup_selmerGroupFull`: **the classes of the `S`-units are precisely
  their own orthogonal complement** under the product of the symbols at all the places.

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

/-- The classes of the `S`-units at the finite places of `S` and at the infinite places, modulo
`n`-th powers. -/
noncomputable def fullClassHom (ι : Y → HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ↥(sUnits K (Set.range ι)) →*
      (((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n)) :=
  (sUnitClassHom ι n).prod
    ((Pi.monoidHom fun w : InfinitePlace K => infClassHom w n).comp (Subgroup.subtype _))

omit [Fintype Y] in
@[simp]
theorem fullClassHom_apply_fst (ι : Y → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : ↥(sUnits K (Set.range ι))) (y : Y) :
    (fullClassHom ι n a).1 y = localClassHom (ι y) n (a : Kˣ) := rfl

omit [Fintype Y] in
@[simp]
theorem fullClassHom_apply_snd (ι : Y → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a : ↥(sUnits K (Set.range ι))) (w : InfinitePlace K) :
    (fullClassHom ι n a).2 w = infClassHom w n (a : Kˣ) := rfl

/-- The classes of the `S`-units, read inside the local classes at the finite places of `S` and at
the infinite places. -/
noncomputable def selmerGroupFull (ι : Y → HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n)) :=
  MonoidHom.range
    (N := ((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n))
    (fullClassHom ι n)

omit [Fintype Y] in
theorem mem_selmerGroupFull {ι : Y → HeightOneSpectrum (𝓞 K)} {m : ℕ}
    {x : ((y : Y) → localClasses (ι y) m) × ((w : InfinitePlace K) → infClasses w m)} :
    x ∈ selmerGroupFull ι m
      ↔ ∃ a : ↥(sUnits K (Set.range ι)), fullClassHom ι m a = x := Iff.rfl

omit [NeZero n] [Fintype Y] in
/-- Every class at a place, finite or infinite, is killed by the exponent. -/
theorem pow_eq_one_prod_classes {ι : Y → HeightOneSpectrum (𝓞 K)}
    (x : ((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n)) :
    x ^ n = 1 :=
  Prod.ext (funext fun y => pow_eq_one_of_quotient_range_powMonoidHom n (x.1 y))
    (funext fun w => pow_eq_one_of_quotient_range_powMonoidHom n (x.2 w))

omit [NeZero n] in
/-- **The classes of the `S`-units inject into the local classes at the finite places of `S` and at
the infinite places**, when `S` carries every prime above the exponent and every divisor supported
outside `S` is principal. -/
theorem ker_fullClassHom (hn : n.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hpι : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v) :
    (fullClassHom ι n).ker
      = (powMonoidHom n : ↥(sUnits K (Set.range ι)) →* ↥(sUnits K (Set.range ι))).range := by
  refine le_antisymm (fun a ha => ?_) ?_
  · have hker := MonoidHom.mem_ker.mp ha
    have hfin : sUnitClassHom ι n a = 1 := congrArg Prod.fst hker
    have hinf : ∀ w : InfinitePlace K, infClassHom w n (a : Kˣ) = 1 :=
      fun w => congrFun (congrArg Prod.snd hker) w
    have hbS : ∀ v ∈ Set.range ι,
        ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) ((a : Kˣ) : K) := by
      rintro v ⟨y, rfl⟩
      have h := congrFun hfin y
      rw [Pi.one_apply, sUnitClassHom_apply, localClassHom, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨(z : (ι y).adicCompletion K), by
        rw [← Units.val_pow_eq_pow_val, show z ^ n = powMonoidHom n z from rfl, hz]; rfl⟩
    obtain ⟨y, hy⟩ := exists_pow_eq_of_forall_localPow hn hζ (Set.finite_range ι)
      Set.finite_empty (fun v hv => absurd hv (Set.notMem_empty v)) hpι hrepr
      (fun _ _ => ⟨1, one_mem _, fun v hv => absurd hv (Set.notMem_empty v)⟩)
      (fun w => exists_pow_eq_of_infClassHom_eq_one (hinf w))
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
    refine MonoidHom.mem_ker.mpr ?_
    rw [show powMonoidHom n c = c ^ n from rfl, _root_.map_pow]
    exact pow_eq_one_prod_classes _

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

/-- The pairing of the local classes at the finite places of `S` and at the infinite places whose
value is the product of the symbols at all those places. -/
noncomputable def fullPairing
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (ι : Y → HeightOneSpectrum (𝓞 K)) :
    (((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n)) →*
      (((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n)) →*
        Multiplicative QModZ :=
  prodPairing (A := (y : Y) → localClasses (ι y) n)
    (B := (w : InfinitePlace K) → infClasses w n) (M := Multiplicative QModZ)
    (localSymbolPiPairing hres hζ ι) (infSymbolPiPairing K n)

/-- **The local classes at the finite places of `S` and at the infinite places number the exponent
to twice the number of places of `S`**, for a field carrying the roots of unity. -/
theorem card_prod_classes {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {ι : Y → HeightOneSpectrum (𝓞 K)} (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι) :
    Nat.card (((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n))
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
  have hptw : ∀ w : InfinitePlace K, Nat.card (infClasses w n)
      = (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index := fun _ => rfl
  rw [Nat.card_prod, Nat.card_pi, Nat.card_pi]
  simp only [hpt, hptw]
  rw [mul_comm, ← hprod,
    prod_index_range_powMonoidHom_units_of_isPrimitiveRoot hζ (Finset.univ.image ι) hTmem, hcard]

/-- **The classes of the `S`-units number the exponent to the number of places of `S`.** -/
theorem card_selmerGroupFull (hn : n.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)} (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v) :
    Nat.card ↥(selmerGroupFull ι n)
      = n ^ (Fintype.card (InfinitePlace K) + Fintype.card Y) := by
  haveI : HasEnoughRootsOfUnity K n := ⟨⟨ζ, hζ⟩, rootsOfUnity.isCyclic K n⟩
  have hpι : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ Set.range ι := by
    intro v hv
    exact hnι v fun h => (finitePlace_natCast_eq_one_iff v n).mp h hv
  rw [selmerGroupFull, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (H := ((y : Y) → localClasses (ι y) n) × ((w : InfinitePlace K) → infClasses w n))
      (fullClassHom ι n)).toEquiv,
    show Nat.card (↥(sUnits K (Set.range ι)) ⧸ (fullClassHom ι n).ker)
      = (fullClassHom ι n).ker.index from rfl,
    ker_fullClassHom hn hζ hpι hrepr, index_range_powMonoidHom_sUnits n hinj]

/-- **The classes of the `S`-units pair trivially with themselves**: the product formula for the
symbol over all the places, since the symbols away from `S` are symbols of two units of a valuation
ring whose residue characteristic does not divide the exponent. -/
theorem selmerGroupFull_le_perpSubgroup (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι) :
    selmerGroupFull ι n
      ≤ perpSubgroup (A := ((y : Y) → localClasses (ι y) n) ×
          ((w : InfinitePlace K) → infClasses w n))
        (fullPairing hres hζ ι) (selmerGroupFull ι n) := by
  classical
  rintro _ ⟨b, rfl⟩
  rw [mem_perpSubgroup]
  rintro _ ⟨a, rfl⟩
  have hprod := prod_localSymbol_mul_prod_archSymbol_eq_one hn hres hζ (b : Kˣ) (a : Kˣ)
    (Finset.univ.image ι) ?_
  · rw [Finset.prod_image fun x _ y _ h => hinj h] at hprod
    have hinf : infSymbolPiPairing K n (fullClassHom ι n a).2 (fullClassHom ι n b).2
        = ∏ w : InfinitePlace K, archSymbol K w (b : Kˣ) (a : Kˣ) := by
      rw [infSymbolPiPairing_apply]
      exact Finset.prod_congr rfl fun w _ =>
        infSymbolQuotDual_infClassHom (fun hw => two_dvd_of_isReal_of_isPrimitiveRoot hn hζ hw)
          (b : Kˣ) (a : Kˣ)
    rw [fullPairing, prodPairing_apply, hinf, localSymbolPiPairing, piPairing_apply]
    simpa only [fullClassHom_apply_fst, localClassHom, MonoidHom.comp_apply,
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
classes at the finite places of `S` and at the infinite places**, under the product of the symbols
at all those places.  They pair trivially with themselves by the product formula, and there are
exactly as many of them as the square root of the number of local classes, so the counting lemma
for a perfect self-pairing turns the inclusion into an equality. -/
theorem perpSubgroup_selmerGroupFull (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v) :
    perpSubgroup (A := ((y : Y) → localClasses (ι y) n) ×
          ((w : InfinitePlace K) → infClasses w n))
        (fullPairing hres hζ ι) (selmerGroupFull ι n) = selmerGroupFull ι n := by
  classical
  haveI : ∀ y : Y, Finite (localClasses (ι y) n) := by
    intro y
    haveI := finiteIndex_range_powMonoidHom_units_adicCompletion (ι y) (NeZero.ne n)
    infer_instance
  haveI : Finite ((y : Y) → localClasses (ι y) n) := Pi.finite
  haveI : ∀ w : InfinitePlace K, Finite (infClasses w n) :=
    fun w => finite_infClasses w (NeZero.ne n)
  haveI : Finite ((w : InfinitePlace K) → infClasses w n) := Pi.finite
  haveI : Finite (((y : Y) → localClasses (ι y) n) ×
    ((w : InfinitePlace K) → infClasses w n)) := inferInstance
  refine perpSubgroup_eq_self ?_
    (selmerGroupFull_le_perpSubgroup hn hres hζ hinj hnι) ?_
  · rw [fullPairing]
    exact injective_flip_prodPairing
      (injective_flip_piPairing fun y => injective_flip_localSymbolQuotDual _ _ _)
      (injective_flip_infSymbolPiPairing K (NeZero.ne n))
  · rw [card_selmerGroupFull hn hζ hinj hnι hrepr, card_prod_classes hζ hinj hnι,
      ← pow_add, two_mul]

end Maximal

end InverseGalois.CFT
