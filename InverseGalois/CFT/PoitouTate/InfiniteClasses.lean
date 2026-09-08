/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RealSymbol
import InverseGalois.CFT.Local.InfinitePowIndex
import InverseGalois.CFT.PoitouTate.Isotropic

/-!
# The classes at an infinite place and the symbol pairing them

The completion of a number field at an infinite place is the reals or the complexes, so its units
modulo `n`-th powers form a group of order two or one: two exactly when the place is real and the
exponent is even.  That group carries a pairing of its own, the symbol of the two real
representatives, and the pairing is nondegenerate for the same reason as at a finite place: a
nontrivial class has a negative representative, and the symbol against a negative unit is the sign.

This is the archimedean companion of the norm residue symbol.  Assembling the symbols over all the
infinite places gives a nondegenerate pairing on the product of the local classes there, and that
pairing is the archimedean half of the product formula for the power residue symbol.  The exponent
is carried as a parameter and the symbol is declared trivial for an odd exponent, which is the right
convention: an odd power exhausts the real units, so the group of classes is then trivial anyway.

## Main definitions

* `InverseGalois.CFT.realSymbolN`: the symbol of a pair of real units at a given exponent, trivial
  when the exponent is odd.
* `InverseGalois.CFT.infClasses`: the units of the completion at an infinite place modulo `n`-th
  powers.
* `InverseGalois.CFT.infSymbolQuotDual`: the symbol at an infinite place, read as a map of the
  classes into their own character group.
* `InverseGalois.CFT.infSymbolPiPairing`: the pairing of the classes at all the infinite places.

## Main results

* `InverseGalois.CFT.injective_flip_infSymbolQuotDual`: **the classes at an infinite place pair
  nondegenerately with themselves.**
* `InverseGalois.CFT.infSymbolQuotDual_infClassHom`: **the symbol of the classes of two units of a
  number field is the symbol at the place**, when a real place forces the exponent to be even.
* `InverseGalois.CFT.eq_two_of_isReal_of_isPrimitiveRoot`: a field carrying a real place and a
  primitive root of unity of prime order has that order equal to two.

## Tags

infinite place, real place, Hilbert symbol, local classes, nondegenerate pairing, class field
theory
-/

namespace InverseGalois.CFT

open NumberField

/-! ### The symbol of a pair of real units at a given exponent -/

section RealN

/-- The symbol of a pair of real units whose first member is one is trivial. -/
theorem realSymbol_one_left (b : ℝˣ) : realSymbol 1 b = 1 := by
  rw [realSymbol_comm]
  exact realSymbol_of_pos_right b (by norm_num)

/-- The symbol of a pair of real units, read as a character of the first argument. -/
noncomputable def realSymbolHom (b : ℝˣ) : ℝˣ →* Multiplicative QModZ where
  toFun a := realSymbol a b
  map_one' := realSymbol_one_left b
  map_mul' a₁ a₂ := realSymbol_mul_left a₁ a₂ b

/-- The symbol of a pair of real units carries a power of the first argument to a power. -/
theorem realSymbol_pow_left (a b : ℝˣ) (k : ℕ) : realSymbol (a ^ k) b = realSymbol a b ^ k :=
  _root_.map_pow (realSymbolHom b) a k

/-- **The symbol of a pair of real units at a given exponent**: the symbol itself for an even
exponent, and trivial for an odd one, since an odd power exhausts the real units. -/
noncomputable def realSymbolN (n : ℕ) (a b : ℝˣ) : Multiplicative QModZ :=
  if 2 ∣ n then realSymbol a b else 1

/-- At an even exponent the symbol is the symbol of the two real units. -/
theorem realSymbolN_of_dvd {n : ℕ} (hn : 2 ∣ n) (a b : ℝˣ) :
    realSymbolN n a b = realSymbol a b := by
  simp only [realSymbolN, if_pos hn]

/-- At an odd exponent the symbol is trivial. -/
theorem realSymbolN_of_not_dvd {n : ℕ} (hn : ¬ 2 ∣ n) (a b : ℝˣ) : realSymbolN n a b = 1 := by
  simp only [realSymbolN, if_neg hn]

theorem realSymbolN_mul_left (n : ℕ) (a₁ a₂ b : ℝˣ) :
    realSymbolN n (a₁ * a₂) b = realSymbolN n a₁ b * realSymbolN n a₂ b := by
  by_cases hd : 2 ∣ n
  · rw [realSymbolN_of_dvd hd, realSymbolN_of_dvd hd, realSymbolN_of_dvd hd, realSymbol_mul_left]
  · rw [realSymbolN_of_not_dvd hd, realSymbolN_of_not_dvd hd, realSymbolN_of_not_dvd hd, one_mul]

theorem realSymbolN_mul_right (n : ℕ) (a b₁ b₂ : ℝˣ) :
    realSymbolN n a (b₁ * b₂) = realSymbolN n a b₁ * realSymbolN n a b₂ := by
  by_cases hd : 2 ∣ n
  · rw [realSymbolN_of_dvd hd, realSymbolN_of_dvd hd, realSymbolN_of_dvd hd, realSymbol_mul_right]
  · rw [realSymbolN_of_not_dvd hd, realSymbolN_of_not_dvd hd, realSymbolN_of_not_dvd hd, one_mul]

theorem realSymbolN_one_left (n : ℕ) (b : ℝˣ) : realSymbolN n 1 b = 1 := by
  by_cases hd : 2 ∣ n
  · rw [realSymbolN_of_dvd hd, realSymbol_one_left]
  · rw [realSymbolN_of_not_dvd hd]

/-- The symbol of a pair of real units at a given exponent is symmetric. -/
theorem realSymbolN_comm (n : ℕ) (a b : ℝˣ) : realSymbolN n a b = realSymbolN n b a := by
  by_cases hd : 2 ∣ n
  · rw [realSymbolN_of_dvd hd, realSymbolN_of_dvd hd, realSymbol_comm]
  · rw [realSymbolN_of_not_dvd hd, realSymbolN_of_not_dvd hd]

theorem realSymbolN_one_right (n : ℕ) (a : ℝˣ) : realSymbolN n a 1 = 1 := by
  rw [realSymbolN_comm, realSymbolN_one_left]

/-- **An `n`-th power pairs trivially at the exponent `n`**: the symbol has order dividing two, so
an even exponent kills it, and an odd exponent makes it trivial to start with. -/
theorem realSymbolN_pow_self_left (n : ℕ) (a b : ℝˣ) : realSymbolN n (a ^ n) b = 1 := by
  by_cases hd : 2 ∣ n
  · obtain ⟨m, hm⟩ := hd
    rw [realSymbolN_of_dvd ⟨m, hm⟩, realSymbol_pow_left, hm, pow_mul, realSymbol_sq, one_pow]
  · rw [realSymbolN_of_not_dvd hd]

theorem realSymbolN_pow_self_right (n : ℕ) (a b : ℝˣ) : realSymbolN n a (b ^ n) = 1 := by
  rw [realSymbolN_comm, realSymbolN_pow_self_left]

/-- The symbol of a pair of real units at a given exponent, as a pairing. -/
noncomputable def realSymbolNHom (n : ℕ) : ℝˣ →* ℝˣ →* Multiplicative QModZ where
  toFun a :=
    { toFun := fun b => realSymbolN n a b
      map_one' := realSymbolN_one_right n a
      map_mul' := realSymbolN_mul_right n a }
  map_one' := by
    ext b
    exact realSymbolN_one_left n b
  map_mul' a₁ a₂ := by
    ext b
    exact realSymbolN_mul_left n a₁ a₂ b

@[simp]
theorem realSymbolNHom_apply (n : ℕ) (a b : ℝˣ) : realSymbolNHom n a b = realSymbolN n a b := rfl

end RealN

/-! ### Pulling a pairing back along a homomorphism -/

section Comp

variable {A B M : Type*} [CommGroup A] [CommGroup B] [CommGroup M]

/-- A pairing pulled back along a homomorphism. -/
def pairingComp (ψ : B →* B →* M) (f : A →* B) : A →* A →* M where
  toFun a := (ψ (f a)).comp f
  map_one' := by
    ext b
    simp
  map_mul' a₁ a₂ := by
    ext b
    simp

@[simp]
theorem pairingComp_apply (ψ : B →* B →* M) (f : A →* B) (a b : A) :
    pairingComp ψ f a b = ψ (f a) (f b) := rfl

/-- Being an `n`-th power is carried along an isomorphism. -/
theorem mem_range_powMonoidHom_of_mulEquiv (e : A ≃* B) (n : ℕ) {a : A}
    (h : e a ∈ (powMonoidHom n : B →* B).range) : a ∈ (powMonoidHom n : A →* A).range := by
  obtain ⟨u, hu⟩ := h
  refine ⟨e.symm u, ?_⟩
  rw [show (powMonoidHom n (e.symm u) : A) = e.symm u ^ n from rfl, ← _root_.map_pow,
    show (u ^ n : B) = powMonoidHom n u from rfl, hu, e.symm_apply_apply]

end Comp

/-! ### The classes at an infinite place -/

section Place

variable {K : Type} [Field K]

/-- The units of the completion of a number field at a real infinite place, identified with the
real units. -/
noncomputable def realUnitsEquiv {w : InfinitePlace K} (hw : w.IsReal) : w.Completionˣ ≃* ℝˣ :=
  Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv

/-- The units of the completion at an infinite place, modulo `n`-th powers. -/
abbrev infClasses (w : InfinitePlace K) (n : ℕ) : Type :=
  w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range

/-- The class of a unit of a number field in the units of the completion at an infinite place
modulo `n`-th powers. -/
noncomputable def infClassHom (w : InfinitePlace K) (n : ℕ) : Kˣ →* infClasses w n :=
  (QuotientGroup.mk' _).comp (Units.map (algebraMap K w.Completion).toMonoidHom)

theorem infClassHom_apply (w : InfinitePlace K) (n : ℕ) (x : Kˣ) :
    infClassHom w n x
      = ((Units.map (algebraMap K w.Completion).toMonoidHom x : w.Completionˣ) :
          infClasses w n) := rfl

/-- The `n`-th powers have finite index in the units of the completion at an infinite place. -/
theorem finiteIndex_range_powMonoidHom_units_completion (w : InfinitePlace K) {n : ℕ}
    (hn : n ≠ 0) : (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.FiniteIndex := by
  rcases w.isReal_or_isComplex with hw | hw
  · refine ⟨?_⟩
    rw [index_range_powMonoidHom_units_congr (InfinitePlace.Completion.ringEquivRealOfIsReal hw) n,
      index_range_powMonoidHom_units_real hn]
    split <;> omega
  · refine ⟨?_⟩
    rw [index_range_powMonoidHom_units_congr
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) n,
      index_range_powMonoidHom_units_complex hn]
    omega

/-- The classes at an infinite place are finite in number. -/
theorem finite_infClasses (w : InfinitePlace K) {n : ℕ} (hn : n ≠ 0) :
    Finite (infClasses w n) := by
  haveI := finiteIndex_range_powMonoidHom_units_completion w hn
  infer_instance

open Classical in
/-- **The symbol at an infinite place**, read on the units of the completion: the symbol of the two
real representatives at a real place, and trivial at a complex place. -/
noncomputable def infSymbolUnits (w : InfinitePlace K) (n : ℕ) :
    w.Completionˣ →* w.Completionˣ →* Multiplicative QModZ :=
  if hw : w.IsReal then pairingComp (realSymbolNHom n) (realUnitsEquiv hw).toMonoidHom else 1

/-- At a real place the symbol is the symbol of the two real representatives. -/
theorem infSymbolUnits_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (n : ℕ)
    (a b : w.Completionˣ) :
    infSymbolUnits w n a b = realSymbolN n (realUnitsEquiv hw a) (realUnitsEquiv hw b) := by
  simp only [infSymbolUnits, dif_pos hw, pairingComp_apply, realSymbolNHom_apply,
    MulEquiv.coe_toMonoidHom]

/-- At a complex place the symbol is trivial. -/
theorem infSymbolUnits_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (n : ℕ)
    (a b : w.Completionˣ) : infSymbolUnits w n a b = 1 := by
  simp only [infSymbolUnits, dif_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hw),
    MonoidHom.one_apply]

/-- An `n`-th power pairs trivially on the left. -/
theorem infSymbolUnits_pow_self_left (w : InfinitePlace K) (n : ℕ) (a b : w.Completionˣ) :
    infSymbolUnits w n (a ^ n) b = 1 := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [infSymbolUnits_of_isReal hw, _root_.map_pow, realSymbolN_pow_self_left]
  · rw [infSymbolUnits_of_isComplex hw]

/-- An `n`-th power pairs trivially on the right. -/
theorem infSymbolUnits_pow_self_right (w : InfinitePlace K) (n : ℕ) (a b : w.Completionˣ) :
    infSymbolUnits w n a (b ^ n) = 1 := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [infSymbolUnits_of_isReal hw, _root_.map_pow, realSymbolN_pow_self_right]
  · rw [infSymbolUnits_of_isComplex hw]

/-- The symbol at an infinite place against a fixed element, read on the classes modulo `n`-th
powers. -/
noncomputable def infSymbolLeftQuot (w : InfinitePlace K) (n : ℕ) (b : w.Completionˣ) :
    infClasses w n →* Multiplicative QModZ :=
  QuotientGroup.lift _ ((infSymbolUnits w n).flip b) (by
    rintro _ ⟨c, rfl⟩
    exact infSymbolUnits_pow_self_left w n c b)

@[simp]
theorem infSymbolLeftQuot_mk (w : InfinitePlace K) (n : ℕ) (b a : w.Completionˣ) :
    infSymbolLeftQuot w n b (a : infClasses w n) = infSymbolUnits w n a b := rfl

/-- The symbol at an infinite place, read as a map of the units into the characters of the classes
modulo `n`-th powers. -/
noncomputable def infSymbolDual (w : InfinitePlace K) (n : ℕ) :
    w.Completionˣ →* (infClasses w n →* Multiplicative QModZ) where
  toFun := infSymbolLeftQuot w n
  map_one' := by
    refine MonoidHom.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | _ a => exact _root_.map_one (infSymbolUnits w n a)
  map_mul' b₁ b₂ := by
    refine MonoidHom.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | _ a => exact _root_.map_mul (infSymbolUnits w n a) b₁ b₂

/-- The symbol at an infinite place, read as a map of the classes modulo `n`-th powers into their
own character group. -/
noncomputable def infSymbolQuotDual (w : InfinitePlace K) (n : ℕ) :
    infClasses w n →* (infClasses w n →* Multiplicative QModZ) :=
  QuotientGroup.lift _ (infSymbolDual w n) (by
    rintro _ ⟨c, rfl⟩
    refine MonoidHom.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | _ a => exact infSymbolUnits_pow_self_right w n a c)

@[simp]
theorem infSymbolQuotDual_mk (w : InfinitePlace K) (n : ℕ) (b a : w.Completionˣ) :
    infSymbolQuotDual w n (b : infClasses w n) (a : infClasses w n)
      = infSymbolUnits w n a b := rfl

/-- **The classes at an infinite place pair nondegenerately with themselves.**  At a complex place,
or at a real place with an odd exponent, there is only one class; at a real place with an even
exponent a class pairing trivially with the class of minus one has a positive representative, and
the positive real units are exactly the `n`-th powers. -/
theorem injective_flip_infSymbolQuotDual (w : InfinitePlace K) {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (infSymbolQuotDual w n).flip := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ a =>
    rw [QuotientGroup.eq_one_iff]
    rcases w.isReal_or_isComplex with hw | hw
    · refine mem_range_powMonoidHom_of_mulEquiv (realUnitsEquiv hw) n ?_
      by_cases hd : 2 ∣ n
      · have hev : Even n := Nat.even_iff.mpr (by omega)
        rw [range_powMonoidHom_units_real_of_even hn hev, mem_normSubgroup_real_complex_iff]
        have hb := congrArg
          (fun f => f (((realUnitsEquiv hw).symm (-1) : w.Completionˣ) : infClasses w n)) hx
        simp only [MonoidHom.flip_apply, MonoidHom.one_apply] at hb
        rw [infSymbolQuotDual_mk, infSymbolUnits_of_isReal hw, realSymbolN_of_dvd hd,
          MulEquiv.apply_symm_apply,
          realSymbol_of_neg_right _ (by norm_num : ((-1 : ℝˣ) : ℝ) < 0)] at hb
        exact (realCyclicInvariant_eq_one_iff _).mp hb
      · have hod : Odd n := Nat.odd_iff.mpr (by omega)
        rw [range_powMonoidHom_units_real_of_odd hod]
        exact Subgroup.mem_top _
    · refine mem_range_powMonoidHom_of_mulEquiv
        (Units.mapEquiv
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv) n ?_
      rw [range_powMonoidHom_units_complex hn]
      exact Subgroup.mem_top _

end Place

/-! ### The symbol of two units of a number field at an infinite place -/

section Global

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- **The symbol of the classes of two units of a number field at an infinite place is the symbol
at that place**, whenever a real place forces the exponent to be even. -/
theorem infSymbolQuotDual_infClassHom {w : InfinitePlace K} {n : ℕ} (hw2 : w.IsReal → 2 ∣ n)
    (a b : Kˣ) :
    infSymbolQuotDual w n (infClassHom w n b) (infClassHom w n a) = archSymbol K w a b := by
  rcases w.isReal_or_isComplex with hw | hw
  · have hmap : ∀ x : Kˣ,
        realUnitsEquiv hw (Units.map (algebraMap K w.Completion).toMonoidHom x)
          = Units.map (InfinitePlace.embedding_of_isReal hw).toMonoidHom x := fun x =>
      Units.ext (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw (x : K))
    rw [infClassHom_apply, infClassHom_apply, infSymbolQuotDual_mk, infSymbolUnits_of_isReal hw,
      realSymbolN_of_dvd (hw2 hw), hmap a, hmap b, archSymbol_of_isReal K hw]
  · rw [infClassHom_apply, infClassHom_apply, infSymbolQuotDual_mk, infSymbolUnits_of_isComplex hw,
      archSymbol_of_isComplex K hw]

/-- A number field carrying a real place and a primitive root of unity of prime order has that
order equal to two: a field containing the roots of unity of any bigger order is totally
complex. -/
theorem eq_two_of_isReal_of_isPrimitiveRoot {n : ℕ} (hn : n.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {w : InfinitePlace K} (hw : w.IsReal) : n = 2 := by
  by_contra hne
  haveI := isTotallyComplex_of_isPrimitiveRoot (lt_of_le_of_ne hn.two_le (Ne.symm hne)) hζ
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) hw

/-- A number field carrying a real place and a primitive root of unity of prime order has that
order even. -/
theorem two_dvd_of_isReal_of_isPrimitiveRoot {n : ℕ} (hn : n.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {w : InfinitePlace K} (hw : w.IsReal) : 2 ∣ n := by
  rw [eq_two_of_isReal_of_isPrimitiveRoot hn hζ hw]

/-- **A number field carrying a primitive root of unity of odd prime order asks nothing at the
infinite places**: such a field is totally complex, and every unit of a complex completion is an
`n`-th power there. -/
theorem infClassHom_eq_one_of_ne_two {n : ℕ} (hn : n.Prime) (hn2 : n ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (w : InfinitePlace K) (u : Kˣ) : infClassHom w n u = 1 := by
  have hw : w.IsComplex := by
    rcases w.isReal_or_isComplex with hw | hw
    · exact absurd (eq_two_of_isReal_of_isPrimitiveRoot hn hζ hw) hn2
    · exact hw
  have htop : (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range = ⊤ := by
    rw [← Subgroup.index_eq_one, index_range_powMonoidHom_units_congr
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) n,
      index_range_powMonoidHom_units_complex hn.ne_zero]
  rw [infClassHom_apply, QuotientGroup.eq_one_iff, htop]
  exact Subgroup.mem_top _

/-- **The symbol at an infinite place of two units of a number field is trivial as soon as the
second is a local power there**, the symbol depending only on the classes. -/
theorem archSymbol_eq_one_of_infClassHom_eq_one {n : ℕ} (hn : n.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {w : InfinitePlace K} (a : Kˣ) {b : Kˣ}
    (hb : infClassHom w n b = 1) :
    archSymbol K w a b = 1 := by
  rw [← infSymbolQuotDual_infClassHom
    (fun hw => two_dvd_of_isReal_of_isPrimitiveRoot hn hζ hw) a b, hb, _root_.map_one,
    MonoidHom.one_apply]

/-- **The product over the infinite places of the symbols of two units of a number field is trivial
as soon as the second is a local power at every infinite place.** -/
theorem prod_archSymbol_eq_one_of_infClassHom_eq_one {n : ℕ} (hn : n.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (a : Kˣ) {b : Kˣ}
    (hb : ∀ w : InfinitePlace K, infClassHom w n b = 1) :
    ∏ w : InfinitePlace K, archSymbol K w a b = 1 :=
  Finset.prod_eq_one fun w _ => archSymbol_eq_one_of_infClassHom_eq_one hn hζ a (hb w)

omit [NumberField K] in
/-- A unit of a number field whose class at an infinite place is trivial is an `n`-th power in the
completion there. -/
theorem exists_pow_eq_of_infClassHom_eq_one {w : InfinitePlace K} {n : ℕ} {u : Kˣ}
    (h : infClassHom w n u = 1) :
    ∃ c : w.Completion, c ^ n = algebraMap K w.Completion (u : K) := by
  rw [infClassHom_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨(z : w.Completion), ?_⟩
  rw [← Units.val_pow_eq_pow_val, show z ^ n = powMonoidHom n z from rfl, hz]
  rfl

end Global

/-! ### The classes at all the infinite places -/

section Family

variable (K : Type) [Field K] [NumberField K]

/-- The pairing of the classes at all the infinite places whose value is the product of the symbols
at the places. -/
noncomputable def infSymbolPiPairing (n : ℕ) :
    ((w : InfinitePlace K) → infClasses w n) →*
      ((w : InfinitePlace K) → infClasses w n) →* Multiplicative QModZ :=
  piPairing (A := fun w : InfinitePlace K => infClasses w n) fun w => infSymbolQuotDual w n

theorem infSymbolPiPairing_apply (n : ℕ) (a b : (w : InfinitePlace K) → infClasses w n) :
    infSymbolPiPairing K n a b = ∏ w : InfinitePlace K, infSymbolQuotDual w n (a w) (b w) := rfl

/-- **The classes at the infinite places pair nondegenerately with themselves.** -/
theorem injective_flip_infSymbolPiPairing {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (infSymbolPiPairing K n).flip := by
  classical
  exact injective_flip_piPairing fun w => injective_flip_infSymbolQuotDual w hn

/-- The classes at the infinite places are finite in number. -/
theorem finite_pi_infClasses {n : ℕ} (hn : n ≠ 0) :
    Finite ((w : InfinitePlace K) → infClasses w n) := by
  haveI : ∀ w : InfinitePlace K, Finite (infClasses w n) := fun w => finite_infClasses w hn
  infer_instance

/-- The number of classes at the infinite places is the product of the local indices. -/
theorem card_pi_infClasses (n : ℕ) :
    Nat.card ((w : InfinitePlace K) → infClasses w n)
      = ∏ w : InfinitePlace K,
        (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range.index := by
  rw [Nat.card_pi]
  rfl

end Family

end InverseGalois.CFT
