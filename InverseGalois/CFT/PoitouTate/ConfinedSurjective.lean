/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedUnits

/-!
# The orders of the confined units, read modulo the exponent

The descent through the units of a number field runs on a valuation which is onto the free abelian
group on a finite set of places.  For the confined units — those which are local powers at one set
of places and have order divisible by the exponent outside another — being onto is a genuine
arithmetic demand, because the order at a place is constrained by the class group and by the local
conditions.

Half of the demand costs nothing.  Every exponent-th power of an element of the field is a confined
unit, whatever the two sets of places are: it is a global power, hence a local one, and its order is
divisible by the exponent at every place at once.  So the image of the valuation contains every
multiple of the exponent, provided the plain order vector is onto — and the plain order vector is
onto, because the Chinese remainder theorem realises any prescribed system of orders at finitely
many places.

What is left is the demand read modulo the exponent: the orders of the confined units at the chosen
places fill out the whole of the free module over the integers modulo the exponent.  That is a
statement about a finite vector space over a finite field, and it is where the class group and the
local conditions really enter.

## Main results

* `InverseGalois.CFT.exists_forall_ord_eq`: **every prescribed system of orders at finitely many
  places is realised by an element of the field.**
* `InverseGalois.CFT.ordAt_surjective`: the vector of orders at a finite set of places is onto.
* `InverseGalois.CFT.pow_mem_confinedUnits`: **an exponent-th power is a confined unit.**
* `InverseGalois.CFT.surjective_confinedOrd_of_dvd_sub`: **the vector of orders of the confined
  units is onto as soon as it is onto modulo the exponent.**

## Tags

number field, height one prime, order, Chinese remainder theorem, confined unit, valuation
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### Prescribing the orders at finitely many places -/

section Prescribe

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- **A uniformiser at a height one prime**: an element of order exactly one there.  A nonzero
prime strictly contains its square, and an element of the one which is not in the other has order
at least one and less than two. -/
theorem exists_ord_eq_one (v : HeightOneSpectrum R) :
    ∃ π : R, π ∈ v.asIdeal ∧ π ∉ v.asIdeal ^ 2 ∧ ord K v (algebraMap R K π) = 1 := by
  have hlt : ¬ v.asIdeal ≤ v.asIdeal ^ 2 := by
    have h := (Ideal.pow_succ_lt_pow (P := v.asIdeal) v.ne_bot 1).not_ge
    rwa [pow_one] at h
  obtain ⟨π, hπ, hπ2⟩ := SetLike.not_le_iff_exists.1 hlt
  have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ Submodule.zero_mem _)
  refine ⟨π, hπ, hπ2, ?_⟩
  have h := ord_eq_of_mem_pow_of_notMem_pow (K := K) v hπ0 (j := 1) (by rwa [pow_one])
    (by simpa using hπ2)
  simpa using h

/-- **Every prescribed system of nonnegative orders at finitely many places is realised by an
element of the ring of integers.**  A power of a uniformiser has the prescribed order at its own
place, and the Chinese remainder theorem glues those local answers into a single element, agreeing
with each of them to one order beyond the one prescribed. -/
theorem exists_forall_ord_eq_natCast (s : Finset (HeightOneSpectrum R))
    (e : HeightOneSpectrum R → ℕ) :
    ∃ y : R, y ≠ 0 ∧ ∀ v ∈ s, ord K v (algebraMap R K y) = (e v : ℤ) := by
  classical
  choose π hπmem hπ2 hπord using exists_ord_eq_one (R := R) K
  have hπ0 : ∀ v : HeightOneSpectrum R, π v ≠ 0 := fun v h => hπ2 v (h ▸ Submodule.zero_mem _)
  have hpow : ∀ v : HeightOneSpectrum R,
      ord K v (algebraMap R K (π v ^ e v)) = (e v : ℤ) := by
    intro v
    have hne : algebraMap R K (π v) ≠ 0 := fun hzero =>
      hπ0 v ((IsFractionRing.to_map_eq_zero_iff (R := R) (K := K)).1 hzero)
    rw [_root_.map_pow, ord_pow v hne, hπord v, mul_one]
  rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨1, one_ne_zero, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun v : HeightOneSpectrum R => v.asIdeal) (fun v => e v + 1) (fun v _ => v.prime)
    (fun _ _ _ _ hij h => hij (HeightOneSpectrum.ext h))
    (fun v : {v // v ∈ s} => π (v : HeightOneSpectrum R) ^ e (v : HeightOneSpectrum R))
  have hmem : ∀ v ∈ s, y ∈ v.asIdeal ^ e v := by
    intro v hv
    have h1 : y - π v ^ e v ∈ v.asIdeal ^ e v :=
      Ideal.pow_le_pow_right (Nat.le_succ _) (hy v hv)
    have h2 : π v ^ e v ∈ v.asIdeal ^ e v := Ideal.pow_mem_pow (hπmem v) _
    simpa using Ideal.add_mem _ h1 h2
  have hnot : ∀ v ∈ s, y ∉ v.asIdeal ^ (e v + 1) := by
    intro v hv hcon
    have h1 : π v ^ e v ∈ v.asIdeal ^ (e v + 1) := by
      have := Ideal.sub_mem _ hcon (hy v hv)
      simpa using this
    have h2 := (mem_pow_iff_le_ord (K := K) v (pow_ne_zero _ (hπ0 v)) (e v + 1)).1 h1
    rw [hpow v] at h2
    push_cast at h2
    omega
  have hy0 : y ≠ 0 := fun h => hnot v₀ hv₀ (by rw [h]; exact Submodule.zero_mem _)
  exact ⟨y, hy0, fun v hv =>
    ord_eq_of_mem_pow_of_notMem_pow (K := K) v hy0 (hmem v hv) (hnot v hv)⟩

/-- **Every prescribed system of orders at finitely many places is realised by an element of the
field**, a quotient of two elements of the ring of integers realising the positive and the negative
parts of the system. -/
theorem exists_forall_ord_eq (s : Finset (HeightOneSpectrum R)) (d : HeightOneSpectrum R → ℤ) :
    ∃ a : Kˣ, ∀ v ∈ s, ord K v (a : K) = d v := by
  obtain ⟨y, hy0, hy⟩ := exists_forall_ord_eq_natCast (R := R) K s fun v => (d v).toNat
  obtain ⟨z, hz0, hz⟩ := exists_forall_ord_eq_natCast (R := R) K s fun v => (-d v).toNat
  have hy' : algebraMap R K y ≠ 0 := fun hzero =>
    hy0 ((IsFractionRing.to_map_eq_zero_iff (R := R) (K := K)).1 hzero)
  have hz' : algebraMap R K z ≠ 0 := fun hzero =>
    hz0 ((IsFractionRing.to_map_eq_zero_iff (R := R) (K := K)).1 hzero)
  refine ⟨Units.mk0 _ hy' * (Units.mk0 _ hz')⁻¹, fun v hv => ?_⟩
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0,
    ← div_eq_mul_inv, ord_div v hy' hz', hy v hv, hz v hv]
  omega

end Prescribe

/-! ### The vector of orders at a finite set of places is onto -/

section OrdAt

variable {K : Type} [Field K] [NumberField K]
variable (Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]

/-- **The vector of orders at a finite set of places is onto.** -/
theorem ordAt_surjective : Function.Surjective (ordAt (K := K) Xs) := by
  classical
  haveI : Fintype ↥Xs := Fintype.ofFinite _
  intro b
  obtain ⟨a, ha⟩ := exists_forall_ord_eq (R := 𝓞 K) K
    (Finset.image (Subtype.val : ↥Xs → HeightOneSpectrum (𝓞 K)) Finset.univ)
    fun v => if h : v ∈ Xs then b ⟨v, h⟩ else 0
  refine ⟨Additive.ofMul a, Finsupp.ext fun y => ?_⟩
  have hy : (y : HeightOneSpectrum (𝓞 K)) ∈
      Finset.image (Subtype.val : ↥Xs → HeightOneSpectrum (𝓞 K)) Finset.univ :=
    Finset.mem_image.2 ⟨y, Finset.mem_univ y, rfl⟩
  rw [ordAt_apply, show ((Additive.ofMul a).toMul : Kˣ) = a from rfl, ha _ hy]
  exact dif_pos y.2

end OrdAt

/-! ### The confined units and the exponent -/

section Confined

variable {K : Type} [Field K] [NumberField K] (n : ℕ)
variable (Tz Y : Set (HeightOneSpectrum (𝓞 K)))

/-- **An exponent-th power is a confined unit**, whatever the two sets of places are: a global
power is a local power, and its order is divisible by the exponent at every place. -/
theorem pow_mem_confinedUnits (x : Kˣ) : x ^ n ∈ confinedUnits K n Tz Y := by
  refine ⟨fun v _ => ?_, fun v _ => ?_⟩
  · rw [MonoidHom.mem_ker, _root_.map_pow]
    exact pow_eq_one_of_quotient_range_powMonoidHom n _
  · rw [Units.val_pow_eq_pow_val, ord_pow v (Units.ne_zero x)]
    exact dvd_mul_right _ _

variable (Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]

/-- The orders of an exponent-th power at the named places are the exponent times the orders of the
element itself. -/
theorem confinedOrd_pow (x : Kˣ) (y : ↥Xs) :
    confinedOrd n Tz Y Xs (Additive.ofMul (⟨x ^ n, pow_mem_confinedUnits n Tz Y x⟩ :
        ↥(confinedUnits K n Tz Y))) y
      = (n : ℤ) * ordAt Xs (Additive.ofMul x) y := by
  show ord K (y : HeightOneSpectrum (𝓞 K)) (((x ^ n : Kˣ) : K))
      = (n : ℤ) * ord K (y : HeightOneSpectrum (𝓞 K)) ((x : Kˣ) : K)
  rw [Units.val_pow_eq_pow_val, ord_pow (y : HeightOneSpectrum (𝓞 K)) (Units.ne_zero x)]

/-- **The vector of orders of the confined units is onto as soon as it is onto modulo the
exponent.**  The gap between a prescribed system of orders and one that is realised is divisible by
the exponent, so it is the system of orders of an exponent-th power, and an exponent-th power is a
confined unit. -/
theorem surjective_confinedOrd_of_dvd_sub
    (h : ∀ d : ↥Xs →₀ ℤ, ∃ u : Additive ↥(confinedUnits K n Tz Y),
      ∀ y : ↥Xs, (n : ℤ) ∣ (d y - confinedOrd n Tz Y Xs u y)) :
    Function.Surjective (confinedOrd n Tz Y Xs) := by
  classical
  intro d
  obtain ⟨u, hu⟩ := h d
  set c : ↥Xs →₀ ℤ := (d - confinedOrd n Tz Y Xs u).mapRange (fun z => z / (n : ℤ)) (by simp)
    with hc
  obtain ⟨x₀, hx⟩ := ordAt_surjective Xs c
  refine ⟨u + Additive.ofMul (⟨Additive.toMul x₀ ^ n,
    pow_mem_confinedUnits n Tz Y _⟩ : ↥(confinedUnits K n Tz Y)), Finsupp.ext fun y => ?_⟩
  have hval : ordAt Xs (Additive.ofMul (Additive.toMul x₀)) y = c y := by
    rw [_root_.ofMul_toMul, hx]
  rw [_root_.map_add, Finsupp.add_apply, confinedOrd_pow n Tz Y Xs (Additive.toMul x₀) y, hval]
  have hcy : c y = (d y - confinedOrd n Tz Y Xs u y) / (n : ℤ) := by
    rw [hc, Finsupp.mapRange_apply, Finsupp.sub_apply]
  rw [hcy, Int.mul_ediv_cancel' (hu y)]
  ring

end Confined

end InverseGalois.CFT
