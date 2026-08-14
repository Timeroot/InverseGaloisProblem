/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Trinomial
import InverseGalois.Rigidity.RET.MorseSymmetric
import InverseGalois.Rigidity.RET.Genus.OrdDomain

/-!
# Orders of the roots of the trinomial family at the origin

The trinomial `Y ^ (m + 1) = X ^ m (c Y + 1)` degenerates completely at `X = 0`: every root of the
equation vanishes there.  Reading the equation through the order function at a place of the integral
model lying over the origin turns that qualitative statement into an exact one.  The factor
`c Y + 1` is a unit at such a place — its value is `1` modulo the place — so the equation says that
`m + 1` times the order of a root equals `m` times the order of the coordinate.  In particular all
`m + 1` roots vanish to the *same* positive order, and the order of the coordinate is divisible by
`m + 1`.

The roots are therefore indistinguishable to first order, and what distinguishes them is a root of
unity: for a pair of roots `y`, `y'` exactly one `(m+1)`-st root of unity `ζ` makes `y - ζ y'`
vanish deeper than the roots themselves.  Existence comes from the factorization of
`y ^ (m+1) - y' ^ (m+1)` over the `(m+1)`-st roots of unity — the two sides of that identity have
different orders unless one factor is deeper — and uniqueness from the fact that the difference of
two distinct roots of unity is a unit.

## Main definitions

* `Rigidity.RET.coverPlace` — the place of the integral model of a cover cut out by a maximal ideal
  lying over a point of the line.
* `Rigidity.RET.baseX`, `Rigidity.RET.baseC` — the coordinate and the constants of the base line,
  read inside the integral model of a cover.

## Main results

* `Rigidity.RET.intOrd_root` — a root of the trinomial family vanishes to positive order at a place
  over the origin, and `(m+1)` times that order is `m` times the order of the coordinate.
* `Rigidity.RET.intOrd_root_eq_intOrd_root` — all the roots vanish to the same order.
* `Rigidity.RET.succ_dvd_intOrd_baseX` — the coordinate vanishes to order divisible by `m + 1`.
* `Rigidity.RET.exists_unique_root_label` — exactly one `(m+1)`-st root of unity relates two roots
  beyond their common order.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

attribute [local instance] Rigidity.RET.instSMulCommDeck

/-! ### Places of a cover, and the base coordinate inside the integral model -/

/-- The **place of the integral model of a cover** cut out by a maximal ideal lying over a point of
the line.  A prime over a point of the line is nonzero, so it has height one. -/
def coverPlace (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] : HeightOneSpectrum (Bring L.M) :=
  ⟨Q, ‹Q.IsMaximal›.isPrime, Q_ne_bot _ t Q⟩

@[simp] theorem coverPlace_asIdeal (L : LineCover) (t : k) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP t)] : (coverPlace L t Q).asIdeal = Q := rfl

/-- The coordinate of the base line, read inside the integral model of a cover. -/
abbrev baseX (L : LineCover) : Bring L.M := algebraMap (Polynomial k) (Bring L.M) Polynomial.X

/-- A constant of the base field, read inside the integral model of a cover. -/
abbrev baseC (L : LineCover) (a : k) : Bring L.M :=
  algebraMap (Polynomial k) (Bring L.M) (Polynomial.C a)

/-- The constants of the base field, as a ring homomorphism into the integral model. -/
def baseCHom (L : LineCover) : k →+* Bring L.M :=
  (algebraMap (Polynomial k) (Bring L.M)).comp (Polynomial.C : k →+* Polynomial k)

@[simp] theorem baseCHom_apply (L : LineCover) (a : k) : baseCHom L a = baseC L a := rfl

theorem algebraMap_base_injective (L : LineCover) :
    Function.Injective (algebraMap (Polynomial k) (Bring L.M)) :=
  FaithfulSMul.algebraMap_injective (Polynomial k) (Bring L.M)

theorem baseCHom_injective (L : LineCover) : Function.Injective (baseCHom L) :=
  (baseCHom L).injective

theorem baseX_ne_zero (L : LineCover) : baseX L ≠ 0 := fun h =>
  Polynomial.X_ne_zero (algebraMap_base_injective L (h.trans (map_zero _).symm))

theorem baseC_ne_zero (L : LineCover) {a : k} (ha : a ≠ 0) : baseC L a ≠ 0 := by
  intro h
  refine ha (Polynomial.C_injective (algebraMap_base_injective L ?_))
  simp only [map_zero]
  exact h

theorem baseC_pow (L : LineCover) (a : k) (i : ℕ) : baseC L (a ^ i) = baseC L a ^ i := by
  rw [baseC, Polynomial.C_pow, map_pow]

@[simp] theorem baseC_one (L : LineCover) : baseC L (1 : k) = 1 := by
  rw [baseC, Polynomial.C_1, map_one]

theorem baseC_sub (L : LineCover) (a b : k) : baseC L (a - b) = baseC L a - baseC L b := by
  rw [baseC, Polynomial.C_sub, map_sub]

/-- A nonzero constant is a unit in the integral model. -/
theorem isUnit_baseC (L : LineCover) {a : k} (ha : a ≠ 0) : IsUnit (baseC L a) := by
  refine ⟨⟨baseC L a, baseC L a⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← map_mul, ← Polynomial.C_mul, mul_inv_cancel₀ ha, map_one, map_one]
  · rw [← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ ha, map_one, map_one]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The coordinate lies in every prime of the integral model over the origin. -/
theorem baseX_mem (L : LineCover) (Q : Ideal (Bring L.M)) [Q.LiesOver (placeP (0 : k))] :
    baseX L ∈ Q := by
  have hmem : (Polynomial.X : Polynomial k) ∈ placeP (0 : k) := by
    have h : (Polynomial.X - Polynomial.C (0 : k)) ∈ placeP (0 : k) :=
      Ideal.mem_span_singleton_self _
    rwa [map_zero, sub_zero] at h
  have hover : placeP (0 : k) = Q.comap (algebraMap (Polynomial k) (Bring L.M)) :=
    Ideal.LiesOver.over
  rw [hover, Ideal.mem_comap] at hmem
  exact hmem

/-- **The coordinate vanishes at a place over the origin.** -/
theorem intOrd_baseX_pos (L : LineCover) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP (0 : k))] : 0 < intOrd L.M (coverPlace L 0 Q) (baseX L) :=
  (intOrd_pos_iff_mem (baseX_ne_zero L)).mpr (baseX_mem L Q)

/-! ### The equation satisfied by a root -/

variable {m : ℕ} {c : k}

/-- **The relation defining a root of the trinomial family** inside the integral model. -/
theorem trinomial_root_eq (L : LineCover) {y : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    y ^ (m + 1) = baseX L ^ m * (baseC L c * y + 1) := by
  have h := (Polynomial.mem_rootSet'.mp hy).2
  rw [ramTrinomial] at h
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_mul] at h
  linear_combination h

/-- A root of the trinomial family is nonzero: the equation would otherwise make the coordinate
vanish identically. -/
theorem root_ne_zero (L : LineCover) {y : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M)) : y ≠ 0 := by
  rintro rfl
  have h := trinomial_root_eq L hy
  rw [zero_pow (Nat.succ_ne_zero m), mul_zero, zero_add, mul_one] at h
  exact pow_ne_zero m (baseX_ne_zero L) h.symm

/-! ### The order of a root -/

/-- **The order of a root of the trinomial family at a place where the coordinate vanishes.**

The factor `c Y + 1` of the equation is congruent to `1` at such a place, hence contributes
nothing, so the equation reads `(m+1)` times the order of the root equals `m` times the order of
the coordinate; the root vanishes because the coordinate does. -/
theorem intOrd_root (L : LineCover) (hm : 1 ≤ m) {v : HeightOneSpectrum (Bring L.M)}
    (hX : 0 < intOrd L.M v (baseX L)) {y : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    0 < intOrd L.M v y ∧
      ((m : ℤ) + 1) * intOrd L.M v y = m * intOrd L.M v (baseX L) := by
  have hy0 : y ≠ 0 := root_ne_zero L hy
  have hX0 : baseX L ≠ 0 := baseX_ne_zero L
  have hrel := trinomial_root_eq L hy
  set u : Bring L.M := baseC L c * y + 1 with hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, mul_zero] at hrel
    exact pow_ne_zero _ hy0 hrel
  have hXm0 : baseX L ^ m ≠ 0 := pow_ne_zero _ hX0
  have hord : ((m : ℤ) + 1) * intOrd L.M v y
      = m * intOrd L.M v (baseX L) + intOrd L.M v u := by
    have h1 : intOrd L.M v (y ^ (m + 1)) = ((m : ℤ) + 1) * intOrd L.M v y := by
      rw [intOrd_pow hy0]; push_cast; ring
    have h2 : intOrd L.M v (baseX L ^ m * u)
        = m * intOrd L.M v (baseX L) + intOrd L.M v u := by
      rw [intOrd_mul hXm0 hu0, intOrd_pow hX0]
    rw [← h1, hrel, h2]
  have hupos : 0 ≤ intOrd L.M v u := intOrd_nonneg u
  have hmpos : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hmu : 0 < intOrd L.M v y := by nlinarith [hord, hX, hupos, hmpos]
  have hyQ : y ∈ v.asIdeal := (intOrd_pos_iff_mem hy0).mp hmu
  have huQ : u ∉ v.asIdeal := by
    intro hmem
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    have h1 : (1 : Bring L.M) = u - baseC L c * y := by rw [hu]; ring
    rw [h1]
    exact Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ _ hyQ)
  exact ⟨hmu, by rw [hord, intOrd_eq_zero_of_notMem huQ, add_zero]⟩

/-- **All the roots of the trinomial family vanish to the same order.** -/
theorem intOrd_root_eq_intOrd_root (L : LineCover) (hm : 1 ≤ m)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y y' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    intOrd L.M v y = intOrd L.M v y' := by
  have h := (intOrd_root L hm hX hy).2
  have h' := (intOrd_root L hm hX hy').2
  have hne : ((m : ℤ) + 1) ≠ 0 := by positivity
  have hzero : ((m : ℤ) + 1) * (intOrd L.M v y - intOrd L.M v y') = 0 := by
    rw [mul_sub, h, h']; ring
  have := (mul_eq_zero.mp hzero).resolve_left hne
  linarith

/-- **The coordinate vanishes to an order divisible by `m + 1`.**  The equation makes `(m+1)` times
the order of a root equal to `m` times the order of the coordinate, and `m` and `m + 1` are
coprime. -/
theorem succ_dvd_intOrd_baseX (L : LineCover) (hm : 1 ≤ m)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    ((m : ℤ) + 1) ∣ intOrd L.M v (baseX L) := by
  have h := (intOrd_root L hm hX hy).2
  have hdvd : ((m : ℤ) + 1) ∣ (m : ℤ) * intOrd L.M v (baseX L) := ⟨intOrd L.M v y, h.symm⟩
  have hcop : IsCoprime ((m : ℤ) + 1) (m : ℤ) := by
    refine ⟨1, -1, by ring⟩
  exact hcop.dvd_of_dvd_mul_left hdvd

/-! ### The root of unity relating two roots -/

/-- **The `(m+1)`-st roots of unity factor the difference of the `(m+1)`-st powers of two roots**,
and the equation turns that difference into a unit multiple of `X ^ m` times the difference of the
roots themselves. -/
theorem prod_sub_mul_eq (L : LineCover) {ω : k} (hω : IsPrimitiveRoot ω (m + 1))
    {y y' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    ∏ i ∈ Finset.range (m + 1), (y - baseC L (ω ^ i) * y')
      = baseC L c * baseX L ^ m * (y - y') := by
  have hωB : IsPrimitiveRoot (baseC L ω) (m + 1) :=
    hω.map_of_injective (baseCHom_injective L)
  have hprod : ∏ i ∈ Finset.range (m + 1), (y - baseC L ω ^ i * y')
      = y ^ (m + 1) - y' ^ (m + 1) := by
    have h := X_pow_sub_C_eq_prod hωB (Nat.succ_pos m)
      (rfl : y' ^ (m + 1) = y' ^ (m + 1))
    have h2 := congrArg (Polynomial.eval y) h
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at h2
    exact h2.symm
  simp only [baseC_pow]
  rw [hprod, trinomial_root_eq L hy, trinomial_root_eq L hy']
  ring

/-- **Exactly one `(m+1)`-st root of unity relates two roots beyond their common order.**

The roots all vanish to one and the same order `μ`, so no root of unity can bring two of them into
agreement to order `μ` for two different reasons: the difference of two distinct roots of unity is a
unit.  On the other hand one of them must, because the product of the `m + 1` differences
`y - ζ y'` is `c X ^ m (y - y')`, whose order exceeds `(m+1) μ`. -/
theorem exists_unique_root_label (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L))
    {ω : k} (hω : IsPrimitiveRoot ω (m + 1)) {y y' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    ∃! i : Fin (m + 1), y - baseC L (ω ^ (i : ℕ)) * y'
      ∈ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) := by
  classical
  have hy0 : y ≠ 0 := root_ne_zero L hy
  have hy'0 : y' ≠ 0 := root_ne_zero L hy'
  obtain ⟨hpos, hrel⟩ := intOrd_root L hm hX hy'
  have hyy' : intOrd L.M v y = intOrd L.M v y' := intOrd_root_eq_intOrd_root L hm hX hy hy'
  set N : ℕ := (intOrd L.M v y').toNat with hNdef
  have hN : (N : ℤ) = intOrd L.M v y' := Int.toNat_of_nonneg hpos.le
  have hω0 : ω ≠ 0 := hω.ne_zero (Nat.succ_ne_zero m)
  -- the order of `ω ^ i * y'` is the order of `y'`
  have hunit : ∀ i : ℕ, intOrd L.M v (baseC L (ω ^ i) * y') = intOrd L.M v y' := by
    intro i
    rw [intOrd_mul (baseC_ne_zero L (pow_ne_zero i hω0)) hy'0,
      intOrd_eq_zero_of_isUnit (isUnit_baseC L (pow_ne_zero i hω0)), zero_add]
  -- uniqueness
  have key : ∀ i j : Fin (m + 1),
      y - baseC L (ω ^ (i : ℕ)) * y' ∈ v.asIdeal ^ (N + 1) →
      y - baseC L (ω ^ (j : ℕ)) * y' ∈ v.asIdeal ^ (N + 1) → i = j := by
    intro i j hi hj
    by_contra hij
    have hωij : ω ^ (i : ℕ) ≠ ω ^ (j : ℕ) := fun h =>
      hij (Fin.ext (hω.pow_inj i.isLt j.isLt h))
    have hd : ω ^ (j : ℕ) - ω ^ (i : ℕ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hωij)
    have hmem : baseC L (ω ^ (j : ℕ) - ω ^ (i : ℕ)) * y' ∈ v.asIdeal ^ (N + 1) := by
      have hsub := Ideal.sub_mem (v.asIdeal ^ (N + 1)) hi hj
      have heq : baseC L (ω ^ (j : ℕ) - ω ^ (i : ℕ)) * y'
          = (y - baseC L (ω ^ (i : ℕ)) * y') - (y - baseC L (ω ^ (j : ℕ)) * y') := by
        rw [baseC_sub]; ring
      rw [heq]
      exact hsub
    have hne0 : baseC L (ω ^ (j : ℕ) - ω ^ (i : ℕ)) * y' ≠ 0 :=
      mul_ne_zero (baseC_ne_zero L hd) hy'0
    have hle := le_intOrd_of_mem_pow (K := L.M) hne0 hmem
    rw [intOrd_mul (baseC_ne_zero L hd) hy'0,
      intOrd_eq_zero_of_isUnit (isUnit_baseC L hd), zero_add] at hle
    push_cast at hle
    omega
  -- existence
  have hex : ∃ i : Fin (m + 1),
      y - baseC L (ω ^ (i : ℕ)) * y' ∈ v.asIdeal ^ (N + 1) := by
    by_cases hyeq : y = y'
    · refine ⟨⟨0, Nat.succ_pos m⟩, ?_⟩
      have hzero : y - baseC L (ω ^ ((⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) : ℕ)) * y' = 0 := by
        simp [hyeq]
      rw [hzero]
      exact Ideal.zero_mem _
    · by_contra hcon
      push_neg at hcon
      have hcon' : ∀ i ∈ Finset.range (m + 1),
          y - baseC L (ω ^ i) * y' ∉ v.asIdeal ^ (N + 1) := by
        intro i hi
        exact hcon ⟨i, Finset.mem_range.mp hi⟩
      have hne : ∀ i ∈ Finset.range (m + 1), y - baseC L (ω ^ i) * y' ≠ 0 := by
        intro i hi h
        exact hcon' i hi (h ▸ Ideal.zero_mem _)
      have hfac : ∀ i ∈ Finset.range (m + 1),
          intOrd L.M v (y - baseC L (ω ^ i) * y') = intOrd L.M v y' := by
        intro i hi
        have hlow : intOrd L.M v y' ≤ intOrd L.M v (y - baseC L (ω ^ i) * y') := by
          have h := min_intOrd_le_intOrd_sub (K := L.M) (v := v) (hne i hi)
          rw [hyy', hunit i, min_self] at h
          exact h
        have hhigh : intOrd L.M v (y - baseC L (ω ^ i) * y') ≤ intOrd L.M v y' := by
          by_contra hcc
          push_neg at hcc
          refine hcon' i hi (mem_pow_of_le_intOrd (K := L.M) ?_)
          push_cast
          omega
        exact le_antisymm hhigh hlow
      have hprodord : intOrd L.M v (∏ i ∈ Finset.range (m + 1), (y - baseC L (ω ^ i) * y'))
          = ((m : ℤ) + 1) * intOrd L.M v y' := by
        rw [intOrd_prod _ _ hne, Finset.sum_congr rfl hfac, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        push_cast
        ring
      rw [prod_sub_mul_eq L hω hy hy'] at hprodord
      have hyy'0 : y - y' ≠ 0 := sub_ne_zero.mpr hyeq
      rw [intOrd_mul (mul_ne_zero (baseC_ne_zero L hc) (pow_ne_zero m (baseX_ne_zero L))) hyy'0,
        intOrd_mul (baseC_ne_zero L hc) (pow_ne_zero m (baseX_ne_zero L)),
        intOrd_eq_zero_of_isUnit (isUnit_baseC L hc), zero_add,
        intOrd_pow (baseX_ne_zero L)] at hprodord
      have hge : intOrd L.M v y' ≤ intOrd L.M v (y - y') := by
        have h := min_intOrd_le_intOrd_sub (K := L.M) (v := v) hyy'0
        rw [hyy', min_self] at h
        exact h
      linarith
  obtain ⟨i₀, hi₀⟩ := hex
  exact ⟨i₀, hi₀, fun j hj => key j i₀ hj hi₀⟩

/-! ### Roots of unity in the base field -/

/-- The base field of the geometric theory contains a primitive root of unity of every order. -/
theorem exists_primitiveRoot_base (n : ℕ) (hn : 0 < n) : ∃ ζ : k, IsPrimitiveRoot ζ n := by
  haveI : NeZero ((n : ℕ) : k) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot k n

/-! ### Two distinct roots are exactly as close as the roots are deep -/

/-- **Two distinct roots of the trinomial family differ to exactly the common order of the roots.**

If the difference of two roots were deeper than that, then each of the `m` remaining factors of
`y ^ (m+1) - y' ^ (m+1)` would have exactly the common order, since it differs from the difference
of the roots by a unit multiple of a root.  Comparing that total with the order of
`c X ^ m (y - y')` forces the common order of the roots to vanish, which it does not. -/
theorem intOrd_sub_root (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y y' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M)) (hne : y ≠ y') :
    intOrd L.M v (y - y') = intOrd L.M v y' := by
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_base (m + 1) (Nat.succ_pos m)
  have hy'0 : y' ≠ 0 := root_ne_zero L hy'
  have hyy'0 : y - y' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨hpos, hrel⟩ := intOrd_root L hm hX hy'
  have hyy' : intOrd L.M v y = intOrd L.M v y' := intOrd_root_eq_intOrd_root L hm hX hy hy'
  have hge : intOrd L.M v y' ≤ intOrd L.M v (y - y') := by
    have h := min_intOrd_le_intOrd_sub (K := L.M) (v := v) hyy'0
    rw [hyy', min_self] at h
    exact h
  refine le_antisymm ?_ hge
  by_contra hcon
  push_neg at hcon
  have hω0 : ω ≠ 0 := hω.ne_zero (Nat.succ_ne_zero m)
  have hfac : ∀ i ∈ Finset.range (m + 1), i ≠ 0 →
      intOrd L.M v (y - baseC L (ω ^ i) * y') = intOrd L.M v y' := by
    intro i hi hi0
    have hωi : ω ^ i ≠ 1 := by
      intro h
      exact hi0 (hω.pow_inj (Finset.mem_range.mp hi) (Nat.succ_pos m) (by rw [pow_zero]; exact h))
    have hd : (1 : k) - ω ^ i ≠ 0 := sub_ne_zero.mpr (Ne.symm hωi)
    have heq : y - baseC L (ω ^ i) * y' = baseC L (1 - ω ^ i) * y' + (y - y') := by
      rw [baseC_sub, baseC_one]; ring
    have hterm : intOrd L.M v (baseC L (1 - ω ^ i) * y') = intOrd L.M v y' := by
      rw [intOrd_mul (baseC_ne_zero L hd) hy'0,
        intOrd_eq_zero_of_isUnit (isUnit_baseC L hd), zero_add]
    rw [heq, intOrd_add_of_lt (mul_ne_zero (baseC_ne_zero L hd) hy'0)
      (by rw [hterm]; exact hcon), hterm]
  have hnz : ∀ i ∈ Finset.range (m + 1), y - baseC L (ω ^ i) * y' ≠ 0 := by
    intro i hi h0
    by_cases hi0 : i = 0
    · subst hi0
      rw [pow_zero, baseC_one, one_mul, sub_eq_zero] at h0
      exact hne h0
    · have hval := hfac i hi hi0
      rw [h0, intOrd_zero] at hval
      exact hpos.ne hval
  have h0mem : (0 : ℕ) ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.succ_pos m)
  have hcard : ((Finset.range (m + 1)).erase 0).card = m := by
    rw [Finset.card_erase_of_mem h0mem, Finset.card_range]
    omega
  have hsum : intOrd L.M v (∏ i ∈ Finset.range (m + 1), (y - baseC L (ω ^ i) * y'))
      = intOrd L.M v (y - y') + m * intOrd L.M v y' := by
    rw [intOrd_prod _ _ hnz, ← Finset.add_sum_erase _ _ h0mem,
      Finset.sum_congr rfl (fun i hi => hfac i (Finset.mem_of_mem_erase hi)
        (Finset.ne_of_mem_erase hi)),
      Finset.sum_const, hcard, nsmul_eq_mul, pow_zero, baseC_one, one_mul]
  rw [prod_sub_mul_eq L hω hy hy'] at hsum
  rw [intOrd_mul (mul_ne_zero (baseC_ne_zero L hc) (pow_ne_zero m (baseX_ne_zero L))) hyy'0,
    intOrd_mul (baseC_ne_zero L hc) (pow_ne_zero m (baseX_ne_zero L)),
    intOrd_eq_zero_of_isUnit (isUnit_baseC L hc), zero_add,
    intOrd_pow (baseX_ne_zero L)] at hsum
  have hEN : (m : ℤ) * intOrd L.M v (baseX L) = m * intOrd L.M v y' := by linarith
  have hN0 : intOrd L.M v y' = 0 := by linear_combination hrel + hEN
  exact hpos.ne' hN0

/-- **Two distinct roots are congruent to no greater depth than their common order.** -/
theorem sub_notMem_pow_of_ne (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    {v : HeightOneSpectrum (Bring L.M)} (hX : 0 < intOrd L.M v (baseX L)) {y y' : Bring L.M}
    (hy : y ∈ (ramTrinomial m c).rootSet (Bring L.M))
    (hy' : y' ∈ (ramTrinomial m c).rootSet (Bring L.M)) (hne : y ≠ y') :
    y - y' ∉ v.asIdeal ^ ((intOrd L.M v y').toNat + 1) := by
  intro hmem
  have hyy'0 : y - y' ≠ 0 := sub_ne_zero.mpr hne
  have hle := le_intOrd_of_mem_pow (K := L.M) hyy'0 hmem
  rw [intOrd_sub_root L hm hc hX hy hy' hne] at hle
  obtain ⟨hpos, -⟩ := intOrd_root L hm hX hy'
  push_cast at hle
  omega

end Rigidity.RET

end
