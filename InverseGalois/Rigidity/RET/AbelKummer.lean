/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.KummerBlocks
import InverseGalois.Rigidity.RET.KummerIndep

/-!
# The multi-radical twisted Kummer extension

Adjoining to `K(T) = ℚ(ζ)(T)` the `n`-th roots `w i` of the `k` blocked Kummer data of
`Rigidity.RET.Abel` produces a field `M` which is Galois over `K(T)` with group `(ℤ/n) ^ k`.

The point of the *blocked* data is that the coefficient action of `c ∈ (ℤ/n)ˣ` on `K(T)` lifts to
`M`: the twisting identity `c · g i = g i ^ c * h i c ^ n` exhibits `c · g i` as an `n`-th power
times a power of `g i`, so the prescription `w i ↦ w i ^ c * h i c` is consistent.  The lifts are
assembled into a homomorphism `σ : (ℤ/n)ˣ →* Aut(M / ℚ(T))` from the cocycle identity satisfied by
the twisting factors, and they commute with the Kummer automorphisms because the exponent `c` in
the prescription *is* the cyclotomic character.

`M / ℚ(T)` is therefore Galois with group `(ℤ/n) ^ k × (ℤ/n)ˣ`, and the fixed field `L` of the
lifted cyclotomic character is a Galois extension of `ℚ(T)` with group `(ℤ/n) ^ k`.
-/

open Polynomial

namespace Rigidity.RET.Abel

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc IntermediateField

open Rigidity.RET.Cyclic

variable (n : ℕ) [hn : Fact (1 < n)] (k : ℕ)

/-! ### The splitting field of the blocked data -/

/-- The defining polynomial of the multi-radical extension. -/
def pAbel : (EE n)[X] := ∏ i : Fin k, ((X : (EE n)[X]) ^ n - C (gA n k i))

theorem kummerA_ne_zero (i : Fin k) : ((X : (EE n)[X]) ^ n - C (gA n k i)) ≠ 0 :=
  X_pow_sub_C_ne_zero (by have := hn.out; omega) _

theorem pAbel_ne_zero : pAbel n k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => kummerA_ne_zero n k i

/-- **The multi-radical Kummer extension** `M = K(T)(g₁ ^ (1/n), …, g_k ^ (1/n))`. -/
abbrev MA : Type := (pAbel n k).SplittingField

/-- A shortcut for a slow instance search. -/
instance (priority := high) algEEMA : Algebra (EE n) (MA n k) :=
  Polynomial.SplittingField.instAlgebra _

/-- A shortcut for a slow instance search. -/
instance (priority := high) algFFMA : Algebra FF (MA n k) :=
  Polynomial.SplittingField.instAlgebra _

/-- A shortcut for a slow instance search. -/
instance (priority := high) isScalarTowerFFEEMA : IsScalarTower FF (EE n) (MA n k) :=
  Polynomial.SplittingField.instIsScalarTower _

instance finiteDimensionalFFMA : FiniteDimensional FF (MA n k) :=
  .trans FF (EE n) (MA n k)

theorem splits_kummerA (i : Fin k) :
    (((X : (EE n)[X]) ^ n - C (gA n k i)).map (algebraMap (EE n) (MA n k))).Splits :=
  Polynomial.Splits.of_dvd (Polynomial.SplittingField.splits (pAbel n k))
    (by rw [Ne, Polynomial.map_eq_zero]; exact pAbel_ne_zero n k)
    (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

theorem map_kummerA (i : Fin k) :
    ((X : (EE n)[X]) ^ n - C (gA n k i)).map (algebraMap (EE n) (MA n k))
      = X ^ n - C (algebraMap (EE n) (MA n k) (gA n k i)) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]

theorem exists_rootA (i : Fin k) :
    ∃ x : MA n k, x ^ n = algebraMap (EE n) (MA n k) (gA n k i) := by
  have hdeg : (((X : (EE n)[X]) ^ n - C (gA n k i)).map
      (algebraMap (EE n) (MA n k))).degree ≠ 0 := by
    rw [map_kummerA, Polynomial.degree_X_pow_sub_C (by have := hn.out; omega)]
    intro hc
    have : n = 0 := by exact_mod_cast hc
    have := hn.out
    omega
  obtain ⟨x, hx⟩ := (splits_kummerA n k i).exists_eval_eq_zero hdeg
  refine ⟨x, ?_⟩
  rw [map_kummerA, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at hx
  exact hx

/-- The chosen `n`-th root of the `i`-th blocked datum. -/
def wA (i : Fin k) : MA n k := (exists_rootA n k i).choose

theorem wA_pow (i : Fin k) : wA n k i ^ n = algebraMap (EE n) (MA n k) (gA n k i) :=
  (exists_rootA n k i).choose_spec

theorem wA_ne_zero (i : Fin k) : wA n k i ≠ 0 := by
  intro h
  refine gA_ne_zero n k i ((algebraMap (EE n) (MA n k)).injective ?_)
  rw [map_zero, ← wA_pow n k i, h, zero_pow (by have := hn.out; omega)]

/-! ### The roots of unity -/

/-- `ζ`, as an element of `K(T)`. -/
def zetaE : EE n := algebraMap (KK n) (EE n) (zeta n)

theorem zetaE_isPrimitiveRoot : IsPrimitiveRoot (zetaE n) n :=
  (zeta_spec n).map_of_injective (algebraMap (KK n) (EE n)).injective

/-- `ζ`, as an element of `M`. -/
def zetaMA : MA n k := algebraMap (EE n) (MA n k) (zetaE n)

theorem zetaMA_isPrimitiveRoot : IsPrimitiveRoot (zetaMA n k) n :=
  (zetaE_isPrimitiveRoot n).map_of_injective (algebraMap (EE n) (MA n k)).injective

theorem zetaMA_ne_zero : zetaMA n k ≠ 0 := by
  intro h
  have := (zetaMA_isPrimitiveRoot n k).pow_eq_one
  rw [h, zero_pow (by have := hn.out; omega)] at this
  exact zero_ne_one this

/-! ### The radicals generate -/

theorem adjoin_wA_eq_top : IntermediateField.adjoin (EE n) (Set.range (wA n k)) = ⊤ := by
  set S : IntermediateField (EE n) (MA n k) := IntermediateField.adjoin (EE n) (Set.range (wA n k))
    with hSdef
  have hsub : (pAbel n k).rootSet (MA n k) ⊆ (S : Set (MA n k)) := by
    intro x hx
    rw [Polynomial.mem_rootSet] at hx
    obtain ⟨-, hx0⟩ := hx
    have hx1 : ∏ i : Fin k, (Polynomial.aeval x) ((X : (EE n)[X]) ^ n - C (gA n k i)) = 0 := by
      rw [← map_prod]; exact hx0
    rw [Finset.prod_eq_zero_iff] at hx1
    obtain ⟨i, -, hi⟩ := hx1
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hi
    have hq : (x / wA n k i) ^ n = 1 := by
      rw [div_pow, hi, ← wA_pow n k i, div_self (pow_ne_zero _ (wA_ne_zero n k i))]
    obtain ⟨j, -, hj⟩ := (zetaMA_isPrimitiveRoot n k).eq_pow_of_pow_eq_one hq
    have hxeq : x = zetaMA n k ^ j * wA n k i := by
      rw [hj, div_mul_cancel₀ _ (wA_ne_zero n k i)]
    rw [hxeq]
    exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ _) _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  refine top_unique fun x _ => ?_
  have h1 : x ∈ Algebra.adjoin (EE n) ((pAbel n k).rootSet (MA n k)) := by
    rw [Polynomial.SplittingField.adjoin_rootSet]
    trivial
  exact Algebra.adjoin_le hsub h1

/-! ### The Kummer datum -/

/-- The blocked radicals, packaged for the multi-radical Kummer theory. -/
def setupA : Kummer.Setup (EE n) (MA n k) (Fin k) n where
  zeta := zetaE n
  g := gA n k
  w := wA n k
  isPrimitiveRoot := zetaE_isPrimitiveRoot n
  g_ne_zero := gA_ne_zero n k
  w_pow := wA_pow n k
  adjoin_eq_top := adjoin_wA_eq_top n k
  indep := fun m y hy h i => gA_indep n k m y hy h i

instance isGalois_EE_MA : IsGalois (EE n) (MA n k) := (setupA n k).isGalois

instance finiteDimensional_EE_MA : FiniteDimensional (EE n) (MA n k) :=
  (setupA n k).finiteDimensional

/-- **The multi-radical extension has degree `n ^ k` over `K(T)`.** -/
theorem finrank_EE_MA : Module.finrank (EE n) (MA n k) = n ^ k := by
  rw [(setupA n k).finrank_eq, Fintype.card_fin]

theorem card_aut_EE_MA : Nat.card (MA n k ≃ₐ[EE n] MA n k) = n ^ k := by
  rw [(setupA n k).card_aut, Fintype.card_fin]

/-- Every automorphism over `K(T)` multiplies the radicals by powers of `ζ`. -/
theorem exists_zpow_of_autA (ρ : MA n k ≃ₐ[EE n] MA n k) :
    ∃ m : Fin k → ℤ, ∀ i, ρ (wA n k i) = zetaMA n k ^ m i * wA n k i :=
  (setupA n k).exists_zpow_of_aut ρ

/-- Every prescribed system of powers of `ζ` is realized by an automorphism over `K(T)`. -/
theorem exists_autA (m : Fin k → ℤ) : ∃ ρ : MA n k ≃ₐ[EE n] MA n k,
    ∀ i, ρ (wA n k i) = zetaMA n k ^ m i * wA n k i :=
  (setupA n k).exists_aut_zpow m

/-- Two ring maps out of `M` agreeing on `K(T)` and on every radical agree. -/
theorem ringHom_ext_MA {φ ψ : MA n k →+* MA n k}
    (hbase : ∀ x : EE n, φ (algebraMap (EE n) (MA n k) x) = ψ (algebraMap (EE n) (MA n k) x))
    (hw : ∀ i, φ (wA n k i) = ψ (wA n k i)) (y : MA n k) : φ y = ψ y := by
  have hy : y ∈ Algebra.adjoin (EE n) (Set.range (wA n k)) := by
    show y ∈ Algebra.adjoin (EE n) (Set.range (setupA n k).w)
    rw [(setupA n k).algebra_adjoin_eq_top]; trivial
  induction hy using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hw i
  | algebraMap x => exact hbase x
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

/-- An automorphism of `M` over `ℚ(T)` is determined by its restriction to `K(T)` and its values
on the radicals. -/
theorem algEquiv_ext_MA {f g : MA n k ≃ₐ[FF] MA n k}
    (hbase : ∀ x : EE n, f (algebraMap (EE n) (MA n k) x) = g (algebraMap (EE n) (MA n k) x))
    (hw : ∀ i, f (wA n k i) = g (wA n k i)) : f = g :=
  AlgEquiv.ext fun y =>
    ringHom_ext_MA n k (φ := (f : MA n k →+* MA n k)) (ψ := (g : MA n k →+* MA n k)) hbase hw y

/-! ### Lifting the coefficient action -/

/-- The twisting factor of the `i`-th datum, viewed in `M`. -/
def hMA (i : Fin k) (c : (ZMod n)ˣ) : MA n k := algebraMap (EE n) (MA n k) (hA n k i c)

/-- The prescribed image of the `i`-th radical under the lift of `c`. -/
def uA (i : Fin k) (c : (ZMod n)ˣ) : MA n k := wA n k i ^ cnat n c * hMA n k i c

theorem hMA_ne_zero (i : Fin k) (c : (ZMod n)ˣ) : hMA n k i c ≠ 0 := fun h =>
  hA_ne_zero n k i c ((algebraMap (EE n) (MA n k)).injective (by rw [map_zero, ← hMA, h]))

theorem uA_ne_zero (i : Fin k) (c : (ZMod n)ˣ) : uA n k i c ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (wA_ne_zero n k i)) (hMA_ne_zero n k i c)

/-- The prescription is consistent with the twisting identity. -/
theorem uA_pow (i : Fin k) (c : (ZMod n)ˣ) :
    uA n k i c ^ n = algebraMap (EE n) (MA n k) (sigmaE n c (gA n k i)) := by
  simp only [uA, hMA]
  rw [sigmaE_gA, map_mul, map_pow, map_pow, ← wA_pow, mul_pow, ← pow_mul, ← pow_mul,
    Nat.mul_comm (cnat n c) n]

/-- The coefficient action, viewed as an embedding of `K(T)` into `M` over `ℚ(T)`. -/
def fA (c : (ZMod n)ˣ) : EE n →ₐ[FF] MA n k :=
  (IsScalarTower.toAlgHom FF (EE n) (MA n k)).comp (sigmaE n c).toAlgHom

theorem fA_apply (c : (ZMod n)ˣ) (x : EE n) :
    fA n k c x = algebraMap (EE n) (MA n k) (sigmaE n c x) := rfl

theorem isIntegral_wA (i : Fin k) : IsIntegral (EE n) (wA n k i) :=
  IsIntegral.of_finite _ _

theorem splits_minpoly_wA (c : (ZMod n)ˣ) (i : Fin k) :
    ((minpoly (EE n) (wA n k i)).map (fA n k c).toRingHom).Splits := by
  have hdvd : minpoly (EE n) (wA n k i) ∣ (X : (EE n)[X]) ^ n - C (gA n k i) :=
    minpoly.dvd _ _ (by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, wA_pow, sub_self])
  have hmap : ((X : (EE n)[X]) ^ n - C (gA n k i)).map (fA n k c).toRingHom
      = X ^ n - C (uA n k i c ^ n) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, uA_pow]
    rfl
  have hsplit : (((X : (EE n)[X]) ^ n - C (gA n k i)).map (fA n k c).toRingHom).Splits := by
    rw [hmap]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (zetaMA_isPrimitiveRoot n k) rfl
  exact Polynomial.Splits.of_dvd hsplit
    (by rw [hmap]; exact X_pow_sub_C_ne_zero (by have := hn.out; omega) _)
    (Polynomial.map_dvd _ hdvd)

/-- The coefficient action extends to an endomorphism of `M`. -/
theorem exists_liftA (c : (ZMod n)ˣ) : ∃ φ : MA n k →ₐ[FF] MA n k,
    ∀ x : EE n, φ (algebraMap (EE n) (MA n k) x) = algebraMap (EE n) (MA n k) (sigmaE n c x) := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_adjoin_splits'
    (L := EE n) (S := Set.range (wA n k)) (fA n k c)
    (fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact ⟨isIntegral_wA n k i, splits_minpoly_wA n k c i⟩)
    (adjoin_wA_eq_top n k)
  exact ⟨φ, fun x => DFunLike.congr_fun hφ x⟩

/-- Any lift of the coefficient action acts on `ζ` by the cyclotomic character. -/
theorem hom_zetaMA (c : (ZMod n)ˣ) (φ : MA n k →ₐ[FF] MA n k)
    (hφ : ∀ x : EE n,
      φ (algebraMap (EE n) (MA n k) x) = algebraMap (EE n) (MA n k) (sigmaE n c x)) :
    φ (zetaMA n k) = zetaMA n k ^ cnat n c := by
  rw [zetaMA, hφ, zetaE, sigmaE_algebraMap, sigmaK_zeta, map_pow, map_pow]

/-- The inverse representative undoes the representative modulo `n`. -/
theorem n_dvd_cnat_inv_mul (c : (ZMod n)ˣ) :
    (n : ℤ) ∣ (cnat n c⁻¹ : ℤ) * (cnat n c : ℤ) - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cnat_cast, cnat_cast, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]

/-- **The coefficient action lifts to `M`**, with the prescribed values on the radicals. -/
theorem exists_sigmaA (c : (ZMod n)ˣ) : ∃ φ : MA n k ≃ₐ[FF] MA n k,
    (∀ x : EE n, φ (algebraMap (EE n) (MA n k) x) = algebraMap (EE n) (MA n k) (sigmaE n c x)) ∧
      ∀ i, φ (wA n k i) = uA n k i c := by
  obtain ⟨φ₀, hφ₀⟩ := exists_liftA n k c
  have hroot : ∀ i, ∃ j : ℕ, φ₀ (wA n k i) = zetaMA n k ^ j * uA n k i c := by
    intro i
    have h1 : (φ₀ (wA n k i) / uA n k i c) ^ n = 1 := by
      rw [div_pow, ← map_pow, wA_pow, hφ₀, ← uA_pow,
        div_self (pow_ne_zero _ (uA_ne_zero n k i c))]
    obtain ⟨j, -, hj⟩ := (zetaMA_isPrimitiveRoot n k).eq_pow_of_pow_eq_one h1
    exact ⟨j, by rw [hj, div_mul_cancel₀ _ (uA_ne_zero n k i c)]⟩
  choose j hj using hroot
  obtain ⟨ρ, hρ⟩ := exists_autA n k (fun i => -(j i : ℤ) * (cnat n c⁻¹ : ℤ))
  refine ⟨(ρ.restrictScalars FF).trans (AlgEquiv.ofBijective φ₀ φ₀.bijective), fun x => ?_,
    fun i => ?_⟩
  · show φ₀ (ρ (algebraMap (EE n) (MA n k) x)) = _
    rw [AlgEquiv.commutes, hφ₀]
  · show φ₀ (ρ (wA n k i)) = _
    rw [hρ, map_mul, map_zpow₀, hom_zetaMA n k c φ₀ hφ₀, hj i, ← mul_assoc, ← zpow_natCast _ (j i),
      ← zpow_natCast (zetaMA n k) (cnat n c), ← zpow_mul, ← zpow_add₀ (zetaMA_ne_zero n k)]
    have hz : zetaMA n k ^ ((cnat n c : ℤ) * (-(j i : ℤ) * (cnat n c⁻¹ : ℤ)) + (j i : ℤ)) = 1 := by
      rw [(zetaMA_isPrimitiveRoot n k).zpow_eq_one_iff_dvd]
      obtain ⟨t, ht⟩ := n_dvd_cnat_inv_mul n c
      exact ⟨-(j i : ℤ) * t, by linear_combination -(j i : ℤ) * ht⟩
    rw [hz, one_mul]

/-- **The lift of the unit `c`** to an automorphism of `M / ℚ(T)`. -/
def sigmaMAe (c : (ZMod n)ˣ) : MA n k ≃ₐ[FF] MA n k := (exists_sigmaA n k c).choose

@[simp] theorem sigmaMAe_algebraMap (c : (ZMod n)ˣ) (x : EE n) :
    sigmaMAe n k c (algebraMap (EE n) (MA n k) x) = algebraMap (EE n) (MA n k) (sigmaE n c x) :=
  (exists_sigmaA n k c).choose_spec.1 x

@[simp] theorem sigmaMAe_wA (c : (ZMod n)ˣ) (i : Fin k) :
    sigmaMAe n k c (wA n k i) = uA n k i c :=
  (exists_sigmaA n k c).choose_spec.2 i

@[simp] theorem sigmaMAe_zetaMA (c : (ZMod n)ˣ) :
    sigmaMAe n k c (zetaMA n k) = zetaMA n k ^ cnat n c := by
  rw [zetaMA, sigmaMAe_algebraMap, zetaE, sigmaE_algebraMap, sigmaK_zeta, map_pow, map_pow]

theorem sigmaMAe_one : sigmaMAe n k 1 = 1 := by
  refine algEquiv_ext_MA n k (fun x => ?_) (fun i => ?_)
  · rw [sigmaMAe_algebraMap, map_one, AlgEquiv.one_apply, AlgEquiv.one_apply]
  · rw [sigmaMAe_wA, AlgEquiv.one_apply]
    simp only [uA, hMA]
    rw [cnat_one, pow_one, hA_one, map_one, mul_one]

theorem sigmaMAe_mul (c d : (ZMod n)ˣ) :
    sigmaMAe n k (c * d) = sigmaMAe n k c * sigmaMAe n k d := by
  refine algEquiv_ext_MA n k (fun x => ?_) (fun i => ?_)
  · rw [AlgEquiv.mul_apply, sigmaMAe_algebraMap, sigmaMAe_algebraMap, sigmaMAe_algebraMap,
      map_mul, AlgEquiv.mul_apply]
  · have hcoc := congrArg (algebraMap (EE n) (MA n k)) (hA_cocycle n k i c d)
    rw [map_mul, map_mul, map_zpow₀, map_pow, ← wA_pow] at hcoc
    have hpow : wA n k i ^ (cnat n c * cnat n d)
        = wA n k i ^ cnat n (c * d) * (wA n k i ^ n) ^ kk n c d := by
      rw [← zpow_natCast (wA n k i) (cnat n c * cnat n d),
        ← zpow_natCast (wA n k i) (cnat n (c * d)), ← zpow_natCast (wA n k i) n, ← zpow_mul,
        ← zpow_add₀ (wA_ne_zero n k i)]
      congr 1
      have h := n_mul_kk n c d
      push_cast
      linarith
    simp only [AlgEquiv.mul_apply, sigmaMAe_wA, uA, hMA, map_mul, map_pow, sigmaMAe_algebraMap]
    rw [mul_pow, ← pow_mul, hpow, ← hcoc]
    ring

/-- **The lifted cyclotomic character** on the multi-radical extension. -/
def sigmaMA : (ZMod n)ˣ →* (MA n k ≃ₐ[FF] MA n k) where
  toFun := sigmaMAe n k
  map_one' := sigmaMAe_one n k
  map_mul' := sigmaMAe_mul n k

@[simp] theorem sigmaMA_apply (c : (ZMod n)ˣ) : sigmaMA n k c = sigmaMAe n k c := rfl

theorem sigmaMA_injective : Function.Injective (sigmaMA n k) := by
  intro c d h
  refine sigmaE_injective n (AlgEquiv.ext fun x => ?_)
  refine (algebraMap (EE n) (MA n k)).injective ?_
  rw [← sigmaMAe_algebraMap, ← sigmaMAe_algebraMap, ← sigmaMA_apply, ← sigmaMA_apply, h]

instance finite_range_sigmaMA : Finite ↥(MonoidHom.range (sigmaMA n k)) :=
  Finite.of_equiv _ (MonoidHom.ofInjective (sigmaMA_injective n k)).toEquiv

theorem card_range_sigmaMA : Nat.card ↥(MonoidHom.range (sigmaMA n k)) = n.totient := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (sigmaMA_injective n k)).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-! ### The Galois group of `M / ℚ(T)` -/

/-- **An element of `M` fixed by every automorphism over `K(T)` lies in `K(T)`.** -/
theorem exists_of_aut_fixed {x : MA n k} (hx : ∀ ρ : MA n k ≃ₐ[EE n] MA n k, ρ x = x) :
    ∃ y : EE n, algebraMap (EE n) (MA n k) y = x :=
  IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed x).mpr hx)

/-- **`ℚ(T)` is the whole field of invariants of `M`.** -/
theorem fixedField_top_MA :
    IntermediateField.fixedField (⊤ : Subgroup (MA n k ≃ₐ[FF] MA n k)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := exists_of_aut_fixed n k
    (fun ρ => hx (ρ.restrictScalars FF) (Subgroup.mem_top _))
  have hy : ∀ c, sigmaE n c y = y := by
    intro c
    have hfix := hx (sigmaMAe n k c) (Subgroup.mem_top _)
    rw [sigmaMAe_algebraMap] at hfix
    exact (algebraMap (EE n) (MA n k)).injective hfix
  obtain ⟨z, rfl⟩ := exists_of_sigmaE_fixed n hy
  rw [IntermediateField.mem_bot, ← IsScalarTower.algebraMap_apply]
  exact ⟨z, rfl⟩

instance isGalois_FF_MA : IsGalois FF (MA n k) :=
  IsGalois.of_fixedField_eq_bot FF (MA n k) (fixedField_top_MA n k)

theorem finrank_FF_MA : Module.finrank FF (MA n k) = n.totient * n ^ k := by
  rw [← Module.finrank_mul_finrank FF (EE n) (MA n k), finrank_FF_EE, finrank_EE_MA]

/-! ### The layer of degree `n ^ k` -/

/-- **The layer**: the fixed field of the lifted cyclotomic character. -/
def LA : IntermediateField FF (MA n k) :=
  IntermediateField.fixedField (MonoidHom.range (sigmaMA n k))

instance (priority := high) isScalarTowerFFFFMA : IsScalarTower FF FF (MA n k) :=
  ⟨fun a b c => by rw [smul_eq_mul, mul_smul]⟩

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) algFFLA : Algebra FF (LA n k) := IntermediateField.algebra' (LA n k)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) isScalarTowerFFLAMA : IsScalarTower FF (LA n k) (MA n k) :=
  IntermediateField.isScalarTower_mid' (LA n k)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) finiteDimensionalFFLA : FiniteDimensional FF (LA n k) :=
  IntermediateField.finiteDimensional_left (LA n k)

theorem mem_LA_iff {x : MA n k} : x ∈ LA n k ↔ ∀ c, sigmaMAe n k c x = x := by
  rw [LA, IntermediateField.mem_fixedField_iff]
  refine ⟨fun hx c => hx (sigmaMA n k c) ⟨c, rfl⟩, fun hx f hf => ?_⟩
  obtain ⟨c, rfl⟩ := hf
  exact hx c

theorem finrank_LA_MA : Module.finrank (LA n k) (MA n k) = n.totient := by
  rw [LA, IntermediateField.finrank_fixedField_eq_card, card_range_sigmaMA]

/-- **The layer has degree `n ^ k` over `ℚ(T)`.** -/
theorem finrank_FF_LA : Module.finrank FF (LA n k) = n ^ k := by
  have h := Module.finrank_mul_finrank FF (LA n k) (MA n k)
  rw [finrank_LA_MA, finrank_FF_MA, Nat.mul_comm n.totient (n ^ k)] at h
  exact Nat.eq_of_mul_eq_mul_right (totient_pos n) h

/-! ### Restricting the Kummer automorphisms to the layer -/

theorem zetaMA_zpow_pow_comm (a : ℤ) (b : ℕ) :
    (zetaMA n k ^ a) ^ b = (zetaMA n k ^ b) ^ a := by
  rw [← zpow_natCast (zetaMA n k ^ a) b, ← zpow_mul, ← zpow_natCast (zetaMA n k) b, ← zpow_mul,
    mul_comm]

/-- **The Kummer automorphisms commute with the lifted cyclotomic character**: the exponent in
the lift of `c` is the cyclotomic character of `c`. -/
theorem commute_aut_sigmaMAe (ρ : MA n k ≃ₐ[EE n] MA n k) (c : (ZMod n)ˣ) (x : MA n k) :
    ρ (sigmaMAe n k c x) = sigmaMAe n k c (ρ x) := by
  have key : (ρ.restrictScalars FF) * sigmaMAe n k c
      = sigmaMAe n k c * (ρ.restrictScalars FF) := by
    refine algEquiv_ext_MA n k (fun y => ?_) (fun i => ?_)
    · show ρ (sigmaMAe n k c (algebraMap (EE n) (MA n k) y))
        = sigmaMAe n k c (ρ (algebraMap (EE n) (MA n k) y))
      rw [sigmaMAe_algebraMap, ρ.commutes, ρ.commutes, sigmaMAe_algebraMap]
    · obtain ⟨m, hm⟩ := exists_zpow_of_autA n k ρ
      have hlhs : ρ (sigmaMAe n k c (wA n k i))
          = (zetaMA n k ^ m i) ^ cnat n c * uA n k i c := by
        rw [sigmaMAe_wA]
        simp only [uA, hMA]
        rw [map_mul, map_pow, hm, ρ.commutes, mul_pow]
        ring
      have hrhs : sigmaMAe n k c (ρ (wA n k i))
          = (zetaMA n k ^ cnat n c) ^ m i * uA n k i c := by
        rw [hm, map_mul, map_zpow₀, sigmaMAe_zetaMA, sigmaMAe_wA]
      show ρ (sigmaMAe n k c (wA n k i)) = sigmaMAe n k c (ρ (wA n k i))
      rw [hlhs, hrhs, zetaMA_zpow_pow_comm]
  exact congrArg (fun e : MA n k ≃ₐ[FF] MA n k => e x) key

theorem aut_mem_LA (ρ : MA n k ≃ₐ[EE n] MA n k) {x : MA n k} (hx : x ∈ LA n k) :
    ρ x ∈ LA n k := by
  rw [mem_LA_iff] at hx ⊢
  intro c
  rw [← commute_aut_sigmaMAe n k ρ c x, hx]

/-- A Kummer automorphism, restricted to the layer. -/
def resAHom (ρ : MA n k ≃ₐ[EE n] MA n k) : LA n k →ₐ[FF] LA n k where
  toFun x := ⟨ρ (x : MA n k), aut_mem_LA n k ρ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (by
    show ρ ((algebraMap FF (LA n k) r : LA n k) : MA n k)
      = ((algebraMap FF (LA n k) r : LA n k) : MA n k)
    rw [IntermediateField.coe_algebraMap_apply]
    exact (ρ.restrictScalars FF).commutes r)

/-- A Kummer automorphism, as an automorphism of the layer over `ℚ(T)`. -/
def resAe (ρ : MA n k ≃ₐ[EE n] MA n k) : LA n k ≃ₐ[FF] LA n k :=
  AlgEquiv.ofBijective (resAHom n k ρ) (resAHom n k ρ).bijective

@[simp] theorem resAe_apply (ρ : MA n k ≃ₐ[EE n] MA n k) (x : LA n k) :
    (resAe n k ρ x : MA n k) = ρ (x : MA n k) := rfl

/-- **The restriction homomorphism** from the Kummer group to the automorphisms of the layer. -/
def resA : (MA n k ≃ₐ[EE n] MA n k) →* (LA n k ≃ₐ[FF] LA n k) where
  toFun := resAe n k
  map_one' := AlgEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => Subtype.ext rfl

theorem fixedField_range_resA :
    IntermediateField.fixedField (MonoidHom.range (resA n k)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hfix : ∀ ρ : MA n k ≃ₐ[EE n] MA n k, ρ (x : MA n k) = (x : MA n k) :=
    fun ρ => congrArg Subtype.val (hx (resA n k ρ) ⟨ρ, rfl⟩)
  obtain ⟨y, hy⟩ := exists_of_aut_fixed n k hfix
  have hyfix : ∀ c, sigmaE n c y = y := by
    intro c
    refine (algebraMap (EE n) (MA n k)).injective ?_
    rw [← sigmaMAe_algebraMap, hy]
    exact (mem_LA_iff n k).mp x.2 c
  obtain ⟨z, hz⟩ := exists_of_sigmaE_fixed n hyfix
  refine IntermediateField.mem_bot.mpr ⟨z, Subtype.ext ?_⟩
  rw [IntermediateField.coe_algebraMap_apply, ← hy, ← hz, ← IsScalarTower.algebraMap_apply]

theorem fixedField_top_LA :
    IntermediateField.fixedField (⊤ : Subgroup (LA n k ≃ₐ[FF] LA n k)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hmem : x ∈ IntermediateField.fixedField (MonoidHom.range (resA n k)) := by
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    exact fun f _ => hx f (Subgroup.mem_top f)
  rwa [fixedField_range_resA] at hmem

instance isGalois_FF_LA : IsGalois FF (LA n k) :=
  IsGalois.of_fixedField_eq_bot FF (LA n k) (fixedField_top_LA n k)

theorem card_aut_LA : Nat.card (LA n k ≃ₐ[FF] LA n k) = n ^ k := by
  rw [IsGalois.card_aut_eq_finrank, finrank_FF_LA]

theorem resA_surjective : Function.Surjective (resA n k) := by
  have h := IntermediateField.fixingSubgroup_fixedField (MonoidHom.range (resA n k))
  rw [fixedField_range_resA, IntermediateField.fixingSubgroup_bot] at h
  intro g
  have hg : g ∈ MonoidHom.range (resA n k) := by rw [← h]; trivial
  exact hg

theorem resA_bijective : Function.Bijective (resA n k) :=
  (Nat.bijective_iff_surjective_and_card _).mpr
    ⟨resA_surjective n k, by rw [card_aut_EE_MA, card_aut_LA]⟩

/-- **The Galois group of the layer** is the Kummer group of the multi-radical extension. -/
def galLAEquiv : (MA n k ≃ₐ[EE n] MA n k) ≃* (LA n k ≃ₐ[FF] LA n k) :=
  MulEquiv.ofBijective (resA n k) (resA_bijective n k)

/-- **The Galois group of the layer is a `k`-fold product of the group of `n`-th roots of
unity.** -/
def galLAEquivRoots : (LA n k ≃ₐ[FF] LA n k) ≃* (Fin k → rootsOfUnity n (MA n k)) :=
  (galLAEquiv n k).symm.trans (setupA n k).galEquiv

end

end Rigidity.RET.Abel
