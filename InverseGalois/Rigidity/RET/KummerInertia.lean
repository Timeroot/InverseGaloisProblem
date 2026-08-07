/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.InertiaGen
import InverseGalois.Rigidity.RET.Twist
import InverseGalois.Rigidity.RET.Unramified

/-!
# Ramification of Kummer covers of the line

The cover of the line cut out by `wⁿ = a(T)`, for a polynomial `a` over the algebraically closed
constant field `ℚ̄`, ramifies only where `a` vanishes (and possibly at infinity).  This module
proves that, and instantiates it for the **two-point datum**
`a = (X - t₀)(X - t₁)^{n-1}` with `t₀ ≠ t₁`, whose cover is a connected cyclic cover of the line
branched inside `{t₀, t₁}`.

The unramifiedness argument is elementary and purely local.  Kummer theory (`autEquivZmod`)
says that a deck transformation `σ` scales the chosen root `w` by a root of unity `ζᵐ`, which is a
*constant*.  If `σ` lies in the inertia group of a place `Q`, then `σ w - w = (ζᵐ - 1) w ∈ Q`; at a
place where `w` itself is outside `Q` — which happens exactly where `a` is invertible, since
`wⁿ = a` — primality of `Q` forces the constant `ζᵐ - 1` into `Q`, and a nonzero constant is a
unit.  Hence `ζᵐ = 1` and `σ = 1`.

Irreducibility of `Yⁿ - a` for the two-point datum is Eisenstein at the prime `X - t₀` of `ℚ̄[X]`,
which divides `a` exactly once because `t₀ ≠ t₁`, followed by Gauss's lemma.

## Main definitions

* `Rigidity.RET.kummerRoot` — the chosen `n`-th root of `a` in the splitting field of `Yⁿ - a`.
* `Rigidity.RET.kummerRootB` — that root, as an element of the integral model of the cover.
* `Rigidity.RET.kummerA` — the two-point datum `(X - t₀)(X - t₁)^{n-1}`.

## Main results

* `Rigidity.RET.irreducible_Y_pow_sub_C_of_eisenstein`,
  `Rigidity.RET.irreducible_X_pow_sub_C_ratFunc_of_eisenstein` — Eisenstein for `Yⁿ - a` over
  `F[X]` and over `F(X)`.
* `Rigidity.RET.kummer_smul_root` — a deck transformation of a Kummer extension scales the chosen
  root by a power of the root of unity, and only the identity scales it by `1`.
* `Rigidity.RET.const_eq_one_of_mem_inertia` — an inertia element scaling an element outside the
  place by a constant scales it by `1`.
* `Rigidity.RET.kummer_inertia_eq_one` — the Kummer cover `wⁿ = a` is unramified at every place
  where `a` is invertible.
* `Rigidity.RET.irreducible_kummerA` — irreducibility of the two-point Kummer polynomial.
* `Rigidity.RET.isUnramifiedOutside_kummerCover` — the two-point Kummer cover is unramified
  outside `{t₀, t₁}`.
* `Rigidity.RET.le_ramificationIdx_of_pow_dvd`, `Rigidity.RET.geomInertia_eq_top_of_finrank_le` —
  a place whose power divides the extended place is totally ramified, and a totally ramified place
  has full inertia.
* `Rigidity.RET.geomInertia_eq_top_kummerCover`, `Rigidity.RET.isInertiaGenAt_kummerCover` — the
  two-point Kummer cover is totally ramified at `t₀`, so a generator of its (cyclic) deck group is
  a distinguished inertia element there.
-/

open Polynomial
open scoped Pointwise

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

/-! ### Eisenstein irreducibility for `Yⁿ - a` -/

section Eisenstein

variable {F : Type*} [Field F]

theorem irreducible_Y_pow_sub_C_of_eisenstein {n : ℕ} (hn : n ≠ 0) {a p : Polynomial F}
    (hp : Prime p) (h1 : p ∣ a) (h2 : ¬ (p ^ 2 ∣ a)) :
    Irreducible ((X : (Polynomial F)[X]) ^ n - C a) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hmonic : ((X : (Polynomial F)[X]) ^ n - C a).Monic := monic_X_pow_sub_C _ hn
  have hdeg : ((X : (Polynomial F)[X]) ^ n - C a).degree = (n : WithBot ℕ) :=
    degree_X_pow_sub_C hn0 _
  have hP : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  refine irreducible_of_eisenstein_criterion (P := Ideal.span {p}) hP ?_ ?_ ?_ ?_
    hmonic.isPrimitive
  · rw [hmonic.leadingCoeff]
    exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro m hm
    rw [hdeg] at hm
    have hmn : ¬ m = n := by
      intro h
      exact absurd hm (by simp [h])
    rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hmn]
    by_cases hm0 : m = 0
    · rw [if_pos hm0, zero_sub]
      exact neg_mem (Ideal.mem_span_singleton.mpr h1)
    · rw [if_neg hm0, sub_zero]
      exact Ideal.zero_mem _
  · rw [hdeg]
    exact_mod_cast hn0
  · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg (Ne.symm hn), if_pos rfl, zero_sub,
      Ideal.span_singleton_pow]
    intro h
    exact h2 (dvd_neg.mp (Ideal.mem_span_singleton.mp h))

theorem irreducible_X_pow_sub_C_ratFunc_of_eisenstein {n : ℕ} (hn : n ≠ 0) {a p : Polynomial F}
    (hp : Prime p) (h1 : p ∣ a) (h2 : ¬ (p ^ 2 ∣ a)) :
    Irreducible ((X : (RatFunc F)[X]) ^ n -
      C (algebraMap (Polynomial F) (RatFunc F) a)) := by
  have hmonic : ((X : (Polynomial F)[X]) ^ n - C a).Monic := monic_X_pow_sub_C _ hn
  have := (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc F)).mp
    (irreducible_Y_pow_sub_C_of_eisenstein hn hp h1 h2)
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using this

end Eisenstein

section Kummer

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] {a : K} (H : Irreducible (X ^ n - C a))
  (L : Type*) [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)]
  {ζ : K} (hζ : IsPrimitiveRoot ζ n)

/-- The chosen `n`-th root of `a` in the splitting field. -/
abbrev kummerRoot (n : ℕ) [NeZero n] (a : K) (L : Type*) [Field L] [Algebra K L]
    [IsSplittingField K L (X ^ n - C a)] : L := rootOfSplitsXPowSubC (NeZero.pos n) a L

theorem kummerRoot_pow : (kummerRoot n a L) ^ n = algebraMap K L a :=
  rootOfSplitsXPowSubC_pow a L

include H hζ in
/-- **Every deck transformation of a Kummer extension scales the chosen root by a power of the
root of unity**, and only the identity scales it by `1`. -/
theorem kummer_smul_root (σ : L ≃ₐ[K] L) :
    ∃ m : ℕ, σ (kummerRoot n a L) = algebraMap K L (ζ ^ m) * kummerRoot n a L ∧
      (ζ ^ m = 1 → σ = 1) := by
  obtain ⟨m, hm⟩ : ∃ m : ZMod n, σ = (autEquivZmod H L hζ).symm (Multiplicative.ofAdd m) :=
    ⟨((autEquivZmod H L hζ) σ).toAdd, by simp⟩
  have hcast : ((m.val : ℕ) : ZMod n) = m := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hkey0 := autEquivZmod_symm_apply_natCast H L (kummerRoot_pow (n := n) (a := a) L) hζ m.val
  rw [hcast] at hkey0
  have hkey : σ (kummerRoot n a L) = ζ ^ m.val • kummerRoot n a L := by rw [hm]; exact hkey0
  refine ⟨m.val, ?_, ?_⟩
  · rw [hkey, Algebra.smul_def, map_pow]
  · intro hone
    have hdvd : n ∣ m.val := (hζ.pow_eq_one_iff_dvd _).mp hone
    have hzero : m.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt m)
    have hm0 : m = 0 := by rw [← hcast, hzero, Nat.cast_zero]
    rw [hm, hm0]
    simp

end Kummer

/-! ### Constants and geometric inertia -/

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω]
  [IsGalois (RatFunc k) Ω]
  [Algebra (Polynomial k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω]

omit [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- A nonzero constant is not in a place of the geometric model. -/
theorem const_notMem (Q : Ideal (Bring Ω)) [hQ : Q.IsMaximal] {c : k} (hc : c ≠ 0) :
    algebraMap (Polynomial k) (Bring Ω) (C c) ∉ Q := by
  intro hmem
  refine hQ.ne_top ?_
  have hu : IsUnit (algebraMap (Polynomial k) (Bring Ω) (C c)) :=
    (Polynomial.isUnit_C.mpr hc.isUnit).map _
  exact Ideal.eq_top_of_isUnit_mem _ hmem hu

omit [FiniteDimensional (RatFunc k) Ω] in
/-- An inertia element scaling an element outside the place by a constant scales it by `1`. -/
theorem const_eq_one_of_mem_inertia (Q : Ideal (Bring Ω)) [hQ : Q.IsMaximal]
    {σ : Ω ≃ₐ[RatFunc k] Ω} (hσ : σ ∈ geomInertia Ω Q) {w : Bring Ω} (hw : w ∉ Q) {c : k}
    (hcw : σ • w = algebraMap (Polynomial k) (Bring Ω) (C c) * w) : c = 1 := by
  haveI := hQ.isPrime
  have hmem : σ • w - w ∈ Q := AddSubgroup.mem_inertia.mp hσ w
  rw [hcw] at hmem
  have hfac : algebraMap (Polynomial k) (Bring Ω) (C c) * w - w
      = algebraMap (Polynomial k) (Bring Ω) (C (c - 1)) * w := by
    simp [map_sub, sub_mul]
  rw [hfac] at hmem
  rcases Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› hmem with h | h
  · by_contra hne
    exact const_notMem (Ω := Ω) Q (sub_ne_zero.mpr hne) h
  · exact absurd h hw

/-! ### The Kummer cover of the line: inertia away from the branch locus -/

section GeomKummer

variable {n : ℕ} [NeZero n] {a : Polynomial k}

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- The chosen `n`-th root of `a` lies in the integral model of the cover. -/
theorem kummerRoot_isIntegral
    [IsSplittingField (RatFunc k) Ω
      (X ^ n - C (algebraMap (Polynomial k) (RatFunc k) a))] :
    IsIntegral (Polynomial k)
      (kummerRoot n (algebraMap (Polynomial k) (RatFunc k) a) Ω) := by
  refine ⟨(X : (Polynomial k)[X]) ^ n - C a, monic_X_pow_sub_C _ (NeZero.ne n), ?_⟩
  have hpow := kummerRoot_pow (n := n) (a := algebraMap (Polynomial k) (RatFunc k) a) Ω
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hpow,
    ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) Ω, sub_self]

/-- The chosen `n`-th root of `a`, as an element of the integral model. -/
def kummerRootB (Ω : Type) [Field Ω] [Algebra (RatFunc k) Ω]
    [Algebra (Polynomial k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω]
    (n : ℕ) [NeZero n] (a : Polynomial k)
    [IsSplittingField (RatFunc k) Ω
      (X ^ n - C (algebraMap (Polynomial k) (RatFunc k) a))] : Bring Ω :=
  ⟨kummerRoot n (algebraMap (Polynomial k) (RatFunc k) a) Ω, kummerRoot_isIntegral⟩

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
theorem kummerRootB_pow
    [IsSplittingField (RatFunc k) Ω
      (X ^ n - C (algebraMap (Polynomial k) (RatFunc k) a))] :
    (kummerRootB Ω n a) ^ n = algebraMap (Polynomial k) (Bring Ω) a := by
  apply Subtype.ext
  push_cast
  have hpow := kummerRoot_pow (n := n) (a := algebraMap (Polynomial k) (RatFunc k) a) Ω
  simpa [kummerRootB, IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) Ω] using hpow

omit [FiniteDimensional (RatFunc k) Ω] in
/-- **Away from the zeros of `a` the Kummer cover `wⁿ = a` is unramified**: an inertia element at
a place not containing `a` is the identity. -/
theorem kummer_inertia_eq_one
    [IsSplittingField (RatFunc k) Ω
      (X ^ n - C (algebraMap (Polynomial k) (RatFunc k) a))]
    (H : Irreducible ((X : (RatFunc k)[X]) ^ n -
      C (algebraMap (Polynomial k) (RatFunc k) a)))
    {ζ₀ : k} (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (Q : Ideal (Bring Ω)) [hQ : Q.IsMaximal]
    (hQa : algebraMap (Polynomial k) (Bring Ω) a ∉ Q)
    {σ : Ω ≃ₐ[RatFunc k] Ω} (hσ : σ ∈ geomInertia Ω Q) : σ = 1 := by
  haveI := hQ.isPrime
  have hζ : IsPrimitiveRoot (algebraMap k (RatFunc k) ζ₀) n :=
    hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective
  -- the root is outside the place, since its `n`-th power is
  have hwQ : kummerRootB Ω n a ∉ Q := by
    intro hmem
    exact hQa (kummerRootB_pow (Ω := Ω) (n := n) (a := a) ▸ Ideal.pow_mem_of_mem Q hmem n
      (NeZero.pos n))
  obtain ⟨m, hm, hone⟩ := kummer_smul_root H Ω hζ σ
  -- the action on the root, transported to the integral model
  have hsmul : σ • kummerRootB Ω n a
      = algebraMap (Polynomial k) (Bring Ω) (C (ζ₀ ^ m)) * kummerRootB Ω n a := by
    apply Subtype.ext
    push_cast
    rw [coe_smul_geom]
    have hC : algebraMap (Polynomial k) Ω (C ζ₀) = algebraMap (RatFunc k) Ω (RatFunc.C ζ₀) := by
      rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) Ω, RatFunc.algebraMap_C]
    simpa [kummerRootB, hC] using hm
  have hc : ζ₀ ^ m = 1 := const_eq_one_of_mem_inertia (Ω := Ω) Q hσ hwQ hsmul
  exact hone (by rw [← map_pow, hc, map_one])

omit [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- A polynomial not vanishing at `t` is outside every place of the cover above `t`. -/
theorem notMem_of_eval_ne_zero {t : k} {b : Polynomial k} (hb : b.eval t ≠ 0)
    (Q : Ideal (Bring Ω)) [Q.LiesOver (placeP t)] :
    algebraMap (Polynomial k) (Bring Ω) b ∉ Q := by
  intro hmem
  have hover : placeP t = Q.comap (algebraMap (Polynomial k) (Bring Ω)) := Ideal.LiesOver.over
  have hcom : b ∈ placeP t := by rw [hover]; exact hmem
  exact hb (dvd_iff_isRoot.mp (Ideal.mem_span_singleton.mp hcom))

end GeomKummer

/-! ### The two-point Kummer cover -/

section TwoPoint

/-- The datum of the two-point Kummer cover: `wⁿ = (X - t₀)(X - t₁)^{n-1}`. -/
def kummerA (n : ℕ) (t₀ t₁ : k) : Polynomial k := (X - C t₀) * (X - C t₁) ^ (n - 1)

theorem kummerA_eval {n : ℕ} {t₀ t₁ t : k} (h0 : t ≠ t₀) (h1 : t ≠ t₁) :
    (kummerA n t₀ t₁).eval t ≠ 0 := by
  simp only [kummerA, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  exact mul_ne_zero (sub_ne_zero.mpr h0) (pow_ne_zero _ (sub_ne_zero.mpr h1))

/-- **The two-point Kummer polynomial is irreducible over `ℚ̄(T)`**, by Eisenstein at `X - t₀`. -/
theorem irreducible_kummerA {n : ℕ} (hn : n ≠ 0) {t₀ t₁ : k} (h01 : t₀ ≠ t₁) :
    Irreducible ((X : (RatFunc k)[X]) ^ n -
      C (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁))) := by
  refine irreducible_X_pow_sub_C_ratFunc_of_eisenstein hn (p := X - C t₀) (prime_X_sub_C t₀)
    (Dvd.intro _ rfl) ?_
  intro hdvd
  rw [kummerA, pow_two] at hdvd
  have hcancel : (X - C t₀) ∣ ((X - C t₁) ^ (n - 1) : Polynomial k) :=
    (mul_dvd_mul_iff_left (X_sub_C_ne_zero t₀)).mp hdvd
  have hroot : (((X - C t₁) ^ (n - 1) : Polynomial k)).eval t₀ = 0 := dvd_iff_isRoot.mp hcancel
  simp only [eval_pow, eval_sub, eval_X, eval_C] at hroot
  exact absurd (sub_eq_zero.mp (pow_eq_zero_iff'.mp hroot).1) h01

/-- The constant field `ℚ̄` has primitive roots of unity of every order. -/
theorem exists_primitiveRoot_k (n : ℕ) [NeZero n] : ∃ ζ₀ : k, IsPrimitiveRoot ζ₀ n := by
  haveI : NeZero ((n : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n

/-- **The two-point Kummer cover is unramified away from `t₀` and `t₁`.** -/
theorem isUnramifiedOutside_kummerCover (n : ℕ) [NeZero n] (t₀ t₁ : k) (h01 : t₀ ≠ t₁)
    (L : LineCover) [IsSplittingField (RatFunc k) L.M
      ((X : (RatFunc k)[X]) ^ n -
        C (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁)))] :
    L.IsUnramifiedOutside {t₀, t₁} := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_k n
  rintro t ht σ ⟨Q, hQmax, hQover, hσ⟩
  have h0 : t ≠ t₀ := fun h => ht (by simp [h])
  have h1 : t ≠ t₁ := fun h => ht (by simp [h])
  haveI := hQmax
  haveI := hQover
  exact kummer_inertia_eq_one (Ω := L.M) (irreducible_kummerA (NeZero.ne n) h01) hζ₀ Q
    (notMem_of_eval_ne_zero (kummerA_eval h0 h1) Q) hσ

end TwoPoint

/-! ### The two-point datum in the coordinate at infinity -/

/-- The two-point Kummer datum, read in the coordinate `S = T⁻¹` at infinity: the polynomial
`(1 - t₀S)(1 - t₁S)^{n-1}`, which takes the value `1` at `S = 0`. -/
def revKummerA (n : ℕ) (t₀ t₁ : k) : Polynomial k :=
  (1 - C t₀ * X) * (1 - C t₁ * X) ^ (n - 1)

/-- The datum at infinity does not vanish at the origin of the new coordinate. -/
theorem revKummerA_eval_zero (n : ℕ) (t₀ t₁ : k) : (revKummerA n t₀ t₁).eval 0 = 1 := by
  simp [revKummerA]

/-- **The inversion carries the datum at infinity to the two-point datum**, up to the `n`-th
power `Tⁿ`: the Kummer equation for the two-point cover, read at infinity, is the equation for
the datum `revKummerA`, whose value at the point at infinity is a unit. -/
theorem invSubst_revKummerA (n : ℕ) (hn : n ≠ 0) (t₀ t₁ : k) :
    invSubst (algebraMap (Polynomial k) (RatFunc k) (revKummerA n t₀ t₁)) * (RatFunc.X) ^ n
      = algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁) := by
  have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)
  have hX : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  have hxn : (RatFunc.X : RatFunc k) ^ n = RatFunc.X ^ (n - 1) * RatFunc.X := by
    rw [← pow_succ, h]
  have hc' : ∀ c : k, algebraMap (Polynomial k) (RatFunc k) (C c) = algebraMap k (RatFunc k) c := by
    intro c
    simp
  have hXmap : algebraMap (Polynomial k) (RatFunc k) (X : Polynomial k) = RatFunc.X :=
    RatFunc.algebraMap_X
  have hcc : ∀ c : k, invSubst (algebraMap k (RatFunc k) c) = algebraMap k (RatFunc k) c :=
    fun c => invSubst.commutes c
  have h0 : (1 - algebraMap k (RatFunc k) t₀ * (RatFunc.X)⁻¹) * RatFunc.X
      = RatFunc.X - algebraMap k (RatFunc k) t₀ := by field_simp
  have h1 : (1 - algebraMap k (RatFunc k) t₁ * (RatFunc.X)⁻¹) * RatFunc.X
      = RatFunc.X - algebraMap k (RatFunc k) t₁ := by field_simp
  rw [revKummerA, kummerA]
  simp only [map_mul, map_pow, map_sub, map_one, hXmap, hc', hcc, invSubst_X, hxn]
  calc (1 - algebraMap k (RatFunc k) t₀ * (RatFunc.X)⁻¹) *
        (1 - algebraMap k (RatFunc k) t₁ * (RatFunc.X)⁻¹) ^ (n - 1) *
        (RatFunc.X ^ (n - 1) * RatFunc.X)
      = ((1 - algebraMap k (RatFunc k) t₀ * (RatFunc.X)⁻¹) * RatFunc.X) *
        ((1 - algebraMap k (RatFunc k) t₁ * (RatFunc.X)⁻¹) * RatFunc.X) ^ (n - 1) := by
        rw [mul_pow]; ring
    _ = (RatFunc.X - algebraMap k (RatFunc k) t₀) *
        (RatFunc.X - algebraMap k (RatFunc k) t₁) ^ (n - 1) := by rw [h0, h1]

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- The Kummer root, read in the coordinate at infinity: multiplying by `T⁻¹` clears the pole of
order `n` that the root has there. -/
def twistRoot (w : Ω) : Twist invSubst Ω :=
  (w * algebraMap (RatFunc k) Ω (RatFunc.X)⁻¹ : Ω)

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- **In the coordinate at infinity the Kummer root satisfies the equation of the datum
`revKummerA`**, which is a unit at the point at infinity. -/
theorem twistRoot_pow (n : ℕ) (hn : n ≠ 0) (t₀ t₁ : k) (w : Ω)
    (hw : w ^ n =
      algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁))) :
    (twistRoot w) ^ n =
      algebraMap (RatFunc k) (Twist invSubst Ω)
        (algebraMap (Polynomial k) (RatFunc k) (revKummerA n t₀ t₁)) := by
  have hX : algebraMap (RatFunc k) Ω (RatFunc.X) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (algebraMap (RatFunc k) Ω).injective).mpr
      (RatFunc.X_ne_zero (K := k))
  show (w * algebraMap (RatFunc k) Ω (RatFunc.X)⁻¹) ^ n
      = algebraMap (RatFunc k) Ω
        (invSubst (algebraMap (Polynomial k) (RatFunc k) (revKummerA n t₀ t₁)))
  have key := congrArg (algebraMap (RatFunc k) Ω) (invSubst_revKummerA n hn t₀ t₁)
  rw [map_mul, map_pow] at key
  rw [mul_pow, hw, ← key, map_inv₀, mul_assoc, ← mul_pow, mul_inv_cancel₀ hX, one_pow, mul_one]

/-! ### Recognising Kummer covers -/

/-- The twist has the same degree over the base as the original: the coordinate change is a
bijection of the base with itself. -/
theorem twist_finrank (φ : RatFunc k ≃+* RatFunc k) (M : Type) [Field M]
    [Algebra (RatFunc k) M] :
    Module.finrank (RatFunc k) (Twist φ M) = Module.finrank (RatFunc k) M := by
  rw [Module.finrank, Module.finrank, Twist.rank_eq]

/-- **An extension generated by an `n`-th root is the splitting field of that root's equation**,
when the base has the `n`-th roots of unity and the degree is `n`. -/
theorem isSplittingField_of_root_of_adjoin_eq_top {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {n : ℕ}
    (hK : (primitiveRoots n K).Nonempty) (hfr : Module.finrank K L = n)
    {b : K} {α : L} (hα : α ^ n = algebraMap K L b)
    (hgen : IntermediateField.adjoin K {α} = ⊤) :
    IsSplittingField K L (X ^ n - C b) := by
  subst hfr
  exact isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK hα hgen

/-! ### Total ramification of the two-point Kummer cover at `t₀` -/

/-- A power of a place dividing the extended place bounds the ramification index below. -/
theorem le_ramificationIdx_of_pow_dvd (t : k) (Q : Ideal (Bring Ω)) [hQm : Q.IsMaximal]
    [Q.LiesOver (placeP t)] {m : ℕ}
    (hdvd : Q ^ m ∣ Ideal.map (algebraMap (Polynomial k) (Bring Ω)) (placeP t)) :
    m ≤ Ideal.ramificationIdx (algebraMap (Polynomial k) (Bring Ω)) (placeP t) Q := by
  haveI := hQm.isPrime
  have hQ0 : Q ≠ ⊥ := Q_ne_bot Ω t Q
  have hinj : Function.Injective (algebraMap (Polynomial k) (Bring Ω)) :=
    FaithfulSMul.algebraMap_injective (Polynomial k) (Bring Ω)
  have hI0 : Ideal.map (algebraMap (Polynomial k) (Bring Ω)) (placeP t) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj, le_bot_iff]
    exact placeP_ne_bot t
  have hprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQm.isPrime
  have hfin : FiniteMultiplicity Q (Ideal.map (algebraMap (Polynomial k) (Bring Ω)) (placeP t)) := by
    classical
    refine finiteMultiplicity_iff_emultiplicity_ne_top.mpr ?_
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hprime.irreducible hI0]
    exact ENat.coe_ne_top _
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity hI0 hQm.isPrime]
  exact hfin.le_multiplicity_of_pow_dvd hdvd

/-- **A totally ramified place has full inertia.** -/
theorem geomInertia_eq_top_of_finrank_le (t : k) (Q : Ideal (Bring Ω)) [hQm : Q.IsMaximal]
    [Q.LiesOver (placeP t)]
    (hle : Module.finrank (RatFunc k) Ω ≤
      Ideal.ramificationIdx (algebraMap (Polynomial k) (Bring Ω)) (placeP t) Q) :
    geomInertia Ω Q = ⊤ := by
  haveI := residue_isSeparable Ω t Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Ω ≃ₐ[RatFunc k] Ω)
    (placeP t) (placeP_ne_bot t) Q
  have hIn : Ideal.ramificationIdxIn (placeP t) (Bring Ω)
      = Ideal.ramificationIdx (algebraMap (Polynomial k) (Bring Ω)) (placeP t) Q :=
    Ideal.ramificationIdxIn_eq_ramificationIdx (placeP t) Q (Ω ≃ₐ[RatFunc k] Ω)
  have hdeck : Nat.card (Ω ≃ₐ[RatFunc k] Ω) = Module.finrank (RatFunc k) Ω := by
    simpa using IsGalois.card_aut_eq_finrank (RatFunc k) Ω
  refine Subgroup.eq_top_of_le_card _ ?_
  rw [hcard, hIn, hdeck]
  exact hle

/-! ### Total ramification of the two-point Kummer cover -/

section TwoPoint

variable {n : ℕ} [NeZero n] {a : Polynomial k}

omit [NeZero n] in
/-- **A root of the two-point Kummer datum forces total ramification at `t₀`**: the `n`-th power
of a place above `t₀` divides the place extended to the cover. -/
theorem pow_dvd_map_placeP {t₀ t₁ : k} (h01 : t₀ ≠ t₁) (w : Bring Ω)
    (hw : w ^ n = algebraMap (Polynomial k) (Bring Ω) (kummerA n t₀ t₁))
    (Q : Ideal (Bring Ω)) [hQm : Q.IsMaximal] [Q.LiesOver (placeP t₀)] :
    Q ^ n ∣ Ideal.map (algebraMap (Polynomial k) (Bring Ω)) (placeP t₀) := by
  haveI := hQm.isPrime
  have hQ0 : Q ≠ ⊥ := Q_ne_bot Ω t₀ Q
  have hprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQm.isPrime
  -- the datum lies in `Q`, being a multiple of the uniformizer at `t₀`
  have haQ : algebraMap (Polynomial k) (Bring Ω) (kummerA n t₀ t₁) ∈ Q := by
    have hover : placeP t₀ = Q.comap (algebraMap (Polynomial k) (Bring Ω)) := Ideal.LiesOver.over
    have hmem : kummerA n t₀ t₁ ∈ placeP t₀ := by
      rw [kummerA]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [hover] at hmem
    exact hmem
  -- hence the root lies in `Q`, and `Qⁿ` divides the ideal it generates
  have hwQ : w ∈ Q := by
    refine (‹Q.IsPrime›).mem_of_pow_mem n ?_
    rw [hw]
    exact haQ
  have h1 : Q ∣ Ideal.span {w} :=
    Ideal.dvd_iff_le.mpr (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  have h2 : Q ^ n ∣ Ideal.span {w ^ n} := by
    rw [← Ideal.span_singleton_pow]
    exact pow_dvd_pow_of_dvd h1 n
  rw [hw] at h2
  -- split that ideal into the two point contributions
  have hmapa : algebraMap (Polynomial k) (Bring Ω) (kummerA n t₀ t₁)
      = algebraMap (Polynomial k) (Bring Ω) (X - C t₀) *
        (algebraMap (Polynomial k) (Bring Ω) (X - C t₁)) ^ (n - 1) := by
    rw [kummerA, map_mul, map_pow]
  have hsplit : Ideal.span {algebraMap (Polynomial k) (Bring Ω) (kummerA n t₀ t₁)}
      = Ideal.span {algebraMap (Polynomial k) (Bring Ω) (X - C t₀)} *
        Ideal.span {algebraMap (Polynomial k) (Bring Ω) (X - C t₁)} ^ (n - 1) := by
    rw [hmapa, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [hsplit] at h2
  -- the second factor is prime to `Q`
  have hnot : ¬ Q ∣ Ideal.span {algebraMap (Polynomial k) (Bring Ω) (X - C t₁)} := by
    intro hdvd
    have hmem : algebraMap (Polynomial k) (Bring Ω) (X - C t₁) ∈ Q :=
      Ideal.dvd_iff_le.mp hdvd (Ideal.mem_span_singleton_self _)
    refine notMem_of_eval_ne_zero (Ω := Ω) (t := t₀) (b := X - C t₁) ?_ Q hmem
    simpa using sub_ne_zero.mpr h01
  have hnotpow : ¬ Q ∣ Ideal.span {algebraMap (Polynomial k) (Bring Ω) (X - C t₁)} ^ (n - 1) :=
    fun h => hnot (hprime.dvd_of_dvd_pow h)
  have hfinal := hprime.pow_dvd_of_dvd_mul_right n hnotpow h2
  rw [placeP, Ideal.map_span, Set.image_singleton]
  exact hfinal

/-- **The two-point Kummer cover is totally ramified at `t₀`**: the inertia group of any place
above `t₀` is the whole deck group. -/
theorem geomInertia_eq_top_kummerCover (n : ℕ) [NeZero n] {t₀ t₁ : k} (h01 : t₀ ≠ t₁)
    [IsSplittingField (RatFunc k) Ω
      (X ^ n - C (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁)))]
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP t₀)] :
    geomInertia Ω Q = ⊤ := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_k n
  have hprim : (primitiveRoots n (RatFunc k)).Nonempty :=
    ⟨_, (mem_primitiveRoots (NeZero.pos n)).mpr
      (hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective)⟩
  have H := irreducible_kummerA (NeZero.ne n) h01
  have hfr : Module.finrank (RatFunc k) Ω = n :=
    finrank_of_isSplittingField_X_pow_sub_C hprim H Ω
  refine geomInertia_eq_top_of_finrank_le t₀ Q ?_
  rw [hfr]
  exact le_ramificationIdx_of_pow_dvd t₀ Q
    (pow_dvd_map_placeP h01 (kummerRootB Ω n (kummerA n t₀ t₁)) kummerRootB_pow Q)

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] [NeZero n] in
/-- The two orderings of the two-point Kummer datum multiply to a perfect `n`-th power. -/
theorem kummerA_mul_swap (hn : n ≠ 0) (t₀ t₁ : k) :
    kummerA n t₁ t₀ * kummerA n t₀ t₁ = ((X - C t₀) * (X - C t₁)) ^ n := by
  have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)
  have h0 : ((X : Polynomial k) - C t₀) ^ n = (X - C t₀) ^ (n - 1) * (X - C t₀) := by
    rw [← pow_succ, h]
  have h1 : ((X : Polynomial k) - C t₁) ^ n = (X - C t₁) ^ (n - 1) * (X - C t₁) := by
    rw [← pow_succ, h]
  rw [kummerA, kummerA, mul_pow, h0, h1]
  ring

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] [NeZero n] in
/-- The two-point Kummer datum is a nonzero polynomial. -/
theorem kummerA_ne_zero (t₀ t₁ : k) : kummerA n t₀ t₁ ≠ 0 := by
  rw [kummerA]
  exact mul_ne_zero (X_sub_C_ne_zero t₀) (pow_ne_zero _ (X_sub_C_ne_zero t₁))

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] [NeZero n] in
/-- **Swapping the two branch points**: a root of the two-point Kummer datum for `(t₀, t₁)`
produces a root of the datum for `(t₁, t₀)` in the same cover. -/
theorem exists_pow_eq_kummerA_swap (hn : n ≠ 0) {t₀ t₁ : k} (w : Bring Ω)
    (hw : w ^ n = algebraMap (Polynomial k) (Bring Ω) (kummerA n t₀ t₁)) :
    ∃ w₁ : Bring Ω, w₁ ^ n = algebraMap (Polynomial k) (Bring Ω) (kummerA n t₁ t₀) := by
  have hinj : Function.Injective (algebraMap (Polynomial k) Ω) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial k) (RatFunc k) Ω]
    exact (algebraMap (RatFunc k) Ω).injective.comp
      (IsFractionRing.injective (Polynomial k) (RatFunc k))
  have ha0 : algebraMap (Polynomial k) Ω (kummerA n t₀ t₁) ≠ 0 := fun h =>
    kummerA_ne_zero (n := n) t₀ t₁ (hinj (by rw [h, map_zero]))
  have hwΩ : (w : Ω) ^ n = algebraMap (Polynomial k) Ω (kummerA n t₀ t₁) := by
    rw [← Subalgebra.coe_pow, hw, Subalgebra.coe_algebraMap]
  -- the mirrored root, obtained by dividing the total datum by `w`
  set x : Ω := algebraMap (Polynomial k) Ω ((X - C t₀) * (X - C t₁)) / (w : Ω) with hxdef
  have hx : x ^ n = algebraMap (Polynomial k) Ω (kummerA n t₁ t₀) := by
    rw [hxdef, div_pow, hwΩ, ← map_pow, ← kummerA_mul_swap hn t₀ t₁, map_mul,
      mul_div_assoc, div_self ha0, mul_one]
  have hint : IsIntegral (Polynomial k) x :=
    ⟨X ^ n - C (kummerA n t₁ t₀), monic_X_pow_sub_C _ hn, by simp [hx]⟩
  refine ⟨⟨x, hint⟩, Subtype.ext ?_⟩
  rw [Subalgebra.coe_pow, Subalgebra.coe_algebraMap]
  exact hx

/-- **The two-point Kummer cover is totally ramified at `t₁`** as well: the inertia group of any
place above `t₁` is the whole deck group. -/
theorem geomInertia_eq_top_kummerCover' (n : ℕ) [NeZero n] {t₀ t₁ : k} (h01 : t₀ ≠ t₁)
    [IsSplittingField (RatFunc k) Ω
      (X ^ n - C (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁)))]
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP t₁)] :
    geomInertia Ω Q = ⊤ := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_k n
  have hprim : (primitiveRoots n (RatFunc k)).Nonempty :=
    ⟨_, (mem_primitiveRoots (NeZero.pos n)).mpr
      (hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective)⟩
  have H := irreducible_kummerA (NeZero.ne n) h01
  have hfr : Module.finrank (RatFunc k) Ω = n :=
    finrank_of_isSplittingField_X_pow_sub_C hprim H Ω
  obtain ⟨w₁, hw₁⟩ := exists_pow_eq_kummerA_swap (Ω := Ω) (NeZero.ne n)
    (kummerRootB Ω n (kummerA n t₀ t₁)) kummerRootB_pow
  refine geomInertia_eq_top_of_finrank_le t₁ Q ?_
  rw [hfr]
  exact le_ramificationIdx_of_pow_dvd t₁ Q (pow_dvd_map_placeP h01.symm w₁ hw₁ Q)

/-- **A generator of the deck group of the two-point Kummer cover is a distinguished inertia
element at `t₀`.** -/
theorem isInertiaGenAt_kummerCover (n : ℕ) [NeZero n] {t₀ t₁ : k} (h01 : t₀ ≠ t₁) (L : LineCover)
    [IsSplittingField (RatFunc k) L.M
      ((X : (RatFunc k)[X]) ^ n -
        C (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁)))]
    {σ : L.deck} (hσ : Subgroup.zpowers σ = ⊤) : L.IsInertiaGenAt t₀ σ := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP L.M t₀
  haveI := hQmax
  haveI := hQover
  exact ⟨Q, hQmax, hQover, by rw [hσ]; exact geomInertia_eq_top_kummerCover n h01 Q⟩

/-- **A generator of the deck group of the two-point Kummer cover is a distinguished inertia
element at `t₁`** as well. -/
theorem isInertiaGenAt_kummerCover' (n : ℕ) [NeZero n] {t₀ t₁ : k} (h01 : t₀ ≠ t₁) (L : LineCover)
    [IsSplittingField (RatFunc k) L.M
      ((X : (RatFunc k)[X]) ^ n -
        C (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁)))]
    {σ : L.deck} (hσ : Subgroup.zpowers σ = ⊤) : L.IsInertiaGenAt t₁ σ := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP L.M t₁
  haveI := hQmax
  haveI := hQover
  exact ⟨Q, hQmax, hQover, by rw [hσ]; exact geomInertia_eq_top_kummerCover' n h01 Q⟩

/-- The deck group of the two-point Kummer cover is generated by a single element. -/
theorem exists_zpowers_eq_top_kummerCover (n : ℕ) [NeZero n] {t₀ t₁ : k} (h01 : t₀ ≠ t₁) (L : LineCover)
    [IsSplittingField (RatFunc k) L.M
      ((X : (RatFunc k)[X]) ^ n -
        C (algebraMap (Polynomial k) (RatFunc k) (kummerA n t₀ t₁)))] :
    ∃ σ : L.deck, Subgroup.zpowers σ = ⊤ := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_k n
  have hprim : (primitiveRoots n (RatFunc k)).Nonempty :=
    ⟨_, (mem_primitiveRoots (NeZero.pos n)).mpr
      (hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective)⟩
  have H := irreducible_kummerA (NeZero.ne n) h01
  haveI : IsCyclic L.deck := isCyclic_of_isSplittingField_X_pow_sub_C hprim H L.M
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L.deck)
  exact ⟨σ, by ext x; simpa using hσ x⟩

end TwoPoint

end Rigidity.RET
