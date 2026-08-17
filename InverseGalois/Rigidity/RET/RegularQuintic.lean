/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.RatFuncConstants
import InverseGalois.Rigidity.RET.RegularityConverse
import InverseGalois.Rigidity.RET.Statement

/-!
# A regular cyclic quintic extension of `ℚ(T)`

The cyclic group of order five is a **regular** inverse Galois group over `ℚ`.

The construction is Kummer theory twisted by the cyclotomic character.  Write `K = ℚ(ζ)` for the
fifth cyclotomic field and `σ` for the generator of `Gal(K/ℚ)` with `σ ζ = ζ ^ 2`.  Over `K(T)`
one takes the Kummer extension `M = K(T)(g ^ (1/5))` for the carefully weighted product

`g = (T - ζ) (T - ζ ^ 2) ^ 3 (T - ζ ^ 4) ^ 4 (T - ζ ^ 3) ^ 2`,

whose exponents are chosen so that `σ g = g ^ 2 * h ^ 5` with `h = ((T - ζ ^ 2)(T - ζ ^ 4))⁻¹`.
That identity is exactly what allows `σ` to be lifted to `M`, by `w ↦ w ^ 2 * h`; the exponent `2`
matching the cyclotomic character makes the lift *commute* with the Kummer automorphism
`w ↦ ζ * w`.  So `M / ℚ(T)` is abelian of degree `20`, and the fixed field of the order-four part
is a cyclic quintic extension of `ℚ(T)`.

Regularity comes from the multiplicity-one root of `g` at `ζ`: it prevents `g` from becoming a
fifth power in any rational function field, hence prevents `M` from containing constants beyond
`K`.
-/

open Polynomial

namespace Rigidity.RET.Quintic

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc IntermediateField

/-! ### The fifth cyclotomic field -/

/-- The field of fifth roots of unity. -/
abbrev K5 : Type := CyclotomicField 5 ℚ

/-- A primitive fifth root of unity. -/
def zeta : K5 := IsCyclotomicExtension.zeta 5 ℚ K5

theorem zeta_spec : IsPrimitiveRoot zeta 5 := IsCyclotomicExtension.zeta_spec 5 ℚ K5

theorem cyclotomic5_irr : Irreducible (cyclotomic 5 ℚ) := cyclotomic.irreducible_rat (by norm_num)

theorem zeta_pow_five : zeta ^ 5 = 1 := zeta_spec.pow_eq_one

/-- Distinct powers of `ζ` below the fifth are distinct. -/
theorem zeta_pow_ne {i j : ℕ} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
    zeta ^ i ≠ zeta ^ j := fun h => hij (zeta_spec.pow_inj hi hj h)

/-- An automorphism of `K` is determined by its value on `ζ`. -/
theorem algEquiv_ext {f g : K5 ≃ₐ[ℚ] K5} (h : f zeta = g zeta) : f = g := by
  apply AlgEquiv.coe_algHom_injective
  apply (zeta_spec.powerBasis ℚ).algHom_ext
  simpa [IsPrimitiveRoot.powerBasis_gen] using h

/-- The generator `ζ ↦ ζ ^ 2` of the Galois group of `ℚ(ζ) / ℚ`. -/
def sigma : K5 ≃ₐ[ℚ] K5 :=
  IsCyclotomicExtension.fromZetaAut (zeta_spec.pow_of_coprime 2 (by decide)) cyclotomic5_irr

@[simp] theorem sigma_zeta : sigma zeta = zeta ^ 2 :=
  IsCyclotomicExtension.fromZetaAut_spec _ _

theorem sigma_zeta_pow (i : ℕ) : sigma (zeta ^ i) = zeta ^ (2 * i) := by
  rw [map_pow, sigma_zeta, ← pow_mul, Nat.mul_comm]

theorem sigma_pow_zeta (n : ℕ) : (sigma ^ n) zeta = zeta ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, sigma_zeta_pow]
      congr 1
      ring

/-- `σ` has order four. -/
theorem orderOf_sigma : orderOf sigma = 4 := by
  have h4 : sigma ^ 4 = 1 := by
    refine algEquiv_ext ?_
    rw [sigma_pow_zeta, AlgEquiv.one_apply]
    calc zeta ^ (2 ^ 4) = zeta ^ (5 * 3 + 1) := by norm_num
      _ = zeta := by rw [pow_add, pow_mul, zeta_pow_five, one_pow, one_mul, pow_one]
  have h2 : sigma ^ 2 ≠ 1 := by
    intro h
    have hz : (sigma ^ 2) zeta = zeta := by rw [h, AlgEquiv.one_apply]
    rw [sigma_pow_zeta] at hz
    have h41 : zeta ^ 4 = zeta ^ 1 := by rw [pow_one]; simpa using hz
    exact zeta_pow_ne (by norm_num) (by norm_num) (by norm_num) h41
  have hdvd : orderOf sigma ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hmem : orderOf sigma ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by simp [h] : orderOf sigma ∣ 2)) h2
  · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (by simp [h] : orderOf sigma ∣ 2)) h2
  · exact h

/-! ### The twisted Kummer datum -/

/-- The cofactor of `T - ζ` in `g`. -/
def gtail : K5[X] :=
  (X - C (zeta ^ 2)) ^ 3 * ((X - C (zeta ^ 4)) ^ 4 * (X - C (zeta ^ 3)) ^ 2)

/-- The weighted product `g = (T - ζ)(T - ζ²)³(T - ζ⁴)⁴(T - ζ³)²`. -/
def gpoly : K5[X] := (X - C zeta) * gtail

/-- The polynomial `(T - ζ²)(T - ζ⁴)`, whose inverse is the twisting factor. -/
def hpoly : K5[X] := (X - C (zeta ^ 2)) * (X - C (zeta ^ 4))

theorem gtail_eval_zeta_ne_zero : gtail.eval zeta ≠ 0 := by
  have h2 : zeta - zeta ^ 2 ≠ 0 := by
    intro h
    exact zeta_pow_ne (i := 1) (j := 2) (by norm_num) (by norm_num) (by norm_num)
      (by rw [pow_one]; exact sub_eq_zero.mp h)
  have h4 : zeta - zeta ^ 4 ≠ 0 := by
    intro h
    exact zeta_pow_ne (i := 1) (j := 4) (by norm_num) (by norm_num) (by norm_num)
      (by rw [pow_one]; exact sub_eq_zero.mp h)
  have h3 : zeta - zeta ^ 3 ≠ 0 := by
    intro h
    exact zeta_pow_ne (i := 1) (j := 3) (by norm_num) (by norm_num) (by norm_num)
      (by rw [pow_one]; exact sub_eq_zero.mp h)
  simp only [gtail, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  exact mul_ne_zero (pow_ne_zero _ h2) (mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ h3))

theorem gtail_ne_zero : gtail ≠ 0 := fun h => gtail_eval_zeta_ne_zero (by rw [h, eval_zero])

theorem gpoly_ne_zero : gpoly ≠ 0 :=
  mul_ne_zero (X_sub_C_ne_zero zeta) gtail_ne_zero

theorem hpoly_ne_zero : hpoly ≠ 0 :=
  mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)

/-- `g` has a **simple** root at `ζ`: this single fact drives both the irreducibility of the
Kummer extension and its regularity. -/
theorem rootMultiplicity_gpoly : gpoly.rootMultiplicity zeta = 1 := by
  rw [gpoly, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero zeta) gtail_ne_zero),
    rootMultiplicity_X_sub_C_self,
    rootMultiplicity_eq_zero (fun h => gtail_eval_zeta_ne_zero h)]

/-- The bookkeeping behind the choice of exponents: `σ` permutes the four linear factors, and the
resulting monomial matches `g²` after multiplying by `h⁵`. -/
private theorem exponent_identity {R : Type*} [CommRing R] (a b c d : R) :
    b * (c ^ 3 * (d ^ 4 * a ^ 2)) * (b * c) ^ 5 = (a * (b ^ 3 * (c ^ 4 * d ^ 2))) ^ 2 := by
  ring

/-- **The twisting identity** `σ g · h⁵ = g²`, forced by the choice of exponents. -/
theorem map_sigma_gpoly : gpoly.map (sigma : K5 ≃ₐ[ℚ] K5) * hpoly ^ 5 = gpoly ^ 2 := by
  have e6 : zeta ^ 6 = zeta := by
    rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, zeta_pow_five, one_mul, pow_one]
  have e8 : zeta ^ 8 = zeta ^ 3 := by
    rw [show (8 : ℕ) = 5 + 3 by norm_num, pow_add, zeta_pow_five, one_mul]
  have s2 : sigma (zeta ^ 2) = zeta ^ 4 := by
    rw [sigma_zeta_pow, show 2 * 2 = 4 from rfl]
  have s3 : sigma (zeta ^ 3) = zeta := by
    rw [sigma_zeta_pow, show 2 * 3 = 6 from rfl]; exact e6
  have s4 : sigma (zeta ^ 4) = zeta ^ 3 := by
    rw [sigma_zeta_pow, show 2 * 4 = 8 from rfl]; exact e8
  simp only [gpoly, gtail, hpoly, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe, sigma_zeta, s2, s3, s4]
  exact exponent_identity _ _ _ _

/-! ### The Kummer extension -/

/-- The rational function field `ℚ(T)`. -/
abbrev F5 : Type := RatFunc ℚ

/-- The rational function field `K(T) = ℚ(ζ)(T)`. -/
abbrev E5 : Type := RatFunc K5

/-- Shortcut for the scalar action of `ℚ(T)` on `K(T)`, whose search is pathologically slow. -/
instance (priority := high) smulF5E5 : SMul F5 E5 := Algebra.toSMul

/-- The twisted Kummer datum `g`, as an element of `K(T)`. -/
def gE : E5 := algebraMap K5[X] E5 gpoly

/-- The twisting factor `h`, as an element of `K(T)`. -/
def hE : E5 := algebraMap K5[X] E5 hpoly

theorem gE_ne_zero : gE ≠ 0 := by
  simpa [gE] using fun h => gpoly_ne_zero ((IsFractionRing.injective K5[X] E5) (by simpa using h))

theorem hE_ne_zero : hE ≠ 0 := by
  simpa [hE] using fun h => hpoly_ne_zero ((IsFractionRing.injective K5[X] E5) (by simpa using h))

/-- **`g` is not a fifth power in `K(T)`**: its root at `ζ` is simple. -/
theorem not_fifth_power (y : E5) : y ^ 5 ≠ gE := by
  intro hy
  have h5 : (5 : ℕ) ∣ gpoly.rootMultiplicity zeta :=
    rootMultiplicity_dvd_of_pow_eq gpoly_ne_zero hy zeta
  rw [rootMultiplicity_gpoly] at h5
  omega

/-- The Kummer polynomial `X ^ 5 - g` is irreducible over `K(T)`. -/
theorem kummer_irreducible : Irreducible ((X : E5[X]) ^ 5 - C gE) :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) not_fifth_power

instance factKummer : Fact (Irreducible ((X : E5[X]) ^ 5 - C gE)) := ⟨kummer_irreducible⟩

/-- The Kummer extension `M = K(T)(g ^ (1/5))`. -/
abbrev M5 : Type := AdjoinRoot ((X : E5[X]) ^ 5 - C gE)

/-- Shortcut for the `ℚ(T)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algF5M5 : Algebra F5 M5 := AdjoinRoot.instAlgebra _

/-- Shortcut for the `K(T)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algE5M5 : Algebra E5 M5 := AdjoinRoot.instAlgebra _

/-- The chosen fifth root of `g`. -/
def w : M5 := AdjoinRoot.root _

theorem w_pow_five : w ^ 5 = algebraMap E5 M5 gE := by
  rw [w, AdjoinRoot.algebraMap_eq]
  exact root_X_pow_sub_C_pow 5 gE

theorem kummer_ne_zero : ((X : E5[X]) ^ 5 - C gE) ≠ 0 :=
  kummer_irreducible.ne_zero

instance : FiniteDimensional E5 M5 := (AdjoinRoot.powerBasis kummer_ne_zero).finite

theorem finrank_E5_M5 : Module.finrank E5 M5 = 5 := by
  rw [(AdjoinRoot.powerBasis kummer_ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

theorem finrank_F5_E5 : Module.finrank F5 E5 = 4 := by
  rw [RatFunc.finrank_ratFunc_ratFunc ℚ K5,
    IsCyclotomicExtension.finrank K5 cyclotomic5_irr]
  decide

instance : FiniteDimensional F5 E5 :=
  Module.rank_lt_aleph0_iff.mp (by
    rw [RatFunc.rank_ratFunc_ratFunc ℚ K5]; exact Module.rank_lt_aleph0 ℚ K5)

instance : FiniteDimensional F5 M5 := .trans F5 E5 M5

theorem finrank_F5_M5 : Module.finrank F5 M5 = 20 := by
  rw [← Module.finrank_mul_finrank F5 E5 M5, finrank_F5_E5, finrank_E5_M5]

/-! ### The two commuting automorphisms -/

/-- The defining relation of `M`, in the form required to lift a homomorphism out of it. -/
private theorem eval₂_kummer {i : E5 →+* M5} {x : M5} (h : x ^ 5 = i gE) :
    ((X : E5[X]) ^ 5 - C gE).eval₂ i x = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h, sub_self]

/-- `ζ`, viewed in `M`. -/
def zetaM : M5 := algebraMap K5 M5 zeta

theorem zetaM_pow_five : zetaM ^ 5 = 1 := by
  rw [zetaM, ← map_pow, zeta_pow_five, map_one]

theorem zetaM_ne_one : zetaM ≠ 1 := by
  intro h
  refine zeta_spec.ne_one (by norm_num) ((algebraMap K5 M5).injective ?_)
  rw [map_one, ← h, zetaM]

theorem w_ne_zero : w ≠ 0 := root_X_pow_sub_C_ne_zero (by norm_num) gE

/-- The Kummer automorphism `w ↦ ζ w`, as an algebra map. -/
def tauHom : M5 →ₐ[E5] M5 :=
  AdjoinRoot.liftAlgHom ((X : E5[X]) ^ 5 - C gE) (Algebra.ofId E5 M5) (zetaM * w)
    (eval₂_kummer (by rw [mul_pow, zetaM_pow_five, one_mul, w_pow_five]; rfl))

/-- **The Kummer automorphism** `w ↦ ζ w` of `M / K(T)`. -/
def tau : M5 ≃ₐ[E5] M5 := AlgEquiv.ofBijective tauHom tauHom.bijective

@[simp] theorem tau_w : tau w = zetaM * w := by
  simp only [tau, AlgEquiv.coe_ofBijective, tauHom, w, AdjoinRoot.liftAlgHom_root]

/-- The coefficient automorphism `σ` of `K(T)`, fixing `ℚ(T)`. -/
def sigmaE : E5 ≃ₐ[F5] E5 := Rigidity.RET.ratFuncMapAlg (k := ℚ) sigma

theorem sigmaE_algebraMap (c : K5) : sigmaE (algebraMap K5 E5 c) = algebraMap K5 E5 (sigma c) := by
  rw [IsScalarTower.algebraMap_apply K5 K5[X] E5, IsScalarTower.algebraMap_apply K5 K5[X] E5,
    sigmaE, Rigidity.RET.ratFuncMapAlg_apply, Rigidity.RET.ratFuncMap_algebraMap]
  congr 1
  simp

/-- **The twisting identity** in `K(T)`: `σ g · h ^ 5 = g ^ 2`. -/
theorem sigmaE_gE : sigmaE gE * hE ^ 5 = gE ^ 2 := by
  have h := congrArg (algebraMap K5[X] E5) map_sigma_gpoly
  rw [map_mul, map_pow, map_pow] at h
  simp only [sigmaE, Rigidity.RET.ratFuncMapAlg_apply, gE, hE,
    Rigidity.RET.ratFuncMap_algebraMap]
  exact h

/-- `h`, viewed in `M`. -/
def hM : M5 := algebraMap E5 M5 hE

theorem hM_ne_zero : hM ≠ 0 := fun h =>
  hE_ne_zero ((algebraMap E5 M5).injective (by rw [map_zero, ← hM, h]))

/-- The lift of `σ` to `M`, sending `w` to `w ^ 2 / h`. -/
def sigmaHom : M5 →ₐ[F5] M5 :=
  AdjoinRoot.liftAlgHom ((X : E5[X]) ^ 5 - C gE)
    ((IsScalarTower.toAlgHom F5 E5 M5).comp sigmaE.toAlgHom) (w ^ 2 / hM)
    (eval₂_kummer (by
      have hgE : sigmaE gE = gE ^ 2 / hE ^ 5 :=
        (eq_div_iff (pow_ne_zero 5 hE_ne_zero)).mpr sigmaE_gE
      show (w ^ 2 / hM) ^ 5 = algebraMap E5 M5 (sigmaE gE)
      rw [hgE, map_div₀, map_pow, map_pow, ← w_pow_five, div_pow, ← pow_mul, ← pow_mul, hM]))

/-- **The lift of `σ`** to an automorphism of `M / ℚ(T)`. -/
def sigmaM : M5 ≃ₐ[F5] M5 := AlgEquiv.ofBijective sigmaHom sigmaHom.bijective

@[simp] theorem sigmaM_w : sigmaM w = w ^ 2 / hM := by
  simp only [sigmaM, AlgEquiv.coe_ofBijective, sigmaHom, w, AdjoinRoot.liftAlgHom_root]

@[simp] theorem sigmaM_algebraMap (x : E5) :
    sigmaM (algebraMap E5 M5 x) = algebraMap E5 M5 (sigmaE x) := by
  rw [sigmaM, AlgEquiv.coe_ofBijective, sigmaHom, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.liftAlgHom_of]
  rfl

/-! ### The order of the two automorphisms -/

/-- An automorphism of `M` over `K(T)` is determined by its value on `w`. -/
private theorem tau_ext {f g : M5 ≃ₐ[E5] M5} (h : f w = g w) : f = g := by
  apply AlgEquiv.coe_algHom_injective
  exact AdjoinRoot.algHom_ext h

/-- `ζ` comes from `K(T)`. -/
theorem zetaM_eq : zetaM = algebraMap E5 M5 (algebraMap K5 E5 zeta) := by
  rw [zetaM, ← IsScalarTower.algebraMap_apply]

@[simp] theorem tau_zetaM : tau zetaM = zetaM := by
  rw [zetaM_eq]; exact tau.commutes _

theorem tau_pow_w (n : ℕ) : (tau ^ n) w = zetaM ^ n * w := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ' tau m, AlgEquiv.mul_apply, ih, map_mul, map_pow, tau_zetaM, tau_w,
        pow_succ zetaM m]
      ring

theorem tau_pow_five : tau ^ 5 = 1 := by
  refine tau_ext ?_
  rw [tau_pow_w, zetaM_pow_five, one_mul, AlgEquiv.one_apply]

theorem tau_ne_one : tau ≠ 1 := by
  intro h
  refine zetaM_ne_one (mul_right_cancel₀ w_ne_zero ?_)
  rw [one_mul, ← tau_w, h, AlgEquiv.one_apply]

theorem orderOf_tau : orderOf tau = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime tau_pow_five tau_ne_one

theorem orderOf_sigmaE : orderOf sigmaE = 4 := by
  rw [sigmaE, Rigidity.RET.orderOf_ratFuncMapAlg, orderOf_sigma]

/-- A subfield over which the whole extension has the same degree is the base field. -/
private theorem eq_bot_of_finrank_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (S : IntermediateField F E)
    (h : Module.finrank S E = Module.finrank F E) : S = ⊥ := by
  have hmul := Module.finrank_mul_finrank F S E
  rw [h] at hmul
  refine IntermediateField.finrank_eq_one_iff.mp
    (Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := F) (M := E)) ?_)
  rw [one_mul]
  exact hmul

/-! ### The fixed fields of the two automorphisms -/

theorem fixedField_tau : IntermediateField.fixedField (Subgroup.zpowers tau) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_tau, finrank_E5_M5]

theorem fixedField_sigmaE : IntermediateField.fixedField (Subgroup.zpowers sigmaE) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_sigmaE, finrank_F5_E5]

/-- **An element of `M` fixed by the Kummer automorphism lies in `K(T)`.** -/
theorem exists_of_tau_fixed {x : M5} (hx : tau x = x) : ∃ y : E5, algebraMap E5 M5 y = x := by
  have hle : Subgroup.zpowers tau ≤ MulAction.stabilizer (M5 ≃ₐ[E5] M5) x :=
    Subgroup.zpowers_le.mpr hx
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers tau) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun f hf => hle hf
  rw [fixedField_tau, IntermediateField.mem_bot] at hmem
  exact hmem

/-- **An element of `K(T)` fixed by the coefficient automorphism lies in `ℚ(T)`.** -/
theorem exists_of_sigmaE_fixed {y : E5} (hy : sigmaE y = y) : ∃ z : F5, algebraMap F5 E5 z = y := by
  have hle : Subgroup.zpowers sigmaE ≤ MulAction.stabilizer (E5 ≃ₐ[F5] E5) y :=
    Subgroup.zpowers_le.mpr hy
  have hmem : y ∈ IntermediateField.fixedField (Subgroup.zpowers sigmaE) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun f hf => hle hf
  rw [fixedField_sigmaE, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### The Galois group of `M / ℚ(T)` -/

/-- Two ring maps out of `M` agreeing on `K(T)` and on `w` agree. -/
private theorem ringHom_ext_M {φ ψ : M5 →+* M5}
    (hbase : ∀ x : E5, φ (algebraMap E5 M5 x) = ψ (algebraMap E5 M5 x))
    (hw : φ w = ψ w) (y : M5) : φ y = ψ y := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial i c =>
      have hmk : AdjoinRoot.mk ((X : E5[X]) ^ 5 - C gE) (Polynomial.monomial i c)
          = algebraMap E5 M5 c * w ^ i := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
          AdjoinRoot.algebraMap_eq]
        rfl
      rw [hmk, map_mul, map_mul, map_pow, map_pow, hbase, hw]

/-- An automorphism of `M` over `ℚ(T)` is determined by its restriction to `K(T)` and its value
on `w`. -/
private theorem algEquiv_ext_M {f g : M5 ≃ₐ[F5] M5}
    (hbase : ∀ x : E5, f (algebraMap E5 M5 x) = g (algebraMap E5 M5 x)) (hw : f w = g w) :
    f = g :=
  AlgEquiv.ext fun y =>
    ringHom_ext_M (φ := (f : M5 →+* M5)) (ψ := (g : M5 →+* M5)) hbase hw y

/-- `τ`, as an automorphism of `M` over `ℚ(T)`. -/
def tauF : M5 ≃ₐ[F5] M5 := AlgEquiv.restrictScalars F5 tau

@[simp] theorem tauF_apply (x : M5) : tauF x = tau x := rfl

theorem tauF_pow_apply (n : ℕ) (x : M5) : (tauF ^ n) x = (tau ^ n) x := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ' tauF m, pow_succ' tau m, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]
      rfl

theorem tauF_pow_five : tauF ^ 5 = 1 :=
  AlgEquiv.ext fun x => by
    rw [tauF_pow_apply, tau_pow_five, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem tauF_ne_one : tauF ≠ 1 := by
  intro h
  refine tau_ne_one (AlgEquiv.ext fun x => ?_)
  rw [← tauF_apply, h, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem orderOf_tauF : orderOf tauF = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime tauF_pow_five tauF_ne_one

@[simp] theorem tau_hM : tau hM = hM := by
  rw [hM]; exact tau.commutes _

@[simp] theorem sigmaM_zetaM : sigmaM zetaM = zetaM ^ 2 := by
  rw [zetaM_eq, sigmaM_algebraMap, sigmaE_algebraMap, sigma_zeta, map_pow, map_pow]

/-- **The two automorphisms commute**: the exponent `2` in the lift of `σ` is the cyclotomic
character of `σ`. -/
theorem commute_tauF_sigmaM : tauF * sigmaM = sigmaM * tauF := by
  refine algEquiv_ext_M (fun x => ?_) ?_
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaM_algebraMap, tauF_apply, tau.commutes,
      tauF_apply, tau.commutes, sigmaM_algebraMap]
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaM_w, tauF_apply, map_div₀, map_pow, tau_w,
      tau_hM, tauF_apply, tau_w, map_mul, sigmaM_zetaM, sigmaM_w, mul_pow]
    ring

/-- **`ℚ(T)` is the whole field of invariants of `M`.** -/
theorem fixedField_top : IntermediateField.fixedField (⊤ : Subgroup (M5 ≃ₐ[F5] M5)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := exists_of_tau_fixed (hx tauF (Subgroup.mem_top _))
  have hy : sigmaE y = y := by
    have hfix := hx sigmaM (Subgroup.mem_top _)
    rw [sigmaM_algebraMap] at hfix
    exact (algebraMap E5 M5).injective hfix
  obtain ⟨z, rfl⟩ := exists_of_sigmaE_fixed hy
  rw [IntermediateField.mem_bot, ← IsScalarTower.algebraMap_apply]
  exact ⟨z, rfl⟩

instance isGalois_F5_M5 : IsGalois F5 M5 := IsGalois.of_fixedField_eq_bot F5 M5 fixedField_top

theorem card_aut_M5 : Nat.card (M5 ≃ₐ[F5] M5) = 20 := by
  rw [IsGalois.card_aut_eq_finrank, finrank_F5_M5]

instance finite_aut_M5 : Finite (M5 ≃ₐ[F5] M5) :=
  Nat.finite_of_card_ne_zero (by rw [card_aut_M5]; norm_num)

/-! ### The quintic layer -/

theorem sigmaM_pow_algebraMap (n : ℕ) (x : E5) :
    (sigmaM ^ n) (algebraMap E5 M5 x) = algebraMap E5 M5 ((sigmaE ^ n) x) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ' sigmaM m, pow_succ' sigmaE m, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih,
        sigmaM_algebraMap]

theorem sigmaE_pow_four : sigmaE ^ 4 = 1 := by
  have h := pow_orderOf_eq_one sigmaE
  rwa [orderOf_sigmaE] at h

theorem orderOf_sigmaE_dvd : orderOf sigmaE ∣ orderOf sigmaM := by
  refine orderOf_dvd_of_pow_eq_one (AlgEquiv.ext fun x => ?_)
  refine (algebraMap E5 M5).injective ?_
  rw [← sigmaM_pow_algebraMap, pow_orderOf_eq_one, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem orderOf_sigmaM : orderOf sigmaM = 4 ∨ orderOf sigmaM = 20 := by
  have h1 : orderOf sigmaM ∣ 20 := by
    have h := orderOf_dvd_natCard sigmaM
    rwa [card_aut_M5] at h
  have h2 : 4 ∣ orderOf sigmaM := by
    have h := orderOf_sigmaE_dvd
    rwa [orderOf_sigmaE] at h
  have hle : orderOf sigmaM ≤ 20 := Nat.le_of_dvd (by norm_num) h1
  obtain ⟨d, hd⟩ : ∃ d, orderOf sigmaM = d := ⟨_, rfl⟩
  rw [hd] at h1 h2 hle ⊢
  interval_cases d <;> revert h1 h2 <;> decide

/-- The order-four automorphism `σ ^ 5` of `M`; the quintic layer is its fixed field. -/
def sigmaQ : M5 ≃ₐ[F5] M5 := sigmaM ^ 5

theorem orderOf_sigmaQ : orderOf sigmaQ = 4 := by
  rw [sigmaQ, orderOf_pow' (x := sigmaM) (n := 5) (h := by norm_num)]
  rcases orderOf_sigmaM with h | h <;> rw [h] <;> decide

theorem commute_tauF_sigmaQ : sigmaQ * tauF = tauF * sigmaQ :=
  (Commute.pow_right commute_tauF_sigmaM 5).symm

/-- **The quintic layer**: the fixed field of `⟨σ ^ 5⟩`, a degree-five extension of `ℚ(T)`. -/
def L5 : IntermediateField F5 M5 := IntermediateField.fixedField (Subgroup.zpowers sigmaQ)

instance (priority := high) smulF5F5 : SMul F5 F5 := instSMulOfMul

instance (priority := high) isScalarTowerF5F5M5 : IsScalarTower F5 F5 M5 :=
  ⟨fun a b c => by rw [smul_eq_mul, mul_smul]⟩

instance (priority := high) algF5L5 : Algebra F5 L5 := IntermediateField.algebra' L5

instance (priority := high) isScalarTowerF5L5M5 : IsScalarTower F5 L5 M5 :=
  IntermediateField.isScalarTower_mid' L5

instance (priority := high) finiteDimensionalF5L5 : FiniteDimensional F5 L5 :=
  IntermediateField.finiteDimensional_left L5

theorem mem_L5_iff {x : M5} : x ∈ L5 ↔ sigmaQ x = x := by
  rw [L5, IntermediateField.mem_fixedField_iff]
  refine ⟨fun hx => hx sigmaQ (Subgroup.mem_zpowers _), fun hx f hf => ?_⟩
  have hle : Subgroup.zpowers sigmaQ ≤ MulAction.stabilizer (M5 ≃ₐ[F5] M5) x :=
    Subgroup.zpowers_le.mpr hx
  exact hle hf

theorem finrank_L5_M5 : Module.finrank L5 M5 = 4 := by
  rw [L5, IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_sigmaQ]

theorem finrank_F5_L5 : Module.finrank F5 L5 = 5 := by
  have h := Module.finrank_mul_finrank F5 L5 M5
  rw [finrank_L5_M5, finrank_F5_M5] at h
  omega

theorem tauF_mem_L5 {x : M5} (hx : x ∈ L5) : tauF x ∈ L5 := by
  rw [mem_L5_iff] at hx ⊢
  have h := congrArg (fun e : M5 ≃ₐ[F5] M5 => e x) commute_tauF_sigmaQ
  simp only [AlgEquiv.mul_apply] at h
  rw [h, hx]

theorem tauF_pow_mem_L5 (n : ℕ) {x : M5} (hx : x ∈ L5) : (tauF ^ n) x ∈ L5 := by
  induction n with
  | zero => simpa using hx
  | succ m ih =>
      rw [pow_succ' tauF m, AlgEquiv.mul_apply]
      exact tauF_mem_L5 ih

/-- `τ`, viewed as an endomorphism of the quintic layer. -/
def tauLHom : L5 →ₐ[F5] L5 where
  toFun x := ⟨tauF (x : M5), tauF_mem_L5 x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (by
    show tauF ((algebraMap F5 L5 r : L5) : M5) = ((algebraMap F5 L5 r : L5) : M5)
    rw [IntermediateField.coe_algebraMap_apply]
    exact tauF.commutes r)

@[simp] theorem tauLHom_apply (x : L5) : (tauLHom x : M5) = tauF (x : M5) := rfl

/-- `τ`, as an automorphism of the quintic layer over `ℚ(T)`. -/
def tauL : L5 ≃ₐ[F5] L5 := AlgEquiv.ofBijective tauLHom tauLHom.bijective

@[simp] theorem tauL_apply (x : L5) : (tauL x : M5) = tauF (x : M5) := rfl

theorem tauL_pow_apply (n : ℕ) (x : L5) : ((tauL ^ n) x : M5) = (tauF ^ n) (x : M5) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ' tauL m, pow_succ' tauF m, AlgEquiv.mul_apply, AlgEquiv.mul_apply, tauL_apply,
        ih]

theorem tauL_pow_five : tauL ^ 5 = 1 := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  show ((tauL ^ 5) x : M5) = ((1 : L5 ≃ₐ[F5] L5) x : M5)
  rw [tauL_pow_apply, tauF_pow_five, AlgEquiv.one_apply, AlgEquiv.one_apply]

/-- The quintic layer is not `ℚ(T)`: an element fixed by `τ` and by `σ ^ 5` is a rational
function over `ℚ`. -/
theorem L5_ne_bot : L5 ≠ ⊥ := by
  intro hbot
  have h : Module.finrank F5 L5 = 1 := IntermediateField.finrank_eq_one_iff.mpr hbot
  rw [finrank_F5_L5] at h
  omega

theorem tauL_ne_one : tauL ≠ 1 := by
  intro h
  refine L5_ne_bot (bot_unique fun x hx => ?_)
  have hfix : tauF x = x := by
    have hx' : (tauL ⟨x, hx⟩ : M5) = ((1 : L5 ≃ₐ[F5] L5) ⟨x, hx⟩ : M5) := by rw [h]
    rw [tauL_apply, AlgEquiv.one_apply] at hx'
    exact hx'
  obtain ⟨y, rfl⟩ := exists_of_tau_fixed hfix
  have hy : sigmaE y = y := by
    have hq : sigmaQ (algebraMap E5 M5 y) = algebraMap E5 M5 y := mem_L5_iff.mp hx
    rw [sigmaQ, sigmaM_pow_algebraMap] at hq
    have h5 : sigmaE ^ 5 = sigmaE := by
      rw [pow_succ' sigmaE 4, sigmaE_pow_four, mul_one]
    rw [h5] at hq
    exact (algebraMap E5 M5).injective hq
  obtain ⟨z, rfl⟩ := exists_of_sigmaE_fixed hy
  rw [IntermediateField.mem_bot, ← IsScalarTower.algebraMap_apply]
  exact ⟨z, rfl⟩

theorem orderOf_tauL : orderOf tauL = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime tauL_pow_five tauL_ne_one

theorem fixedField_tauL : IntermediateField.fixedField (Subgroup.zpowers tauL) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_tauL, finrank_F5_L5]

theorem fixedField_top_L5 :
    IntermediateField.fixedField (⊤ : Subgroup (L5 ≃ₐ[F5] L5)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers tauL) := by
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    exact fun f _ => hx f (Subgroup.mem_top f)
  rwa [fixedField_tauL] at hmem

instance isGalois_F5_L5 : IsGalois F5 L5 := IsGalois.of_fixedField_eq_bot F5 L5 fixedField_top_L5

/-- **The quintic layer is a cyclic degree-five Galois extension of `ℚ(T)`.** -/
theorem card_aut_L5 : Nat.card (L5 ≃ₐ[F5] L5) = 5 := by
  rw [IsGalois.card_aut_eq_finrank, finrank_F5_L5]

/-! ### The constants of the Kummer extension -/

/-- An algebraic closure of `K`. -/
abbrev Kbar : Type := AlgebraicClosure K5

/-- The geometric base field `K̄(T)`. -/
abbrev G5 : Type := RatFunc Kbar

instance charZeroE5 : CharZero E5 :=
  charZero_of_injective_algebraMap (algebraMap K5 E5).injective

/-- `g`, read over the algebraic closure of `K`. -/
def gbar : Kbar[X] := gpoly.map (algebraMap K5 Kbar)

theorem gbar_ne_zero : gbar ≠ 0 := by
  rw [gbar, Ne, Polynomial.map_eq_zero]
  exact gpoly_ne_zero

/-- The simple root of `g` at `ζ` survives the passage to the algebraic closure. -/
theorem rootMultiplicity_gbar : gbar.rootMultiplicity (algebraMap K5 Kbar zeta) = 1 := by
  have htail : (gtail.map (algebraMap K5 Kbar)).eval (algebraMap K5 Kbar zeta) ≠ 0 := by
    rw [eval_map, Polynomial.eval₂_at_apply]
    exact fun h => gtail_eval_zeta_ne_zero ((algebraMap K5 Kbar).injective (by rw [h, map_zero]))
  have htail0 : gtail.map (algebraMap K5 Kbar) ≠ 0 := fun h => htail (by rw [h, eval_zero])
  have hmap : gbar
      = (X - C (algebraMap K5 Kbar zeta)) * gtail.map (algebraMap K5 Kbar) := by
    rw [gbar, gpoly, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hmap, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) htail0),
    rootMultiplicity_X_sub_C_self, rootMultiplicity_eq_zero htail]

theorem algebraMap_gE_geom : algebraMap E5 G5 gE = algebraMap Kbar[X] G5 gbar :=
  Rigidity.RET.algebraMap_ratFunc_ratFunc (k := K5) (K := Kbar) gpoly

/-- **`g` is not a fifth power over the algebraic closure either.** -/
theorem not_fifth_power_geom (y : G5) : y ^ 5 ≠ algebraMap E5 G5 gE := by
  rw [algebraMap_gE_geom]
  intro hy
  have h5 : (5 : ℕ) ∣ gbar.rootMultiplicity (algebraMap K5 Kbar zeta) :=
    Rigidity.RET.rootMultiplicity_dvd_of_pow_eq gbar_ne_zero hy _
  rw [rootMultiplicity_gbar] at h5
  omega

/-- The Kummer polynomial stays irreducible over `K̄(T)`: the extension is geometric. -/
theorem kummer_irreducible_geom :
    Irreducible (((X : E5[X]) ^ 5 - C gE).map (algebraMap E5 G5)) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime (by norm_num) not_fifth_power_geom

theorem minpoly_w : minpoly E5 w = (X : E5[X]) ^ 5 - C gE := by
  have hm : ((X : E5[X]) ^ 5 - C gE).Monic := monic_X_pow_sub_C gE (by norm_num)
  rw [w, AdjoinRoot.minpoly_root kummer_ne_zero, hm.leadingCoeff, inv_one, map_one, mul_one]

theorem adjoin_w_top : IntermediateField.adjoin E5 ({w} : Set M5) = ⊤ := by
  refine top_unique fun x _ => ?_
  have h : x ∈ Algebra.adjoin E5 ({w} : Set M5) := by
    rw [w, AdjoinRoot.adjoinRoot_eq_top]
    trivial
  exact IntermediateField.algebra_adjoin_le_adjoin E5 _ h

/-- Every polynomial over `K` splits in the geometric base field `K̄(T)`. -/
theorem splits_geom (p : K5[X]) :
    ((p.map (algebraMap K5 E5)).map (algebraMap E5 G5)).Splits := by
  have hconst : ∀ a : K5, algebraMap K5 E5 a = algebraMap K5[X] E5 (C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply K5 K5[X] E5]
    rfl
  have hcomp : (algebraMap E5 G5).comp (algebraMap K5 E5)
      = ((algebraMap Kbar[X] G5).comp (C : Kbar →+* Kbar[X])).comp (algebraMap K5 Kbar) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, hconst, Rigidity.RET.algebraMap_ratFunc_ratFunc, Polynomial.map_C]
    rfl
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map]
  exact (IsAlgClosed.splits (p.map (algebraMap K5 Kbar))).map _

/-- **The constants of `M` are exactly `K`**: the Kummer extension is geometric over `K`. -/
theorem algebraicClosure_K5_M5 : algebraicClosure K5 M5 = ⊥ :=
  Rigidity.RET.algebraicClosure_eq_bot_of_isField_tensor (F := K5) (K := E5) (K' := G5) (L := M5)
    splits_geom (Rigidity.RET.algebraicClosure_ratFunc K5)
    (Rigidity.RET.isField_tensor_of_primitive_irreducible M5 w adjoin_w_top
      (by rw [minpoly_w]; exact kummer_irreducible_geom))

theorem exists_const_of_isIntegral {y : M5} (hy : IsIntegral K5 y) :
    ∃ c : K5, algebraMap K5 M5 c = y := by
  have hmem : y ∈ algebraicClosure K5 M5 := mem_algebraicClosure_iff'.mpr hy
  rw [algebraicClosure_K5_M5, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### Regularity of the quintic layer -/

set_option synthInstance.maxHeartbeats 400000 in
/-- The quintic layer sits over `ℚ` through `ℚ(T)`; a shortcut for a slow instance search. -/
instance (priority := high) isScalarTowerQF5L5 : IsScalarTower ℚ F5 ↥L5 := inferInstance

/-- The two routes from `ℚ` into `M`, through the constants and through `ℚ(T)`, agree: `ℚ` is
initial. -/
theorem rationalMaps_eq :
    (algebraMap K5 M5).comp (algebraMap ℚ K5) = (algebraMap F5 M5).comp (algebraMap ℚ F5) :=
  Subsingleton.elim _ _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The quintic layer is regular**: it gains no constants over `ℚ`. -/
theorem regular_L5 : algebraicClosure ℚ L5 = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.mp hx
  have hpm : (minpoly ℚ x).Monic := minpoly.monic hxint
  have hpx : aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
  -- the image of `x` in `M` is a constant, i.e. an element of `K`
  have hPx : aeval x ((minpoly ℚ x).map (algebraMap ℚ F5)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hpx
  have hPy : aeval (x : M5) ((minpoly ℚ x).map (algebraMap ℚ F5)) = 0 := by
    have hval := Polynomial.aeval_algHom_apply L5.val x ((minpoly ℚ x).map (algebraMap ℚ F5))
    rw [hPx, map_zero] at hval
    exact hval
  have hyint : IsIntegral K5 (x : M5) := by
    refine ⟨(minpoly ℚ x).map (algebraMap ℚ K5), hpm.map _, ?_⟩
    rw [eval₂_map, rationalMaps_eq, ← eval₂_map]
    exact hPy
  obtain ⟨c, hc⟩ := exists_const_of_isIntegral hyint
  -- `x` therefore satisfies a polynomial of degree at most four over `ℚ(T)`
  have hcm : (minpoly ℚ c).Monic := minpoly.monic (IsIntegral.of_finite ℚ c)
  have hq0 : (minpoly ℚ c).map (algebraMap ℚ F5) ≠ 0 := (hcm.map _).ne_zero
  have hcM : aeval (x : M5) ((minpoly ℚ c).map (algebraMap ℚ F5)) = 0 := by
    rw [aeval_def, eval₂_map, ← rationalMaps_eq, ← hc, ← Polynomial.hom_eval₂, ← aeval_def,
      minpoly.aeval, map_zero]
  have hqx : aeval x ((minpoly ℚ c).map (algebraMap ℚ F5)) = 0 := by
    have hval : aeval (x : M5) ((minpoly ℚ c).map (algebraMap ℚ F5))
        = L5.val (aeval x ((minpoly ℚ c).map (algebraMap ℚ F5))) :=
      Polynomial.aeval_algHom_apply L5.val x _
    exact ZeroMemClass.coe_eq_zero.mp (hval.symm.trans hcM)
  have hdvd : minpoly F5 x ∣ (minpoly ℚ c).map (algebraMap ℚ F5) := minpoly.dvd F5 x hqx
  have hdeg : (minpoly F5 x).natDegree ≤ 4 := by
    have h1 : (minpoly F5 x).natDegree ≤ ((minpoly ℚ c).map (algebraMap ℚ F5)).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hq0
    have h2 : ((minpoly ℚ c).map (algebraMap ℚ F5)).natDegree = (minpoly ℚ c).natDegree :=
      hcm.natDegree_map _
    have h3 : (minpoly ℚ c).natDegree ≤ Module.finrank ℚ K5 := minpoly.natDegree_le c
    have h4 : Module.finrank ℚ K5 = 4 := by
      rw [IsCyclotomicExtension.finrank K5 cyclotomic5_irr]
      decide
    omega
  -- but its degree also divides five
  have hxF5 : IsIntegral F5 x := IsIntegral.of_finite F5 x
  have hadj : Module.finrank F5 F5⟮x⟯ = (minpoly F5 x).natDegree :=
    IntermediateField.adjoin.finrank hxF5
  have hdvd5 : (minpoly F5 x).natDegree ∣ 5 := by
    have h := minpoly.degree_dvd hxF5
    rwa [finrank_F5_L5] at h
  have hone : (minpoly F5 x).natDegree = 1 := by
    obtain ⟨d, hd⟩ : ∃ d, (minpoly F5 x).natDegree = d := ⟨_, rfl⟩
    rw [hd] at hdvd5 hdeg ⊢
    interval_cases d <;> revert hdvd5 <;> decide
  -- degree one means `x` already lies in `ℚ(T)`
  have hbot : F5⟮x⟯ = ⊥ := IntermediateField.finrank_eq_one_iff.mp (by rw [hadj, hone])
  have hxmem : x ∈ (⊥ : IntermediateField F5 L5) := by
    rw [← hbot]
    exact IntermediateField.mem_adjoin_simple_self F5 x
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hxmem
  -- and a constant of `ℚ(T)` is rational
  have hzint : IsIntegral ℚ z := by
    refine ⟨minpoly ℚ x, hpm, ?_⟩
    refine (algebraMap F5 L5).injective ?_
    rw [map_zero]
    have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ F5 L5) z (minpoly ℚ x)
    rw [IsScalarTower.coe_toAlgHom', hz, hpx] at h
    rw [← aeval_def]
    exact h.symm
  have hzmem : z ∈ algebraicClosure ℚ F5 := mem_algebraicClosure_iff'.mpr hzint
  rw [Rigidity.RET.regular_ratFunc, IntermediateField.mem_bot] at hzmem
  obtain ⟨q, hq⟩ := hzmem
  refine IntermediateField.mem_bot.mpr ⟨q, ?_⟩
  rw [IsScalarTower.algebraMap_apply ℚ F5 L5, hq, hz]

/-! ### The regular realization -/

/-- **The Galois group of the quintic layer is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_aut : IsRegularInverseGalois (L5 ≃ₐ[F5] L5) :=
  ⟨L5, inferInstance, algF5L5, inferInstance, isGalois_F5_L5, inferInstance, inferInstance,
    regular_L5, ⟨MulEquiv.refl _⟩⟩

/-- **Every group of order five is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_of_card_eq_five {G : Type*} [Group G] (hG : Nat.card G = 5) :
    IsRegularInverseGalois G :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  isRegularInverseGalois_aut.of_mulEquiv (mulEquivOfPrimeCardEq card_aut_L5 hG)

end

end Rigidity.RET.Quintic
