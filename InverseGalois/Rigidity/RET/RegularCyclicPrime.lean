/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.RatFuncConstants
import InverseGalois.Rigidity.RET.RegularityConverse
import InverseGalois.Rigidity.RET.Statement

/-!
# Regular cyclic extensions of `ℚ(T)` of prime degree

For every prime `p`, the cyclic group of order `p` is a **regular** inverse Galois group over `ℚ`.

The construction is Kummer theory twisted by the cyclotomic character.  Write `K = ℚ(ζ)` for the
`p`-th cyclotomic field, pick a primitive root `c` modulo `p`, and let `σ` be the generator of
`Gal(K / ℚ)` with `σ ζ = ζ ^ c`.  Over `K(T)` one takes the Kummer extension `M = K(T)(g ^ (1/p))`
for the weighted product over the units of `ℤ/p`

`g = ∏ (T - ζ ^ v) ^ a v`,   `a v = ` the representative of `v⁻¹`.

The weights are the inverses mod `p` precisely so that applying `σ` — which permutes the linear
factors by multiplication by `c` — reproduces `g ^ c` up to a `p`-th power:

`σ g = g ^ c * h ^ p`.

That identity is what allows `σ` to be lifted to `M`, by `w ↦ w ^ c * h`, and the exponent `c`
matching the cyclotomic character makes the lift *commute* with the Kummer automorphism `w ↦ ζ w`.
So `M / ℚ(T)` is abelian of degree `p (p - 1)`, and the fixed field of the order-`(p-1)` part is a
cyclic degree-`p` extension of `ℚ(T)`.

Regularity comes from the multiplicity-one root of `g` at `ζ`: it prevents `g` from becoming a
`p`-th power in any rational function field, hence prevents `M` from containing constants beyond
`K`.
-/

open Polynomial

namespace Rigidity.RET.CyclicPrime

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc IntermediateField

/-! ### A weighted product of distinct linear factors -/

section Aux

variable {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]

/-- **The multiplicity of a root of a weighted product of distinct linear factors is its
weight.** -/
theorem rootMultiplicity_prod_pow (α : ι → L) (hinj : Function.Injective α) (A : ι → ℕ) (i : ι) :
    (∏ j, (X - C (α j)) ^ A j).rootMultiplicity (α i) = A i := by
  have htail : (∏ j ∈ Finset.univ.erase i, (X - C (α j)) ^ A j).eval (α i) ≠ 0 := by
    rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hj).1 (hinj h.symm))
  have htail0 : (∏ j ∈ Finset.univ.erase i, (X - C (α j)) ^ A j) ≠ 0 := fun h => htail (by
    rw [h, eval_zero])
  have hsplit : ∏ j, (X - C (α j)) ^ A j
      = (X - C (α i)) ^ A i * ∏ j ∈ Finset.univ.erase i, (X - C (α j)) ^ A j :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplit, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero (α i))) htail0),
    rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero htail, add_zero]

omit [DecidableEq ι] in
/-- A weighted product of linear factors is nonzero. -/
theorem prod_pow_ne_zero (α : ι → L) (A : ι → ℕ) : (∏ j, (X - C (α j)) ^ A j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (X_sub_C_ne_zero (α j))

end Aux

variable (p : ℕ) [hp : Fact p.Prime]

instance neZero_of_prime : NeZero p := ⟨hp.out.ne_zero⟩

/-! ### The `p`-th cyclotomic field -/

/-- The field of `p`-th roots of unity. -/
abbrev KK : Type := CyclotomicField p ℚ

/-- A primitive `p`-th root of unity. -/
def zeta : KK p := IsCyclotomicExtension.zeta p ℚ (KK p)

theorem zeta_spec : IsPrimitiveRoot (zeta p) p := IsCyclotomicExtension.zeta_spec p ℚ (KK p)

theorem cyclotomic_irr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.out.pos

/-- `ζ` raised to a residue class: legitimate because `ζ ^ p = 1`. -/
def zetaPow (x : ZMod p) : KK p := zeta p ^ x.val

theorem zetaPow_natCast (n : ℕ) : zetaPow p (n : ZMod p) = zeta p ^ n := by
  rw [zetaPow, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n p]
  rw [pow_add, pow_mul, (zeta_spec p).pow_eq_one, one_pow, one_mul]

theorem zetaPow_injective : Function.Injective (zetaPow p) := fun x y h =>
  ZMod.val_injective p ((zeta_spec p).pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)

theorem zetaPow_one : zetaPow p 1 = zeta p := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [zetaPow, ZMod.val_one, pow_one]

/-- An automorphism of `K` is determined by its value on `ζ`. -/
theorem algEquiv_ext {f g : KK p ≃ₐ[ℚ] KK p} (h : f (zeta p) = g (zeta p)) : f = g := by
  apply AlgEquiv.coe_algHom_injective
  apply ((zeta_spec p).powerBasis ℚ).algHom_ext
  simpa [IsPrimitiveRoot.powerBasis_gen] using h

/-! ### The cyclotomic character -/

/-- A primitive root modulo `p`. -/
def gen : (ZMod p)ˣ := (IsCyclic.exists_generator (α := (ZMod p)ˣ)).choose

theorem gen_spec (x : (ZMod p)ˣ) : x ∈ Subgroup.zpowers (gen p) :=
  (IsCyclic.exists_generator (α := (ZMod p)ˣ)).choose_spec x

theorem orderOf_gen : orderOf (gen p) = p - 1 := by
  have h := orderOf_eq_card_of_forall_mem_zpowers (gen_spec p)
  rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h

/-- The natural-number representative of the chosen primitive root. -/
def genVal : ℕ := ((gen p : ZMod p)).val

theorem genVal_coprime : Nat.Coprime (genVal p) p := ZMod.val_coe_unit_coprime (gen p)

theorem genVal_cast : ((genVal p : ℕ) : ZMod p) = (gen p : ZMod p) := by
  rw [genVal, ZMod.natCast_val, ZMod.cast_id]

/-- The generator of `Gal(ℚ(ζ) / ℚ)` attached to the chosen primitive root. -/
def sigma : KK p ≃ₐ[ℚ] KK p :=
  IsCyclotomicExtension.fromZetaAut
    ((zeta_spec p).pow_of_coprime (genVal p) (genVal_coprime p)) (cyclotomic_irr p)

@[simp] theorem sigma_zeta : sigma p (zeta p) = zeta p ^ genVal p :=
  IsCyclotomicExtension.fromZetaAut_spec _ _

theorem sigma_zetaPow (x : ZMod p) :
    sigma p (zetaPow p x) = zetaPow p ((gen p : ZMod p) * x) := by
  rw [zetaPow, map_pow, sigma_zeta, ← pow_mul, ← zetaPow_natCast, Nat.cast_mul, genVal_cast,
    ZMod.natCast_val, ZMod.cast_id]

theorem sigma_pow_zeta (n : ℕ) :
    (sigma p ^ n) (zeta p) = zetaPow p (((gen p ^ n : (ZMod p)ˣ) : ZMod p)) := by
  induction n with
  | zero => simpa using (zetaPow_one p).symm
  | succ m ih =>
      rw [pow_succ' (sigma p) m, AlgEquiv.mul_apply, ih, sigma_zetaPow, pow_succ' (gen p) m,
        Units.val_mul]

theorem sigma_pow_eq_one_iff (n : ℕ) : sigma p ^ n = 1 ↔ gen p ^ n = 1 := by
  constructor
  · intro h
    have hz : (sigma p ^ n) (zeta p) = zeta p := by rw [h, AlgEquiv.one_apply]
    rw [sigma_pow_zeta, ← zetaPow_one p] at hz
    exact Units.ext (by rw [Units.val_one]; exact zetaPow_injective p hz)
  · intro h
    refine algEquiv_ext p ?_
    rw [sigma_pow_zeta, h, AlgEquiv.one_apply, Units.val_one, zetaPow_one]

theorem orderOf_sigma : orderOf (sigma p) = p - 1 := by
  rw [← orderOf_gen p]
  exact orderOf_eq_orderOf_iff.mpr (sigma_pow_eq_one_iff p)

/-! ### The twisted Kummer datum -/

/-- The exponent attached to a unit `v`: the representative of `v⁻¹`. -/
def expo (v : (ZMod p)ˣ) : ℕ := ((v⁻¹ : (ZMod p)ˣ) : ZMod p).val

theorem expo_cast (v : (ZMod p)ˣ) : ((expo p v : ℕ) : ZMod p) = ((v⁻¹ : (ZMod p)ˣ) : ZMod p) := by
  rw [expo, ZMod.natCast_val, ZMod.cast_id]

theorem expo_one : expo p 1 = 1 := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [expo, inv_one, Units.val_one, ZMod.val_one]

/-- The roots of the Kummer datum: the primitive `p`-th roots of unity. -/
def rt (v : (ZMod p)ˣ) : KK p := zetaPow p (v : ZMod p)

theorem rt_injective : Function.Injective (rt p) := fun _ _ h =>
  Units.ext (zetaPow_injective p h)

theorem rt_one : rt p 1 = zeta p := by rw [rt, Units.val_one, zetaPow_one]

theorem sigma_rt (v : (ZMod p)ˣ) : sigma p (rt p v) = rt p (gen p * v) := by
  rw [rt, rt, sigma_zetaPow, Units.val_mul]

/-- The weighted product `g = ∏ (T - ζ ^ v) ^ a v`, the exponents being the inverses mod `p`. -/
def gpoly : (KK p)[X] := ∏ v : (ZMod p)ˣ, (X - C (rt p v)) ^ expo p v

theorem gpoly_ne_zero : gpoly p ≠ 0 := prod_pow_ne_zero _ _

/-- `g` has a **simple** root at `ζ`: this single fact drives both the irreducibility of the
Kummer extension and its regularity. -/
theorem rootMultiplicity_gpoly : (gpoly p).rootMultiplicity (zeta p) = 1 := by
  rw [gpoly, ← rt_one p, rootMultiplicity_prod_pow _ (rt_injective p), expo_one]

/-- The correction exponent: the exact amount by which `σ g` and `g ^ c` differ by a `p`-th
power. -/
def ee (v : (ZMod p)ˣ) : ℤ :=
  ((expo p ((gen p)⁻¹ * v) : ℤ) - (genVal p : ℤ) * (expo p v : ℤ)) / (p : ℤ)

theorem dvd_expo_sub (v : (ZMod p)ˣ) :
    (p : ℤ) ∣ (expo p ((gen p)⁻¹ * v) : ℤ) - (genVal p : ℤ) * (expo p v : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [expo_cast, expo_cast, genVal_cast, mul_inv_rev, inv_inv, Units.val_mul]
  ring

theorem p_mul_ee (v : (ZMod p)ˣ) :
    (p : ℤ) * ee p v = (expo p ((gen p)⁻¹ * v) : ℤ) - (genVal p : ℤ) * (expo p v : ℤ) :=
  Int.mul_ediv_cancel' (dvd_expo_sub p v)

/-! ### The Kummer extension -/

/-- The rational function field `ℚ(T)`. -/
abbrev FF : Type := RatFunc ℚ

/-- The rational function field `K(T) = ℚ(ζ)(T)`. -/
abbrev EE : Type := RatFunc (KK p)

/-- Shortcut for the scalar action of `ℚ(T)` on `K(T)`, whose search is pathologically slow. -/
instance (priority := high) smulFFEE : SMul FF (EE p) := Algebra.toSMul

/-- A linear factor of the Kummer datum, as an element of `K(T)`. -/
def linE (v : (ZMod p)ˣ) : EE p := algebraMap (KK p)[X] (EE p) (X - C (rt p v))

/-- The twisted Kummer datum `g`, as an element of `K(T)`. -/
def gE : EE p := algebraMap (KK p)[X] (EE p) (gpoly p)

theorem linE_ne_zero (v : (ZMod p)ˣ) : linE p v ≠ 0 := fun h =>
  X_sub_C_ne_zero (rt p v)
    ((IsFractionRing.injective (KK p)[X] (EE p)) (by rw [map_zero]; exact h))

theorem gE_ne_zero : gE p ≠ 0 := fun h =>
  gpoly_ne_zero p ((IsFractionRing.injective (KK p)[X] (EE p)) (by rw [map_zero]; exact h))

theorem gE_prod : gE p = ∏ v : (ZMod p)ˣ, linE p v ^ expo p v := by
  rw [gE, gpoly, map_prod]
  exact Finset.prod_congr rfl fun v _ => by rw [map_pow]; rfl

/-- The twisting factor `h`, as an element of `K(T)`. -/
def hE : EE p := ∏ v : (ZMod p)ˣ, linE p v ^ ee p v

theorem hE_ne_zero : hE p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (linE_ne_zero p v)

/-- The coefficient automorphism `σ` of `K(T)`, fixing `ℚ(T)`. -/
def sigmaE : EE p ≃ₐ[FF] EE p := Rigidity.RET.ratFuncMapAlg (k := ℚ) (sigma p)

theorem sigmaE_algebraMap_poly (q : (KK p)[X]) :
    sigmaE p (algebraMap (KK p)[X] (EE p) q)
      = algebraMap (KK p)[X] (EE p) (q.map (sigma p : KK p →+* KK p)) := by
  rw [sigmaE, Rigidity.RET.ratFuncMapAlg_apply, Rigidity.RET.ratFuncMap_algebraMap]

theorem sigmaE_linE (v : (ZMod p)ˣ) : sigmaE p (linE p v) = linE p (gen p * v) := by
  rw [linE, sigmaE_algebraMap_poly, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    linE, RingHom.coe_coe, sigma_rt]

/-- **The twisting identity** in `K(T)`: `σ g = g ^ c * h ^ p`. -/
theorem sigmaE_gE : sigmaE p (gE p) = gE p ^ genVal p * hE p ^ p := by
  have hstep : ∀ v : (ZMod p)ˣ, linE p v ^ expo p ((gen p)⁻¹ * v)
      = (linE p v ^ expo p v) ^ genVal p * (linE p v ^ ee p v) ^ p := by
    intro v
    have hx : linE p v ≠ 0 := linE_ne_zero p v
    have hexp : (expo p ((gen p)⁻¹ * v) : ℤ)
        = (expo p v : ℤ) * (genVal p : ℤ) + ee p v * (p : ℤ) := by
      have h := p_mul_ee p v
      linarith
    calc linE p v ^ expo p ((gen p)⁻¹ * v)
        = linE p v ^ ((expo p ((gen p)⁻¹ * v) : ℕ) : ℤ) := (zpow_natCast _ _).symm
      _ = linE p v ^ ((expo p v : ℤ) * (genVal p : ℤ) + ee p v * (p : ℤ)) := by rw [hexp]
      _ = (linE p v ^ ((expo p v : ℕ) : ℤ)) ^ ((genVal p : ℕ) : ℤ)
            * (linE p v ^ ee p v) ^ ((p : ℕ) : ℤ) := by
          rw [zpow_add₀ hx, zpow_mul, zpow_mul]
      _ = (linE p v ^ expo p v) ^ genVal p * (linE p v ^ ee p v) ^ p := by
          simp only [zpow_natCast]
  calc sigmaE p (gE p)
      = ∏ v : (ZMod p)ˣ, linE p (gen p * v) ^ expo p v := by
        rw [gE_prod, map_prod]
        exact Finset.prod_congr rfl fun v _ => by rw [map_pow, sigmaE_linE]
    _ = ∏ w : (ZMod p)ˣ, linE p w ^ expo p ((gen p)⁻¹ * w) := by
        rw [← Equiv.prod_comp (Equiv.mulLeft (gen p))
          (fun w => linE p w ^ expo p ((gen p)⁻¹ * w))]
        exact Finset.prod_congr rfl fun v _ => by
          rw [Equiv.coe_mulLeft, inv_mul_cancel_left]
    _ = ∏ w : (ZMod p)ˣ, ((linE p w ^ expo p w) ^ genVal p * (linE p w ^ ee p w) ^ p) :=
        Finset.prod_congr rfl fun w _ => hstep w
    _ = (∏ w : (ZMod p)ˣ, (linE p w ^ expo p w) ^ genVal p)
          * ∏ w : (ZMod p)ˣ, (linE p w ^ ee p w) ^ p := Finset.prod_mul_distrib
    _ = (∏ w : (ZMod p)ˣ, linE p w ^ expo p w) ^ genVal p
          * (∏ w : (ZMod p)ˣ, linE p w ^ ee p w) ^ p := by
        rw [Finset.prod_pow, Finset.prod_pow]
    _ = gE p ^ genVal p * hE p ^ p := by rw [← gE_prod, hE]

/-- **`g` is not a `p`-th power in `K(T)`**: its root at `ζ` is simple. -/
theorem not_pow (y : EE p) : y ^ p ≠ gE p := by
  intro hy
  have hdvd : p ∣ (gpoly p).rootMultiplicity (zeta p) :=
    Rigidity.RET.rootMultiplicity_dvd_of_pow_eq (gpoly_ne_zero p) hy (zeta p)
  rw [rootMultiplicity_gpoly] at hdvd
  exact hp.out.ne_one (Nat.dvd_one.mp hdvd)

/-- The Kummer polynomial `X ^ p - g` is irreducible over `K(T)`. -/
theorem kummer_irreducible : Irreducible ((X : (EE p)[X]) ^ p - C (gE p)) :=
  X_pow_sub_C_irreducible_of_prime hp.out (not_pow p)

instance factKummer : Fact (Irreducible ((X : (EE p)[X]) ^ p - C (gE p))) := ⟨kummer_irreducible p⟩

/-- The Kummer extension `M = K(T)(g ^ (1/p))`. -/
abbrev MM : Type := AdjoinRoot ((X : (EE p)[X]) ^ p - C (gE p))

/-- Shortcut for the `ℚ(T)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algFFMM : Algebra FF (MM p) := AdjoinRoot.instAlgebra _

/-- Shortcut for the `K(T)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algEEMM : Algebra (EE p) (MM p) := AdjoinRoot.instAlgebra _

/-- The chosen `p`-th root of `g`. -/
def wr : MM p := AdjoinRoot.root _

theorem wr_pow : wr p ^ p = algebraMap (EE p) (MM p) (gE p) := by
  rw [wr, AdjoinRoot.algebraMap_eq]
  exact root_X_pow_sub_C_pow p (gE p)

theorem kummer_ne_zero : ((X : (EE p)[X]) ^ p - C (gE p)) ≠ 0 := (kummer_irreducible p).ne_zero

instance : FiniteDimensional (EE p) (MM p) := (AdjoinRoot.powerBasis (kummer_ne_zero p)).finite

theorem finrank_EE_MM : Module.finrank (EE p) (MM p) = p := by
  rw [(AdjoinRoot.powerBasis (kummer_ne_zero p)).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

theorem finrank_Q_KK : Module.finrank ℚ (KK p) = p - 1 := by
  rw [IsCyclotomicExtension.finrank (KK p) (cyclotomic_irr p), Nat.totient_prime hp.out]

theorem finrank_FF_EE : Module.finrank FF (EE p) = p - 1 := by
  rw [RatFunc.finrank_ratFunc_ratFunc ℚ (KK p), finrank_Q_KK]

instance : FiniteDimensional FF (EE p) :=
  Module.rank_lt_aleph0_iff.mp (by
    rw [RatFunc.rank_ratFunc_ratFunc ℚ (KK p)]; exact Module.rank_lt_aleph0 ℚ (KK p))

instance : FiniteDimensional FF (MM p) := .trans FF (EE p) (MM p)

theorem finrank_FF_MM : Module.finrank FF (MM p) = (p - 1) * p := by
  rw [← Module.finrank_mul_finrank FF (EE p) (MM p), finrank_FF_EE, finrank_EE_MM]

/-! ### The two commuting automorphisms -/

/-- The defining relation of `M`, in the form required to lift a homomorphism out of it. -/
private theorem eval₂_kummer {i : EE p →+* MM p} {x : MM p} (h : x ^ p = i (gE p)) :
    ((X : (EE p)[X]) ^ p - C (gE p)).eval₂ i x = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h, sub_self]

/-- `ζ`, viewed in `M`. -/
def zetaM : MM p := algebraMap (KK p) (MM p) (zeta p)

theorem zetaM_pow : zetaM p ^ p = 1 := by
  rw [zetaM, ← map_pow, (zeta_spec p).pow_eq_one, map_one]

theorem zetaM_ne_one : zetaM p ≠ 1 := by
  intro h
  refine (zeta_spec p).ne_one hp.out.one_lt ((algebraMap (KK p) (MM p)).injective ?_)
  rw [map_one, ← h, zetaM]

theorem wr_ne_zero : wr p ≠ 0 := root_X_pow_sub_C_ne_zero hp.out.one_lt (gE p)

/-- The Kummer automorphism `w ↦ ζ w`, as an algebra map. -/
def tauHom : MM p →ₐ[EE p] MM p :=
  AdjoinRoot.liftAlgHom ((X : (EE p)[X]) ^ p - C (gE p)) (Algebra.ofId (EE p) (MM p))
    (zetaM p * wr p)
    (eval₂_kummer p (by rw [mul_pow, zetaM_pow, one_mul, wr_pow]; rfl))

/-- **The Kummer automorphism** `w ↦ ζ w` of `M / K(T)`. -/
def tau : MM p ≃ₐ[EE p] MM p := AlgEquiv.ofBijective (tauHom p) (tauHom p).bijective

@[simp] theorem tau_wr : tau p (wr p) = zetaM p * wr p := by
  simp only [tau, AlgEquiv.coe_ofBijective, tauHom, wr, AdjoinRoot.liftAlgHom_root]

/-- `h`, viewed in `M`. -/
def hM : MM p := algebraMap (EE p) (MM p) (hE p)

theorem hM_ne_zero : hM p ≠ 0 := fun h =>
  hE_ne_zero p ((algebraMap (EE p) (MM p)).injective (by rw [map_zero, ← hM, h]))

/-- The lift of `σ` to `M`, sending `w` to `w ^ c * h`. -/
def sigmaHom : MM p →ₐ[FF] MM p :=
  AdjoinRoot.liftAlgHom ((X : (EE p)[X]) ^ p - C (gE p))
    ((IsScalarTower.toAlgHom FF (EE p) (MM p)).comp (sigmaE p).toAlgHom)
    (wr p ^ genVal p * hM p)
    (eval₂_kummer p (by
      show (wr p ^ genVal p * hM p) ^ p = algebraMap (EE p) (MM p) (sigmaE p (gE p))
      rw [sigmaE_gE, map_mul, map_pow, map_pow, mul_pow, ← pow_mul,
        Nat.mul_comm (genVal p) p, pow_mul, wr_pow, hM]))

/-- **The lift of `σ`** to an automorphism of `M / ℚ(T)`. -/
def sigmaM : MM p ≃ₐ[FF] MM p := AlgEquiv.ofBijective (sigmaHom p) (sigmaHom p).bijective

@[simp] theorem sigmaM_wr : sigmaM p (wr p) = wr p ^ genVal p * hM p := by
  simp only [sigmaM, AlgEquiv.coe_ofBijective, sigmaHom, wr, AdjoinRoot.liftAlgHom_root]

@[simp] theorem sigmaM_algebraMap (x : EE p) :
    sigmaM p (algebraMap (EE p) (MM p) x) = algebraMap (EE p) (MM p) (sigmaE p x) := by
  rw [sigmaM, AlgEquiv.coe_ofBijective, sigmaHom, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.liftAlgHom_of]
  rfl

/-! ### The order of the two automorphisms -/

/-- An automorphism of `M` over `K(T)` is determined by its value on `w`. -/
private theorem tau_ext {f g : MM p ≃ₐ[EE p] MM p} (h : f (wr p) = g (wr p)) : f = g := by
  apply AlgEquiv.coe_algHom_injective
  exact AdjoinRoot.algHom_ext h

/-- `ζ` comes from `K(T)`. -/
theorem zetaM_eq : zetaM p = algebraMap (EE p) (MM p) (algebraMap (KK p) (EE p) (zeta p)) := by
  rw [zetaM, ← IsScalarTower.algebraMap_apply]

@[simp] theorem tau_zetaM : tau p (zetaM p) = zetaM p := by
  rw [zetaM_eq]; exact (tau p).commutes _

theorem tau_pow_wr (n : ℕ) : (tau p ^ n) (wr p) = zetaM p ^ n * wr p := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ' (tau p) m, AlgEquiv.mul_apply, ih, map_mul, map_pow, tau_zetaM, tau_wr,
        pow_succ (zetaM p) m]
      ring

theorem tau_pow : tau p ^ p = 1 := by
  refine tau_ext p ?_
  rw [tau_pow_wr, zetaM_pow, one_mul, AlgEquiv.one_apply]

theorem tau_ne_one : tau p ≠ 1 := by
  intro h
  refine zetaM_ne_one p (mul_right_cancel₀ (wr_ne_zero p) ?_)
  rw [one_mul, ← tau_wr, h, AlgEquiv.one_apply]

theorem orderOf_tau : orderOf (tau p) = p := orderOf_eq_prime (tau_pow p) (tau_ne_one p)

theorem orderOf_sigmaE : orderOf (sigmaE p) = p - 1 := by
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

theorem fixedField_tau : IntermediateField.fixedField (Subgroup.zpowers (tau p)) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_tau, finrank_EE_MM]

theorem fixedField_sigmaE : IntermediateField.fixedField (Subgroup.zpowers (sigmaE p)) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_sigmaE,
    finrank_FF_EE]

/-- **An element of `M` fixed by the Kummer automorphism lies in `K(T)`.** -/
theorem exists_of_tau_fixed {x : MM p} (hx : tau p x = x) :
    ∃ y : EE p, algebraMap (EE p) (MM p) y = x := by
  have hle : Subgroup.zpowers (tau p) ≤ MulAction.stabilizer (MM p ≃ₐ[EE p] MM p) x :=
    Subgroup.zpowers_le.mpr hx
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers (tau p)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun f hf => hle hf
  rw [fixedField_tau, IntermediateField.mem_bot] at hmem
  exact hmem

/-- **An element of `K(T)` fixed by the coefficient automorphism lies in `ℚ(T)`.** -/
theorem exists_of_sigmaE_fixed {y : EE p} (hy : sigmaE p y = y) :
    ∃ z : FF, algebraMap FF (EE p) z = y := by
  have hle : Subgroup.zpowers (sigmaE p) ≤ MulAction.stabilizer (EE p ≃ₐ[FF] EE p) y :=
    Subgroup.zpowers_le.mpr hy
  have hmem : y ∈ IntermediateField.fixedField (Subgroup.zpowers (sigmaE p)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun f hf => hle hf
  rw [fixedField_sigmaE, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### The Galois group of `M / ℚ(T)` -/

/-- Two ring maps out of `M` agreeing on `K(T)` and on `w` agree. -/
private theorem ringHom_ext_M {φ ψ : MM p →+* MM p}
    (hbase : ∀ x : EE p, φ (algebraMap (EE p) (MM p) x) = ψ (algebraMap (EE p) (MM p) x))
    (hw : φ (wr p) = ψ (wr p)) (y : MM p) : φ y = ψ y := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  induction q using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | monomial i c =>
      have hmk : AdjoinRoot.mk ((X : (EE p)[X]) ^ p - C (gE p)) (Polynomial.monomial i c)
          = algebraMap (EE p) (MM p) c * wr p ^ i := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
        rfl
      rw [hmk, map_mul, map_mul, map_pow, map_pow, hbase, hw]

/-- An automorphism of `M` over `ℚ(T)` is determined by its restriction to `K(T)` and its value
on `w`. -/
private theorem algEquiv_ext_M {f g : MM p ≃ₐ[FF] MM p}
    (hbase : ∀ x : EE p, f (algebraMap (EE p) (MM p) x) = g (algebraMap (EE p) (MM p) x))
    (hw : f (wr p) = g (wr p)) : f = g :=
  AlgEquiv.ext fun y =>
    ringHom_ext_M p (φ := (f : MM p →+* MM p)) (ψ := (g : MM p →+* MM p)) hbase hw y

/-- `τ`, as an automorphism of `M` over `ℚ(T)`. -/
def tauF : MM p ≃ₐ[FF] MM p := AlgEquiv.restrictScalars FF (tau p)

@[simp] theorem tauF_apply (x : MM p) : tauF p x = tau p x := rfl

theorem tauF_pow_apply (n : ℕ) (x : MM p) : (tauF p ^ n) x = (tau p ^ n) x := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ' (tauF p) m, pow_succ' (tau p) m, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]
      rfl

theorem tauF_pow : tauF p ^ p = 1 :=
  AlgEquiv.ext fun x => by
    rw [tauF_pow_apply, tau_pow, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem tauF_ne_one : tauF p ≠ 1 := by
  intro h
  refine tau_ne_one p (AlgEquiv.ext fun x => ?_)
  rw [← tauF_apply, h, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem orderOf_tauF : orderOf (tauF p) = p := orderOf_eq_prime (tauF_pow p) (tauF_ne_one p)

@[simp] theorem tau_hM : tau p (hM p) = hM p := by
  rw [hM]; exact (tau p).commutes _

theorem sigmaE_algebraMap (c : KK p) :
    sigmaE p (algebraMap (KK p) (EE p) c) = algebraMap (KK p) (EE p) (sigma p c) := by
  rw [IsScalarTower.algebraMap_apply (KK p) (KK p)[X] (EE p),
    IsScalarTower.algebraMap_apply (KK p) (KK p)[X] (EE p), sigmaE,
    Rigidity.RET.ratFuncMapAlg_apply, Rigidity.RET.ratFuncMap_algebraMap]
  congr 1
  simp

@[simp] theorem sigmaM_zetaM : sigmaM p (zetaM p) = zetaM p ^ genVal p := by
  rw [zetaM_eq, sigmaM_algebraMap, sigmaE_algebraMap, sigma_zeta, map_pow, map_pow]

/-- **The two automorphisms commute**: the exponent in the lift of `σ` is the cyclotomic
character of `σ`. -/
theorem commute_tauF_sigmaM : tauF p * sigmaM p = sigmaM p * tauF p := by
  refine algEquiv_ext_M p (fun x => ?_) ?_
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaM_algebraMap, tauF_apply, (tau p).commutes,
      tauF_apply, (tau p).commutes, sigmaM_algebraMap]
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaM_wr, tauF_apply, map_mul, map_pow, tau_wr,
      tau_hM, tauF_apply, tau_wr, map_mul, sigmaM_zetaM, sigmaM_wr, mul_pow]
    ring

/-- **`ℚ(T)` is the whole field of invariants of `M`.** -/
theorem fixedField_top : IntermediateField.fixedField (⊤ : Subgroup (MM p ≃ₐ[FF] MM p)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := exists_of_tau_fixed p (hx (tauF p) (Subgroup.mem_top _))
  have hy : sigmaE p y = y := by
    have hfix := hx (sigmaM p) (Subgroup.mem_top _)
    rw [sigmaM_algebraMap] at hfix
    exact (algebraMap (EE p) (MM p)).injective hfix
  obtain ⟨z, rfl⟩ := exists_of_sigmaE_fixed p hy
  rw [IntermediateField.mem_bot, ← IsScalarTower.algebraMap_apply]
  exact ⟨z, rfl⟩

instance isGalois_FF_MM : IsGalois FF (MM p) :=
  IsGalois.of_fixedField_eq_bot FF (MM p) (fixedField_top p)

theorem card_aut_MM : Nat.card (MM p ≃ₐ[FF] MM p) = (p - 1) * p := by
  rw [IsGalois.card_aut_eq_finrank, finrank_FF_MM]

instance finite_aut_MM : Finite (MM p ≃ₐ[FF] MM p) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_aut_MM]
    exact Nat.mul_ne_zero (by have := hp.out.two_le; omega) hp.out.ne_zero)

/-! ### The degree-`p` layer -/

theorem sigmaM_pow_algebraMap (n : ℕ) (x : EE p) :
    (sigmaM p ^ n) (algebraMap (EE p) (MM p) x)
      = algebraMap (EE p) (MM p) ((sigmaE p ^ n) x) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ' (sigmaM p) m, pow_succ' (sigmaE p) m, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
        ih, sigmaM_algebraMap]

theorem sigmaE_pow_sub_one : sigmaE p ^ (p - 1) = 1 := by
  have h := pow_orderOf_eq_one (sigmaE p)
  rwa [orderOf_sigmaE] at h

theorem orderOf_sigmaE_dvd : orderOf (sigmaE p) ∣ orderOf (sigmaM p) := by
  refine orderOf_dvd_of_pow_eq_one (AlgEquiv.ext fun x => ?_)
  refine (algebraMap (EE p) (MM p)).injective ?_
  rw [← sigmaM_pow_algebraMap, pow_orderOf_eq_one, AlgEquiv.one_apply, AlgEquiv.one_apply]

/-- The order-`(p-1)` automorphism `σ ^ p` of `M`; the degree-`p` layer is its fixed field. -/
def sigmaQ : MM p ≃ₐ[FF] MM p := sigmaM p ^ p

theorem orderOf_sigmaQ : orderOf (sigmaQ p) = p - 1 := by
  have hp2 := hp.out.two_le
  have hdvd : orderOf (sigmaM p) ∣ (p - 1) * p := by
    have h := orderOf_dvd_natCard (sigmaM p)
    rwa [card_aut_MM] at h
  have hsub : (p - 1) ∣ orderOf (sigmaM p) := by
    have h := orderOf_sigmaE_dvd p
    rwa [orderOf_sigmaE] at h
  obtain ⟨d, hd⟩ := hsub
  have hdp : d ∣ p := by
    have h : (p - 1) * d ∣ (p - 1) * p := by rw [← hd]; exact hdvd
    exact (mul_dvd_mul_iff_left (by omega : p - 1 ≠ 0)).mp h
  rw [sigmaQ, orderOf_pow' _ hp.out.ne_zero, hd]
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out d hdp) with h1 | h1
  · have hcop : Nat.gcd ((p - 1) * 1) p = 1 := by
      have h : Nat.gcd (p - 1) ((p - 1) + 1) = 1 :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      have hps : (p - 1) + 1 = p := by omega
      rw [hps] at h
      rw [Nat.mul_one]
      exact h
    rw [h1, hcop, Nat.mul_one, Nat.div_one]
  · have hgcd : Nat.gcd ((p - 1) * p) p = p := Nat.gcd_eq_right ⟨p - 1, Nat.mul_comm _ _⟩
    rw [h1, hgcd, Nat.mul_div_cancel _ hp.out.pos]

theorem commute_tauF_sigmaQ : sigmaQ p * tauF p = tauF p * sigmaQ p :=
  (Commute.pow_right (commute_tauF_sigmaM p) p).symm

/-- **The degree-`p` layer**: the fixed field of `⟨σ ^ p⟩`. -/
def LL : IntermediateField FF (MM p) := IntermediateField.fixedField (Subgroup.zpowers (sigmaQ p))

instance (priority := high) smulFFFF : SMul FF FF := instSMulOfMul

instance (priority := high) isScalarTowerFFFFMM : IsScalarTower FF FF (MM p) :=
  ⟨fun a b c => by rw [smul_eq_mul, mul_smul]⟩

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) algFFLL : Algebra FF (LL p) := IntermediateField.algebra' (LL p)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) isScalarTowerFFLLMM : IsScalarTower FF (LL p) (MM p) :=
  IntermediateField.isScalarTower_mid' (LL p)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) finiteDimensionalFFLL : FiniteDimensional FF (LL p) :=
  IntermediateField.finiteDimensional_left (LL p)

theorem mem_LL_iff {x : MM p} : x ∈ LL p ↔ sigmaQ p x = x := by
  rw [LL, IntermediateField.mem_fixedField_iff]
  refine ⟨fun hx => hx (sigmaQ p) (Subgroup.mem_zpowers _), fun hx f hf => ?_⟩
  have hle : Subgroup.zpowers (sigmaQ p) ≤ MulAction.stabilizer (MM p ≃ₐ[FF] MM p) x :=
    Subgroup.zpowers_le.mpr hx
  exact hle hf

theorem finrank_LL_MM : Module.finrank (LL p) (MM p) = p - 1 := by
  rw [LL, IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_sigmaQ]

theorem finrank_FF_LL : Module.finrank FF (LL p) = p := by
  have h := Module.finrank_mul_finrank FF (LL p) (MM p)
  rw [finrank_LL_MM, finrank_FF_MM, Nat.mul_comm (p - 1) p] at h
  exact Nat.eq_of_mul_eq_mul_right (by have := hp.out.two_le; omega) h

theorem tauF_mem_LL {x : MM p} (hx : x ∈ LL p) : tauF p x ∈ LL p := by
  rw [mem_LL_iff] at hx ⊢
  have h := congrArg (fun e : MM p ≃ₐ[FF] MM p => e x) (commute_tauF_sigmaQ p)
  simp only [AlgEquiv.mul_apply] at h
  rw [h, hx]

/-- `τ`, viewed as an endomorphism of the degree-`p` layer. -/
def tauLHom : LL p →ₐ[FF] LL p where
  toFun x := ⟨tauF p (x : MM p), tauF_mem_LL p x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (by
    show tauF p ((algebraMap FF (LL p) r : LL p) : MM p)
      = ((algebraMap FF (LL p) r : LL p) : MM p)
    rw [IntermediateField.coe_algebraMap_apply]
    exact (tauF p).commutes r)

@[simp] theorem tauLHom_apply (x : LL p) : (tauLHom p x : MM p) = tauF p (x : MM p) := rfl

/-- `τ`, as an automorphism of the degree-`p` layer over `ℚ(T)`. -/
def tauL : LL p ≃ₐ[FF] LL p := AlgEquiv.ofBijective (tauLHom p) (tauLHom p).bijective

@[simp] theorem tauL_apply (x : LL p) : (tauL p x : MM p) = tauF p (x : MM p) := rfl

theorem tauL_pow_apply (n : ℕ) (x : LL p) : ((tauL p ^ n) x : MM p) = (tauF p ^ n) (x : MM p) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ' (tauL p) m, pow_succ' (tauF p) m, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
        tauL_apply, ih]

theorem tauL_pow : tauL p ^ p = 1 := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  show ((tauL p ^ p) x : MM p) = ((1 : LL p ≃ₐ[FF] LL p) x : MM p)
  rw [tauL_pow_apply, tauF_pow, AlgEquiv.one_apply, AlgEquiv.one_apply]

theorem LL_ne_bot : LL p ≠ ⊥ := by
  intro hbot
  have h : Module.finrank FF (LL p) = 1 := IntermediateField.finrank_eq_one_iff.mpr hbot
  rw [finrank_FF_LL] at h
  exact hp.out.ne_one h

theorem tauL_ne_one : tauL p ≠ 1 := by
  intro h
  refine LL_ne_bot p (bot_unique fun x hx => ?_)
  have hfix : tauF p x = x := by
    have hx' : (tauL p ⟨x, hx⟩ : MM p) = ((1 : LL p ≃ₐ[FF] LL p) ⟨x, hx⟩ : MM p) := by rw [h]
    rw [tauL_apply, AlgEquiv.one_apply] at hx'
    exact hx'
  obtain ⟨y, rfl⟩ := exists_of_tau_fixed p hfix
  have hy : sigmaE p y = y := by
    have hq : sigmaQ p (algebraMap (EE p) (MM p) y) = algebraMap (EE p) (MM p) y :=
      mem_LL_iff p |>.mp hx
    rw [sigmaQ, sigmaM_pow_algebraMap] at hq
    have hpow : sigmaE p ^ p = sigmaE p := by
      have h1 : sigmaE p ^ p = sigmaE p ^ (p - 1) * sigmaE p := by
        rw [← pow_succ]
        congr 1
        have := hp.out.two_le
        omega
      rw [h1, sigmaE_pow_sub_one, one_mul]
    rw [hpow] at hq
    exact (algebraMap (EE p) (MM p)).injective hq
  obtain ⟨z, rfl⟩ := exists_of_sigmaE_fixed p hy
  rw [IntermediateField.mem_bot, ← IsScalarTower.algebraMap_apply]
  exact ⟨z, rfl⟩

theorem orderOf_tauL : orderOf (tauL p) = p := orderOf_eq_prime (tauL_pow p) (tauL_ne_one p)

theorem fixedField_tauL : IntermediateField.fixedField (Subgroup.zpowers (tauL p)) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_tauL, finrank_FF_LL]

theorem fixedField_top_LL :
    IntermediateField.fixedField (⊤ : Subgroup (LL p ≃ₐ[FF] LL p)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers (tauL p)) := by
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    exact fun f _ => hx f (Subgroup.mem_top f)
  rwa [fixedField_tauL] at hmem

instance isGalois_FF_LL : IsGalois FF (LL p) :=
  IsGalois.of_fixedField_eq_bot FF (LL p) (fixedField_top_LL p)

/-- **The layer is a cyclic degree-`p` Galois extension of `ℚ(T)`.** -/
theorem card_aut_LL : Nat.card (LL p ≃ₐ[FF] LL p) = p := by
  rw [IsGalois.card_aut_eq_finrank, finrank_FF_LL]

/-! ### The constants of the Kummer extension -/

/-- An algebraic closure of `K`. -/
abbrev Kbar : Type := AlgebraicClosure (KK p)

/-- The geometric base field `K̄(T)`. -/
abbrev GG : Type := RatFunc (Kbar p)

instance charZeroEE : CharZero (EE p) :=
  charZero_of_injective_algebraMap (algebraMap (KK p) (EE p)).injective

/-- `g`, read over the algebraic closure of `K`. -/
def gbar : (Kbar p)[X] := (gpoly p).map (algebraMap (KK p) (Kbar p))

theorem gbar_eq : gbar p
    = ∏ v : (ZMod p)ˣ, (X - C (algebraMap (KK p) (Kbar p) (rt p v))) ^ expo p v := by
  rw [gbar, gpoly, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun v _ => by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

theorem gbar_ne_zero : gbar p ≠ 0 := by
  rw [gbar, Ne, Polynomial.map_eq_zero]
  exact gpoly_ne_zero p

/-- The simple root of `g` at `ζ` survives the passage to the algebraic closure. -/
theorem rootMultiplicity_gbar :
    (gbar p).rootMultiplicity (algebraMap (KK p) (Kbar p) (zeta p)) = 1 := by
  have hinj : Function.Injective (fun v => algebraMap (KK p) (Kbar p) (rt p v)) :=
    fun _ _ h => rt_injective p ((algebraMap (KK p) (Kbar p)).injective h)
  rw [gbar_eq, ← rt_one p]
  exact (rootMultiplicity_prod_pow (fun v => algebraMap (KK p) (Kbar p) (rt p v)) hinj
    (expo p) 1).trans (expo_one p)

theorem algebraMap_gE_geom :
    algebraMap (EE p) (GG p) (gE p) = algebraMap (Kbar p)[X] (GG p) (gbar p) :=
  Rigidity.RET.algebraMap_ratFunc_ratFunc (k := KK p) (K := Kbar p) (gpoly p)

/-- **`g` is not a `p`-th power over the algebraic closure either.** -/
theorem not_pow_geom (y : GG p) : y ^ p ≠ algebraMap (EE p) (GG p) (gE p) := by
  rw [algebraMap_gE_geom]
  intro hy
  have hdvd : p ∣ (gbar p).rootMultiplicity (algebraMap (KK p) (Kbar p) (zeta p)) :=
    Rigidity.RET.rootMultiplicity_dvd_of_pow_eq (gbar_ne_zero p) hy _
  rw [rootMultiplicity_gbar] at hdvd
  exact hp.out.ne_one (Nat.dvd_one.mp hdvd)

/-- The Kummer polynomial stays irreducible over `K̄(T)`: the extension is geometric. -/
theorem kummer_irreducible_geom :
    Irreducible (((X : (EE p)[X]) ^ p - C (gE p)).map (algebraMap (EE p) (GG p))) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime hp.out (not_pow_geom p)

theorem minpoly_wr : minpoly (EE p) (wr p) = (X : (EE p)[X]) ^ p - C (gE p) := by
  have hm : ((X : (EE p)[X]) ^ p - C (gE p)).Monic := monic_X_pow_sub_C (gE p) hp.out.ne_zero
  rw [wr, AdjoinRoot.minpoly_root (kummer_ne_zero p), hm.leadingCoeff, inv_one, map_one, mul_one]

theorem adjoin_wr_top : IntermediateField.adjoin (EE p) ({wr p} : Set (MM p)) = ⊤ := by
  refine top_unique fun x _ => ?_
  have h : x ∈ Algebra.adjoin (EE p) ({wr p} : Set (MM p)) := by
    rw [wr, AdjoinRoot.adjoinRoot_eq_top]
    trivial
  exact IntermediateField.algebra_adjoin_le_adjoin (EE p) _ h

omit hp in
/-- Every polynomial over `K` splits in the geometric base field `K̄(T)`. -/
theorem splits_geom (q : (KK p)[X]) :
    ((q.map (algebraMap (KK p) (EE p))).map (algebraMap (EE p) (GG p))).Splits := by
  have hconst : ∀ a : KK p,
      algebraMap (KK p) (EE p) a = algebraMap (KK p)[X] (EE p) (C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply (KK p) (KK p)[X] (EE p)]
    rfl
  have hcomp : (algebraMap (EE p) (GG p)).comp (algebraMap (KK p) (EE p))
      = ((algebraMap (Kbar p)[X] (GG p)).comp (C : Kbar p →+* (Kbar p)[X])).comp
        (algebraMap (KK p) (Kbar p)) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, hconst, Rigidity.RET.algebraMap_ratFunc_ratFunc, Polynomial.map_C]
    rfl
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map]
  exact (IsAlgClosed.splits (q.map (algebraMap (KK p) (Kbar p)))).map _

/-- **The constants of `M` are exactly `K`**: the Kummer extension is geometric over `K`. -/
theorem algebraicClosure_KK_MM : algebraicClosure (KK p) (MM p) = ⊥ :=
  Rigidity.RET.algebraicClosure_eq_bot_of_isField_tensor (F := KK p) (K := EE p) (K' := GG p)
    (L := MM p) (splits_geom p) (Rigidity.RET.algebraicClosure_ratFunc (KK p))
    (Rigidity.RET.isField_tensor_of_primitive_irreducible (MM p) (wr p) (adjoin_wr_top p)
      (by rw [minpoly_wr]; exact kummer_irreducible_geom p))

theorem exists_const_of_isIntegral {y : MM p} (hy : IsIntegral (KK p) y) :
    ∃ c : KK p, algebraMap (KK p) (MM p) c = y := by
  have hmem : y ∈ algebraicClosure (KK p) (MM p) := mem_algebraicClosure_iff'.mpr hy
  rw [algebraicClosure_KK_MM, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### Regularity of the layer -/

set_option synthInstance.maxHeartbeats 400000 in
/-- The layer sits over `ℚ` through `ℚ(T)`; a shortcut for a slow instance search. -/
instance (priority := high) isScalarTowerQFFLL : IsScalarTower ℚ FF ↥(LL p) := inferInstance

/-- The two routes from `ℚ` into `M`, through the constants and through `ℚ(T)`, agree: `ℚ` is
initial. -/
theorem rationalMaps_eq :
    (algebraMap (KK p) (MM p)).comp (algebraMap ℚ (KK p))
      = (algebraMap FF (MM p)).comp (algebraMap ℚ FF) :=
  Subsingleton.elim _ _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The layer is regular**: it gains no constants over `ℚ`. -/
theorem regular_LL : algebraicClosure ℚ (LL p) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.mp hx
  have hpm : (minpoly ℚ x).Monic := minpoly.monic hxint
  have hpx : aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
  -- the image of `x` in `M` is a constant, i.e. an element of `K`
  have hPx : aeval x ((minpoly ℚ x).map (algebraMap ℚ FF)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hpx
  have hPy : aeval (x : MM p) ((minpoly ℚ x).map (algebraMap ℚ FF)) = 0 := by
    have hval := Polynomial.aeval_algHom_apply (LL p).val x ((minpoly ℚ x).map (algebraMap ℚ FF))
    rw [hPx, map_zero] at hval
    exact hval
  have hyint : IsIntegral (KK p) (x : MM p) := by
    refine ⟨(minpoly ℚ x).map (algebraMap ℚ (KK p)), hpm.map _, ?_⟩
    rw [eval₂_map, rationalMaps_eq, ← eval₂_map]
    exact hPy
  obtain ⟨c, hc⟩ := exists_const_of_isIntegral p hyint
  -- `x` therefore satisfies a polynomial of degree at most `p - 1` over `ℚ(T)`
  have hcm : (minpoly ℚ c).Monic := minpoly.monic (IsIntegral.of_finite ℚ c)
  have hq0 : (minpoly ℚ c).map (algebraMap ℚ FF) ≠ 0 := (hcm.map _).ne_zero
  have hcM : aeval (x : MM p) ((minpoly ℚ c).map (algebraMap ℚ FF)) = 0 := by
    rw [aeval_def, eval₂_map, ← rationalMaps_eq, ← hc, ← Polynomial.hom_eval₂, ← aeval_def,
      minpoly.aeval, map_zero]
  have hqx : aeval x ((minpoly ℚ c).map (algebraMap ℚ FF)) = 0 := by
    have hval : aeval (x : MM p) ((minpoly ℚ c).map (algebraMap ℚ FF))
        = (LL p).val (aeval x ((minpoly ℚ c).map (algebraMap ℚ FF))) :=
      Polynomial.aeval_algHom_apply (LL p).val x _
    exact ZeroMemClass.coe_eq_zero.mp (hval.symm.trans hcM)
  have hdvd : minpoly FF x ∣ (minpoly ℚ c).map (algebraMap ℚ FF) := minpoly.dvd FF x hqx
  have hdeg : (minpoly FF x).natDegree ≤ p - 1 := by
    have h1 : (minpoly FF x).natDegree ≤ ((minpoly ℚ c).map (algebraMap ℚ FF)).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hq0
    have h2 : ((minpoly ℚ c).map (algebraMap ℚ FF)).natDegree = (minpoly ℚ c).natDegree :=
      hcm.natDegree_map _
    have h3 : (minpoly ℚ c).natDegree ≤ Module.finrank ℚ (KK p) := minpoly.natDegree_le c
    rw [finrank_Q_KK] at h3
    omega
  -- but its degree also divides `p`
  have hxFF : IsIntegral FF x := IsIntegral.of_finite FF x
  have hadj : Module.finrank FF FF⟮x⟯ = (minpoly FF x).natDegree :=
    IntermediateField.adjoin.finrank hxFF
  have hdvdp : (minpoly FF x).natDegree ∣ p := by
    have h := minpoly.degree_dvd hxFF
    rwa [finrank_FF_LL] at h
  have hone : (minpoly FF x).natDegree = 1 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ hdvdp) with h | h
    · exact h
    · have := hp.out.two_le
      omega
  -- degree one means `x` already lies in `ℚ(T)`
  have hbot : FF⟮x⟯ = ⊥ := IntermediateField.finrank_eq_one_iff.mp (by rw [hadj, hone])
  have hxmem : x ∈ (⊥ : IntermediateField FF (LL p)) := by
    rw [← hbot]
    exact IntermediateField.mem_adjoin_simple_self FF x
  obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp hxmem
  -- and a constant of `ℚ(T)` is rational
  have hzint : IsIntegral ℚ z := by
    refine ⟨minpoly ℚ x, hpm, ?_⟩
    refine (algebraMap FF (LL p)).injective ?_
    rw [map_zero]
    have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ FF (LL p)) z (minpoly ℚ x)
    rw [IsScalarTower.coe_toAlgHom', hz, hpx] at h
    rw [← aeval_def]
    exact h.symm
  have hzmem : z ∈ algebraicClosure ℚ FF := mem_algebraicClosure_iff'.mpr hzint
  rw [Rigidity.RET.regular_ratFunc, IntermediateField.mem_bot] at hzmem
  obtain ⟨q, hq⟩ := hzmem
  refine IntermediateField.mem_bot.mpr ⟨q, ?_⟩
  rw [IsScalarTower.algebraMap_apply ℚ FF (LL p), hq, hz]

/-! ### The regular realization -/

/-- **The Galois group of the degree-`p` layer is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_aut : IsRegularInverseGalois (LL p ≃ₐ[FF] LL p) :=
  ⟨LL p, inferInstance, algFFLL p, inferInstance, isGalois_FF_LL p, inferInstance, inferInstance,
    regular_LL p, ⟨MulEquiv.refl _⟩⟩

end

end Rigidity.RET.CyclicPrime

namespace Rigidity.RET

/-- **Every group of prime order is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_of_card_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) : IsRegularInverseGalois G :=
  haveI : Fact p.Prime := ⟨hp⟩
  (CyclicPrime.isRegularInverseGalois_aut p).of_mulEquiv
    (mulEquivOfPrimeCardEq (CyclicPrime.card_aut_LL p) hG)

/-- **Every group of order five is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_of_card_eq_five {G : Type*} [Group G] (hG : Nat.card G = 5) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_card_prime (by norm_num) hG

/-- **Every group of order seven is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_of_card_eq_seven {G : Type*} [Group G] (hG : Nat.card G = 7) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_card_prime (by norm_num) hG

end Rigidity.RET
