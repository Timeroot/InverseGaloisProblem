/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.RatFuncConstants
import InverseGalois.Rigidity.RET.RegularityConverse
import InverseGalois.Rigidity.RET.RegularCriterion
import InverseGalois.Rigidity.RET.Statement

/-!
# Regular cyclic extensions of `ℚ(T)` of arbitrary degree

Every finite cyclic group is a **regular** inverse Galois group over `ℚ`.

The construction is Kummer theory twisted by the full cyclotomic character.  Write `K = ℚ(ζ)` for
the `n`-th cyclotomic field and identify `Gal(K / ℚ)` with `(ℤ/n)ˣ`, the unit `c` acting by
`ζ ↦ ζ ^ c`.  Over `K(T)` one takes the Kummer extension `M = K(T)(g ^ (1/n))` for the weighted
product over the units of `ℤ/n`

`g = ∏ (T - ζ ^ v) ^ a v`,   `a v = ` the representative of `v⁻¹`.

Exponent vectors are handled uniformly: the map `Φ e = ∏ (T - ζ ^ v) ^ e v`, defined for any
`e : (ℤ/n)ˣ → ℤ`, is a homomorphism from the additive group of exponent vectors to `K(T)ˣ`, it is
injective because the root multiplicities of a product of distinct linear factors read off the
exponents, and the coefficient action of `c` permutes the factors:

`c · Φ e = Φ (e ∘ (c⁻¹ * ·))`.

Choosing the weights to be the inverses mod `n` makes `c · g` differ from `g ^ c` by an exact
`n`-th power `h c ^ n`, so `c` lifts to `M` by `w ↦ w ^ c * h c`.  Because `Φ` is injective the
lifts satisfy the *exact* cocycle identity they need to form a group: `c ↦ (w ↦ w ^ c * h c)` is a
homomorphism `(ℤ/n)ˣ → Aut(M / ℚ(T))`, a complement to the Kummer group `⟨w ↦ ζ w⟩`.  Its fixed
field is therefore a cyclic extension of `ℚ(T)` of degree exactly `n`.

Irreducibility of `X ^ n - g` in every degree — including even ones, where the usual `n`-th power
criteria are unavailable — comes from `Rigidity.RET.irreducible_X_pow_sub_C_ratFunc`: `g` has a
simple root at `ζ`, so the Kummer polynomial is Eisenstein at `T - ζ`.  The same simple root makes
the extension geometric, and the constants are then pinned down by the cyclotomic character: a
constant of the layer is fixed by all of `Gal(K / ℚ)`, hence rational.
-/

open Polynomial

namespace Rigidity.RET.Cyclic

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc IntermediateField

open Rigidity.RET (rootMultiplicity_prod_pow prod_pow_ne_zero irreducible_X_pow_sub_C_ratFunc)

variable (n : ℕ) [hn : Fact (1 < n)]

instance neZero_of_one_lt : NeZero n := ⟨by have := hn.out; omega⟩

/-! ### The `n`-th cyclotomic field -/

/-- The field of `n`-th roots of unity. -/
abbrev KK : Type := CyclotomicField n ℚ

/-- A primitive `n`-th root of unity. -/
def zeta : KK n := IsCyclotomicExtension.zeta n ℚ (KK n)

theorem zeta_spec : IsPrimitiveRoot (zeta n) n := IsCyclotomicExtension.zeta_spec n ℚ (KK n)

theorem cyclotomic_irr : Irreducible (cyclotomic n ℚ) :=
  cyclotomic.irreducible_rat (by have := hn.out; omega)

instance isGalois_Q_KK : IsGalois ℚ (KK n) := IsCyclotomicExtension.isGalois {n} ℚ (KK n)

/-- `ζ` raised to a residue class: legitimate because `ζ ^ n = 1`. -/
def zetaPow (x : ZMod n) : KK n := zeta n ^ x.val

theorem zetaPow_natCast (m : ℕ) : zetaPow n (m : ZMod n) = zeta n ^ m := by
  rw [zetaPow, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod m n]
  rw [pow_add, pow_mul, (zeta_spec n).pow_eq_one, one_pow, one_mul]

theorem zetaPow_injective : Function.Injective (zetaPow n) := fun x y h =>
  ZMod.val_injective n ((zeta_spec n).pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)

theorem zetaPow_one : zetaPow n 1 = zeta n := by rw [zetaPow, ZMod.val_one, pow_one]

/-! ### The cyclotomic character -/

/-- The natural-number representative of a unit modulo `n`. -/
def cnat (c : (ZMod n)ˣ) : ℕ := ((c : ZMod n)).val

theorem cnat_cast (c : (ZMod n)ˣ) : ((cnat n c : ℕ) : ZMod n) = (c : ZMod n) := by
  rw [cnat, ZMod.natCast_val, ZMod.cast_id]

theorem cnat_one : cnat n 1 = 1 := by rw [cnat, Units.val_one, ZMod.val_one]

/-- **The cyclotomic character**, read backwards: the unit `c` names the automorphism `ζ ↦ ζ ^ c`
of the `n`-th cyclotomic field. -/
def sigmaK : (ZMod n)ˣ →* (KK n ≃ₐ[ℚ] KK n) :=
  (IsCyclotomicExtension.autEquivPow (KK n) (cyclotomic_irr n)).symm.toMonoidHom

theorem sigmaK_injective : Function.Injective (sigmaK n) :=
  (IsCyclotomicExtension.autEquivPow (KK n) (cyclotomic_irr n)).symm.injective

theorem sigmaK_surjective : Function.Surjective (sigmaK n) :=
  (IsCyclotomicExtension.autEquivPow (KK n) (cyclotomic_irr n)).symm.surjective

@[simp] theorem sigmaK_zeta (c : (ZMod n)ˣ) : sigmaK n c (zeta n) = zeta n ^ cnat n c := by
  have h := (zeta_spec n).autToPow_spec (R := ℚ) (sigmaK n c)
  have h2 : ((zeta_spec n).autToPow ℚ (sigmaK n c)) = c := by
    have hc := (IsCyclotomicExtension.autEquivPow (KK n) (cyclotomic_irr n)).apply_symm_apply c
    simpa [sigmaK] using hc
  rw [cnat, ← h, h2]

theorem sigmaK_zetaPow (c : (ZMod n)ˣ) (x : ZMod n) :
    sigmaK n c (zetaPow n x) = zetaPow n ((c : ZMod n) * x) := by
  rw [zetaPow, map_pow, sigmaK_zeta, ← pow_mul, ← zetaPow_natCast]
  congr 1
  push_cast [cnat, ZMod.natCast_val, ZMod.cast_id]
  ring

/-! ### Exponent vectors -/

/-- The root of the Kummer datum attached to a unit `v`. -/
def rt (v : (ZMod n)ˣ) : KK n := zetaPow n (v : ZMod n)

theorem rt_injective : Function.Injective (rt n) := fun _ _ h =>
  Units.ext (zetaPow_injective n h)

theorem rt_one : rt n 1 = zeta n := by rw [rt, Units.val_one, zetaPow_one]

theorem sigmaK_rt (c v : (ZMod n)ˣ) : sigmaK n c (rt n v) = rt n (c * v) := by
  rw [rt, rt, sigmaK_zetaPow, Units.val_mul]

/-- The rational function field `ℚ(T)`. -/
abbrev FF : Type := RatFunc ℚ

/-- The rational function field `K(T) = ℚ(ζ)(T)`. -/
abbrev EE : Type := RatFunc (KK n)

/-- Shortcut for the scalar action of `ℚ(T)` on `K(T)`, whose search is pathologically slow. -/
instance (priority := high) smulFFEE : SMul FF (EE n) := Algebra.toSMul

/-- A linear factor of the Kummer datum, as an element of `K(T)`. -/
def linE (v : (ZMod n)ˣ) : EE n := algebraMap (KK n)[X] (EE n) (X - C (rt n v))

theorem linE_ne_zero (v : (ZMod n)ˣ) : linE n v ≠ 0 := fun h =>
  X_sub_C_ne_zero (rt n v)
    ((IsFractionRing.injective (KK n)[X] (EE n)) (by rw [map_zero]; exact h))

/-- **The exponent-vector homomorphism** `Φ e = ∏ (T - ζ ^ v) ^ e v`. -/
def phi (e : (ZMod n)ˣ → ℤ) : EE n := ∏ v : (ZMod n)ˣ, linE n v ^ e v

theorem phi_ne_zero (e : (ZMod n)ˣ → ℤ) : phi n e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (linE_ne_zero n v)

theorem phi_congr {e₁ e₂ : (ZMod n)ˣ → ℤ} (h : ∀ v, e₁ v = e₂ v) : phi n e₁ = phi n e₂ :=
  Finset.prod_congr rfl fun v _ => by rw [h v]

theorem phi_zero : phi n (fun _ => 0) = 1 := by
  rw [phi]
  exact Finset.prod_eq_one fun v _ => zpow_zero _

theorem phi_add (e₁ e₂ : (ZMod n)ˣ → ℤ) :
    phi n (fun v => e₁ v + e₂ v) = phi n e₁ * phi n e₂ := by
  rw [phi, phi, phi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => zpow_add₀ (linE_ne_zero n v) _ _

theorem phi_zpow (e : (ZMod n)ˣ → ℤ) (m : ℤ) : phi n e ^ m = phi n (fun v => m * e v) := by
  rw [phi, phi, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun v _ => by rw [← zpow_mul, mul_comm]

/-- `Φ` of a vector of natural numbers is the image of an honest polynomial. -/
theorem phi_natCast (A : (ZMod n)ˣ → ℕ) :
    phi n (fun v => (A v : ℤ))
      = algebraMap (KK n)[X] (EE n) (∏ v : (ZMod n)ˣ, (X - C (rt n v)) ^ A v) := by
  rw [phi, map_prod]
  exact Finset.prod_congr rfl fun v _ => by rw [map_pow, zpow_natCast]; rfl

/-- **`Φ` is injective**: the exponents are recovered as root multiplicities. -/
theorem exponent_eq_zero_of_phi_eq_one {e : (ZMod n)ˣ → ℤ} (he : phi n e = 1)
    (w : (ZMod n)ˣ) : e w = 0 := by
  obtain ⟨A, B, hAB⟩ : ∃ A B : (ZMod n)ˣ → ℕ, ∀ v, (A v : ℤ) - (B v : ℤ) = e v :=
    ⟨fun v => (e v).toNat, fun v => (-(e v)).toNat, fun v => by
      show ((e v).toNat : ℤ) - ((-(e v)).toNat : ℤ) = e v
      omega⟩
  have hphi : phi n (fun v => (A v : ℤ)) = phi n (fun v => (B v : ℤ)) := by
    have hfun : (fun v => (A v : ℤ)) = fun v => e v + (B v : ℤ) :=
      funext fun v => by have := hAB v; omega
    rw [hfun, phi_add, he, one_mul]
  have hpoly : (∏ v : (ZMod n)ˣ, (X - C (rt n v)) ^ A v)
      = ∏ v : (ZMod n)ˣ, (X - C (rt n v)) ^ B v :=
    IsFractionRing.injective (KK n)[X] (EE n) (by rw [← phi_natCast, ← phi_natCast]; exact hphi)
  have hmul : (∏ v : (ZMod n)ˣ, (X - C (rt n v)) ^ A v).rootMultiplicity (rt n w)
      = (∏ v : (ZMod n)ˣ, (X - C (rt n v)) ^ B v).rootMultiplicity (rt n w) := by rw [hpoly]
  rw [rootMultiplicity_prod_pow _ (rt_injective n), rootMultiplicity_prod_pow _ (rt_injective n)]
    at hmul
  have := hAB w
  omega

/-! ### The coefficient action on exponent vectors -/

/-- The coefficient automorphism of `K(T)` attached to a unit, fixing `ℚ(T)`. -/
def sigmaE : (ZMod n)ˣ →* (EE n ≃ₐ[FF] EE n) :=
  (Rigidity.RET.ratFuncMapHom (k := ℚ) (K := KK n)).comp (sigmaK n)

theorem sigmaE_injective : Function.Injective (sigmaE n) := fun _ _ h =>
  sigmaK_injective n (Rigidity.RET.ratFuncMapHom_injective h)

theorem sigmaE_algebraMap_poly (c : (ZMod n)ˣ) (q : (KK n)[X]) :
    sigmaE n c (algebraMap (KK n)[X] (EE n) q)
      = algebraMap (KK n)[X] (EE n) (q.map (sigmaK n c : KK n →+* KK n)) := by
  rw [sigmaE, MonoidHom.comp_apply, Rigidity.RET.ratFuncMapHom,
    MonoidHom.coe_mk, OneHom.coe_mk, Rigidity.RET.ratFuncMapAlg_apply,
    Rigidity.RET.ratFuncMap_algebraMap]

theorem sigmaE_algebraMap (c : (ZMod n)ˣ) (a : KK n) :
    sigmaE n c (algebraMap (KK n) (EE n) a) = algebraMap (KK n) (EE n) (sigmaK n c a) := by
  rw [IsScalarTower.algebraMap_apply (KK n) (KK n)[X] (EE n),
    IsScalarTower.algebraMap_apply (KK n) (KK n)[X] (EE n), sigmaE_algebraMap_poly]
  congr 1
  simp

theorem sigmaE_linE (c v : (ZMod n)ˣ) : sigmaE n c (linE n v) = linE n (c * v) := by
  rw [linE, sigmaE_algebraMap_poly, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    linE, RingHom.coe_coe, sigmaK_rt]

/-- **The coefficient action permutes the exponents.** -/
theorem sigmaE_phi (c : (ZMod n)ˣ) (e : (ZMod n)ˣ → ℤ) :
    sigmaE n c (phi n e) = phi n (fun v => e (c⁻¹ * v)) := by
  have h1 : sigmaE n c (phi n e) = ∏ v : (ZMod n)ˣ, linE n (c * v) ^ e v := by
    rw [phi, map_prod]
    exact Finset.prod_congr rfl fun v _ => by rw [map_zpow₀, sigmaE_linE]
  have h2 : phi n (fun v => e (c⁻¹ * v)) = ∏ v : (ZMod n)ˣ, linE n (c * v) ^ e v := by
    rw [phi, ← Equiv.prod_comp (Equiv.mulLeft c) (fun w => linE n w ^ e (c⁻¹ * w))]
    exact Finset.prod_congr rfl fun v _ => by rw [Equiv.coe_mulLeft, inv_mul_cancel_left]
  rw [h1, h2]

/-! ### The twisted Kummer datum -/

/-- The exponent attached to a unit `v`: the representative of `v⁻¹`. -/
def anat (v : (ZMod n)ˣ) : ℕ := ((v⁻¹ : (ZMod n)ˣ) : ZMod n).val

theorem anat_cast (v : (ZMod n)ˣ) : ((anat n v : ℕ) : ZMod n) = ((v⁻¹ : (ZMod n)ˣ) : ZMod n) := by
  rw [anat, ZMod.natCast_val, ZMod.cast_id]

theorem anat_one : anat n 1 = 1 := by rw [anat, inv_one, Units.val_one, ZMod.val_one]

/-- The weighted product `g = ∏ (T - ζ ^ v) ^ a v`, the exponents being the inverses mod `n`. -/
def gpoly : (KK n)[X] := ∏ v : (ZMod n)ˣ, (X - C (rt n v)) ^ anat n v

theorem gpoly_ne_zero : gpoly n ≠ 0 := prod_pow_ne_zero _ _

/-- `g` has a **simple** root at `ζ`: this single fact drives both the irreducibility of the
Kummer extension and its regularity. -/
theorem rootMultiplicity_gpoly : (gpoly n).rootMultiplicity (zeta n) = 1 := by
  rw [gpoly, ← rt_one n, rootMultiplicity_prod_pow _ (rt_injective n), anat_one]

/-- The twisted Kummer datum `g`, as an element of `K(T)`. -/
def gE : EE n := algebraMap (KK n)[X] (EE n) (gpoly n)

theorem gE_eq_phi : gE n = phi n (fun v => (anat n v : ℤ)) := (phi_natCast n (anat n)).symm

theorem gE_ne_zero : gE n ≠ 0 := by rw [gE_eq_phi]; exact phi_ne_zero n _

theorem gE_pow_nat (m : ℕ) : gE n ^ m = phi n (fun v => (m : ℤ) * (anat n v : ℤ)) := by
  rw [gE_eq_phi, ← zpow_natCast _ m, phi_zpow]

/-- The correction exponents: the exact amount by which `c · g` and `g ^ c` differ by an `n`-th
power. -/
def hexp (c v : (ZMod n)ˣ) : ℤ :=
  ((anat n (c⁻¹ * v) : ℤ) - (cnat n c : ℤ) * (anat n v : ℤ)) / (n : ℤ)

theorem dvd_anat_sub (c v : (ZMod n)ˣ) :
    (n : ℤ) ∣ (anat n (c⁻¹ * v) : ℤ) - (cnat n c : ℤ) * (anat n v : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [anat_cast, anat_cast, cnat_cast, mul_inv_rev, inv_inv, Units.val_mul]
  ring

theorem n_mul_hexp (c v : (ZMod n)ˣ) :
    (n : ℤ) * hexp n c v = (anat n (c⁻¹ * v) : ℤ) - (cnat n c : ℤ) * (anat n v : ℤ) :=
  Int.mul_ediv_cancel' (dvd_anat_sub n c v)

theorem hexp_one (v : (ZMod n)ˣ) : hexp n 1 v = 0 := by
  rw [hexp, inv_one, one_mul, cnat_one, Nat.cast_one, one_mul, sub_self, Int.zero_ediv]

/-- The twisting factor attached to a unit. -/
def hE (c : (ZMod n)ˣ) : EE n := phi n (hexp n c)

theorem hE_ne_zero (c : (ZMod n)ˣ) : hE n c ≠ 0 := phi_ne_zero n _

theorem hE_one : hE n 1 = 1 := by
  rw [hE, phi_congr n (e₂ := fun _ => (0 : ℤ)) (hexp_one n), phi_zero]

theorem hE_pow_nat (c : (ZMod n)ˣ) (m : ℕ) :
    hE n c ^ m = phi n (fun v => (m : ℤ) * hexp n c v) := by
  rw [hE, ← zpow_natCast _ m, phi_zpow]

/-- **The twisting identity** in `K(T)`: `c · g = g ^ c * h c ^ n`. -/
theorem sigmaE_gE (c : (ZMod n)ˣ) : sigmaE n c (gE n) = gE n ^ cnat n c * hE n c ^ n := by
  rw [gE_pow_nat, hE_pow_nat, ← phi_add, gE_eq_phi, sigmaE_phi]
  refine phi_congr n fun v => ?_
  have h := n_mul_hexp n c v
  linarith

/-- The amount by which the representatives of `c`, `d` and `c * d` fail to be multiplicative. -/
def kk (c d : (ZMod n)ˣ) : ℤ :=
  ((cnat n c : ℤ) * (cnat n d : ℤ) - (cnat n (c * d) : ℤ)) / (n : ℤ)

theorem dvd_cnat_sub (c d : (ZMod n)ˣ) :
    (n : ℤ) ∣ (cnat n c : ℤ) * (cnat n d : ℤ) - (cnat n (c * d) : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [cnat_cast, cnat_cast, cnat_cast, Units.val_mul]
  ring

theorem n_mul_kk (c d : (ZMod n)ˣ) :
    (n : ℤ) * kk n c d = (cnat n c : ℤ) * (cnat n d : ℤ) - (cnat n (c * d) : ℤ) :=
  Int.mul_ediv_cancel' (dvd_cnat_sub n c d)

/-- **The cocycle identity** satisfied by the twisting factors.  It is what makes the lifts of the
cyclotomic character to the Kummer extension multiply correctly. -/
theorem hE_cocycle (c d : (ZMod n)ˣ) :
    gE n ^ kk n c d * hE n c ^ cnat n d * sigmaE n c (hE n d) = hE n (c * d) := by
  rw [gE_eq_phi, phi_zpow, hE_pow_nat, hE, sigmaE_phi, hE, ← phi_add, ← phi_add]
  refine phi_congr n fun v => ?_
  have hn0 : (n : ℤ) ≠ 0 := by have := hn.out; positivity
  refine mul_left_cancel₀ hn0 ?_
  have h1 := n_mul_kk n c d
  have h2 := n_mul_hexp n c v
  have h3 := n_mul_hexp n d (c⁻¹ * v)
  have h4 := n_mul_hexp n (c * d) v
  rw [show (c * d)⁻¹ * v = d⁻¹ * (c⁻¹ * v) by rw [mul_inv_rev, mul_assoc]] at h4
  linear_combination (anat n v : ℤ) * h1 + (cnat n d : ℤ) * h2 + h3 - h4

/-! ### The Kummer extension -/

/-- The Kummer polynomial `X ^ n - g` is irreducible over `K(T)`: `g` has a simple root, so the
polynomial is Eisenstein at `T - ζ`. -/
theorem kummer_irreducible : Irreducible ((X : (EE n)[X]) ^ n - C (gE n)) :=
  irreducible_X_pow_sub_C_ratFunc (rootMultiplicity_gpoly n) (by have := hn.out; omega)

instance factKummer : Fact (Irreducible ((X : (EE n)[X]) ^ n - C (gE n))) := ⟨kummer_irreducible n⟩

/-- The Kummer extension `M = K(T)(g ^ (1/n))`. -/
abbrev MM : Type := AdjoinRoot ((X : (EE n)[X]) ^ n - C (gE n))

/-- Shortcut for the `ℚ(T)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algFFMM : Algebra FF (MM n) := AdjoinRoot.instAlgebra _

/-- Shortcut for the `K(T)`-algebra structure of `M`, whose search is pathologically slow. -/
instance (priority := high) algEEMM : Algebra (EE n) (MM n) := AdjoinRoot.instAlgebra _

/-- The chosen `n`-th root of `g`. -/
def wr : MM n := AdjoinRoot.root _

theorem wr_pow : wr n ^ n = algebraMap (EE n) (MM n) (gE n) := by
  rw [wr, AdjoinRoot.algebraMap_eq]
  exact root_X_pow_sub_C_pow n (gE n)

theorem kummer_ne_zero : ((X : (EE n)[X]) ^ n - C (gE n)) ≠ 0 := (kummer_irreducible n).ne_zero

instance : FiniteDimensional (EE n) (MM n) := (AdjoinRoot.powerBasis (kummer_ne_zero n)).finite

theorem finrank_EE_MM : Module.finrank (EE n) (MM n) = n := by
  rw [(AdjoinRoot.powerBasis (kummer_ne_zero n)).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

theorem finrank_Q_KK : Module.finrank ℚ (KK n) = n.totient :=
  IsCyclotomicExtension.finrank (KK n) (cyclotomic_irr n)

theorem finrank_FF_EE : Module.finrank FF (EE n) = n.totient := by
  rw [RatFunc.finrank_ratFunc_ratFunc ℚ (KK n), finrank_Q_KK]

instance : FiniteDimensional FF (EE n) :=
  Module.rank_lt_aleph0_iff.mp (by
    rw [RatFunc.rank_ratFunc_ratFunc ℚ (KK n)]; exact Module.rank_lt_aleph0 ℚ (KK n))

instance : FiniteDimensional FF (MM n) := .trans FF (EE n) (MM n)

theorem finrank_FF_MM : Module.finrank FF (MM n) = n.totient * n := by
  rw [← Module.finrank_mul_finrank FF (EE n) (MM n), finrank_FF_EE, finrank_EE_MM]

theorem totient_pos : 0 < n.totient := Nat.totient_pos.mpr (by have := hn.out; omega)

/-! ### The two families of automorphisms -/

/-- The defining relation of `M`, in the form required to lift a homomorphism out of it. -/
private theorem eval₂_kummer {i : EE n →+* MM n} {x : MM n} (h : x ^ n = i (gE n)) :
    ((X : (EE n)[X]) ^ n - C (gE n)).eval₂ i x = 0 := by
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h, sub_self]

/-- `ζ`, viewed in `M`. -/
def zetaM : MM n := algebraMap (KK n) (MM n) (zeta n)

theorem zetaM_pow_eq_one_iff (m : ℕ) : zetaM n ^ m = 1 ↔ n ∣ m := by
  rw [zetaM, ← map_pow, ← (zeta_spec n).pow_eq_one_iff_dvd m]
  constructor
  · intro h
    exact (algebraMap (KK n) (MM n)).injective (by rw [h, map_one])
  · intro h; rw [h, map_one]

theorem zetaM_pow : zetaM n ^ n = 1 := (zetaM_pow_eq_one_iff n n).mpr dvd_rfl

theorem wr_ne_zero : wr n ≠ 0 := root_X_pow_sub_C_ne_zero hn.out (gE n)

/-- The Kummer automorphism `w ↦ ζ w`, as an algebra map. -/
def tauHom : MM n →ₐ[EE n] MM n :=
  AdjoinRoot.liftAlgHom ((X : (EE n)[X]) ^ n - C (gE n)) (Algebra.ofId (EE n) (MM n))
    (zetaM n * wr n)
    (eval₂_kummer n (by rw [mul_pow, zetaM_pow, one_mul, wr_pow]; rfl))

/-- **The Kummer automorphism** `w ↦ ζ w` of `M / K(T)`. -/
def tau : MM n ≃ₐ[EE n] MM n := AlgEquiv.ofBijective (tauHom n) (tauHom n).bijective

@[simp] theorem tau_wr : tau n (wr n) = zetaM n * wr n := by
  simp only [tau, AlgEquiv.coe_ofBijective, tauHom, wr, AdjoinRoot.liftAlgHom_root]

/-- The twisting factor, viewed in `M`. -/
def hM (c : (ZMod n)ˣ) : MM n := algebraMap (EE n) (MM n) (hE n c)

theorem hM_ne_zero (c : (ZMod n)ˣ) : hM n c ≠ 0 := fun h =>
  hE_ne_zero n c ((algebraMap (EE n) (MM n)).injective (by rw [map_zero, ← hM, h]))

/-- The lift of the unit `c` to `M`, sending `w` to `w ^ c * h c`. -/
def sigmaHomM (c : (ZMod n)ˣ) : MM n →ₐ[FF] MM n :=
  AdjoinRoot.liftAlgHom ((X : (EE n)[X]) ^ n - C (gE n))
    ((IsScalarTower.toAlgHom FF (EE n) (MM n)).comp (sigmaE n c).toAlgHom)
    (wr n ^ cnat n c * hM n c)
    (eval₂_kummer n (by
      show (wr n ^ cnat n c * hM n c) ^ n = algebraMap (EE n) (MM n) (sigmaE n c (gE n))
      rw [sigmaE_gE, map_mul, map_pow, map_pow, mul_pow, ← pow_mul,
        Nat.mul_comm (cnat n c) n, pow_mul, wr_pow, hM]))

/-- The lift of the unit `c` to an automorphism of `M / ℚ(T)`. -/
def sigmaMe (c : (ZMod n)ˣ) : MM n ≃ₐ[FF] MM n :=
  AlgEquiv.ofBijective (sigmaHomM n c) (sigmaHomM n c).bijective

@[simp] theorem sigmaMe_wr (c : (ZMod n)ˣ) :
    sigmaMe n c (wr n) = wr n ^ cnat n c * hM n c := by
  simp only [sigmaMe, AlgEquiv.coe_ofBijective, sigmaHomM, wr, AdjoinRoot.liftAlgHom_root]

@[simp] theorem sigmaMe_algebraMap (c : (ZMod n)ˣ) (x : EE n) :
    sigmaMe n c (algebraMap (EE n) (MM n) x) = algebraMap (EE n) (MM n) (sigmaE n c x) := by
  rw [sigmaMe, AlgEquiv.coe_ofBijective, sigmaHomM, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.liftAlgHom_of]
  rfl

/-- Two ring maps out of `M` agreeing on `K(T)` and on `w` agree. -/
private theorem ringHom_ext_M {φ ψ : MM n →+* MM n}
    (hbase : ∀ x : EE n, φ (algebraMap (EE n) (MM n) x) = ψ (algebraMap (EE n) (MM n) x))
    (hw : φ (wr n) = ψ (wr n)) (y : MM n) : φ y = ψ y := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  induction q using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | monomial i c =>
      have hmk : AdjoinRoot.mk ((X : (EE n)[X]) ^ n - C (gE n)) (Polynomial.monomial i c)
          = algebraMap (EE n) (MM n) c * wr n ^ i := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
        rfl
      rw [hmk, map_mul, map_mul, map_pow, map_pow, hbase, hw]

/-- An automorphism of `M` over `ℚ(T)` is determined by its restriction to `K(T)` and its value
on `w`. -/
private theorem algEquiv_ext_M {f g : MM n ≃ₐ[FF] MM n}
    (hbase : ∀ x : EE n, f (algebraMap (EE n) (MM n) x) = g (algebraMap (EE n) (MM n) x))
    (hw : f (wr n) = g (wr n)) : f = g :=
  AlgEquiv.ext fun y =>
    ringHom_ext_M n (φ := (f : MM n →+* MM n)) (ψ := (g : MM n →+* MM n)) hbase hw y

theorem sigmaMe_one : sigmaMe n 1 = 1 := by
  refine algEquiv_ext_M n (fun x => ?_) ?_
  · rw [sigmaMe_algebraMap, map_one, AlgEquiv.one_apply, AlgEquiv.one_apply]
  · rw [sigmaMe_wr, cnat_one, pow_one, hM, hE_one, map_one, mul_one, AlgEquiv.one_apply]

theorem sigmaMe_mul (c d : (ZMod n)ˣ) : sigmaMe n (c * d) = sigmaMe n c * sigmaMe n d := by
  refine algEquiv_ext_M n (fun x => ?_) ?_
  · rw [AlgEquiv.mul_apply, sigmaMe_algebraMap, sigmaMe_algebraMap, sigmaMe_algebraMap, map_mul,
      AlgEquiv.mul_apply]
  · have hcoc := congrArg (algebraMap (EE n) (MM n)) (hE_cocycle n c d)
    rw [map_mul, map_mul, map_zpow₀, map_pow, ← wr_pow] at hcoc
    have hpow : wr n ^ (cnat n c * cnat n d)
        = wr n ^ cnat n (c * d) * (wr n ^ n) ^ kk n c d := by
      rw [← zpow_natCast (wr n) (cnat n c * cnat n d), ← zpow_natCast (wr n) (cnat n (c * d)),
        ← zpow_natCast (wr n) n, ← zpow_mul, ← zpow_add₀ (wr_ne_zero n)]
      congr 1
      have h := n_mul_kk n c d
      push_cast
      linarith
    simp only [AlgEquiv.mul_apply, sigmaMe_wr, hM, map_mul, map_pow, sigmaMe_algebraMap]
    rw [mul_pow, ← pow_mul, hpow, ← hcoc]
    ring

/-- **The lifted cyclotomic character**: a homomorphism from the units of `ℤ/n` to the
automorphism group of `M / ℚ(T)`. -/
def sigmaM : (ZMod n)ˣ →* (MM n ≃ₐ[FF] MM n) where
  toFun := sigmaMe n
  map_one' := sigmaMe_one n
  map_mul' := sigmaMe_mul n

@[simp] theorem sigmaM_apply (c : (ZMod n)ˣ) : sigmaM n c = sigmaMe n c := rfl

theorem sigmaM_injective : Function.Injective (sigmaM n) := by
  intro c d h
  refine sigmaE_injective n (AlgEquiv.ext fun x => ?_)
  refine (algebraMap (EE n) (MM n)).injective ?_
  rw [← sigmaMe_algebraMap, ← sigmaMe_algebraMap, ← sigmaM_apply, ← sigmaM_apply, h]

instance finite_range_sigmaM : Finite ↥(MonoidHom.range (sigmaM n)) :=
  Finite.of_equiv _ (MonoidHom.ofInjective (sigmaM_injective n)).toEquiv

theorem card_range_sigmaM : Nat.card ↥(MonoidHom.range (sigmaM n)) = n.totient := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (sigmaM_injective n)).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

instance finite_range_sigmaE : Finite ↥(MonoidHom.range (sigmaE n)) :=
  Finite.of_equiv _ (MonoidHom.ofInjective (sigmaE_injective n)).toEquiv

theorem card_range_sigmaE : Nat.card ↥(MonoidHom.range (sigmaE n)) = n.totient := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (sigmaE_injective n)).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-! ### The fixed fields -/

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

/-- `ζ` comes from `K(T)`. -/
theorem zetaM_eq : zetaM n = algebraMap (EE n) (MM n) (algebraMap (KK n) (EE n) (zeta n)) := by
  rw [zetaM, ← IsScalarTower.algebraMap_apply]

@[simp] theorem tau_zetaM : tau n (zetaM n) = zetaM n := by
  rw [zetaM_eq]; exact (tau n).commutes _

theorem tau_pow_wr (m : ℕ) : (tau n ^ m) (wr n) = zetaM n ^ m * wr n := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ' (tau n) k, AlgEquiv.mul_apply, ih, map_mul, map_pow, tau_zetaM, tau_wr,
        pow_succ (zetaM n) k]
      ring

theorem tau_pow_eq_one_iff (m : ℕ) : tau n ^ m = 1 ↔ n ∣ m := by
  constructor
  · intro h
    have hz : zetaM n ^ m * wr n = wr n := by
      rw [← tau_pow_wr, h, AlgEquiv.one_apply]
    have hz1 : zetaM n ^ m = 1 :=
      mul_right_cancel₀ (wr_ne_zero n) (by rw [hz, one_mul])
    exact (zetaM_pow_eq_one_iff n m).mp hz1
  · intro h
    refine AlgEquiv.coe_algHom_injective (AdjoinRoot.algHom_ext ?_)
    show (tau n ^ m) (wr n) = (1 : MM n ≃ₐ[EE n] MM n) (wr n)
    rw [tau_pow_wr, (zetaM_pow_eq_one_iff n m).mpr h, one_mul, AlgEquiv.one_apply]

theorem orderOf_tau : orderOf (tau n) = n :=
  Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((tau_pow_eq_one_iff n n).mpr dvd_rfl))
    ((tau_pow_eq_one_iff n (orderOf (tau n))).mp (pow_orderOf_eq_one _))

theorem fixedField_tau : IntermediateField.fixedField (Subgroup.zpowers (tau n)) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_tau, finrank_EE_MM]

theorem fixedField_sigmaE : IntermediateField.fixedField (MonoidHom.range (sigmaE n)) = ⊥ := by
  refine eq_bot_of_finrank_eq _ ?_
  rw [IntermediateField.finrank_fixedField_eq_card, card_range_sigmaE, finrank_FF_EE]

/-- **An element of `M` fixed by the Kummer automorphism lies in `K(T)`.** -/
theorem exists_of_tau_fixed {x : MM n} (hx : tau n x = x) :
    ∃ y : EE n, algebraMap (EE n) (MM n) y = x := by
  have hle : Subgroup.zpowers (tau n) ≤ MulAction.stabilizer (MM n ≃ₐ[EE n] MM n) x :=
    Subgroup.zpowers_le.mpr hx
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers (tau n)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun f hf => hle hf
  rw [fixedField_tau, IntermediateField.mem_bot] at hmem
  exact hmem

/-- **An element of `K(T)` fixed by the whole cyclotomic character lies in `ℚ(T)`.** -/
theorem exists_of_sigmaE_fixed {y : EE n} (hy : ∀ c, sigmaE n c y = y) :
    ∃ z : FF, algebraMap FF (EE n) z = y := by
  have hmem : y ∈ IntermediateField.fixedField (MonoidHom.range (sigmaE n)) := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro f ⟨c, rfl⟩
    exact hy c
  rw [fixedField_sigmaE, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### The Galois group of `M / ℚ(T)` -/

/-- `τ`, as an automorphism of `M` over `ℚ(T)`. -/
def tauF : MM n ≃ₐ[FF] MM n := AlgEquiv.restrictScalars FF (tau n)

@[simp] theorem tauF_apply (x : MM n) : tauF n x = tau n x := rfl

@[simp] theorem tau_hM (c : (ZMod n)ˣ) : tau n (hM n c) = hM n c := by
  rw [hM]; exact (tau n).commutes _

@[simp] theorem sigmaMe_zetaM (c : (ZMod n)ˣ) :
    sigmaMe n c (zetaM n) = zetaM n ^ cnat n c := by
  rw [zetaM_eq, sigmaMe_algebraMap, sigmaE_algebraMap, sigmaK_zeta, map_pow, map_pow]

/-- **The two families of automorphisms commute**: the exponent in the lift of `c` is the
cyclotomic character of `c`. -/
theorem commute_tauF_sigmaM (c : (ZMod n)ˣ) : tauF n * sigmaMe n c = sigmaMe n c * tauF n := by
  refine algEquiv_ext_M n (fun x => ?_) ?_
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaMe_algebraMap, tauF_apply, (tau n).commutes,
      tauF_apply, (tau n).commutes, sigmaMe_algebraMap]
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, sigmaMe_wr, tauF_apply, map_mul, map_pow, tau_wr,
      tau_hM, tauF_apply, tau_wr, map_mul, sigmaMe_zetaM, sigmaMe_wr, mul_pow]
    ring

/-- **`ℚ(T)` is the whole field of invariants of `M`.** -/
theorem fixedField_top : IntermediateField.fixedField (⊤ : Subgroup (MM n ≃ₐ[FF] MM n)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := exists_of_tau_fixed n (hx (tauF n) (Subgroup.mem_top _))
  have hy : ∀ c, sigmaE n c y = y := by
    intro c
    have hfix := hx (sigmaMe n c) (Subgroup.mem_top _)
    rw [sigmaMe_algebraMap] at hfix
    exact (algebraMap (EE n) (MM n)).injective hfix
  obtain ⟨z, rfl⟩ := exists_of_sigmaE_fixed n hy
  rw [IntermediateField.mem_bot, ← IsScalarTower.algebraMap_apply]
  exact ⟨z, rfl⟩

instance isGalois_FF_MM : IsGalois FF (MM n) :=
  IsGalois.of_fixedField_eq_bot FF (MM n) (fixedField_top n)

/-! ### The degree-`n` layer -/

/-- **The degree-`n` layer**: the fixed field of the lifted cyclotomic character. -/
def LL : IntermediateField FF (MM n) :=
  IntermediateField.fixedField (MonoidHom.range (sigmaM n))

instance (priority := high) smulFFFF : SMul FF FF := instSMulOfMul

instance (priority := high) isScalarTowerFFFFMM : IsScalarTower FF FF (MM n) :=
  ⟨fun a b c => by rw [smul_eq_mul, mul_smul]⟩

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) algFFLL : Algebra FF (LL n) := IntermediateField.algebra' (LL n)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) isScalarTowerFFLLMM : IsScalarTower FF (LL n) (MM n) :=
  IntermediateField.isScalarTower_mid' (LL n)

set_option synthInstance.maxHeartbeats 400000 in
instance (priority := high) finiteDimensionalFFLL : FiniteDimensional FF (LL n) :=
  IntermediateField.finiteDimensional_left (LL n)

theorem mem_LL_iff {x : MM n} : x ∈ LL n ↔ ∀ c, sigmaMe n c x = x := by
  rw [LL, IntermediateField.mem_fixedField_iff]
  refine ⟨fun hx c => hx (sigmaM n c) ⟨c, rfl⟩, fun hx f hf => ?_⟩
  obtain ⟨c, rfl⟩ := hf
  exact hx c

theorem finrank_LL_MM : Module.finrank (LL n) (MM n) = n.totient := by
  rw [LL, IntermediateField.finrank_fixedField_eq_card, card_range_sigmaM]

theorem finrank_FF_LL : Module.finrank FF (LL n) = n := by
  have h := Module.finrank_mul_finrank FF (LL n) (MM n)
  rw [finrank_LL_MM, finrank_FF_MM, Nat.mul_comm n.totient n] at h
  exact Nat.eq_of_mul_eq_mul_right (totient_pos n) h

theorem tauF_mem_LL {x : MM n} (hx : x ∈ LL n) : tauF n x ∈ LL n := by
  rw [mem_LL_iff] at hx ⊢
  intro c
  have h := congrArg (fun e : MM n ≃ₐ[FF] MM n => e x) (commute_tauF_sigmaM n c)
  simp only [AlgEquiv.mul_apply] at h
  rw [← h, hx]

/-- `τ`, viewed as an endomorphism of the degree-`n` layer. -/
def tauLHom : LL n →ₐ[FF] LL n where
  toFun x := ⟨tauF n (x : MM n), tauF_mem_LL n x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (by
    show tauF n ((algebraMap FF (LL n) r : LL n) : MM n)
      = ((algebraMap FF (LL n) r : LL n) : MM n)
    rw [IntermediateField.coe_algebraMap_apply]
    exact (tauF n).commutes r)

/-- `τ`, as an automorphism of the degree-`n` layer over `ℚ(T)`. -/
def tauL : LL n ≃ₐ[FF] LL n := AlgEquiv.ofBijective (tauLHom n) (tauLHom n).bijective

@[simp] theorem tauL_apply (x : LL n) : (tauL n x : MM n) = tauF n (x : MM n) := rfl

theorem fixedField_tauL : IntermediateField.fixedField (Subgroup.zpowers (tauL n)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hfix : tauF n (x : MM n) = (x : MM n) := by
    have h := hx (tauL n) (Subgroup.mem_zpowers _)
    exact congrArg (Subtype.val) h
  obtain ⟨y, hy⟩ := exists_of_tau_fixed n hfix
  have hyfix : ∀ c, sigmaE n c y = y := by
    intro c
    refine (algebraMap (EE n) (MM n)).injective ?_
    rw [← sigmaMe_algebraMap, hy]
    exact (mem_LL_iff n).mp x.2 c
  obtain ⟨z, hz⟩ := exists_of_sigmaE_fixed n hyfix
  refine IntermediateField.mem_bot.mpr ⟨z, Subtype.ext ?_⟩
  rw [IntermediateField.coe_algebraMap_apply, ← hy, ← hz, ← IsScalarTower.algebraMap_apply]

theorem fixedField_top_LL :
    IntermediateField.fixedField (⊤ : Subgroup (LL n ≃ₐ[FF] LL n)) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hmem : x ∈ IntermediateField.fixedField (Subgroup.zpowers (tauL n)) := by
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    exact fun f _ => hx f (Subgroup.mem_top f)
  rwa [fixedField_tauL] at hmem

instance isGalois_FF_LL : IsGalois FF (LL n) :=
  IsGalois.of_fixedField_eq_bot FF (LL n) (fixedField_top_LL n)

/-- **The layer is a degree-`n` Galois extension of `ℚ(T)`.** -/
theorem card_aut_LL : Nat.card (LL n ≃ₐ[FF] LL n) = n := by
  rw [IsGalois.card_aut_eq_finrank, finrank_FF_LL]

theorem zpowers_tauL_top : Subgroup.zpowers (tauL n) = ⊤ := by
  have h := IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (tauL n))
  rw [fixedField_tauL, IntermediateField.fixingSubgroup_bot] at h
  exact h.symm

/-- **The Galois group of the layer is cyclic**, generated by the Kummer automorphism. -/
instance isCyclic_aut_LL : IsCyclic (LL n ≃ₐ[FF] LL n) := by
  refine ⟨tauL n, fun x => ?_⟩
  have hx : x ∈ Subgroup.zpowers (tauL n) := by rw [zpowers_tauL_top n]; trivial
  exact Subgroup.mem_zpowers_iff.mp hx

/-! ### The constants of the Kummer extension -/

/-- An algebraic closure of `K`. -/
abbrev Kbar : Type := AlgebraicClosure (KK n)

/-- The geometric base field `K̄(T)`. -/
abbrev GG : Type := RatFunc (Kbar n)

instance charZeroEE : CharZero (EE n) :=
  charZero_of_injective_algebraMap (algebraMap (KK n) (EE n)).injective

/-- `g`, read over the algebraic closure of `K`. -/
def gbar : (Kbar n)[X] := (gpoly n).map (algebraMap (KK n) (Kbar n))

theorem gbar_eq : gbar n
    = ∏ v : (ZMod n)ˣ, (X - C (algebraMap (KK n) (Kbar n) (rt n v))) ^ anat n v := by
  rw [gbar, gpoly, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun v _ => by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

theorem gbar_ne_zero : gbar n ≠ 0 := by
  rw [gbar, Ne, Polynomial.map_eq_zero]
  exact gpoly_ne_zero n

/-- The simple root of `g` at `ζ` survives the passage to the algebraic closure. -/
theorem rootMultiplicity_gbar :
    (gbar n).rootMultiplicity (algebraMap (KK n) (Kbar n) (zeta n)) = 1 := by
  have hinj : Function.Injective (fun v => algebraMap (KK n) (Kbar n) (rt n v)) :=
    fun _ _ h => rt_injective n ((algebraMap (KK n) (Kbar n)).injective h)
  rw [gbar_eq, ← rt_one n]
  exact (rootMultiplicity_prod_pow (fun v => algebraMap (KK n) (Kbar n) (rt n v)) hinj
    (anat n) 1).trans (anat_one n)

theorem algebraMap_gE_geom :
    algebraMap (EE n) (GG n) (gE n) = algebraMap (Kbar n)[X] (GG n) (gbar n) :=
  Rigidity.RET.algebraMap_ratFunc_ratFunc (k := KK n) (K := Kbar n) (gpoly n)

/-- The Kummer polynomial stays irreducible over `K̄(T)`: the extension is geometric. -/
theorem kummer_irreducible_geom :
    Irreducible (((X : (EE n)[X]) ^ n - C (gE n)).map (algebraMap (EE n) (GG n))) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    algebraMap_gE_geom]
  exact irreducible_X_pow_sub_C_ratFunc (rootMultiplicity_gbar n) (by have := hn.out; omega)

theorem minpoly_wr : minpoly (EE n) (wr n) = (X : (EE n)[X]) ^ n - C (gE n) := by
  have hm : ((X : (EE n)[X]) ^ n - C (gE n)).Monic :=
    monic_X_pow_sub_C (gE n) (by have := hn.out; omega)
  rw [wr, AdjoinRoot.minpoly_root (kummer_ne_zero n), hm.leadingCoeff, inv_one, map_one, mul_one]

theorem adjoin_wr_top : IntermediateField.adjoin (EE n) ({wr n} : Set (MM n)) = ⊤ := by
  refine top_unique fun x _ => ?_
  have h : x ∈ Algebra.adjoin (EE n) ({wr n} : Set (MM n)) := by
    rw [wr, AdjoinRoot.adjoinRoot_eq_top]
    trivial
  exact IntermediateField.algebra_adjoin_le_adjoin (EE n) _ h

omit hn in
/-- Every polynomial over `K` splits in the geometric base field `K̄(T)`. -/
theorem splits_geom (q : (KK n)[X]) :
    ((q.map (algebraMap (KK n) (EE n))).map (algebraMap (EE n) (GG n))).Splits := by
  have hconst : ∀ a : KK n,
      algebraMap (KK n) (EE n) a = algebraMap (KK n)[X] (EE n) (C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply (KK n) (KK n)[X] (EE n)]
    rfl
  have hcomp : (algebraMap (EE n) (GG n)).comp (algebraMap (KK n) (EE n))
      = ((algebraMap (Kbar n)[X] (GG n)).comp (C : Kbar n →+* (Kbar n)[X])).comp
        (algebraMap (KK n) (Kbar n)) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, hconst, Rigidity.RET.algebraMap_ratFunc_ratFunc, Polynomial.map_C]
    rfl
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map]
  exact (IsAlgClosed.splits (q.map (algebraMap (KK n) (Kbar n)))).map _

/-- **The constants of `M` are exactly `K`**: the Kummer extension is geometric over `K`. -/
theorem algebraicClosure_KK_MM : algebraicClosure (KK n) (MM n) = ⊥ :=
  Rigidity.RET.algebraicClosure_eq_bot_of_isField_tensor (F := KK n) (K := EE n) (K' := GG n)
    (L := MM n) (splits_geom n) (Rigidity.RET.algebraicClosure_ratFunc (KK n))
    (Rigidity.RET.isField_tensor_of_primitive_irreducible (MM n) (wr n) (adjoin_wr_top n)
      (by rw [minpoly_wr]; exact kummer_irreducible_geom n))

theorem exists_const_of_isIntegral {y : MM n} (hy : IsIntegral (KK n) y) :
    ∃ a : KK n, algebraMap (KK n) (MM n) a = y := by
  have hmem : y ∈ algebraicClosure (KK n) (MM n) := mem_algebraicClosure_iff'.mpr hy
  rw [algebraicClosure_KK_MM, IntermediateField.mem_bot] at hmem
  exact hmem

/-! ### Regularity of the layer -/

set_option synthInstance.maxHeartbeats 400000 in
/-- The layer sits over `ℚ` through `ℚ(T)`; a shortcut for a slow instance search. -/
instance (priority := high) isScalarTowerQFFLL : IsScalarTower ℚ FF ↥(LL n) := inferInstance

/-- The two routes from `ℚ` into `M`, through the constants and through `ℚ(T)`, agree: `ℚ` is
initial. -/
theorem rationalMaps_eq :
    (algebraMap (KK n) (MM n)).comp (algebraMap ℚ (KK n))
      = (algebraMap FF (MM n)).comp (algebraMap ℚ FF) :=
  Subsingleton.elim _ _

set_option synthInstance.maxHeartbeats 400000 in
/-- The two routes from `ℚ` into `M`, through the layer and through the constants, agree. -/
theorem rationalMaps_LL :
    (algebraMap ↥(LL n) (MM n)).comp (algebraMap ℚ ↥(LL n))
      = (algebraMap (KK n) (MM n)).comp (algebraMap ℚ (KK n)) :=
  Subsingleton.elim _ _

theorem sigmaMe_algebraMap_KK (c : (ZMod n)ˣ) (a : KK n) :
    sigmaMe n c (algebraMap (KK n) (MM n) a) = algebraMap (KK n) (MM n) (sigmaK n c a) := by
  rw [IsScalarTower.algebraMap_apply (KK n) (EE n) (MM n),
    IsScalarTower.algebraMap_apply (KK n) (EE n) (MM n), sigmaMe_algebraMap, sigmaE_algebraMap]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The layer is regular**: it gains no constants over `ℚ`. -/
theorem regular_LL : algebraicClosure ℚ (LL n) = ⊥ := by
  refine bot_unique fun x hx => ?_
  have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.mp hx
  have hpm : (minpoly ℚ x).Monic := minpoly.monic hxint
  have hpx : aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
  -- the image of `x` in `M` is a constant, i.e. an element of `K`
  have hPx : aeval x ((minpoly ℚ x).map (algebraMap ℚ FF)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hpx
  have hPy : aeval (x : MM n) ((minpoly ℚ x).map (algebraMap ℚ FF)) = 0 := by
    have hval := Polynomial.aeval_algHom_apply (LL n).val x ((minpoly ℚ x).map (algebraMap ℚ FF))
    rw [hPx, map_zero] at hval
    exact hval
  have hyint : IsIntegral (KK n) (x : MM n) := by
    refine ⟨(minpoly ℚ x).map (algebraMap ℚ (KK n)), hpm.map _, ?_⟩
    rw [eval₂_map, rationalMaps_eq, ← eval₂_map]
    exact hPy
  obtain ⟨a, ha⟩ := exists_const_of_isIntegral n hyint
  -- being in the layer, the constant is fixed by the whole cyclotomic character
  have hfix : ∀ f : KK n ≃ₐ[ℚ] KK n, f a = a := by
    intro f
    obtain ⟨c, rfl⟩ := sigmaK_surjective n f
    refine (algebraMap (KK n) (MM n)).injective ?_
    rw [← sigmaMe_algebraMap_KK, ha]
    exact (mem_LL_iff n).mp x.2 c
  have hmem : a ∈ (⊥ : IntermediateField ℚ (KK n)) := (IsGalois.mem_bot_iff_fixed a).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hmem
  refine IntermediateField.mem_bot.mpr ⟨q, Subtype.ext ?_⟩
  have h1 : ((algebraMap ℚ ↥(LL n) q : ↥(LL n)) : MM n)
      = (algebraMap ↥(LL n) (MM n)).comp (algebraMap ℚ ↥(LL n)) q := rfl
  rw [h1, rationalMaps_LL, RingHom.comp_apply, hq, ha]

/-! ### The regular realization -/

/-- **The Galois group of the degree-`n` layer is a regular inverse Galois group over `ℚ`.** -/
theorem isRegularInverseGalois_aut : IsRegularInverseGalois (LL n ≃ₐ[FF] LL n) :=
  ⟨LL n, inferInstance, algFFLL n, inferInstance, isGalois_FF_LL n, inferInstance, inferInstance,
    regular_LL n, ⟨MulEquiv.refl _⟩⟩

end

end Rigidity.RET.Cyclic

namespace Rigidity.RET.IsRegularInverseGalois

/-- **Every finite cyclic group is a regular inverse Galois group over `ℚ`.** -/
theorem of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] :
    IsRegularInverseGalois G := by
  by_cases h1 : Nat.card G = 1
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact IsRegularInverseGalois.of_subsingleton
  · have hlt : 1 < Nat.card G := by
      have := Nat.card_pos (α := G)
      omega
    haveI : Fact (1 < Nat.card G) := ⟨hlt⟩
    exact (Rigidity.RET.Cyclic.isRegularInverseGalois_aut (Nat.card G)).of_mulEquiv
      (mulEquivOfCyclicCardEq (Rigidity.RET.Cyclic.card_aut_LL (Nat.card G)))

/-- **Every cyclic group of a given finite order is a regular inverse Galois group over `ℚ`.** -/
theorem of_isCyclic_card {G : Type*} [Group G] [IsCyclic G] {m : ℕ}
    (hm : 0 < m) (hG : Nat.card G = m) : IsRegularInverseGalois G :=
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; omega)
  of_isCyclic

end Rigidity.RET.IsRegularInverseGalois
