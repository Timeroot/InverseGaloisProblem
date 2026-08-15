/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The field of meromorphic germs at a point, and its order valuation

A germ at the punctured neighbourhood of a point `x : ℂ` is an equivalence class of complex
functions, two of them being identified when they agree near `x` (but not necessarily at `x`).
Those germs that are represented by a meromorphic function form a subring, and that subring is a
field: a meromorphic function is either identically zero near `x`, or nowhere zero on a punctured
neighbourhood, and in the second case its pointwise inverse is again meromorphic.

The order of vanishing `meromorphicOrderAt` descends to the germ field, where it becomes an
additive valuation with values in `WithTop ℤ`.  Its valuation ring `meroInt` consists of the germs
of functions with at worst a removable singularity, and its maximal ideal `meroMax` of the germs
that vanish.  Two consequences are recorded, and they are the reason this file exists: a germ
integral over any subring of the valuation ring has nonnegative order, and a germ lying in the
`e`-th power of the maximal ideal vanishes to order at least `e`.

## Main definitions

* `Rigidity.RET.Analytic.MeroGerm` — the field of meromorphic germs at a point.
* `Rigidity.RET.Analytic.MeroGerm.ord` — the order of vanishing of such a germ.
* `Rigidity.RET.Analytic.MeroGerm.meroVal` — the order, packaged as an `AddValuation`.
* `Rigidity.RET.Analytic.MeroGerm.meroInt`, `Rigidity.RET.Analytic.MeroGerm.meroMax` — the
  valuation ring and its maximal ideal.

## Main results

* `Rigidity.RET.Analytic.isField_meroGerm` — the meromorphic germs form a field.
* `Rigidity.RET.Analytic.MeroGerm.ord_nonneg_of_isIntegral_of_le` — a germ integral over a subring
  of the valuation ring has nonnegative order.
* `Rigidity.RET.Analytic.MeroGerm.le_ord_of_mem_pow` — a germ in the `e`-th power of the maximal
  ideal vanishes to order at least `e`.
* `Rigidity.RET.Analytic.MeroGerm.meroMax_isMaximal` — the vanishing germs are a maximal ideal of
  the valuation ring.
-/

open Filter Topology

noncomputable section

namespace Rigidity.RET.Analytic

/-- Germs of complex functions at the punctured neighbourhood of a point. -/
abbrev PunctGerm (x : ℂ) : Type := Filter.Germ (𝓝[≠] x) ℂ

/-- The order of vanishing of a germ at a punctured neighbourhood of a point. -/
def germOrd (x : ℂ) (g : PunctGerm x) : WithTop ℤ :=
  Filter.Germ.liftOn g (fun f => meromorphicOrderAt f x) fun _ _ h => meromorphicOrderAt_congr h

@[simp] theorem germOrd_coe (x : ℂ) (f : ℂ → ℂ) :
    germOrd x (f : PunctGerm x) = meromorphicOrderAt f x := rfl

/-- The subring of germs represented by a meromorphic function. -/
def meroGerms (x : ℂ) : Subring (PunctGerm x) where
  carrier := {g | ∃ f : ℂ → ℂ, MeromorphicAt f x ∧ (f : PunctGerm x) = g}
  zero_mem' := ⟨0, MeromorphicAt.const 0 x, rfl⟩
  one_mem' := ⟨1, MeromorphicAt.const 1 x, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

theorem mem_meroGerms {x : ℂ} {g : PunctGerm x} :
    g ∈ meroGerms x ↔ ∃ f : ℂ → ℂ, MeromorphicAt f x ∧ (f : PunctGerm x) = g := Iff.rfl

theorem coe_mem_meroGerms {x : ℂ} {f : ℂ → ℂ} (hf : MeromorphicAt f x) :
    (f : PunctGerm x) ∈ meroGerms x := ⟨f, hf, rfl⟩

/-- The field of meromorphic germs at a point. -/
def MeroGerm (x : ℂ) : Type := ↥(meroGerms x)

instance (x : ℂ) : CommRing (MeroGerm x) := inferInstanceAs (CommRing ↥(meroGerms x))

instance (x : ℂ) : Nontrivial (MeroGerm x) := inferInstanceAs (Nontrivial ↥(meroGerms x))

/-- **The meromorphic germs at a point form a field.**  A meromorphic function that is not
identically zero near the point is nowhere zero on a punctured neighbourhood, so its pointwise
inverse represents an inverse germ. -/
theorem isField_meroGerm (x : ℂ) : IsField (MeroGerm x) := by
  refine ⟨exists_pair_ne _, mul_comm, ?_⟩
  rintro ⟨g, f, hf, rfl⟩ hne
  have hne' : ¬ (f =ᶠ[𝓝[≠] x] 0) := by
    intro h
    exact hne (Subtype.ext (Filter.Germ.coe_eq.2 h))
  have hev : ∀ᶠ z in 𝓝[≠] x, f z ≠ 0 :=
    (hf.eventually_eq_zero_or_eventually_ne_zero).resolve_left hne'
  refine ⟨⟨(f⁻¹ : ℂ → ℂ), f⁻¹, hf.inv, rfl⟩, Subtype.ext ?_⟩
  show ((f : PunctGerm x) * (f⁻¹ : ℂ → ℂ) : PunctGerm x) = 1
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [hev] with z hz
  simp [mul_inv_cancel₀ hz]

noncomputable instance (x : ℂ) : Field (MeroGerm x) := (isField_meroGerm x).toField

namespace MeroGerm

variable {x : ℂ}

/-- The germ of a meromorphic function, as an element of the field of meromorphic germs. -/
def of {f : ℂ → ℂ} (hf : MeromorphicAt f x) : MeroGerm x := ⟨(f : PunctGerm x), f, hf, rfl⟩

/-- The order of vanishing of a meromorphic germ. -/
def ord (a : MeroGerm x) : WithTop ℤ := germOrd x a.1

@[simp] theorem ord_of {f : ℂ → ℂ} (hf : MeromorphicAt f x) :
    ord (of hf) = meromorphicOrderAt f x := rfl

@[simp] theorem of_val {f : ℂ → ℂ} (hf : MeromorphicAt f x) :
    (of hf).1 = (f : PunctGerm x) := rfl

theorem exists_of (a : MeroGerm x) : ∃ (f : ℂ → ℂ) (hf : MeromorphicAt f x), a = of hf := by
  obtain ⟨g, f, hf, hfg⟩ := a
  exact ⟨f, hf, Subtype.ext hfg.symm⟩

@[simp] theorem of_mul {f g : ℂ → ℂ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    of hf * of hg = of (hf.mul hg) := rfl

@[simp] theorem of_add {f g : ℂ → ℂ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    of hf + of hg = of (hf.add hg) := rfl

theorem of_pow {f : ℂ → ℂ} (hf : MeromorphicAt f x) (n : ℕ) : of hf ^ n = of (hf.pow n) := rfl

theorem of_eq_zero_iff {f : ℂ → ℂ} (hf : MeromorphicAt f x) :
    of hf = 0 ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  constructor
  · intro h
    have : (f : PunctGerm x) = ((0 : ℂ → ℂ) : PunctGerm x) := congrArg Subtype.val h
    exact Filter.Germ.coe_eq.1 this
  · intro h
    exact Subtype.ext (Filter.Germ.coe_eq.2 h)

theorem ord_mul (a b : MeroGerm x) : ord (a * b) = ord a + ord b := by
  obtain ⟨f, hf, rfl⟩ := exists_of a
  obtain ⟨g, hg, rfl⟩ := exists_of b
  rw [of_mul, ord_of, ord_of, ord_of, meromorphicOrderAt_mul hf hg]

theorem ord_add (a b : MeroGerm x) : min (ord a) (ord b) ≤ ord (a + b) := by
  obtain ⟨f, hf, rfl⟩ := exists_of a
  obtain ⟨g, hg, rfl⟩ := exists_of b
  rw [of_add, ord_of, ord_of, ord_of]
  exact meromorphicOrderAt_add hf hg

@[simp] theorem ord_eq_top_iff {a : MeroGerm x} : ord a = ⊤ ↔ a = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_of a
  rw [ord_of, meromorphicOrderAt_eq_top_iff, of_eq_zero_iff hf]

@[simp] theorem ord_zero : ord (0 : MeroGerm x) = ⊤ := ord_eq_top_iff.2 rfl

theorem ord_ne_top {a : MeroGerm x} (ha : a ≠ 0) : ord a ≠ ⊤ := fun h => ha (ord_eq_top_iff.1 h)

@[simp] theorem ord_one : ord (1 : MeroGerm x) = 0 := by
  have h : (1 : MeroGerm x) = of (MeromorphicAt.const (1 : ℂ) x) := rfl
  rw [h, ord_of]
  simpa using meromorphicOrderAt_const (E := ℂ) x 1

theorem ord_mul_inv {a : MeroGerm x} (ha : a ≠ 0) : ord a + ord a⁻¹ = 0 := by
  rw [← ord_mul, mul_inv_cancel₀ ha, ord_one]

theorem ord_inv (a : MeroGerm x) : ord a⁻¹ = -ord a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have h := ord_mul_inv ha
    have hne : ord a ≠ ⊤ := ord_ne_top ha
    lift ord a to ℤ using hne with n hn
    generalize hb : ord a⁻¹ = b at h ⊢
    match b with
    | ⊤ => simp at h
    | (m : ℤ) =>
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at h
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_inj]
      omega

theorem ord_neg (a : MeroGerm x) : ord (-a) = ord a := by
  have h1 : ord (-1 : MeroGerm x) = 0 := by
    have h2 : ord ((-1 : MeroGerm x) * (-1 : MeroGerm x)) = 0 := by
      rw [neg_mul_neg, one_mul, ord_one]
    rw [ord_mul] at h2
    have hne : ord (-1 : MeroGerm x) ≠ ⊤ := ord_ne_top (by simp)
    lift ord (-1 : MeroGerm x) to ℤ using hne with n hn
    rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at h2
    rw [← WithTop.coe_zero, WithTop.coe_inj]
    omega
  rw [show -a = (-1 : MeroGerm x) * a by ring, ord_mul, h1, zero_add]

theorem ord_pow (a : MeroGerm x) (n : ℕ) : ord (a ^ n) = n * ord a := by
  obtain ⟨f, hf, rfl⟩ := exists_of a
  rw [of_pow, ord_of, ord_of, meromorphicOrderAt_pow hf]

theorem ord_nonneg_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f x) :
    0 ≤ ord (of hf.meromorphicAt) := by
  rw [ord_of]
  exact hf.meromorphicOrderAt_nonneg

theorem of_congr {f g : ℂ → ℂ} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
    (h : ∀ᶠ z in 𝓝[≠] x, f z = g z) : of hf = of hg :=
  Subtype.ext (Filter.Germ.coe_eq.2 h)

/-- A germ analytic and nonzero at the point has order zero. -/
theorem ord_eq_zero_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f x) (h : f x ≠ 0) :
    ord (of hf.meromorphicAt) = 0 := by
  rw [ord_of, hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.2 (Or.inr h)]
  simp

/-- The order of a germ read off from an eventual factorization `(z - x) ^ n • g` with `g`
analytic and nonvanishing at the point. -/
theorem ord_eq_of_eventually_smul {f g : ℂ → ℂ} (hf : MeromorphicAt f x) {n : ℤ}
    (hg : AnalyticAt ℂ g x) (hg0 : g x ≠ 0) (h : ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z) :
    ord (of hf) = (n : WithTop ℤ) :=
  (meromorphicOrderAt_eq_int_iff hf).2 ⟨g, hg, hg0, h⟩

/-! ### The order as an additive valuation -/

/-- The order of vanishing at `x`, as an additive valuation on the field of meromorphic germs. -/
def meroVal (x : ℂ) : AddValuation (MeroGerm x) (WithTop ℤ) :=
  AddValuation.of ord ord_zero ord_one ord_add ord_mul

@[simp] theorem meroVal_apply (a : MeroGerm x) : meroVal x a = ord a := rfl

/-- The valuation ring of the order: the germs of functions with at worst a removable
singularity at the point. -/
def meroInt (x : ℂ) : Subring (MeroGerm x) := (AddValuation.toValuation (meroVal x)).integer

@[simp] theorem mem_meroInt {a : MeroGerm x} : a ∈ meroInt x ↔ 0 ≤ ord a := Iff.rfl

theorem ord_nonneg (a : meroInt x) : 0 ≤ ord (a : MeroGerm x) := a.2

theorem ord_nonneg_of_isIntegral {a : MeroGerm x} (ha : IsIntegral (meroInt x) a) : 0 ≤ ord a :=
  mem_meroInt.1 (Valuation.Integers.mem_of_integral (Valuation.integer.integers _) ha)

theorem isIntegral_of_subring_le {A : Subring (MeroGerm x)} (hA : A ≤ meroInt x)
    {a : MeroGerm x} (ha : IsIntegral A a) : IsIntegral (meroInt x) a := by
  obtain ⟨p, hp, hev⟩ := ha
  exact ⟨p.map (Subring.inclusion hA), hp.map _, by rwa [Polynomial.eval₂_map]⟩

/-- **An integral germ has no pole**: a germ integral over a subring of the valuation ring has
nonnegative order.  The valuation ring is integrally closed in the germ field, so integrality over
any smaller ring already forces the singularity to be removable. -/
theorem ord_nonneg_of_isIntegral_of_le {A : Subring (MeroGerm x)} (hA : A ≤ meroInt x)
    {a : MeroGerm x} (ha : IsIntegral A a) : 0 ≤ ord a :=
  ord_nonneg_of_isIntegral (isIntegral_of_subring_le hA ha)

/-- **An integral germ has no pole**, in the form the constructions use: a germ killed by a monic
polynomial whose coefficients are germs without poles has no pole either. -/
theorem ord_nonneg_of_eval₂_eq_zero {R : Type*} [CommRing R] (f : R →+* MeroGerm x)
    (hf : ∀ r, 0 ≤ ord (f r)) {a : MeroGerm x} {p : Polynomial R} (hp : p.Monic)
    (hpa : Polynomial.eval₂ f a p = 0) : 0 ≤ ord a := by
  refine ord_nonneg_of_isIntegral_of_le (A := f.range) ?_ ⟨p.map f.rangeRestrict, hp.map _, ?_⟩
  · rintro _ ⟨r, rfl⟩
    exact mem_meroInt.2 (hf r)
  · rw [Polynomial.eval₂_map]
    exact hpa

/-! ### The maximal ideal -/

private theorem add_pos_of_nonneg_of_pos {p q : WithTop ℤ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 < p + q :=
  lt_of_lt_of_le hq (le_add_of_nonneg_left hp)

private theorem one_le_of_pos {q : WithTop ℤ} (hq : 0 < q) : (1 : WithTop ℤ) ≤ q := by
  induction q using WithTop.recTopCoe with
  | top => exact le_top
  | coe m =>
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe] at hq
    rw [← WithTop.coe_one, WithTop.coe_le_coe]
    omega

/-- The maximal ideal of the valuation ring: the germs that vanish at the point. -/
def meroMax (x : ℂ) : Ideal (meroInt x) where
  carrier := {a | 0 < ord (a : MeroGerm x)}
  zero_mem' := by
    show (0 : WithTop ℤ) < ord ((0 : meroInt x) : MeroGerm x)
    rw [show ((0 : meroInt x) : MeroGerm x) = 0 from rfl, ord_zero]
    simp
  add_mem' := by
    intro a b ha hb
    have ha' : (0 : WithTop ℤ) < ord (a : MeroGerm x) := ha
    have hb' : (0 : WithTop ℤ) < ord (b : MeroGerm x) := hb
    show (0 : WithTop ℤ) < ord ((a + b : meroInt x) : MeroGerm x)
    rw [show ((a + b : meroInt x) : MeroGerm x) = (a : MeroGerm x) + (b : MeroGerm x) from rfl]
    exact lt_of_lt_of_le (lt_min ha' hb') (ord_add _ _)
  smul_mem' := by
    intro c a ha
    have hca : ((c • a : meroInt x) : MeroGerm x) = (c : MeroGerm x) * (a : MeroGerm x) := rfl
    show (0 : WithTop ℤ) < ord ((c • a : meroInt x) : MeroGerm x)
    rw [hca, ord_mul]
    exact add_pos_of_nonneg_of_pos (ord_nonneg c) ha

@[simp] theorem mem_meroMax {a : meroInt x} : a ∈ meroMax x ↔ 0 < ord (a : MeroGerm x) := Iff.rfl

/-- **A germ in the `e`-th power of the maximal ideal vanishes to order at least `e`.** -/
theorem le_ord_of_mem_pow {e : ℕ} {a : meroInt x} (ha : a ∈ (meroMax x) ^ e) :
    (e : WithTop ℤ) ≤ ord (a : MeroGerm x) := by
  induction e generalizing a with
  | zero => simpa using ord_nonneg a
  | succ n ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro m hm b hb
      have h1 : (n : WithTop ℤ) ≤ ord (m : MeroGerm x) := ih hm
      have h2 : (1 : WithTop ℤ) ≤ ord (b : MeroGerm x) := one_le_of_pos hb
      have hmb : ((m * b : meroInt x) : MeroGerm x) = (m : MeroGerm x) * (b : MeroGerm x) := rfl
      rw [hmb, ord_mul]
      calc ((n + 1 : ℕ) : WithTop ℤ) = (n : WithTop ℤ) + 1 := Nat.cast_succ n
        _ ≤ ord (m : MeroGerm x) + ord (b : MeroGerm x) := add_le_add h1 h2
    · intro u v hu hv
      have huv : ((u + v : meroInt x) : MeroGerm x) = (u : MeroGerm x) + (v : MeroGerm x) := rfl
      rw [huv]
      exact le_trans (le_min hu hv) (ord_add _ _)

/-- A germ without a pole and not vanishing at the point is a unit of the valuation ring. -/
theorem isUnit_of_ord_eq_zero {a : meroInt x} (ha : ord (a : MeroGerm x) = 0) : IsUnit a := by
  have ha0 : (a : MeroGerm x) ≠ 0 := by
    intro h
    rw [h, ord_zero] at ha
    simp at ha
  have hinv : (a : MeroGerm x)⁻¹ ∈ meroInt x := by
    rw [mem_meroInt, ord_inv, ha]
    simp
  have hmul : a * (⟨(a : MeroGerm x)⁻¹, hinv⟩ : meroInt x) = 1 :=
    Subtype.ext (mul_inv_cancel₀ ha0)
  exact IsUnit.of_mul_eq_one _ hmul

/-- The vanishing germs are the non-units of the valuation ring, so they form a maximal ideal. -/
instance meroMax_isMaximal : (meroMax x).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · show ¬ (0 : WithTop ℤ) < ord ((1 : meroInt x) : MeroGerm x)
    rw [show ((1 : meroInt x) : MeroGerm x) = 1 from rfl, ord_one]
    simp
  · intro J b hJ hb hbJ
    have h0 : ord (b : MeroGerm x) = 0 :=
      le_antisymm (not_lt.1 fun h => hb (mem_meroMax.2 h)) (ord_nonneg b)
    obtain ⟨u, hu⟩ := isUnit_of_ord_eq_zero h0
    have h1 : (1 : meroInt x) = b * ↑u⁻¹ := by rw [← hu]; simp
    rw [h1]
    exact Ideal.mul_mem_right _ _ hbJ

/-! ### Constants -/

/-- A complex number, as the germ of a constant function. -/
def constHom (x : ℂ) : ℂ →+* MeroGerm x where
  toFun c := of (MeromorphicAt.const c x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem constHom_apply (c : ℂ) :
    constHom x c = of (MeromorphicAt.const c x) := rfl

instance (x : ℂ) : Algebra ℂ (MeroGerm x) := (constHom x).toAlgebra

theorem algebraMap_eq (x : ℂ) : algebraMap ℂ (MeroGerm x) = constHom x := rfl

theorem ord_constHom {c : ℂ} (hc : c ≠ 0) : ord (constHom x c) = 0 := by
  classical
  rw [constHom_apply, ord_of, meromorphicOrderAt_const]
  simp [hc]

end MeroGerm

end Rigidity.RET.Analytic

end
