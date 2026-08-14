/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.CenterlessExtension
import InverseGalois.Rigidity.RET.Descent.TameRamification
import InverseGalois.Rigidity.RET.Descent.WildInertia
import InverseGalois.Rigidity.RET.Descent.ConstField

/-!
# The arithmetic AKLB model over `ℚ[X]`, and Fried's branch-cycle formula on it

For a finite Galois extension `Ω` of `ℚ(T) = RatFunc ℚ` this module builds the arithmetic integral
model `ℚ[X] ⊆ B` with `B := integralClosure (Polynomial ℚ) Ω`, on which the *arithmetic* Galois
group `E = Gal(Ω/ℚ(T))` acts, and proves on it the two ramification facts the branch-cycle descent
needs:

* the inertia group at a nonzero maximal ideal of `B` is **cyclic**;
* **Fried's branch-cycle formula**: if `σ ∈ E` stabilizes the prime `Q` and `g` is an inertia
  element at `Q` killed by `M`, then `σ g σ⁻¹ = g ^ χ(σ)` where `χ(σ)` is the power to which `σ`
  raises a primitive `M`-th root of unity of `Ω` (`IsPrimitiveRoot.autToPow`).

Both are unconditional here.  The base `ℚ[X]` is a `ℚ`-algebra, so the order of an inertia group is
invertible in `B`; averaging over an inertia orbit then produces invariant residue representatives
(`Rigidity.RET.residueFixed_of_algebraRat`), which is exactly the input making the tame character
injective.  Residue characteristic zero also kills wild inertia
(`Rigidity.RET.inertia_pow_sq_eq_bot`), so all inertia is tame.

The exponent is stated through `IsPrimitiveRoot.autToPow` — the cyclotomic character of `E` — which
is the form the tame inertia data of the arithmetic tower consumes.

## Main results

* `ArithAKLB.Aring Ω` — the arithmetic integral model `B`, with its instance stack.
* `ArithAKLB.isCyclic_arithInertia` — inertia at a nonzero maximal ideal is cyclic.
* `ArithAKLB.rootOfUnityMem` — a root of unity of `Ω` lies in the integral model, and stays a
  primitive root there.
* `ArithAKLB.conj_eq_pow_autToPow` — Fried's branch-cycle formula with the cyclotomic exponent.
-/

open Polynomial
open scoped Pointwise

noncomputable section

namespace ArithAKLB


attribute [local instance] Ideal.Quotient.field

variable
  (Ω : Type) [Field Ω] [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω]
  [IsGalois (RatFunc ℚ) Ω]
  [Algebra (Polynomial ℚ) Ω] [IsScalarTower (Polynomial ℚ) (RatFunc ℚ) Ω]

/-! ## The integral model `A = ℚ[X] ⊆ B = integralClosure A Ω` with the arithmetic Galois action. -/

/-- Integral closure of `ℚ[X]` in `Ω`; the arithmetic model `B`. -/
abbrev Aring : Type := integralClosure (Polynomial ℚ) Ω

noncomputable local instance instMSA :
    MulSemiringAction (Ω ≃ₐ[RatFunc ℚ] Ω) (Aring Ω) :=
  IsIntegralClosure.MulSemiringAction (Polynomial ℚ) (RatFunc ℚ) Ω (Aring Ω)

local instance instIsFrac : IsFractionRing (Aring Ω) Ω :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) (RatFunc ℚ) Ω (Aring Ω)

local instance instIGG : IsGaloisGroup (Ω ≃ₐ[RatFunc ℚ] Ω) (Polynomial ℚ) (Aring Ω) :=
  IsGaloisGroup.of_isFractionRing (Ω ≃ₐ[RatFunc ℚ] Ω) (Polynomial ℚ) (Aring Ω) (RatFunc ℚ) Ω

local instance instFinite : Module.Finite (Polynomial ℚ) (Aring Ω) :=
  IsIntegralClosure.finite (Polynomial ℚ) (RatFunc ℚ) Ω (Aring Ω)

local instance instIntegral : Algebra.IsIntegral (Polynomial ℚ) (Aring Ω) :=
  IsIntegralClosure.isIntegral_algebra (Polynomial ℚ) Ω

local instance instFaithfulBase : FaithfulSMul (Polynomial ℚ) (Aring Ω) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have hAL : Function.Injective (algebraMap (Polynomial ℚ) Ω) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) (RatFunc ℚ) Ω]
    exact (algebraMap (RatFunc ℚ) Ω).injective.comp
      (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))
  intro x y hxy
  apply hAL
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) (Aring Ω) Ω,
    IsScalarTower.algebraMap_apply (Polynomial ℚ) (Aring Ω) Ω, hxy]

local instance instDedekind : IsDedekindDomain (Aring Ω) :=
  integralClosure.isDedekindDomain (Polynomial ℚ) (RatFunc ℚ) Ω

local instance instFiniteGal : Finite (Ω ≃ₐ[RatFunc ℚ] Ω) := inferInstance

local instance instFaithfulGal : FaithfulSMul (Ω ≃ₐ[RatFunc ℚ] Ω) (Aring Ω) :=
  IsGaloisGroup.faithful (A := Polynomial ℚ)

/-- The arithmetic model is a `ℚ`-algebra: `ℚ ⊆ ℚ[X] ⊆ B`.  This is what makes the order of an
inertia group invertible in `B`, hence all ramification tame. -/
local instance instAlgRat : Algebra ℚ (Aring Ω) :=
  ((algebraMap (Polynomial ℚ) (Aring Ω)).comp (algebraMap ℚ (Polynomial ℚ))).toAlgebra

/-! ## Cyclicity of the arithmetic inertia groups. -/

/-- `Q.inertia E` as a genuine `Subgroup` of the arithmetic Galois group `E = Ω ≃ₐ[ℚ(T)] Ω`. -/
abbrev arithInertia (Q : Ideal (Aring Ω)) : Subgroup (Ω ≃ₐ[RatFunc ℚ] Ω) :=
  Q.inertia (Ω ≃ₐ[RatFunc ℚ] Ω)

/-- **The inertia group at a nonzero maximal ideal of the arithmetic model is cyclic.**

The residue fields are of characteristic zero, so wild inertia vanishes and the tame character
embeds the inertia group into the multiplicative group of the residue field. -/
theorem isCyclic_arithInertia (Q : Ideal (Aring Ω)) [Q.IsMaximal] (hQ0 : Q ≠ ⊥) :
    IsCyclic (arithInertia Ω Q) :=
  Rigidity.RET.isCyclic_inertia_of_algebraRat Q hQ0

/-! ## Roots of unity live in the integral model. -/

/-- A root of unity of `Ω` is integral over `ℚ[X]`, hence lies in the arithmetic model. -/
def rootOfUnityMem {M : ℕ} (hM : M ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) : Aring Ω :=
  ⟨ζ, IsIntegral.of_pow (Nat.pos_of_ne_zero hM) (by rw [hζ.pow_eq_one]; exact isIntegral_one)⟩

omit [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω]
  [IsScalarTower (Polynomial ℚ) (RatFunc ℚ) Ω] in
@[simp] theorem coe_rootOfUnityMem {M : ℕ} (hM : M ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) :
    ((rootOfUnityMem Ω hM hζ : Aring Ω) : Ω) = ζ := rfl

omit [IsGalois (RatFunc ℚ) Ω] in
/-- A primitive root of unity of `Ω` is a primitive root of unity of the integral model. -/
theorem isPrimitiveRoot_rootOfUnityMem {M : ℕ} (hM : M ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) :
    IsPrimitiveRoot (rootOfUnityMem Ω hM hζ) M :=
  IsPrimitiveRoot.of_map_of_injective (f := algebraMap (Aring Ω) Ω) hζ
    (IsFractionRing.injective (Aring Ω) Ω)

omit [FiniteDimensional (RatFunc ℚ) Ω] in
/-- The Galois action on the integral model is the restriction of the action on `Ω`. -/
theorem coe_smul_arith (σ : Ω ≃ₐ[RatFunc ℚ] Ω) (x : Aring Ω) : ((σ • x : Aring Ω) : Ω) = σ x :=
  algebraMap_galRestrict_apply (Polynomial ℚ) σ x

/-! ## Fried's branch-cycle formula on the arithmetic model. -/

/-- **Fried's branch-cycle formula on the arithmetic model.**

Let `Q` be a nonzero maximal ideal of `B`, `σ` an arithmetic automorphism stabilizing `Q`, and `g`
an inertia element at `Q` with `g ^ M = 1`.  If `ζ ∈ Ω` is a primitive `M`-th root of unity raised
by `σ` to the power `c`, then

  `σ g σ⁻¹ = g ^ c`.

The tame character sends `g` to an `M`-th root of unity of the residue field at `Q`; the reduction
of `ζ` is still primitive there, so that root of unity is a power of `ζ`, on which `σ` acts by
`c`.  Injectivity of the tame character then transports the identity back to `E`. -/
theorem conj_eq_pow_of_apply_root (Q : Ideal (Aring Ω)) [Q.IsMaximal] (hQ0 : Q ≠ ⊥)
    {σ : Ω ≃ₐ[RatFunc ℚ] Ω} (hσ : σ • Q = Q) {M : ℕ} [NeZero M] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ M) {c : ℕ} (hc : σ ζ = ζ ^ c) (g : arithInertia Ω Q)
    (hgM : g ^ M = 1) :
    σ * (g : Ω ≃ₐ[RatFunc ℚ] Ω) * σ⁻¹ = (g : Ω ≃ₐ[RatFunc ℚ] Ω) ^ c := by
  set ζB := rootOfUnityMem Ω (NeZero.ne M) hζ with hζB
  have hsmul : σ • ζB = ζB ^ c := by
    apply Subtype.ext
    rw [coe_smul_arith, SubmonoidClass.coe_pow, coe_rootOfUnityMem]
    exact hc
  exact Rigidity.RET.conj_eq_pow_of_smul_root Q hQ0 hσ (isPrimitiveRoot_rootOfUnityMem Ω _ hζ)
    hsmul g hgM

/-- **Fried's branch-cycle formula with the cyclotomic exponent.**  The exponent of the previous
theorem is the cyclotomic character `IsPrimitiveRoot.autToPow` of the arithmetic Galois group. -/
theorem conj_eq_pow_autToPow (Q : Ideal (Aring Ω)) [Q.IsMaximal] (hQ0 : Q ≠ ⊥)
    {σ : Ω ≃ₐ[RatFunc ℚ] Ω} (hσ : σ • Q = Q) {M : ℕ} [NeZero M] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ M) (g : arithInertia Ω Q) (hgM : g ^ M = 1) :
    σ * (g : Ω ≃ₐ[RatFunc ℚ] Ω) * σ⁻¹
      = (g : Ω ≃ₐ[RatFunc ℚ] Ω) ^ ((hζ.autToPow (RatFunc ℚ) σ : ZMod M).val) :=
  conj_eq_pow_of_apply_root Ω Q hQ0 hσ hζ (hζ.autToPow_spec (RatFunc ℚ) σ).symm g hgM

/-! ## Fried's formula in conjugacy form, for a normal subgroup acting transitively on the fibre.

The branch-cycle descent does not see the individual prime `Q`: it sees the geometric group
`N ⊴ E` and the inertia generators only up to `N`-conjugacy.  The two extra inputs converting the
formula above into that shape are that `N` acts transitively on the primes above the branch place
(so any `e : E` agrees with an element of the decomposition group up to `N`) and that `N` fixes the
roots of unity (so the cyclotomic exponent is unchanged by that correction). -/

/-- The group-theoretic step: an identity `(n⁻¹ e) g (n⁻¹ e)⁻¹ = g ^ c` in `E` becomes an
`N`-conjugacy between `conjN N e g` and `g ^ c`. -/
theorem isConj_conjN_of_conj_eq_pow {E : Type*} [Group E] (N : Subgroup E) [N.Normal] (e : E)
    (n : N) (g : N) {c : ℕ}
    (h : ((n : E)⁻¹ * e) * (g : E) * ((n : E)⁻¹ * e)⁻¹ = (g : E) ^ c) :
    IsConj (Rigidity.RET.conjN N e g) (g ^ c) := by
  rw [isConj_iff]
  refine ⟨n⁻¹, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, inv_inv,
    Rigidity.RET.conjN_coe]
  rw [← h]
  group

/-- **Fried's branch-cycle formula in conjugacy form.**

Let `N ⊴ E` be a normal subgroup of the arithmetic Galois group which fixes the primitive `M`-th
root of unity `ζ` and acts transitively on the `E`-orbit of the prime `Q`.  Then for every `e : E`
and every inertia element `g ∈ N` at `Q` killed by `M`,

  `e g e⁻¹ ∼_N g ^ χ(e)`,

with `χ(e)` the power to which `e` raises `ζ`.

Choose `n ∈ N` with `σ := n⁻¹ e` stabilizing `Q`.  Then `σ` acts on `ζ` exactly as `e` does, so the
branch-cycle formula applies to `σ` and gives `σ g σ⁻¹ = g ^ χ(e)`; conjugating back by `n` moves
the identity into `N`-conjugacy. -/
theorem isConj_conjN_pow_autToPow (N : Subgroup (Ω ≃ₐ[RatFunc ℚ] Ω)) [N.Normal]
    (Q : Ideal (Aring Ω)) [Q.IsMaximal] (hQ0 : Q ≠ ⊥) {M : ℕ} [NeZero M] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ M) (hNfix : ∀ n : N, (n : Ω ≃ₐ[RatFunc ℚ] Ω) ζ = ζ)
    (htrans : ∀ e : Ω ≃ₐ[RatFunc ℚ] Ω, ∃ n : N, ((n : Ω ≃ₐ[RatFunc ℚ] Ω)⁻¹ * e) • Q = Q)
    (g : N) (hg : (g : Ω ≃ₐ[RatFunc ℚ] Ω) ∈ arithInertia Ω Q) (hgM : g ^ M = 1)
    (e : Ω ≃ₐ[RatFunc ℚ] Ω) :
    IsConj (Rigidity.RET.conjN N e g) (g ^ ((hζ.autToPow (RatFunc ℚ) e : ZMod M).val)) := by
  classical
  set c := ((hζ.autToPow (RatFunc ℚ) e : ZMod M).val) with hcdef
  obtain ⟨n, hn⟩ := htrans e
  set σ : Ω ≃ₐ[RatFunc ℚ] Ω := (n : Ω ≃ₐ[RatFunc ℚ] Ω)⁻¹ * e with hσdef
  have hζinv : (n : Ω ≃ₐ[RatFunc ℚ] Ω)⁻¹ ζ = ζ := by
    have := hNfix n⁻¹
    simpa using this
  have hcζ : σ ζ = ζ ^ c := by
    have he : e ζ = ζ ^ c := (hζ.autToPow_spec (RatFunc ℚ) e).symm
    have : σ ζ = (n : Ω ≃ₐ[RatFunc ℚ] Ω)⁻¹ (e ζ) := rfl
    rw [this, he, map_pow, hζinv]
  have hgI : ((⟨(g : Ω ≃ₐ[RatFunc ℚ] Ω), hg⟩ : arithInertia Ω Q)) ^ M = 1 := by
    apply Subtype.ext
    have : ((g : Ω ≃ₐ[RatFunc ℚ] Ω)) ^ M = 1 := by
      have := congrArg (fun x : N => (x : Ω ≃ₐ[RatFunc ℚ] Ω)) hgM
      simpa using this
    simpa using this
  have hmain := conj_eq_pow_of_apply_root Ω Q hQ0 hn hζ hcζ ⟨_, hg⟩ hgI
  exact isConj_conjN_of_conj_eq_pow N e n g hmain

/-! ## Places of the integral model above a place of the line

A prime of `B` above a place of the line inherits both of the properties the branch-cycle data needs
— being nonzero and being maximal — from the place below it: `B` is a torsion-free `ℚ[X]`-module and
is integral over `ℚ[X]`. -/

set_option synthInstance.maxHeartbeats 200000 in
omit [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω] in
/-- A prime of the integral model above a nonzero place of the line is nonzero. -/
theorem ne_bot_of_liesOver {P : Ideal (Polynomial ℚ)} (hP : P ≠ ⊥) (Q : Ideal (Aring Ω))
    [Q.LiesOver P] : Q ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot hP Q

omit [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω]
  [IsScalarTower (Polynomial ℚ) (RatFunc ℚ) Ω] in
/-- A prime of the integral model above a maximal place of the line is maximal: the model is
integral over `ℚ[X]`, and integral extensions have no room between a prime and a maximal one. -/
theorem isMaximal_of_liesOver {P : Ideal (Polynomial ℚ)} (hP : P.IsMaximal)
    (Q : Ideal (Aring Ω)) [Q.IsPrime] [Q.LiesOver P] : Q.IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q
    (by rw [show Q.comap (algebraMap (Polynomial ℚ) (Aring Ω)) = P from
        (Ideal.over_def Q P).symm]; exact hP)

/-! ## The decomposition group at a rational place acts on the constants through the whole group

The transitivity hypothesis `htrans` of `isConj_conjN_pow_autToPow` is not an extra assumption at a
**`ℚ`-rational** place: it is a theorem.  Over a place `P` of `ℚ[X]` with residue field `ℚ` the
decomposition group of a place `Q` of the integral model above `P` surjects onto the Galois group of
the residue extension (`Ideal.Quotient.stabilizerHom_surjective`), and the residue extension already
sees all the constants — a constant is determined by its residue at `Q`, since a nonzero constant is
a unit of the integral model.  So every arithmetic automorphism agrees on the constants with one
stabilizing `Q` (`exists_stabilizer_eqOn_const`), which is exactly transitivity of the geometric
group on the places above `P`. -/

section Decomposition

variable [CharZero Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω]

/-- `ℚ ⊆ ℚ[X] ⊆ Ω` is a tower: both composites are ring homs `ℚ → Ω` into a division ring. -/
local instance instTowerRatPoly : IsScalarTower ℚ (Polynomial ℚ) Ω :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- The arithmetic Galois group acts on the integral model over the base `ℚ[X]`. -/
local instance instInvariant :
    Algebra.IsInvariant (Polynomial ℚ) (Aring Ω) (Ω ≃ₐ[RatFunc ℚ] Ω) :=
  Algebra.isInvariant_of_isGalois (Polynomial ℚ) (RatFunc ℚ) Ω (Aring Ω)

/-- A constant of `Ω` is integral over `ℚ[X]`, hence an element of the integral model. -/
def constMem {x : Ω} (hx : IsIntegral ℚ x) : Aring Ω :=
  ⟨x, hx.tower_top⟩

omit [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω]
  [IsScalarTower (Polynomial ℚ) (RatFunc ℚ) Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω] in
@[simp] theorem coe_constMem {x : Ω} (hx : IsIntegral ℚ x) :
    ((constMem Ω hx : Aring Ω) : Ω) = x := rfl

omit [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω]
  [IsScalarTower (Polynomial ℚ) (RatFunc ℚ) Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω] in
/-- A nonzero constant is a unit of the integral model, so it lies in no proper ideal: the inverse
of a constant is again a constant, hence again integral over `ℚ[X]`. -/
theorem const_notMem_of_ne_zero {x : Ω} (hx : IsIntegral ℚ x) (hx0 : x ≠ 0)
    (Q : Ideal (Aring Ω)) (hQ : Q ≠ ⊤) : constMem Ω hx ∉ Q := by
  intro hmem
  have hxinv : IsIntegral ℚ x⁻¹ := by
    have hmemK : x ∈ algebraicClosure ℚ Ω := mem_algebraicClosure_iff'.2 hx
    exact mem_algebraicClosure_iff'.1 ((algebraicClosure ℚ Ω).inv_mem hmemK)
  have hone : constMem Ω hx * constMem Ω hxinv = 1 := by
    apply Subtype.ext
    push_cast
    simp [mul_inv_cancel₀ hx0]
  exact hQ (Ideal.eq_top_of_isUnit_mem Q hmem ⟨⟨_, _, hone, by rw [mul_comm]; exact hone⟩, rfl⟩)

set_option maxHeartbeats 400000 in
omit [IsGalois (RatFunc ℚ) Ω] [IsScalarTower ℚ (RatFunc ℚ) Ω] in
/-- A polynomial relation over `ℚ` satisfied by an element of the integral model in `Ω` already
holds in the integral model (which embeds in `Ω`). -/
theorem aeval_arith_eq_zero {b : Aring Ω} {p : ℚ[X]} (hb : (Polynomial.aeval (b : Ω)) p = 0) :
    (Polynomial.aeval b) p = 0 := by
  have hcomp : ((algebraMap (Aring Ω) Ω).comp (algebraMap ℚ (Aring Ω)))
      = algebraMap ℚ Ω := RingHom.ext_rat _ _
  have h := Polynomial.hom_eval₂ p (algebraMap ℚ (Aring Ω)) (algebraMap (Aring Ω) Ω) b
  rw [hcomp] at h
  have h0 : (algebraMap (Aring Ω) Ω) ((Polynomial.aeval b) p) = 0 := by
    rw [Polynomial.aeval_def, h]
    rw [Polynomial.aeval_def] at hb
    exact hb
  exact (map_eq_zero_iff _ (IsFractionRing.injective (Aring Ω) Ω)).1 h0

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in
omit [IsScalarTower ℚ (RatFunc ℚ) Ω] in
/-- **The decomposition group at a rational place realizes every conjugate of a constant.**

Let `Q` be a place of the integral model above a place `P` of `ℚ[X]` with residue field `ℚ`, and let
`α` be a constant.  For any arithmetic automorphism `e` there is one stabilizing `Q` and agreeing
with `e` at `α`.

The residues of `α` and `e α` have the same minimal polynomial over the residue field `ℚ[X]/P` —
namely the reduction of `minpoly ℚ α`, which stays irreducible because the residue field is `ℚ`
itself.  The residue extension is normal, so a residue automorphism carries one to the other, and it
lifts to the decomposition group of `Q`.  Two constants with the same residue are equal, since their
difference is a constant lying in `Q` and a nonzero constant is a unit. -/
theorem exists_stabilizer_apply_eq (P : Ideal (Polynomial ℚ)) [P.IsMaximal]
    (Q : Ideal (Aring Ω)) [Q.IsMaximal] [Q.LiesOver P]
    (hP : Function.Surjective (algebraMap ℚ (Polynomial ℚ ⧸ P)))
    {α : Ω} (hα : IsIntegral ℚ α) (e : Ω ≃ₐ[RatFunc ℚ] Ω) :
    ∃ d : Ω ≃ₐ[RatFunc ℚ] Ω, d • Q = Q ∧ d α = e α := by
  classical
  haveI : Normal (Polynomial ℚ ⧸ P) (Aring Ω ⧸ Q) :=
    Ideal.Quotient.normal (A := Polynomial ℚ) (Ω ≃ₐ[RatFunc ℚ] Ω) P Q
  set a : Aring Ω := constMem Ω hα with ha
  have hea : IsIntegral ℚ (e α) := hα.map (e.restrictScalars ℚ).toAlgHom
  -- the minimal polynomial of the constant `α`, and its reduction to the residue field of `P`
  set p : ℚ[X] := minpoly ℚ α with hp
  have hpm : p.Monic := minpoly.monic hα
  have hpirr : Irreducible p := minpoly.irreducible hα
  set φ : ℚ →+* (Polynomial ℚ ⧸ P) := algebraMap ℚ (Polynomial ℚ ⧸ P) with hφ
  set ψ : ℚ ≃+* (Polynomial ℚ ⧸ P) := RingEquiv.ofBijective φ ⟨φ.injective, hP⟩ with hψ
  set pF : Polynomial (Polynomial ℚ ⧸ P) := p.map φ with hpF
  have hpFm : pF.Monic := hpm.map φ
  have hpFirr : Irreducible pF := by
    have hmap : pF = Polynomial.mapEquiv ψ p := rfl
    rw [hmap]
    exact hpirr.map (Polynomial.mapEquiv ψ)
  -- reduction of a `ℚ`-polynomial relation modulo `Q`
  have hres : ∀ b : Aring Ω, (Polynomial.aeval (b : Ω)) p = 0 →
      (Polynomial.aeval (Ideal.Quotient.mk Q b)) pF = 0 := by
    intro b hb
    have hb' : (Polynomial.aeval b) p = 0 := aeval_arith_eq_zero Ω hb
    have hcomp : ((algebraMap (Polynomial ℚ ⧸ P) (Aring Ω ⧸ Q)).comp φ)
        = (Ideal.Quotient.mk Q : Aring Ω →+* Aring Ω ⧸ Q).comp
            (algebraMap ℚ (Aring Ω)) := RingHom.ext_rat _ _
    have hhom := Polynomial.hom_eval₂ p (algebraMap ℚ (Aring Ω))
      (Ideal.Quotient.mk Q : Aring Ω →+* Aring Ω ⧸ Q) b
    rw [Polynomial.aeval_def, hpF, Polynomial.eval₂_map, hcomp, ← hhom, ← Polynomial.aeval_def,
      hb', map_zero]
  have hmin_a : minpoly (Polynomial ℚ ⧸ P) (Ideal.Quotient.mk Q a) = pF :=
    (minpoly.eq_of_irreducible_of_monic hpFirr (hres a (minpoly.aeval ℚ α)) hpFm).symm
  have hmin_ea : minpoly (Polynomial ℚ ⧸ P) (Ideal.Quotient.mk Q (e • a)) = pF := by
    refine (minpoly.eq_of_irreducible_of_monic hpFirr (hres (e • a) ?_) hpFm).symm
    have h : (Polynomial.aeval (e α)) p = e ((Polynomial.aeval α) p) :=
      Polynomial.aeval_algHom_apply (e.restrictScalars ℚ).toAlgHom α p
    rw [coe_smul_arith, ha, coe_constMem, h, hp, minpoly.aeval, map_zero]
  -- both residues have the same minimal polynomial, hence are conjugate in the residue field
  obtain ⟨σ, hσ⟩ : (Ideal.Quotient.mk Q (e • a)) ∈
      MulAction.orbit ((Aring Ω ⧸ Q) ≃ₐ[Polynomial ℚ ⧸ P] (Aring Ω ⧸ Q))
        (Ideal.Quotient.mk Q a) :=
    (Normal.minpoly_eq_iff_mem_orbit (Aring Ω ⧸ Q)).1 (by rw [hmin_ea, hmin_a])
  -- lift the residue automorphism to the decomposition group
  obtain ⟨d₀, hd₀⟩ := Ideal.Quotient.stabilizerHom_surjective (Ω ≃ₐ[RatFunc ℚ] Ω) P Q σ
  refine ⟨(d₀ : Ω ≃ₐ[RatFunc ℚ] Ω), d₀.2, ?_⟩
  have hd : Ideal.Quotient.mk Q ((d₀ : Ω ≃ₐ[RatFunc ℚ] Ω) • a)
      = Ideal.Quotient.mk Q (e • a) := by
    have h1 := Ideal.Quotient.stabilizerHom_apply Q P (Ω ≃ₐ[RatFunc ℚ] Ω) d₀ a
    rw [hd₀] at h1
    calc Ideal.Quotient.mk Q ((d₀ : Ω ≃ₐ[RatFunc ℚ] Ω) • a)
        = Ideal.Quotient.mk Q ((d₀ : MulAction.stabilizer (Ω ≃ₐ[RatFunc ℚ] Ω) Q) • a) := rfl
      _ = σ (Ideal.Quotient.mk Q a) := h1.symm
      _ = Ideal.Quotient.mk Q (e • a) := hσ
  -- the two constants have the same residue, so their difference is a constant lying in `Q`
  by_contra hne
  have hc : IsIntegral ℚ ((d₀ : Ω ≃ₐ[RatFunc ℚ] Ω) α - e α) :=
    (hα.map ((d₀ : Ω ≃ₐ[RatFunc ℚ] Ω).restrictScalars ℚ).toAlgHom).sub hea
  have hc0 : (d₀ : Ω ≃ₐ[RatFunc ℚ] Ω) α - e α ≠ 0 := sub_ne_zero.2 hne
  refine const_notMem_of_ne_zero Ω hc hc0 Q (Ideal.IsMaximal.ne_top ‹Q.IsMaximal›) ?_
  have hsub : constMem Ω hc = (d₀ : Ω ≃ₐ[RatFunc ℚ] Ω) • a - e • a := by
    apply Subtype.ext
    push_cast
    rw [coe_smul_arith, coe_smul_arith]
    rfl
  rw [hsub, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, hd, sub_self]

/-- **The decomposition group at a rational place covers the whole action on the constants.**

Every arithmetic automorphism agrees on all of the constant field with one stabilizing the place
`Q`: apply `exists_stabilizer_apply_eq` to a primitive element of the constant field
(`exists_primitive_const`) and propagate the agreement along the generation. -/
theorem exists_stabilizer_eqOn_const (P : Ideal (Polynomial ℚ)) [P.IsMaximal]
    (Q : Ideal (Aring Ω)) [Q.IsMaximal] [Q.LiesOver P]
    (hP : Function.Surjective (algebraMap ℚ (Polynomial ℚ ⧸ P)))
    (e : Ω ≃ₐ[RatFunc ℚ] Ω) :
    ∃ d : Ω ≃ₐ[RatFunc ℚ] Ω, d • Q = Q ∧ ∀ x ∈ algebraicClosure ℚ Ω, d x = e x := by
  obtain ⟨α, hα, hk⟩ := exists_primitive_const Ω
  obtain ⟨d, hdQ, hdα⟩ := exists_stabilizer_apply_eq Ω P Q hP hα e
  refine ⟨d, hdQ, ?_⟩
  intro x hx
  rw [hk] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdα
  | algebraMap q =>
      rw [IsScalarTower.algebraMap_apply ℚ (RatFunc ℚ) Ω, AlgEquiv.commutes, AlgEquiv.commutes]
  | add y z _ _ ihy ihz => rw [map_add, map_add, ihy, ihz]
  | inv y _ ihy => rw [map_inv₀, map_inv₀, ihy]
  | mul y z _ _ ihy ihz => rw [map_mul, map_mul, ihy, ihz]

end Decomposition

end ArithAKLB
