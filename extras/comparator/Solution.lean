/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
A self-contained statement of the Riemann Existence Theorem as proven in this development,
together with its proof.

The definitions below are repeated verbatim from `Challenge.lean`; the `### Solution` section at
the end bridges them to the development and discharges the three statements.
-/
import Mathlib
import InverseGalois

/-!
# The Riemann Existence Theorem over `ℚ̄`

Fix `r` distinct points `t₀, …, t_{r-1}` of the affine line over `ℚ̄`.  Finite Galois covers of
`ℙ¹` branched only over those points are, classically, the same thing as finite quotients of the
fundamental group of the `r`-punctured sphere,

  `Γ_r = ⟨x₀, …, x_{r-1} | x₀ ⋯ x_{r-1} = 1⟩`,

which is to say the same thing as generating `r`-tuples with product `1`.  The correspondence sends
a cover to its *branch cycles*: the monodromy of a small loop around each puncture.

Everything here is phrased algebraically and from scratch.  A cover is a finite Galois extension
`M / ℚ̄(T)` together with its integral model `ℚ̄[X] ⊆ B = integralClosure ℚ̄[X] M`; the point `t` of
the line is the maximal ideal `(X - t)` of `ℚ̄[X]`; and the inertia group at `t` is the inertia
group, in the sense of `Ideal.inertia`, of a prime of `B` over `(X - t)`.  The point at infinity is
reached by the coordinate change `T ↦ 1/T`, which is built below and exchanges `∞` with `0`.

## The statements

* `ret_existence` — a generating product-one `r`-tuple in a finite group `H` is the system of
  branch cycles of a cover of `ℙ¹` with deck group `H`, branched only over `t₀, …, t_{r-1}`.
* `ret_completeness` — conversely, every cover branched only over those points carries such a
  system of branch cycles.
* `geometric_igp` — the immediate consequence: every finite group is the Galois group of a finite
  Galois extension of `ℚ̄(T)`.

The inertia clause in both directions is the *distinguished* one: the branch cycle does not merely
lie in an inertia group, it generates one.  That is what makes it comparable with a prescribed
conjugacy class, and it is what the rigidity method consumes.
-/

-- The development names shortcut instances for structures whose generic instance search is slow
-- (`InverseGalois/Core/InstanceShortcuts.lean`).  Each is `inferInstance`, so nothing about the
-- resulting structure changes, but the *term* elaboration produces does.  They are switched off
-- here so that the definitions below elaborate to exactly the terms `Challenge.lean` produces.
attribute [-instance] integralClosure.smulShortcut integralClosure.moduleShortcut
  integralClosure.algebraShortcut RatFunc.smulSelf RatFunc.algebraSelf

open Polynomial

noncomputable section

/-! ## Substituting a rational function for the parameter

The inversion `T ↦ 1/T` of `ℚ̄(T)`, built as the substitution of the transcendental element
`T⁻¹` for the parameter.  It is used only to reach the point at infinity. -/

/-- A `K`-algebra map out of `K(u)` is determined by its value at the parameter. -/
theorem ratFunc_algHom_ext {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {f g : RatFunc K →ₐ[K] L} (h : f RatFunc.X = g RatFunc.X) : f = g := by
  have hpoly : ∀ p : K[X],
      f (algebraMap K[X] (RatFunc K) p) = g (algebraMap K[X] (RatFunc K) p) := by
    have : f.comp (IsScalarTower.toAlgHom K K[X] (RatFunc K))
        = g.comp (IsScalarTower.toAlgHom K K[X] (RatFunc K)) := by
      refine Polynomial.algHom_ext ?_
      simpa [RatFunc.algebraMap_X] using h
    intro p
    exact congrArg (fun φ => φ p) this
  refine AlgHom.ext fun x => ?_
  induction x using RatFunc.induction_on with
  | _ p q hq => rw [map_div₀, map_div₀, hpoly, hpoly]

/-- The `K`-algebra map `K(u) → K(u)` with `u ↦ g`, for `g` transcendental over `K`. -/
def ratFuncSubst {K : Type*} [Field K] (g : RatFunc K) (hg : Transcendental K g) :
    RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (Polynomial.aeval g)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp hg))

@[simp]
theorem ratFuncSubst_X {K : Type*} [Field K] (g : RatFunc K) (hg : Transcendental K g) :
    ratFuncSubst g hg RatFunc.X = g := by
  have h := RatFunc.liftAlgHom_apply_div (S := K) (L := RatFunc K)
    (φ := Polynomial.aeval g)
    (hφ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp hg)) Polynomial.X 1
  simpa [ratFuncSubst, RatFunc.algebraMap_X] using h

/-- Two mutually inverse substitutions form an automorphism of `K(u)`. -/
def ratFuncSubstEquiv {K : Type*} [Field K] {g g' : RatFunc K} (hg : Transcendental K g)
    (hg' : Transcendental K g') (h : ratFuncSubst g hg g' = RatFunc.X)
    (h' : ratFuncSubst g' hg' g = RatFunc.X) : RatFunc K ≃ₐ[K] RatFunc K :=
  AlgEquiv.ofAlgHom (ratFuncSubst g hg) (ratFuncSubst g' hg')
    (ratFunc_algHom_ext (by simp [h]))
    (ratFunc_algHom_ext (by simp [h']))

/-- The inverse of the parameter is transcendental, so `u ↦ u⁻¹` is a substitution. -/
theorem transcendental_inv_X {K : Type*} [Field K] :
    Transcendental K (RatFunc.X : RatFunc K)⁻¹ := fun h =>
  RatFunc.transcendental_X (K := K) (IsAlgebraic.inv_iff.mp h)

/-- Inversion is an involution of the parameter. -/
theorem ratFuncSubst_inv_inv {K : Type*} [Field K] :
    ratFuncSubst (RatFunc.X : RatFunc K)⁻¹ transcendental_inv_X (RatFunc.X)⁻¹ = RatFunc.X := by
  rw [map_inv₀, ratFuncSubst_X, inv_inv]

/-- **The inversion `u ↦ u⁻¹` of `K(u)`**, which exchanges the point `0` of the line with the
point at infinity. -/
def ratFuncInv {K : Type*} [Field K] : RatFunc K ≃ₐ[K] RatFunc K :=
  ratFuncSubstEquiv transcendental_inv_X transcendental_inv_X
    ratFuncSubst_inv_inv ratFuncSubst_inv_inv

/-! ## Covers of the line over `ℚ̄` -/

/-- `ℚ̄`, the algebraic closure of the rationals: the constant field. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- **A cover of the line**: a finite Galois extension `M` of `ℚ̄(T)`, carrying the integral model
`ℚ̄[X] ⊆ M`.  The scalar-tower condition pins that model uniquely: `ℚ̄[X]` acts through its
inclusion into `ℚ̄(T)`. -/
structure Cover where
  /-- the function field of the cover. -/
  M : Type
  [field : Field M]
  [alg : Algebra (RatFunc Qbar) M]
  [algPoly : Algebra (Polynomial Qbar) M]
  [tower : IsScalarTower (Polynomial Qbar) (RatFunc Qbar) M]
  [findim : FiniteDimensional (RatFunc Qbar) M]
  [isGalois : IsGalois (RatFunc Qbar) M]

attribute [instance] Cover.field Cover.alg Cover.algPoly Cover.tower Cover.findim Cover.isGalois

namespace Cover

variable (L : Cover)

/-- The **deck group** `Gal(M / ℚ̄(T))` of a cover. -/
abbrev deck : Type := L.M ≃ₐ[RatFunc Qbar] L.M

/-- The **integral model** `B = integralClosure ℚ̄[X] M` of a cover: the affine chart. -/
abbrev model : Type := integralClosure (Polynomial Qbar) L.M

instance instModelAction : MulSemiringAction L.deck L.model :=
  IsIntegralClosure.MulSemiringAction (Polynomial Qbar) (RatFunc Qbar) L.M L.model

/-- The point `t` of the affine line, as the maximal ideal `(X - t)` of `ℚ̄[X]`. -/
abbrev place (t : Qbar) : Ideal (Polynomial Qbar) := Ideal.span {(X - C t : Polynomial Qbar)}

/-- A deck transformation is an **inertia element at `t`** if it lies in the inertia group of some
prime of the integral model lying over the point `t`. -/
def IsInertiaAt (t : Qbar) (σ : L.deck) : Prop :=
  ∃ Q : Ideal L.model, Q.IsMaximal ∧ Q.LiesOver (place t) ∧ σ ∈ Q.inertia L.deck

/-- A deck transformation is a **distinguished inertia element at `t`** — a branch cycle at `t` —
if it *generates* the inertia group of some prime of the integral model lying over `t`. -/
def IsInertiaGenAt (t : Qbar) (σ : L.deck) : Prop :=
  ∃ Q : Ideal L.model, Q.IsMaximal ∧ Q.LiesOver (place t) ∧
    Q.inertia L.deck = Subgroup.zpowers σ

/-- A cover is **unramified outside `S`** if every inertia element at a point outside `S` is
trivial. -/
def IsUnramifiedOutside (S : Set Qbar) : Prop :=
  ∀ t ∉ S, ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1

end Cover

/-! ## The point at infinity

`Twist φ M` is the field `M` with the base `ℚ̄(T)` acting through the coordinate change `φ`.  For
`φ` the inversion this moves the point at infinity to `0`, where the affine chart can see it. -/

/-- The field `M`, viewed as an extension of `ℚ̄(T)` through the coordinate change `φ`. -/
def Twist (_φ : RatFunc Qbar ≃+* RatFunc Qbar) (M : Type) : Type := M

namespace Twist

variable (φ : RatFunc Qbar ≃+* RatFunc Qbar) (M : Type) [Field M]

instance instField : Field (Twist φ M) := inferInstanceAs (Field M)

variable [Algebra (RatFunc Qbar) M]

instance instAlgebraRatFunc : Algebra (RatFunc Qbar) (Twist φ M) :=
  ((algebraMap (RatFunc Qbar) M).comp (φ : RatFunc Qbar →+* RatFunc Qbar)).toAlgebra

instance instAlgebraPoly : Algebra (Polynomial Qbar) (Twist φ M) :=
  ((algebraMap (RatFunc Qbar) (Twist φ M)).comp
    (algebraMap (Polynomial Qbar) (RatFunc Qbar))).toAlgebra

instance instTower : IsScalarTower (Polynomial Qbar) (RatFunc Qbar) (Twist φ M) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {φ M}

/-- The element of `M` underlying an element of the twist. -/
def toBase (x : Twist φ M) : M := x

/-- Scalar multiplication on the twist is scalar multiplication by the transformed scalar. -/
theorem toBase_smul (f : RatFunc Qbar) (x : Twist φ M) :
    toBase (f • x) = φ f • toBase x := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

variable (φ M)

/-- The twist has the same rank over the base as the original. -/
theorem rank_eq : Module.rank (RatFunc Qbar) (Twist φ M) = Module.rank (RatFunc Qbar) M :=
  rank_eq_of_equiv_equiv (R := RatFunc Qbar) (R' := RatFunc Qbar) (M := Twist φ M) (M₁ := M)
    (fun f => φ f) (AddEquiv.refl M) φ.bijective (fun f x => toBase_smul f x)

instance instFiniteDimensional [FiniteDimensional (RatFunc Qbar) M] :
    FiniteDimensional (RatFunc Qbar) (Twist φ M) :=
  Module.rank_lt_aleph0_iff.mp (by rw [rank_eq]; exact Module.rank_lt_aleph0 (RatFunc Qbar) M)

instance instIsGalois [FiniteDimensional (RatFunc Qbar) M] [IsGalois (RatFunc Qbar) M] :
    IsGalois (RatFunc Qbar) (Twist φ M) :=
  IsGalois.of_equiv_equiv (F := RatFunc Qbar) (E := M) (M := RatFunc Qbar) (N := Twist φ M)
    (f := φ.symm) (g := RingEquiv.refl M)
    (by ext f; show (algebraMap (RatFunc Qbar) M) (φ (φ.symm f)) = _; rw [φ.apply_symm_apply]; rfl)

end Twist

namespace Cover

/-- **The cover read in the coordinate `φ`**: the same field, with the base acting through the
coordinate change, so that the branch points are moved by `φ`. -/
def twist (L : Cover) (φ : RatFunc Qbar ≃+* RatFunc Qbar) : Cover where
  M := Twist φ L.M
  field := Twist.instField φ L.M
  alg := Twist.instAlgebraRatFunc φ L.M
  algPoly := Twist.instAlgebraPoly φ L.M
  tower := Twist.instTower φ L.M
  findim := Twist.instFiniteDimensional φ L.M
  isGalois := Twist.instIsGalois φ L.M

/-- **A cover is unramified at the point at infinity** if, read in the coordinate `T ↦ 1/T` — in
which infinity has become the point `0` — it has no nontrivial inertia there. -/
def IsUnramifiedAtInfinity (L : Cover) : Prop :=
  ∀ σ : (L.twist ratFuncInv.toRingEquiv).deck,
    (L.twist ratFuncInv.toRingEquiv).IsInertiaAt 0 σ → σ = 1

end Cover

/-! ### Solution

The definitions above are the development's own, spelled out.  `Cover` is
`Rigidity.RET.LineCover` field for field, `Cover.model` is `GeomAKLB.Bring`, `Cover.place` is
`GeomAKLB.placeP`, `Cover.instModelAction` is `GeomAKLB.instMSA`, `Twist` is
`Rigidity.RET.Twist`, and `ratFuncInv` is `Rigidity.RET.invSubst`.  Each pair agrees
definitionally — the bridge lemmas below are `Iff.rfl` — so the three statements are read off
`Rigidity.RET.geomRET` and `isGeometricGaloisCover_of_finite`.
-/

namespace Solution

open Rigidity.RET GeomAKLB

/-- A cover of the line, as the development's `LineCover`. -/
def toLineCover (L : Cover) : LineCover where
  M := L.M
  field := L.field
  alg := L.alg
  algPoly := L.algPoly
  tower := L.tower
  findim := L.findim
  isGalois := L.isGalois

/-- The development's `LineCover`, as a cover of the line. -/
def ofLineCover (L : LineCover) : Cover where
  M := L.M
  field := L.field
  alg := L.alg
  algPoly := L.algPoly
  tower := L.tower
  findim := L.findim
  isGalois := L.isGalois

/-- Distinguished inertia is the development's. -/
theorem inertiaGen_ofLineCover (L : LineCover) (t : Qbar) (σ : L.deck) :
    L.IsInertiaGenAt t σ ↔ (ofLineCover L).IsInertiaGenAt t σ := Iff.rfl

/-- Unramifiedness outside a set is the development's. -/
theorem unramifiedOutside_ofLineCover (L : LineCover) (S : Set Qbar) :
    L.IsUnramifiedOutside S ↔ (ofLineCover L).IsUnramifiedOutside S := Iff.rfl

/-- Unramifiedness at infinity is the development's. -/
theorem unramifiedAtInfinity_ofLineCover (L : LineCover) :
    L.IsUnramifiedAtInfinity ↔ (ofLineCover L).IsUnramifiedAtInfinity := Iff.rfl

/-- Distinguished inertia is the development's, in the other direction. -/
theorem inertiaGen_toLineCover (L : Cover) (t : Qbar) (σ : L.deck) :
    L.IsInertiaGenAt t σ ↔ (toLineCover L).IsInertiaGenAt t σ := Iff.rfl

/-- Unramifiedness outside a set is the development's, in the other direction. -/
theorem unramifiedOutside_toLineCover (L : Cover) (S : Set Qbar) :
    L.IsUnramifiedOutside S ↔ (toLineCover L).IsUnramifiedOutside S := Iff.rfl

/-- Unramifiedness at infinity is the development's, in the other direction. -/
theorem unramifiedAtInfinity_toLineCover (L : Cover) :
    L.IsUnramifiedAtInfinity ↔ (toLineCover L).IsUnramifiedAtInfinity := Iff.rfl

end Solution

/-- **The Riemann Existence Theorem, existence direction.**

A generating `r`-tuple with product `1` in a finite group `H` — equivalently, a surjection onto
`H` from the fundamental group `Γ_r = ⟨x₀,…,x_{r-1} | x₀⋯x_{r-1} = 1⟩` of the `r`-punctured
sphere — is the system of branch cycles of a finite Galois cover of `ℙ¹` over `ℚ̄` with deck group
`H`, branched only over the prescribed points `t₀, …, t_{r-1}`: unramified at every other point of
the affine line, unramified at infinity, and with `hᵢ` generating an inertia group at `tᵢ`. -/
theorem ret_existence {r : ℕ} (t : Fin r → Qbar) (ht : Function.Injective t)
    (H : Type) [Group H] [Finite H] (h : Fin r → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : Cover) (e : L.deck ≃* H),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i)) := by
  obtain ⟨L, e, hout, hinf, hgi⟩ := (Rigidity.RET.geomRET t ht).exists_cover h hprod hgen
  exact ⟨Solution.ofLineCover L, e, hout, hinf, hgi⟩

/-- **The Riemann Existence Theorem, completeness direction.**

Conversely, a finite Galois cover of `ℙ¹` over `ℚ̄` branched only over `t₀, …, t_{r-1}` carries a
system of branch cycles over those points: inertia generators `g₀, …, g_{r-1}`, one at each `tᵢ`,
which generate the deck group and whose ordered product is `1`. -/
theorem ret_completeness {r : ℕ} (t : Fin r → Qbar) (ht : Function.Injective t) (L : Cover)
    (hout : L.IsUnramifiedOutside (Set.range t)) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck,
      (∀ i, L.IsInertiaGenAt (t i) (g i)) ∧
      Subgroup.closure (Set.range g) = ⊤ ∧ (List.ofFn g).prod = 1 := by
  obtain ⟨g, hg⟩ := (Rigidity.RET.geomRET t ht).exists_cycles (Solution.toLineCover L) hout hinf
  exact ⟨g, hg.inertia, hg.top, hg.prod⟩

/-- **The geometric inverse Galois problem over `ℚ̄(T)`.**

Every finite group is the Galois group of a finite Galois extension of `ℚ̄(T)`.  This is the
existence direction applied to a large enough generating tuple: the sphere group `Γ_r` is free of
rank `r - 1`, so every finite group receives a surjection from one. -/
theorem geometric_igp (G : Type) [Group G] [Finite G] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc Qbar) L)
      (_ : FiniteDimensional (RatFunc Qbar) L) (_ : IsGalois (RatFunc Qbar) L),
      Nonempty ((L ≃ₐ[RatFunc Qbar] L) ≃* G) :=
  isGeometricGaloisCover_of_finite
