/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.RegularProduct
import InverseGalois.Solvable.WreathRecognition

/-!
# Conjugate layers of a regular realization, and the wreath product they generate

Let `E / ℚ(T)` be a regular Galois extension with group `H` and let `N / ℚ(x)` be a regular Galois
extension with a finite abelian group `A`.  Realize `E` inside a fixed algebraic closure `ℚ̄(T)`
and choose a primitive element `θ` of `E / ℚ(T)` that is transcendental over `ℚ`; its conjugates
`θ_h`, indexed by `h : H`, are then transcendental too.  Fixing a rational `c`, the assignment
`x ↦ θ_h + c` is a field embedding of `ℚ(x)` into `ℚ̄(T)`, and since `ℚ̄(T)` is algebraically
closed it extends to an embedding `ε h : N → ℚ̄(T)`: one *layer* over each conjugate of `θ`.  The
compositum `M` of `E` with all the layers is a finite Galois extension of `ℚ(T)`.

The translation `c` is deliberately left free.  Only finitely many values of `c` fail to make the
layers independent, and that finite bad set can only be described once `E` and `θ` are in hand, so
the construction of the layers is kept separate from the construction of the base.

The group `G = Gal(M / ℚ(T))` acts on this picture in a very rigid way.  Restriction to `E` gives
`π : G → H`, and because `σ` carries `θ_h` to `θ_{π σ * h}` it carries the layer `h` onto the layer
`π σ * h`; normality of `N / ℚ(x)` then produces a *unique* automorphism `a h σ` of `N` with
`σ ∘ ε h = ε (π σ * h) ∘ a h σ`.  Composing two automorphisms and comparing the two descriptions of
the result gives the cocycle identity `a h (σ τ) = a (π τ * h) σ * a h τ`, which is exactly the
identity that `RegularWreathProduct.coordHom` turns into a homomorphism `G → A ≀ᵣ H`.  Its kernel is
trivial for a cheap reason: `M` is generated over `ℚ(T)` by `θ` together with the layers, and an
element with trivial image in `H` and trivial coordinates fixes every one of those generators.

This file contains no geometry: it stops at the injection `G → A ≀ᵣ H`, and it is a separate matter
— a degree count — to know when that injection is onto.  That count is isolated in the hypothesis
of `ConjugateData.nonempty_mulEquiv_of_card`.

All the twisting is carried by bare ring homomorphisms `ε h : N →+* ℚ̄(T)` rather than by algebra
structures, so that `ℚ̄(T)` never acquires a second `ℚ(T)`-algebra structure.

## Main results

* `Rigidity.RET.Wreath.ConjugateData` — the bundle of a regular realization of `H`, a regular
  realization of an abelian `A`, a transcendental primitive element and the family of layer
  embeddings.
* `Rigidity.RET.Wreath.exists_baseField` — a regular realization of `H` sits inside `ℚ̄(T)` with a
  primitive element transcendental over the rationals.
* `Rigidity.RET.Wreath.exists_epsilon` — the layers over a prescribed translate exist.
* `Rigidity.RET.Wreath.nonempty_conjugateData` — such a bundle exists for any two regular
  realizations and any rational translation `x ↦ x + c`.
* `Rigidity.RET.Wreath.ConjugateData.coordAut_mul` — the wreath cocycle identity for the layer
  automorphisms.
* `Rigidity.RET.Wreath.ConjugateData.isGalois_M` — the compositum of the layers is a finite Galois
  extension of `ℚ(T)`.
* `Rigidity.RET.Wreath.ConjugateData.wreathHom_injective` — the coordinates embed
  `Gal(M / ℚ(T))` into `A ≀ᵣ H`.
* `Rigidity.RET.Wreath.ConjugateData.nonempty_mulEquiv_of_card` — that embedding is an isomorphism
  as soon as the orders agree.
-/

open Polynomial Module IntermediateField

noncomputable section

namespace Rigidity.RET.Wreath

/-- The base field `ℚ(T)`. -/
abbrev QT : Type := RatFunc ℚ

/-- The algebraic closure `ℚ̄(T)` of `ℚ(T)` in which all the layers live. -/
abbrev QTbar : Type := AlgebraicClosure (RatFunc ℚ)

/-! ## Generalities -/

/-- A ring homomorphism between fields of characteristic zero is a homomorphism of
`ℚ`-algebras. -/
def ratAlgHom {X Y : Type*} [Field X] [Field Y] [Algebra ℚ X] [Algebra ℚ Y] (f : X →+* Y) :
    X →ₐ[ℚ] Y where
  __ := f
  commutes' q := by
    have hX : algebraMap ℚ X q = (q : X) := by simp
    have hY : algebraMap ℚ Y q = (q : Y) := by simp
    rw [hX, hY]
    exact map_ratCast f q

@[simp]
theorem ratAlgHom_apply {X Y : Type*} [Field X] [Field Y] [Algebra ℚ X] [Algebra ℚ Y]
    (f : X →+* Y) (x : X) : ratAlgHom f x = f x := rfl

/-- **Transcendence over `ℚ` transfers along a ring homomorphism** of characteristic-zero
fields, in both directions: such a homomorphism is injective and fixes `ℚ`. -/
theorem transcendental_ringHom {X Y : Type*} [Field X] [Field Y] [Algebra ℚ X] [Algebra ℚ Y]
    (f : X →+* Y) {x : X} (hx : Transcendental ℚ x) : Transcendental ℚ (f x) := by
  rintro ⟨p, hp, hpx⟩
  refine hx ⟨p, hp, f.injective ?_⟩
  have := (aeval_algHom_apply (ratAlgHom f) x p).symm
  rw [ratAlgHom_apply] at this
  rw [map_zero]
  exact (this.trans hpx : (ratAlgHom f) (aeval x p) = 0)

/-- The variable of `ℚ(T)` is transcendental over `ℚ`. -/
theorem transcendental_ratFunc_X : Transcendental ℚ (RatFunc.X : QT) := by
  rw [Transcendental, IsAlgebraic]
  push_neg
  intro p hp
  have hX : (RatFunc.X : QT) = algebraMap ℚ[X] QT Polynomial.X := (RatFunc.algebraMap_X).symm
  rw [hX, aeval_algebraMap_apply, aeval_X_left, AlgHom.id_apply]
  intro hc
  exact hp (IsFractionRing.injective ℚ[X] (RatFunc ℚ) (hc.trans (map_zero _).symm))

/-- A nonzero rational multiple of a transcendental element, shifted by a rational constant, is
again transcendental. -/
theorem transcendental_linear {Y : Type*} [Field Y] [Algebra ℚ Y] {lam c : ℚ} (hlam : lam ≠ 0)
    {y : Y} (hy : Transcendental ℚ y) : Transcendental ℚ ((lam : Y) * y + (c : Y)) := by
  haveI : CharZero Y := charZero_of_injective_algebraMap (algebraMap ℚ Y).injective
  intro hz
  refine hy ?_
  rw [← mem_algebraicClosure_iff] at hz ⊢
  have hlamY : ((lam : Y)) ∈ algebraicClosure ℚ Y := by
    have h : ((lam : Y)) = algebraMap ℚ Y lam := by simp
    rw [h]; exact IntermediateField.algebraMap_mem _ _
  have hcY : ((c : Y)) ∈ algebraicClosure ℚ Y := by
    have h : ((c : Y)) = algebraMap ℚ Y c := by simp
    rw [h]; exact IntermediateField.algebraMap_mem _ _
  have hne : (lam : Y) ≠ 0 := Rat.cast_ne_zero.mpr hlam
  have key : y = ((lam : Y) * y + (c : Y) - (c : Y)) * ((lam : Y))⁻¹ := by
    field_simp
    ring
  rw [key]
  exact mul_mem (sub_mem hz hcY) (inv_mem hlamY)

/-- Two ring homomorphisms out of `ℚ(T)` into a field of characteristic zero that agree on the
variable are equal. -/
theorem ringHom_ratFunc_ext {Ω : Type*} [Field Ω] [CharZero Ω] (f g : QT →+* Ω)
    (h : f RatFunc.X = g RatFunc.X) : f = g := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (ℚ[X])) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    have := (Subsingleton.elim
      (f.comp ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.C : ℚ →+* ℚ[X])))
      (g.comp ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.C : ℚ →+* ℚ[X]))))
    exact congrFun (congrArg (fun r : ℚ →+* Ω => (r : ℚ → Ω)) this) a
  · simpa using h

/-- The image of a field generated by a single element over a base is controlled by the images of
the base and of the generator. -/
theorem range_subset_of_adjoin_eq_top {F N Ω : Type*} [Field F] [Field N] [Field Ω]
    [Algebra F N] {β : N} (hβ : IntermediateField.adjoin F {β} = ⊤)
    (f : N →+* Ω) (Z : Subfield Ω)
    (hF : ∀ r : F, f (algebraMap F N r) ∈ Z) (hb : f β ∈ Z) (n : N) : f n ∈ Z := by
  have hmem : n ∈ (IntermediateField.adjoin F ({β} : Set N)).toSubfield := by
    rw [hβ]; trivial
  rw [IntermediateField.adjoin_toSubfield] at hmem
  have hle : Subfield.closure (Set.range (algebraMap F N) ∪ {β}) ≤ Subfield.comap f Z := by
    rw [Subfield.closure_le]
    rintro x (⟨r, rfl⟩ | rfl)
    · exact hF r
    · exact hb
  exact hle hmem

/-- **The embeddings of a normal extension into a field form a torsor under its automorphism
group**: two embeddings that agree on the base differ by a unique automorphism. -/
theorem existsUnique_algEquiv_comp {F N Ω : Type*} [Field F] [Field N] [Field Ω]
    [Algebra F N] [Normal F N] (g f : N →+* Ω)
    (hfg : ∀ r : F, f (algebraMap F N r) = g (algebraMap F N r)) :
    ∃! β : N ≃ₐ[F] N, ∀ n, f n = g (β n) := by
  letI : Algebra F Ω := (g.comp (algebraMap F N)).toAlgebra
  letI : Algebra N Ω := g.toAlgebra
  haveI : IsScalarTower F N Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f' : N →ₐ[F] Ω := { f with commutes' := fun r => hfg r }
  refine ⟨Normal.algHomEquivAut (F := F) (K₁ := Ω) (E := N) f', ?_, ?_⟩
  · intro n
    have := (Normal.algHomEquivAut (F := F) (K₁ := Ω) (E := N)).symm_apply_apply f'
    exact (congrFun (congrArg (fun p : N →ₐ[F] Ω => (p : N → Ω)) this) n).symm
  · intro β hβ
    have : (Normal.algHomEquivAut (F := F) (K₁ := Ω) (E := N)).symm β = f' := by
      ext n
      exact (hβ n).symm
    rw [← this, Equiv.apply_symm_apply]

/-- An element fixed by an automorphism lies in the field fixed by the subgroup it generates. -/
theorem mem_fixedField_closure_singleton {K L : Type*} [Field K] [Field L] [Algebra K L]
    {σ : L ≃ₐ[K] L} {x : L} (hx : σ x = x) :
    x ∈ IntermediateField.fixedField (Subgroup.closure ({σ} : Set (L ≃ₐ[K] L))) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  have hle : Subgroup.closure ({σ} : Set (L ≃ₐ[K] L)) ≤ MulAction.stabilizer (L ≃ₐ[K] L) x := by
    rw [Subgroup.closure_le]
    rintro y rfl
    exact hx
  exact hle hg

/-! ## The conjugate configuration -/

/-- **The conjugate configuration** underlying the wreath construction.

It records a regular Galois extension `N / ℚ(T)` with group `A`, a regular Galois subextension
`E` of `ℚ̄(T) / ℚ(T)` with group `H`, a primitive element `θ` of `E`, the intercept `c` of the
substitution `x ↦ θ + c`, and, for each `h : H`, an embedding `ε h` of `N` into `ℚ̄(T)` whose
restriction to the base sends the variable to `h(θ) + c`. -/
structure ConjugateData (H A : Type*) [Group H] [CommGroup A] where
  /-- The abstract extension of the base carrying the group `A`. -/
  N : Type
  [field_N : Field N]
  [algebra_N : Algebra QT N]
  [algebra_rat_N : Algebra ℚ N]
  [tower_N : IsScalarTower ℚ QT N]
  [finiteDimensional_N : FiniteDimensional QT N]
  [isGalois_N : IsGalois QT N]
  /-- `N` acquires no constants over `ℚ`. -/
  regular_N : algebraicClosure ℚ N = ⊥
  /-- The identification of the Galois group of `N` with `A`. -/
  galA : (N ≃ₐ[QT] N) ≃* A
  /-- The subextension of `ℚ̄(T) / ℚ(T)` carrying the group `H`. -/
  E : IntermediateField QT QTbar
  [finiteDimensional_E : FiniteDimensional QT ↥E]
  [isGalois_E : IsGalois QT ↥E]
  /-- `E` acquires no constants over `ℚ`. -/
  regular_E : algebraicClosure ℚ ↥E = ⊥
  /-- The identification of the Galois group of `E` with `H`. -/
  galH : (↥E ≃ₐ[QT] ↥E) ≃* H
  /-- A primitive element of `E / ℚ(T)`. -/
  θ : ↥E
  /-- `θ` generates `E` over the base. -/
  adjoin_θ : IntermediateField.adjoin QT {θ} = ⊤
  /-- `θ` is not algebraic over the rationals. -/
  transcendental_θ : Transcendental ℚ θ
  /-- The intercept of the substitution. -/
  c : ℚ
  /-- The family of embeddings of `N`, one for each conjugate of `θ`. -/
  ε : H → (N →+* QTbar)
  /-- Each embedding carries the base into `E`. -/
  ε_mem : ∀ (h : H) (r : QT), ε h (algebraMap QT N r) ∈ E
  /-- The embedding indexed by `h` extends the substitution `x ↦ h(θ) + c`. -/
  ε_X : ∀ h : H, ε h (algebraMap QT N RatFunc.X)
      = ((galH.symm h θ : ↥E) : QTbar) + (c : QTbar)

attribute [instance] ConjugateData.field_N ConjugateData.algebra_N ConjugateData.algebra_rat_N
  ConjugateData.tower_N ConjugateData.finiteDimensional_N ConjugateData.isGalois_N
  ConjugateData.finiteDimensional_E ConjugateData.isGalois_E

namespace ConjugateData

variable {H A : Type*} [Group H] [CommGroup A] (d : ConjugateData H A)

include d in
/-- The group `H` is finite: it is the Galois group of a finite extension. -/
theorem finite_H : Finite H := by
  letI := AlgEquiv.fintype QT ↥d.E
  exact Finite.of_equiv _ d.galH.toEquiv

include d in
/-- The group `A` is finite: it is the Galois group of a finite extension. -/
theorem finite_A : Finite A := by
  letI := AlgEquiv.fintype QT d.N
  exact Finite.of_equiv _ d.galA.toEquiv

/-- The conjugate `h(θ)` of the primitive element, seen inside `ℚ̄(T)`. -/
def conj (h : H) : QTbar := ((d.galH.symm h d.θ : ↥d.E) : QTbar)

theorem conj_mem (h : H) : d.conj h ∈ d.E := SetLike.coe_mem _

theorem ε_X' (h : H) :
    d.ε h (algebraMap QT d.N RatFunc.X) = d.conj h + (d.c : QTbar) := d.ε_X h

/-- The restriction to `E` of an automorphism of `ℚ̄(T)`, read in `H`. -/
def π₀ : (QTbar ≃ₐ[QT] QTbar) →* H :=
  d.galH.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.E)

theorem π₀_apply (σ : QTbar ≃ₐ[QT] QTbar) :
    d.π₀ σ = d.galH (AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.E σ) := rfl

/-- **An automorphism of `ℚ̄(T)` permutes the conjugates of `θ`** the way its restriction to `E`
does. -/
theorem map_conj (σ : QTbar ≃ₐ[QT] QTbar) (h : H) : σ (d.conj h) = d.conj (d.π₀ σ * h) := by
  have hres : d.galH.symm (d.π₀ σ) =
      AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.E σ := by
    rw [π₀_apply, MulEquiv.symm_apply_apply]
  have key : d.conj (d.π₀ σ * h) =
      ((AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.E σ (d.galH.symm h d.θ) :
        ↥d.E) : QTbar) := by
    rw [conj, map_mul, hres, AlgEquiv.mul_apply]
  rw [key]
  exact (AlgEquiv.restrictNormalHom_apply d.E σ (d.galH.symm h d.θ)).symm

/-! ## The coordinates -/

/-- **An automorphism of `ℚ̄(T)` carries the layer `h` onto the layer `π₀ σ * h`**, and it does so
through a unique automorphism of `N`. -/
theorem existsUnique_coordAut (h : H) (σ : QTbar ≃ₐ[QT] QTbar) :
    ∃! β : d.N ≃ₐ[QT] d.N, ∀ n, σ (d.ε h n) = d.ε (d.π₀ σ * h) (β n) := by
  refine existsUnique_algEquiv_comp (F := QT) (d.ε (d.π₀ σ * h))
    (σ.toAlgHom.toRingHom.comp (d.ε h)) ?_
  have hext : (σ.toAlgHom.toRingHom.comp (d.ε h)).comp (algebraMap QT d.N)
      = (d.ε (d.π₀ σ * h)).comp (algebraMap QT d.N) := by
    refine ringHom_ratFunc_ext _ _ ?_
    show σ (d.ε h (algebraMap QT d.N RatFunc.X)) = d.ε (d.π₀ σ * h) (algebraMap QT d.N RatFunc.X)
    rw [d.ε_X' h, d.ε_X' (d.π₀ σ * h), map_add, map_ratCast, d.map_conj]
  intro r
  exact congrFun (congrArg (fun f : QT →+* QTbar => (f : QT → QTbar)) hext) r

/-- The coordinate of `σ` at the layer `h`, as an automorphism of `N`. -/
def coordAut (h : H) (σ : QTbar ≃ₐ[QT] QTbar) : d.N ≃ₐ[QT] d.N :=
  (d.existsUnique_coordAut h σ).choose

theorem coordAut_spec (h : H) (σ : QTbar ≃ₐ[QT] QTbar) (n : d.N) :
    σ (d.ε h n) = d.ε (d.π₀ σ * h) (d.coordAut h σ n) :=
  (d.existsUnique_coordAut h σ).choose_spec.1 n

theorem coordAut_unique {h : H} {σ : QTbar ≃ₐ[QT] QTbar} {β : d.N ≃ₐ[QT] d.N}
    (hβ : ∀ n, σ (d.ε h n) = d.ε (d.π₀ σ * h) (β n)) : β = d.coordAut h σ :=
  (d.existsUnique_coordAut h σ).choose_spec.2 β hβ

@[simp]
theorem coordAut_one (h : H) : d.coordAut h 1 = 1 := by
  refine (d.coordAut_unique ?_).symm
  intro n
  rw [map_one, one_mul]
  rfl

/-- **The wreath cocycle identity.**  The coordinate of a product at the layer `h` is the
coordinate of the left factor at the layer to which the right factor has already moved `h`,
composed with the coordinate of the right factor at `h`. -/
theorem coordAut_mul (h : H) (σ τ : QTbar ≃ₐ[QT] QTbar) :
    d.coordAut h (σ * τ) = d.coordAut (d.π₀ τ * h) σ * d.coordAut h τ := by
  refine (d.coordAut_unique ?_).symm
  intro n
  have hστ : d.π₀ (σ * τ) * h = d.π₀ σ * (d.π₀ τ * h) := by
    rw [map_mul, mul_assoc]
  rw [hστ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← d.coordAut_spec (d.π₀ τ * h) σ,
    ← d.coordAut_spec h τ]

/-! ## The compositum of the layers -/

/-- The generators of the compositum: the primitive element of `E` together with the images of
all the embeddings. -/
def gens : Set QTbar := insert (d.θ : QTbar) (⋃ h : H, Set.range (d.ε h))

/-- **The compositum `M`** of `E` with all the layers `ε h (N)`. -/
def M : IntermediateField QT QTbar := IntermediateField.adjoin QT d.gens

theorem theta_mem_gens : (d.θ : QTbar) ∈ d.gens := Set.mem_insert _ _

theorem ε_mem_gens (h : H) (n : d.N) : d.ε h n ∈ d.gens :=
  Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨h, Set.mem_range_self n⟩)

theorem gens_subset_M : d.gens ⊆ (d.M : Set QTbar) := IntermediateField.subset_adjoin QT d.gens

theorem theta_mem_M : (d.θ : QTbar) ∈ d.M := d.gens_subset_M d.theta_mem_gens

theorem ε_mem_M (h : H) (n : d.N) : d.ε h n ∈ d.M := d.gens_subset_M (d.ε_mem_gens h n)

/-- `θ` generates `E` inside `ℚ̄(T)`. -/
theorem adjoin_theta : IntermediateField.adjoin QT {(d.θ : QTbar)} = d.E := by
  rw [← IntermediateField.lift_adjoin_simple, d.adjoin_θ, IntermediateField.lift_top]

theorem E_le_M : d.E ≤ d.M := by
  rw [← d.adjoin_theta, IntermediateField.adjoin_le_iff]
  rintro x rfl
  exact d.theta_mem_M

/-- **The compositum is a finite extension of the base.**  Each layer is generated over `E` by the
image of a single primitive element of `N`. -/
instance finiteDimensional_M : FiniteDimensional QT ↥d.M := by
  haveI := d.finite_H
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element QT d.N
  set Z : IntermediateField QT QTbar :=
    d.E ⊔ ⨆ h : H, IntermediateField.adjoin QT {d.ε h β} with hZ
  haveI : ∀ h : H, FiniteDimensional QT ↥(IntermediateField.adjoin QT {d.ε h β}) := by
    intro h
    exact IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := QT) (d.ε h β))
  haveI : FiniteDimensional QT ↥Z := by
    rw [hZ]
    infer_instance
  have hEZ : d.E ≤ Z := le_sup_left
  have hlayer : ∀ h : H, IntermediateField.adjoin QT {d.ε h β} ≤ Z := fun h =>
    (le_iSup (fun h : H => IntermediateField.adjoin QT {d.ε h β}) h).trans le_sup_right
  have hle : d.M ≤ Z := by
    rw [M, IntermediateField.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact hEZ (SetLike.coe_mem d.θ)
    · obtain ⟨_, ⟨h, rfl⟩, n, rfl⟩ := hx
      refine range_subset_of_adjoin_eq_top hβ (d.ε h) Z.toSubfield (fun r => ?_) ?_ n
      · exact hEZ (d.ε_mem h r)
      · exact hlayer h (IntermediateField.mem_adjoin_simple_self QT (d.ε h β))
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

/-- **The compositum is normal over the base**: every automorphism of `ℚ̄(T)` permutes `E` and
permutes the layers. -/
instance normal_M : Normal QT ↥d.M := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [IntermediateField.map_le_iff_le_comap, M, IntermediateField.adjoin_le_iff]
  rintro x (rfl | hx)
  · show σ (d.θ : QTbar) ∈ d.M
    refine d.E_le_M ?_
    exact (IntermediateField.normal_iff_forall_map_le'.mp inferInstance σ)
      ⟨(d.θ : QTbar), SetLike.coe_mem d.θ, rfl⟩
  · obtain ⟨_, ⟨h, rfl⟩, n, rfl⟩ := hx
    show σ (d.ε h n) ∈ d.M
    rw [d.coordAut_spec h σ n]
    exact d.ε_mem_M _ _

instance isGalois_M : IsGalois QT ↥d.M := ⟨⟩

/-! ## The Galois group of the compositum -/

/-- The Galois group of the compositum over `ℚ(T)`. -/
abbrev G : Type := ↥d.M ≃ₐ[QT] ↥d.M

instance finite_G : Finite d.G := by
  letI := AlgEquiv.fintype QT ↥d.M
  infer_instance

theorem restrictNormalHom_M_surjective :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M) :=
  AlgEquiv.restrictNormalHom_surjective _

/-- A chosen extension of an automorphism of the compositum to the whole algebraic closure. -/
def lift (g : d.G) : QTbar ≃ₐ[QT] QTbar :=
  Function.surjInv d.restrictNormalHom_M_surjective g

@[simp]
theorem restrict_lift (g : d.G) :
    AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M (d.lift g) = g :=
  Function.surjInv_eq _ g

/-- Two automorphisms of `ℚ̄(T)` with the same restriction to the compositum agree on it. -/
theorem apply_eq_of_restrict_eq {σ τ : QTbar ≃ₐ[QT] QTbar}
    (h : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M σ
      = AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M τ)
    {x : QTbar} (hx : x ∈ d.M) : σ x = τ x := by
  have h1 := AlgEquiv.restrictNormalHom_apply d.M σ ⟨x, hx⟩
  have h2 := AlgEquiv.restrictNormalHom_apply d.M τ ⟨x, hx⟩
  rw [← h1, ← h2, h]

/-- The image in `H` only depends on the restriction to the compositum. -/
theorem π₀_eq_of_restrict_eq {σ τ : QTbar ≃ₐ[QT] QTbar}
    (h : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M σ
      = AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M τ) :
    d.π₀ σ = d.π₀ τ := by
  rw [π₀_apply, π₀_apply]
  congr 1
  refine AlgEquiv.ext fun y => ?_
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  exact d.apply_eq_of_restrict_eq h (d.E_le_M (SetLike.coe_mem y))

/-- The coordinates only depend on the restriction to the compositum. -/
theorem coordAut_eq_of_restrict_eq {σ τ : QTbar ≃ₐ[QT] QTbar}
    (h : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M σ
      = AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M τ) (hh : H) :
    d.coordAut hh σ = d.coordAut hh τ := by
  have hπ := d.π₀_eq_of_restrict_eq h
  have key : ∀ n, σ (d.ε hh n) = d.ε (d.π₀ σ * hh) (d.coordAut hh τ n) := by
    intro n
    rw [d.apply_eq_of_restrict_eq h (d.ε_mem_M hh n), hπ]
    exact d.coordAut_spec hh τ n
  exact (d.coordAut_unique key).symm

/-- **The restriction homomorphism to `H`.** -/
def π : d.G →* H where
  toFun g := d.π₀ (d.lift g)
  map_one' := by
    have h : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M (d.lift 1)
        = AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M 1 := by
      rw [d.restrict_lift, map_one]
    rw [d.π₀_eq_of_restrict_eq h, map_one]
  map_mul' g₁ g₂ := by
    have h : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M (d.lift (g₁ * g₂))
        = AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M (d.lift g₁ * d.lift g₂) := by
      rw [d.restrict_lift, map_mul, d.restrict_lift, d.restrict_lift]
    rw [d.π₀_eq_of_restrict_eq h, map_mul]

@[simp]
theorem π_apply (g : d.G) : d.π g = d.π₀ (d.lift g) := rfl

/-- **The coordinate of `g` at the layer `h`**, read in `A`. -/
def coord (h : H) (g : d.G) : A := d.galA (d.coordAut h (d.lift g))

@[simp]
theorem coord_one (h : H) : d.coord h 1 = 1 := by
  have hres : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M (d.lift 1)
      = AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M 1 := by
    rw [d.restrict_lift, map_one]
  rw [coord, d.coordAut_eq_of_restrict_eq hres h, d.coordAut_one, map_one]

/-- **The wreath cocycle identity for the coordinates.** -/
theorem coord_mul (h : H) (g₁ g₂ : d.G) :
    d.coord h (g₁ * g₂) = d.coord (d.π g₂ * h) g₁ * d.coord h g₂ := by
  have hres : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M (d.lift (g₁ * g₂))
      = AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.M (d.lift g₁ * d.lift g₂) := by
    rw [d.restrict_lift, map_mul, d.restrict_lift, d.restrict_lift]
  rw [coord, d.coordAut_eq_of_restrict_eq hres h, d.coordAut_mul, map_mul]
  rfl

/-- **An automorphism with trivial image in `H` and trivial coordinates is the identity**: it
fixes `θ` and every layer, and those generate the compositum. -/
theorem eq_one_of_π_of_coord (g : d.G) (hπ : d.π g = 1) (hc : ∀ h, d.coord h g = 1) : g = 1 := by
  have hπ₀ : d.π₀ (d.lift g) = 1 := hπ
  have hres : AlgEquiv.restrictNormalHom (F := QT) (K₁ := QTbar) ↥d.E (d.lift g) = 1 :=
    d.galH.injective (by rw [← π₀_apply, hπ₀, map_one])
  have hE : ∀ x ∈ d.E, d.lift g x = x := by
    intro x hx
    have h1 := AlgEquiv.restrictNormalHom_apply d.E (d.lift g) ⟨x, hx⟩
    rw [hres] at h1
    exact h1.symm
  have hlayer : ∀ (h : H) (n : d.N), d.lift g (d.ε h n) = d.ε h n := by
    intro h n
    have hcoord : d.coordAut h (d.lift g) = 1 :=
      d.galA.injective (by rw [← coord, hc h, map_one])
    rw [d.coordAut_spec h (d.lift g) n, hcoord, hπ₀, one_mul]
    rfl
  have hfix : d.M ≤ IntermediateField.fixedField
      (Subgroup.closure ({d.lift g} : Set (QTbar ≃ₐ[QT] QTbar))) := by
    rw [M, IntermediateField.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact mem_fixedField_closure_singleton (hE _ (SetLike.coe_mem d.θ))
    · obtain ⟨_, ⟨h, rfl⟩, n, rfl⟩ := hx
      exact mem_fixedField_closure_singleton (hlayer h n)
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.one_apply]
  apply Subtype.ext
  have h3 := AlgEquiv.restrictNormalHom_apply d.M (d.lift g) y
  rw [d.restrict_lift] at h3
  rw [h3]
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hfix (SetLike.coe_mem y)) _
    (Subgroup.subset_closure rfl)

/-! ## The wreath product -/

/-- **The coordinate homomorphism of the compositum into the wreath product `A ≀ᵣ H`.** -/
def wreathHom : d.G →* A ≀ᵣ H :=
  RegularWreathProduct.coordHom d.π d.coord d.coord_mul d.coord_one

@[simp]
theorem wreathHom_right (g : d.G) : (d.wreathHom g).right = d.π g := rfl

@[simp]
theorem wreathHom_left (g : d.G) :
    (d.wreathHom g).left = fun x => d.coord ((d.π g)⁻¹ * x) g := rfl

/-- **The coordinate homomorphism is injective.** -/
theorem wreathHom_injective : Function.Injective d.wreathHom :=
  RegularWreathProduct.coordHom_injective d.π d.coord d.coord_mul d.coord_one
    d.eq_one_of_π_of_coord

/-- **The Galois group of the compositum is the wreath product `A ≀ᵣ H`** as soon as it has the
right order. -/
theorem nonempty_mulEquiv_of_card
    (hcard : Nat.card d.G = Nat.card A ^ Nat.card H * Nat.card H) :
    Nonempty (d.G ≃* A ≀ᵣ H) := by
  haveI := d.finite_H
  haveI := d.finite_A
  exact RegularWreathProduct.mulEquiv_of_injective_of_card d.wreathHom d.wreathHom_injective hcard

end ConjugateData

/-! ## Construction from two regular realizations -/

/-- A finite separable subextension of `ℚ̄(T) / ℚ(T)` has a primitive element that is
transcendental over `ℚ`: if a given primitive element happens to be algebraic, translating it by
the variable produces another one that is not. -/
theorem exists_transcendental_primitive_element (E : IntermediateField QT QTbar)
    [FiniteDimensional QT ↥E] [Algebra.IsSeparable QT ↥E] :
    ∃ θ : ↥E, IntermediateField.adjoin QT {θ} = ⊤ ∧ Transcendental ℚ θ := by
  obtain ⟨θ₀, hθ₀⟩ := Field.exists_primitive_element QT ↥E
  have hX : Transcendental ℚ (algebraMap QT ↥E RatFunc.X) :=
    transcendental_ringHom (algebraMap QT ↥E) transcendental_ratFunc_X
  by_cases hcase : Transcendental ℚ θ₀
  · exact ⟨θ₀, hθ₀, hcase⟩
  · have hmem : θ₀ ∈ IntermediateField.adjoin QT ({θ₀ + algebraMap QT ↥E RatFunc.X} : Set ↥E) := by
      have h1 : θ₀ + algebraMap QT ↥E RatFunc.X ∈
          IntermediateField.adjoin QT ({θ₀ + algebraMap QT ↥E RatFunc.X} : Set ↥E) :=
        IntermediateField.mem_adjoin_simple_self _ _
      have h2 : algebraMap QT ↥E RatFunc.X ∈
          IntermediateField.adjoin QT ({θ₀ + algebraMap QT ↥E RatFunc.X} : Set ↥E) :=
        IntermediateField.algebraMap_mem _ _
      simpa using sub_mem h1 h2
    refine ⟨θ₀ + algebraMap QT ↥E RatFunc.X, ?_, fun halg => ?_⟩
    · rw [eq_top_iff, ← hθ₀, IntermediateField.adjoin_le_iff]
      rintro x rfl
      exact hmem
    · refine hX ?_
      have h1 : θ₀ ∈ algebraicClosure ℚ ↥E := mem_algebraicClosure_iff.mpr (not_not.mp hcase)
      have h2 : θ₀ + algebraMap QT ↥E RatFunc.X ∈ algebraicClosure ℚ ↥E :=
        mem_algebraicClosure_iff.mpr halg
      have h3 : algebraMap QT ↥E RatFunc.X ∈ algebraicClosure ℚ ↥E := by
        simpa using sub_mem h2 h1
      exact mem_algebraicClosure_iff.mp h3

/-- **A regular realization of `H` sits inside `ℚ̄(T)`** with a primitive element transcendental
over the rationals.  This is the half of a conjugate configuration that is independent of the
translation, and it is produced on its own because the translations that have to be avoided can
only be named once the primitive element is known. -/
theorem exists_baseField {H : Type*} [Group H] (hH : IsRegularInverseGalois H) :
    ∃ (E : IntermediateField QT QTbar) (_ : FiniteDimensional QT ↥E) (_ : IsGalois QT ↥E)
      (_galH : (↥E ≃ₐ[QT] ↥E) ≃* H) (θ : ↥E), algebraicClosure ℚ ↥E = ⊥ ∧
        IntermediateField.adjoin QT {θ} = ⊤ ∧ Transcendental ℚ θ := by
  obtain ⟨L₁, _, _, _, _, _, _, hreg₁, ⟨φ₁⟩⟩ := hH
  haveI : Algebra.IsAlgebraic QT L₁ := Algebra.IsAlgebraic.of_finite _ _
  let i₁ : L₁ →ₐ[QT] QTbar := IsAlgClosed.lift
  let ψ₁ := AlgEquiv.ofInjectiveField i₁
  haveI : IsGalois QT ↥i₁.fieldRange := IsGalois.of_algEquiv ψ₁
  haveI : FiniteDimensional QT ↥i₁.fieldRange :=
    FiniteDimensional.of_injective ψ₁.symm.toLinearMap ψ₁.symm.injective
  obtain ⟨θ, hgen, hθ⟩ := exists_transcendental_primitive_element i₁.fieldRange
  exact ⟨i₁.fieldRange, inferInstance, inferInstance, ψ₁.autCongr.symm.trans φ₁, θ,
    Rigidity.RET.algebraicClosure_eq_bot_of_ringHom ψ₁.symm.toRingHom hreg₁, hgen, hθ⟩

/-- **The layers over a prescribed translate exist.**  A translate `h(θ) + c` of a conjugate of the
primitive element is again transcendental over `ℚ`, so it presents `ℚ(x)` inside `E`, and the
resulting embedding of the base extends to any finite extension of it because `ℚ̄(T)` is
algebraically closed. -/
theorem exists_epsilon {H : Type*} [Group H] (E : IntermediateField QT QTbar)
    (galH : (↥E ≃ₐ[QT] ↥E) ≃* H) {θ : ↥E} (hθ : Transcendental ℚ θ)
    (L₂ : Type) [Field L₂] [Algebra QT L₂] [FiniteDimensional QT L₂] (c : ℚ) :
    ∃ ε : H → (L₂ →+* QTbar), (∀ (h : H) (r : QT), ε h (algebraMap QT L₂ r) ∈ E) ∧
      ∀ h : H, ε h (algebraMap QT L₂ RatFunc.X)
        = ((galH.symm h θ : ↥E) : QTbar) + (c : QTbar) := by
  have hex : ∀ h : H, ∃ e : L₂ →+* QTbar,
      (∀ r : QT, e (algebraMap QT L₂ r) ∈ E) ∧
      e (algebraMap QT L₂ RatFunc.X) = ((galH.symm h θ : ↥E) : QTbar) + (c : QTbar) := by
    intro h
    set y : ↥E := galH.symm h θ + (c : ↥E) with hyd
    have hyt : Transcendental ℚ y := by
      have h1 : ((1 : ℚ) : ↥E) * (galH.symm h θ : ↥E) + (c : ↥E) = y := by
        rw [hyd, Rat.cast_one, one_mul]
      rw [← h1]
      exact transcendental_linear one_ne_zero
        (transcendental_ringHom (galH.symm h).toAlgHom.toRingHom hθ)
    have hginj : Function.Injective
        ⇑((Polynomial.aeval y : ℚ[X] →ₐ[ℚ] ↥E).toRingHom) :=
      transcendental_iff_injective.mp hyt
    set tw : QT →+* ↥E := IsFractionRing.lift hginj with htw
    have htwX : tw RatFunc.X = y := by
      rw [htw, ← RatFunc.algebraMap_X, IsFractionRing.lift_algebraMap]
      simp
    set twb : QT →+* QTbar := (IntermediateField.val E).toRingHom.comp tw with htwb
    have hlift : ∃ e : L₂ →+* QTbar, ∀ r : QT, e (algebraMap QT L₂ r) = twb r := by
      letI : Algebra QT QTbar := twb.toAlgebra
      haveI : Algebra.IsAlgebraic QT L₂ := Algebra.IsAlgebraic.of_finite _ _
      exact ⟨(IsAlgClosed.lift : L₂ →ₐ[QT] QTbar).toRingHom, fun r => AlgHom.commutes _ r⟩
    obtain ⟨e, he⟩ := hlift
    refine ⟨e, fun r => ?_, ?_⟩
    · rw [he r, htwb]
      exact SetLike.coe_mem (tw r)
    · rw [he RatFunc.X, htwb, RingHom.comp_apply, htwX, hyd, map_add, map_ratCast]
      rfl
  choose ε hεmem hεX using hex
  exact ⟨ε, hεmem, hεX⟩

/-- **A regular realization of `H` and a regular realization of an abelian group `A` assemble
into a conjugate configuration**, for any rational translation `x ↦ x + c`. -/
theorem nonempty_conjugateData {H A : Type*} [Group H] [CommGroup A]
    (hH : IsRegularInverseGalois H) (hA : IsRegularInverseGalois A) (c : ℚ) :
    Nonempty (ConjugateData H A) := by
  obtain ⟨E, _, _, galH, θ, hregE, hgen, hθ⟩ := exists_baseField hH
  obtain ⟨L₂, _, _, _, _, _, _, hreg₂, ⟨φ₂⟩⟩ := hA
  obtain ⟨ε, hεmem, hεX⟩ := exists_epsilon E galH hθ L₂ c
  exact ⟨{ N := L₂
           regular_N := hreg₂
           galA := φ₂
           E := E
           regular_E := hregE
           galH := galH
           θ := θ
           adjoin_θ := hgen
           transcendental_θ := hθ
           c := c
           ε := ε
           ε_mem := hεmem
           ε_X := hεX }⟩

end Rigidity.RET.Wreath
