/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The first homology of the contragredient representation is dual to the first cohomology

Cochains and chains are put in duality by evaluation: a function on a set with values in a module
is paired with a finitely supported family of functionals on that module by evaluating the one
against the other, one index at a time, and summing.  Over a field the pairing is nondegenerate on
both sides, and when the index set is finite and the module finite dimensional every functional on
either side is represented by an element of the other.

For a representation `A` of a group `G` this pairing matches the inhomogeneous cochains of `A` with
the inhomogeneous chains of the contragredient representation, and the two differentials in the
relevant range are adjoint: the differential from the coefficients to the one cochains is adjoint
to the differential from the one chains to the coefficients, and the differential from the one
cochains to the two cochains is adjoint to the differential from the two chains to the one chains.
Cocycles are therefore the annihilator of the boundaries and cycles the annihilator of the
coboundaries, and for a finite group and finite dimensional coefficients the induced pairing of
`H¹(G, A)` with `H₁(G, A*)` is perfect.

## Main definitions

* `InverseGalois.CFT.evalPairing`: the evaluation pairing of functions on a set with finitely
  supported families of functionals.
* `InverseGalois.CFT.dualRep`: the contragredient of a representation.
* `InverseGalois.CFT.cocyclePairing`: the evaluation pairing restricted to the one cocycles of a
  representation and the one cycles of its contragredient.
* `InverseGalois.CFT.h1PairingQ`: the pairing of the first homology of the contragredient
  representation with the first cohomology, presented on quotients of cycles by boundaries.

## Main results

* `InverseGalois.CFT.evalPairing_d₀₁` and `InverseGalois.CFT.evalPairing_d₁₂`: the differentials
  of the cochain complex of a representation and of the chain complex of its contragredient are
  adjoint for the evaluation pairing.
* `InverseGalois.CFT.h1DualEquiv`: **the first homology of the contragredient representation is
  canonically the dual of the first cohomology**, for a finite group acting on a finite dimensional
  space.

## Tags

group cohomology, group homology, duality, contragredient representation
-/

universe u

namespace InverseGalois.CFT

open Module (Dual)

/-! ### The evaluation pairing -/

section Pairing

variable (k : Type u) [Field k] {α M : Type u} [AddCommGroup M] [Module k M]

/-- The evaluation pairing between functions on a set with values in a module and finitely
supported families of functionals on that module. -/
noncomputable def evalPairing : (α → M) →ₗ[k] (α →₀ Dual k M) →ₗ[k] k where
  toFun f := Finsupp.lsum k fun a ↦ LinearMap.applyₗ (f a)
  map_add' f g := by
    ext a φ
    simp
  map_smul' c f := by
    ext a φ
    simp

@[simp]
theorem evalPairing_single (f : α → M) (a : α) (φ : Dual k M) :
    evalPairing k f (Finsupp.single a φ) = φ (f a) := by
  simp [evalPairing]

theorem evalPairing_eq_sum [Fintype α] (f : α → M) (x : α →₀ Dual k M) :
    evalPairing k f x = ∑ a : α, x a (f a) :=
  Finsupp.sum_fintype _ _ fun _ ↦ rfl

theorem evalPairing_sub (f : α → M) (x y : α →₀ Dual k M) :
    evalPairing k f (x - y) = evalPairing k f x - evalPairing k f y := by
  have h := congrArg (evalPairing k f) (sub_add_cancel x y)
  rw [map_add] at h
  exact eq_sub_of_add_eq h

variable {k}

theorem evalPairing_piSingle [DecidableEq α] (a : α) (m : M) (x : α →₀ Dual k M) :
    evalPairing k (Pi.single a m) x = x a m := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b φ =>
    rcases eq_or_ne b a with rfl | hb
    · simp
    · simp [Finsupp.single_eq_of_ne (Ne.symm hb), Pi.single_eq_of_ne hb]

/-- The evaluation pairing is nondegenerate in the chain variable. -/
theorem eq_zero_of_forall_evalPairing_eq_zero {x : α →₀ Dual k M}
    (h : ∀ f : α → M, evalPairing k f x = 0) : x = 0 := by
  classical
  refine Finsupp.ext fun a ↦ LinearMap.ext fun m ↦ ?_
  simp only [Finsupp.coe_zero, Pi.zero_apply, LinearMap.zero_apply]
  rw [← evalPairing_piSingle a m x]
  exact h _

/-- The evaluation pairing is nondegenerate in the cochain variable. -/
theorem eq_zero_of_forall_evalPairing_eq_zero' {f : α → M}
    (h : ∀ x : α →₀ Dual k M, evalPairing k f x = 0) : f = 0 := by
  funext a
  refine (Module.forall_dual_apply_eq_zero_iff k (f a)).1 fun φ ↦ ?_
  simpa using h (Finsupp.single a φ)

/-- Over a finite index set every functional on the cochains is given by pairing with a chain. -/
theorem exists_forall_evalPairing_eq [Finite α] (ψ : Dual k (α → M)) :
    ∃ x : α →₀ Dual k M, ∀ f : α → M, evalPairing k f x = ψ f := by
  classical
  have : Fintype α := Fintype.ofFinite α
  refine ⟨Finsupp.equivFunOnFinite.symm fun a ↦ ψ ∘ₗ LinearMap.single k (fun _ : α ↦ M) a,
    fun f ↦ ?_⟩
  rw [evalPairing_eq_sum]
  simp only [Finsupp.coe_equivFunOnFinite_symm, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.single_apply]
  rw [← map_sum, LinearMap.sum_single_apply]

/-- Over a finite index set and with finite dimensional coefficients every functional on the chains
is given by pairing with a cochain. -/
theorem exists_forall_evalPairing_eq' [Finite α] [FiniteDimensional k M]
    (ψ : Dual k (α →₀ Dual k M)) :
    ∃ f : α → M, ∀ x : α →₀ Dual k M, evalPairing k f x = ψ x := by
  refine ⟨fun a ↦ (Module.evalEquiv k M).symm (ψ ∘ₗ Finsupp.lsingle a), fun x ↦ ?_⟩
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single a φ => simp

end Pairing

/-! ### The contragredient representation -/

section Duality

variable {k G : Type u} [Field k] [Group G] (A : Rep k G)

/-- The contragredient of a representation: the dual space, with a group element acting through
its inverse. -/
noncomputable abbrev dualRep : Rep k G := Rep.of (Representation.dual A.ρ)

@[simp]
theorem dualRep_ρ_apply (g : G) (φ : Dual k A) (a : A) :
    (dualRep A).ρ g φ a = φ (A.ρ g⁻¹ a) := rfl

/-! ### Adjointness of the differentials -/

/-- The differential from the coefficients to the one cochains is adjoint to the differential from
the one chains to the coefficients of the contragredient representation. -/
theorem evalPairing_d₀₁ (a : A) (x : G →₀ Dual k A) :
    evalPairing k (groupCohomology.d₀₁ A a) x = groupHomology.d₁₀ (dualRep A) x a := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g φ =>
    simp [groupHomology.d₁₀_single (A := dualRep A), Module.Dual.transpose_apply]

/-- The differential from the one cochains to the two cochains is adjoint to the differential from
the two chains to the one chains of the contragredient representation. -/
theorem evalPairing_d₁₂ (f : G → A) (y : G × G →₀ Dual k A) :
    evalPairing k (groupCohomology.d₁₂ A f) y
      = evalPairing k f (groupHomology.d₂₁ (dualRep A) y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g φ =>
    have h : groupHomology.d₂₁ (dualRep A) (Finsupp.single g φ)
        = (Finsupp.single g.2 ((dualRep A).ρ g.1⁻¹ φ)
            - Finsupp.single (g.1 * g.2) φ + Finsupp.single g.1 φ : G →₀ Dual k ↑A.V) := by
      rw [groupHomology.d₂₁_single (A := dualRep A)]
    rw [h, map_add, evalPairing_sub]
    simp [Module.Dual.transpose_apply]

/-! ### Cocycles annihilate boundaries, cycles annihilate coboundaries -/

variable {A}

/-- A cycle of the contragredient representation annihilates the coboundaries. -/
theorem evalPairing_eq_zero_of_mem_coboundaries₁ {f : G → A}
    (hf : f ∈ groupCohomology.coboundaries₁ A) {x : G →₀ Dual k A}
    (hx : x ∈ groupHomology.cycles₁ (dualRep A)) : evalPairing k f x = 0 := by
  obtain ⟨a, rfl⟩ := hf
  have hx' : groupHomology.d₁₀ (dualRep A) x = 0 := hx
  rw [evalPairing_d₀₁, hx']
  rfl

/-- A cocycle annihilates the boundaries of the contragredient representation. -/
theorem evalPairing_eq_zero_of_mem_boundaries₁ {f : G → A}
    (hf : f ∈ groupCohomology.cocycles₁ A) {x : G →₀ Dual k A}
    (hx : x ∈ groupHomology.boundaries₁ (dualRep A)) : evalPairing k f x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have hf' : groupCohomology.d₁₂ A f = 0 := hf
  rw [← evalPairing_d₁₂, hf']
  simp

variable (A)
variable [Finite G] [FiniteDimensional k A]

/-- A cycle of the contragredient representation annihilating every cocycle is a boundary. -/
theorem mem_boundaries₁_of_forall_evalPairing_eq_zero {x : G →₀ Dual k A}
    (h : ∀ f ∈ groupCohomology.cocycles₁ A, evalPairing k f x = 0) :
    x ∈ groupHomology.boundaries₁ (dualRep A) := by
  by_contra hx
  obtain ⟨ψ, hψ, hbot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx (by infer_instance)
  obtain ⟨f, hf⟩ := exists_forall_evalPairing_eq' ψ
  have hker : ∀ y ∈ groupHomology.boundaries₁ (dualRep A), ψ y = 0 := by
    intro y hy
    have hmem : ψ y ∈ Submodule.map ψ (groupHomology.boundaries₁ (dualRep A)) :=
      Submodule.mem_map_of_mem hy
    rw [hbot] at hmem
    simpa using hmem
  have hcoc : f ∈ groupCohomology.cocycles₁ A := by
    have hd : groupCohomology.d₁₂ A f = 0 := by
      refine eq_zero_of_forall_evalPairing_eq_zero' (k := k) fun y ↦ ?_
      rw [evalPairing_d₁₂, hf]
      exact hker _ ⟨y, rfl⟩
    exact hd
  exact hψ ((hf x).symm.trans (h f hcoc))

omit [FiniteDimensional k A] in
/-- A functional on the cocycles vanishing on the coboundaries is given by pairing with a cycle of
the contragredient representation. -/
theorem exists_mem_cycles₁_forall_evalPairing_eq
    (ψ : Dual k ↥(groupCohomology.cocycles₁ A))
    (hψ : ∀ f : ↥(groupCohomology.cocycles₁ A),
      f.1 ∈ groupCohomology.coboundaries₁ A → ψ f = 0) :
    ∃ x ∈ groupHomology.cycles₁ (dualRep A),
      ∀ f : ↥(groupCohomology.cocycles₁ A), evalPairing k f.1 x = ψ f := by
  obtain ⟨Ψ, hΨ⟩ := ψ.exists_extend
  obtain ⟨x, hx⟩ := exists_forall_evalPairing_eq Ψ
  have hres : ∀ f : ↥(groupCohomology.cocycles₁ A), Ψ f.1 = ψ f := fun f ↦
    LinearMap.congr_fun hΨ f
  have hcoefs : ∀ a : A, Ψ (groupCohomology.d₀₁ A a) = 0 := by
    intro a
    have hmem : (groupCohomology.d₀₁ A a) ∈ groupCohomology.coboundaries₁ A := ⟨a, rfl⟩
    exact (hres ⟨_, groupCohomology.coboundaries₁_le_cocycles₁ A hmem⟩).trans
      (hψ ⟨_, groupCohomology.coboundaries₁_le_cocycles₁ A hmem⟩ hmem)
  refine ⟨x, ?_, fun f ↦ (hx f.1).trans (hres f)⟩
  show groupHomology.d₁₀ (dualRep A) x = 0
  refine LinearMap.ext fun a ↦ ?_
  rw [LinearMap.zero_apply, ← evalPairing_d₀₁, hx]
  exact hcoefs a

end Duality

/-! ### The first cohomology and homology as quotients of the cocycles and the cycles -/

section Presentation

variable {k G : Type u} [Field k] [Group G] (A : Rep k G)

/-- The coboundaries, as a submodule of the cocycles. -/
noncomputable def coboundariesSub : Submodule k ↥(groupCohomology.cocycles₁ A) :=
  (groupCohomology.coboundaries₁ A).comap (groupCohomology.cocycles₁ A).subtype

@[simp]
theorem mem_coboundariesSub {f : ↥(groupCohomology.cocycles₁ A)} :
    f ∈ coboundariesSub A ↔ f.1 ∈ groupCohomology.coboundaries₁ A := Iff.rfl

/-- The boundaries, as a submodule of the cycles. -/
noncomputable def boundariesSub : Submodule k ↥(groupHomology.cycles₁ A) :=
  (groupHomology.boundaries₁ A).comap (groupHomology.cycles₁ A).subtype

@[simp]
theorem mem_boundariesSub {x : ↥(groupHomology.cycles₁ A)} :
    x ∈ boundariesSub A ↔ x.1 ∈ groupHomology.boundaries₁ A := Iff.rfl

theorem ker_cohomologyH1π :
    LinearMap.ker (groupCohomology.H1π A).hom = coboundariesSub A :=
  Submodule.ext fun f ↦ groupCohomology.H1π_eq_zero_iff f

theorem ker_homologyH1π :
    LinearMap.ker (groupHomology.H1π A).hom = boundariesSub A :=
  Submodule.ext fun x ↦ groupHomology.H1π_eq_zero_iff x

theorem cohomologyH1π_surjective : Function.Surjective (groupCohomology.H1π A).hom :=
  fun y ↦ groupCohomology.H1_induction_on y fun x ↦ ⟨x, rfl⟩

theorem homologyH1π_surjective : Function.Surjective (groupHomology.H1π A).hom :=
  fun y ↦ groupHomology.H1_induction_on y fun x ↦ ⟨x, rfl⟩

/-- The first cohomology is the cocycles modulo the coboundaries. -/
noncomputable def cohomologyQuotEquiv :
    (↥(groupCohomology.cocycles₁ A) ⧸ coboundariesSub A) ≃ₗ[k] groupCohomology.H1 A :=
  (Submodule.quotEquivOfEq _ _ (ker_cohomologyH1π A).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (cohomologyH1π_surjective A))

@[simp]
theorem cohomologyQuotEquiv_mk (f : ↥(groupCohomology.cocycles₁ A)) :
    cohomologyQuotEquiv A (Submodule.Quotient.mk f) = groupCohomology.H1π A f := rfl

/-- The first homology is the cycles modulo the boundaries. -/
noncomputable def homologyQuotEquiv :
    (↥(groupHomology.cycles₁ A) ⧸ boundariesSub A) ≃ₗ[k] groupHomology.H1 A :=
  (Submodule.quotEquivOfEq _ _ (ker_homologyH1π A).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (homologyH1π_surjective A))

@[simp]
theorem homologyQuotEquiv_mk (x : ↥(groupHomology.cycles₁ A)) :
    homologyQuotEquiv A (Submodule.Quotient.mk x) = groupHomology.H1π A x := rfl

end Presentation

/-! ### The pairing of the first homology with the first cohomology -/

section Perfect

variable {k G : Type u} [Field k] [Group G] (A : Rep k G)

/-- The evaluation pairing of a cocycle with a cycle of the contragredient representation. -/
noncomputable def cocyclePairing :
    ↥(groupCohomology.cocycles₁ A) →ₗ[k] Dual k ↥(groupHomology.cycles₁ (dualRep A)) :=
  LinearMap.domRestrict
    ((evalPairing k).compl₂ (groupHomology.cycles₁ (dualRep A)).subtype)
    (groupCohomology.cocycles₁ A)

@[simp]
theorem cocyclePairing_apply (f : ↥(groupCohomology.cocycles₁ A))
    (x : ↥(groupHomology.cycles₁ (dualRep A))) :
    cocyclePairing A f x = evalPairing k f.1 x.1 := rfl

/-- The evaluation pairing of a cocycle with a cycle of the contragredient representation depends
only on the class of the cocycle. -/
noncomputable def cocyclePairingQ :
    (↥(groupCohomology.cocycles₁ A) ⧸ coboundariesSub A) →ₗ[k]
      Dual k ↥(groupHomology.cycles₁ (dualRep A)) :=
  Submodule.liftQ _ (cocyclePairing A) fun _ hf ↦
    LinearMap.ext fun x ↦ evalPairing_eq_zero_of_mem_coboundaries₁ hf x.2

/-- The evaluation pairing of the first homology of the contragredient representation with the
first cohomology, at the level of the presentations by cycles and cocycles. -/
noncomputable def h1PairingQ :
    (↥(groupHomology.cycles₁ (dualRep A)) ⧸ boundariesSub (dualRep A)) →ₗ[k]
      Dual k (↥(groupCohomology.cocycles₁ A) ⧸ coboundariesSub A) :=
  Submodule.liftQ _ (cocyclePairingQ A).flip fun x hx ↦
    LinearMap.ext fun z ↦ by
      obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ z
      exact evalPairing_eq_zero_of_mem_boundaries₁ f.2 hx

@[simp]
theorem h1PairingQ_mk (x : ↥(groupHomology.cycles₁ (dualRep A)))
    (f : ↥(groupCohomology.cocycles₁ A)) :
    h1PairingQ A (Submodule.Quotient.mk x) (Submodule.Quotient.mk f) = evalPairing k f.1 x.1 :=
  rfl

variable [Finite G] [FiniteDimensional k A]

theorem h1PairingQ_injective : Function.Injective (h1PairingQ A) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine mem_boundariesSub _ |>.2 (mem_boundaries₁_of_forall_evalPairing_eq_zero A fun f hf ↦ ?_)
  simpa using LinearMap.congr_fun hz (Submodule.Quotient.mk (⟨f, hf⟩ :
    ↥(groupCohomology.cocycles₁ A)))

omit [FiniteDimensional k A] in
theorem h1PairingQ_surjective : Function.Surjective (h1PairingQ A) := by
  intro ψ
  obtain ⟨x, hx, hval⟩ := exists_mem_cycles₁_forall_evalPairing_eq A
    (ψ ∘ₗ (coboundariesSub A).mkQ) fun f hf ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.mk_eq_zero _ |>.2 ((mem_coboundariesSub A).2 hf), map_zero]
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, LinearMap.ext fun z ↦ ?_⟩
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ z
  simpa using hval f

/-- **The first homology of the contragredient representation is canonically the dual of the first
cohomology**, for a finite group acting on a finite dimensional space. -/
noncomputable def h1DualEquiv :
    groupHomology.H1 (dualRep A) ≃ₗ[k] Dual k (groupCohomology.H1 A) :=
  (homologyQuotEquiv (dualRep A)).symm.trans
    ((LinearEquiv.ofBijective (h1PairingQ A)
      ⟨h1PairingQ_injective A, h1PairingQ_surjective A⟩).trans
        (cohomologyQuotEquiv A).symm.dualMap)

/-- The duality between the first homology of the contragredient representation and the first
cohomology is induced by the evaluation pairing of chains with cochains. -/
theorem h1DualEquiv_apply (x : ↥(groupHomology.cycles₁ (dualRep A)))
    (f : ↥(groupCohomology.cocycles₁ A)) :
    h1DualEquiv A (groupHomology.H1π (dualRep A) x) (groupCohomology.H1π A f)
      = evalPairing k f.1 x.1 := by
  have hx : (homologyQuotEquiv (dualRep A)).symm (groupHomology.H1π (dualRep A) x)
      = Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).2 (homologyQuotEquiv_mk (dualRep A) x).symm
  have hf : (cohomologyQuotEquiv A).symm (groupCohomology.H1π A f)
      = Submodule.Quotient.mk f :=
    (LinearEquiv.symm_apply_eq _).2 (cohomologyQuotEquiv_mk A f).symm
  simp only [h1DualEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    LinearEquiv.ofBijective_apply, hx, hf]
  exact h1PairingQ_mk A x f

end Perfect

end InverseGalois.CFT
