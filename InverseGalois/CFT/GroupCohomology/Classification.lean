import Mathlib
import InverseGalois.CFT.GroupCohomology.OfCocycle
import InverseGalois.CFT.GroupCohomology.ToCocycle

/-!
# `H²` classifies group extensions with abelian kernel

Let `G` be a group acting on an abelian group `M` by group automorphisms.  Two constructions are
already available: the extension `groupCohomology.ofMulCocycle₂.toGroupExtension` attached to a
multiplicative `2`-cocycle, and the class `GroupExtension.cohomologyClass` in
`groupCohomology.H2` attached to an extension of `G` by `M`.  This file shows that the two are
mutually inverse and deduces the classification of extensions by `H²`.

## Main definitions

* `groupCohomology.ofMulCocycle₂.tautSection`: the section `g ↦ ⟨1, g⟩` of the extension attached
  to a cocycle.
* `groupCohomology.equivToGroupExtensionFactorSet`: an extension inducing the given action is
  equivalent to the extension attached to the factor set of any of its sections.

## Main results

* `groupCohomology.ofMulCocycle₂.conjActHom_toGroupExtension` and
  `groupCohomology.ofMulCocycle₂.mulDistribMulAction_toGroupExtension`: the extension attached to a
  cocycle induces the action of `G` on `M` one started with.
* `groupCohomology.ofMulCocycle₂.factorSet_tautSection`: the factor set of the tautological
  section of the extension attached to `f` is `f` itself.
* `groupCohomology.cohomologyClass_toGroupExtension`: the class of the extension attached to `f`
  is the class of `f`.
* `groupCohomology.exists_isMulCocycle₂_H2π_eq` and
  `groupCohomology.exists_groupExtension_cohomologyClass`: every class in `H²` is the class of an
  extension.
* `groupCohomology.forall_splits_iff_subsingleton_H2`: `H²(G, M)` vanishes if and only if every
  extension of `G` by `M` inducing the given action splits.
-/

namespace groupCohomology

/-! ### From a cocycle to an extension and back -/

namespace ofMulCocycle₂

variable {G M : Type*} [Group G] [CommGroup M] [inst : MulDistribMulAction G M] {f : G × G → M}

/-- The tautological set-theoretic section `g ↦ ⟨1, g⟩` of the extension attached to a
multiplicative `2`-cocycle. -/
def tautSection (hf : IsMulCocycle₂ f) : (toGroupExtension hf).Section where
  toFun g := ⟨1, g⟩
  rightInverse_rightHom _ := rfl

variable {hf : IsMulCocycle₂ f}

@[simp]
theorem tautSection_apply (g : G) : tautSection hf g = ⟨1, g⟩ := rfl

/-- The action of `G` on `M` induced by the extension attached to a multiplicative `2`-cocycle is
the action one started with. -/
theorem conjActHom_toGroupExtension (g : G) (m : M) :
    (toGroupExtension hf).conjActHom g m = g • m := by
  have h : (toGroupExtension hf).conjActHom g = (toGroupExtension hf).conjAct ⟨1, g⟩ :=
    (toGroupExtension hf).conjActHom_rightHom ⟨1, g⟩
  rw [h, conjAct_inl]

/-- The `MulDistribMulAction` induced by the extension attached to a multiplicative `2`-cocycle is
the one it was built from. -/
theorem mulDistribMulAction_toGroupExtension :
    (toGroupExtension hf).mulDistribMulAction = inst := by
  apply MulDistribMulAction.ext
  funext g m
  exact conjActHom_toGroupExtension g m

/-- The factor set of the tautological section of the extension attached to a multiplicative
`2`-cocycle `f` is `f` itself. -/
theorem factorSet_tautSection (g h : G) :
    (toGroupExtension hf).factorSet (tautSection hf) (g, h) = f (g, h) := by
  apply (toGroupExtension hf).inl_injective
  rw [GroupExtension.inl_factorSet]
  have key := smul_map_inv_div_map_inv_of_isMulCocycle₂ hf (g * h)
  rw [map_one_snd_of_isMulCocycle₂ hf (g * h), div_eq_div_iff_mul_eq_mul] at key
  refine ext ?_ (by simp [mul_assoc])
  simp only [tautSection_apply, toGroupExtension_inl_apply, mk_fst, mul_fst, mul_snd,
    inv_fst, inv_snd, smul_one, mul_one, one_mul, smul_mul', smul_inv', inv_one]
  apply Additive.ofMul.injective
  replace key := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at key ⊢
  linear_combination (norm := abel) -key

/-- The factor set of the tautological section of the extension attached to a multiplicative
`2`-cocycle `f`, as a function on `G × G`, is `f`. -/
theorem factorSet_tautSection_eq :
    (toGroupExtension hf).factorSet (tautSection hf) = f :=
  funext fun p ↦ factorSet_tautSection p.1 p.2

end ofMulCocycle₂

/-! ### From an extension to a cocycle and back -/

section Equiv

variable {G M E : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] [Group E]
  (S : GroupExtension M E G) (hS : ∀ (g : G) (m : M), S.conjActHom g m = g • m) (σ : S.Section)

include hS

/-- If an extension induces the ambient action of `G` on `M`, the factor set of any of its
sections is a multiplicative `2`-cocycle for the ambient action. -/
theorem isMulCocycle₂_factorSet_of_conjActHom : IsMulCocycle₂ (S.factorSet σ) := fun g h j ↦ by
  have h1 := S.isMulCocycle₂_factorSet σ g h j
  rw [← hS]
  exact h1

/-- The homomorphism `⟨m, g⟩ ↦ S.inl m * σ g` from the extension attached to the factor set of a
section `σ` to the original extension. -/
def factorSetHom :
    ofMulCocycle₂ (isMulCocycle₂_factorSet_of_conjActHom S hS σ) →* E where
  toFun x := S.inl x.fst * σ x.snd
  map_one' := by
    have h1 : S.inl (S.factorSet σ (1, 1)) = σ 1 := by
      rw [GroupExtension.inl_factorSet, one_mul, mul_inv_cancel_right]
    show S.inl ((S.factorSet σ (1, 1))⁻¹) * σ 1 = 1
    rw [map_inv, h1, inv_mul_cancel]
  map_mul' x y := by
    have hc : S.inl (x.snd • y.fst) = σ x.snd * S.inl y.fst * (σ x.snd)⁻¹ := by
      rw [← hS, S.inl_conjActHom_section σ]
    have h2 : S.inl (S.factorSet σ (x.snd, y.snd)) * σ (x.snd * y.snd) = σ x.snd * σ y.snd :=
      (S.section_mul σ x.snd y.snd).symm
    show S.inl (x.fst * x.snd • y.fst * S.factorSet σ (x.snd, y.snd)) * σ (x.snd * y.snd)
      = S.inl x.fst * σ x.snd * (S.inl y.fst * σ y.snd)
    rw [map_mul, map_mul, mul_assoc (S.inl x.fst * S.inl (x.snd • y.fst)), h2, hc]
    group

@[simp]
theorem factorSetHom_apply (x : ofMulCocycle₂ (isMulCocycle₂_factorSet_of_conjActHom S hS σ)) :
    factorSetHom S hS σ x = S.inl x.fst * σ x.snd := rfl

/-- Every extension inducing the given action of `G` on `M` is equivalent to the extension
attached to the factor set of any of its sections. -/
noncomputable def equivToGroupExtensionFactorSet :
    (ofMulCocycle₂.toGroupExtension
      (isMulCocycle₂_factorSet_of_conjActHom S hS σ)).Equiv S :=
  GroupExtension.Equiv.ofMonoidHom (factorSetHom S hS σ)
    (by
      have h1 : S.inl (S.factorSet σ (1, 1)) = σ 1 := by
        rw [GroupExtension.inl_factorSet, one_mul, mul_inv_cancel_right]
      ext m
      show S.inl (m * (S.factorSet σ (1, 1))⁻¹) * σ 1 = S.inl m
      rw [map_mul, map_inv, h1]
      group)
    (by
      ext x
      show S.rightHom (S.inl x.fst * σ x.snd) = x.snd
      rw [map_mul, S.rightHom_inl, one_mul, GroupExtension.Section.rightHom_section])

end Equiv

/-! ### The cohomology class of the extension attached to a cocycle -/

section Universe

variable {G M : Type} [Group G] [CommGroup M]

/-- Two equal `MulDistribMulAction`s give the same class in `H²` for a given cocycle. -/
theorem heq_H2π_cocyclesOfIsMulCocycle₂ {i j : MulDistribMulAction G M} (h : i = j)
    {f : G × G → M} (hi : letI := i; IsMulCocycle₂ f) (hj : letI := j; IsMulCocycle₂ f) :
    HEq (letI := i; H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hi))
      (letI := j; H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hj)) := by
  subst h
  rfl

variable [inst : MulDistribMulAction G M] {f : G × G → M}

open ofMulCocycle₂ in
/-- A multiplicative `2`-cocycle is still one for the action induced by the extension it
defines. -/
theorem isMulCocycle₂_induced_toGroupExtension (hf : IsMulCocycle₂ f) :
    letI := (toGroupExtension hf).mulDistribMulAction
    IsMulCocycle₂ f := by
  letI := (toGroupExtension hf).mulDistribMulAction
  show IsMulCocycle₂ f
  intro g h j
  simp only [GroupExtension.mulDistribMulAction_smul, conjActHom_toGroupExtension]
  exact hf g h j

open ofMulCocycle₂ in
/-- The class of the extension attached to a multiplicative `2`-cocycle `f` is the class of `f`,
computed for the action induced by that extension. -/
theorem cohomologyClass_toGroupExtension (hf : IsMulCocycle₂ f) :
    (toGroupExtension hf).cohomologyClass
      = H2π _ (@cocyclesOfIsMulCocycle₂ G M _ _ (toGroupExtension hf).mulDistribMulAction f
          (isMulCocycle₂_induced_toGroupExtension hf)) := by
  rw [(toGroupExtension hf).cohomologyClass_eq (tautSection hf)]
  congr 1
  ext g h
  show Additive.ofMul ((toGroupExtension hf).factorSet (tautSection hf) (g, h))
      = Additive.ofMul (f (g, h))
  rw [factorSet_tautSection]

open ofMulCocycle₂ in
/-- The class of the extension attached to a multiplicative `2`-cocycle `f` is the class of `f`,
after identifying the induced action with the ambient one. -/
theorem heq_cohomologyClass_toGroupExtension (hf : IsMulCocycle₂ f) :
    HEq (toGroupExtension hf).cohomologyClass
      (H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf)) := by
  rw [cohomologyClass_toGroupExtension hf]
  exact heq_H2π_cocyclesOfIsMulCocycle₂ (mulDistribMulAction_toGroupExtension (hf := hf))
    (isMulCocycle₂_induced_toGroupExtension hf) hf

/-! ### Surjectivity of the classification -/

/-- Every class in `H²` is the class of a multiplicative `2`-cocycle. -/
theorem exists_isMulCocycle₂_H2π_eq (x : H2 (Rep.ofMulDistribMulAction G M)) :
    ∃ (f : G × G → M) (hf : IsMulCocycle₂ f),
      H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) = x := by
  induction x using H2_induction_on with
  | _ c =>
    refine ⟨Additive.toMul ∘ (c : G × G → Additive M),
      isMulCocycle₂_of_mem_cocycles₂ _ c.2, ?_⟩
    congr 1

/-- Every class in `H²` is the class of a group extension of `G` by `M` inducing the given
action. -/
theorem exists_groupExtension_cohomologyClass (x : H2 (Rep.ofMulDistribMulAction G M)) :
    ∃ (E : Type) (_ : Group E) (S : GroupExtension M E G),
      (∀ (g : G) (m : M), S.conjActHom g m = g • m) ∧ HEq S.cohomologyClass x := by
  obtain ⟨f, hf, hx⟩ := exists_isMulCocycle₂_H2π_eq x
  exact ⟨ofMulCocycle₂ hf, ofMulCocycle₂.instGroup, ofMulCocycle₂.toGroupExtension hf,
    fun g m ↦ ofMulCocycle₂.conjActHom_toGroupExtension g m,
    hx ▸ heq_cohomologyClass_toGroupExtension hf⟩

/-! ### The classification -/

open ofMulCocycle₂ in
/-- A splitting of the extension attached to a multiplicative `2`-cocycle `f` exhibits `f` as a
multiplicative `2`-coboundary. -/
theorem isMulCoboundary₂_of_splitting {hf : IsMulCocycle₂ f}
    (s : (toGroupExtension hf).Splitting) : IsMulCoboundary₂ f := by
  have hsnd : ∀ g : G, (s g : ofMulCocycle₂ hf).snd = g := fun g ↦ s.rightInverse_rightHom g
  refine ⟨fun g ↦ ((s g : ofMulCocycle₂ hf).fst)⁻¹, fun g h ↦ ?_⟩
  show g • ((s h : ofMulCocycle₂ hf).fst)⁻¹ / ((s (g * h) : ofMulCocycle₂ hf).fst)⁻¹
      * ((s g : ofMulCocycle₂ hf).fst)⁻¹ = f (g, h)
  have key : (s (g * h) : ofMulCocycle₂ hf).fst
      = (s g : ofMulCocycle₂ hf).fst * g • (s h : ofMulCocycle₂ hf).fst * f (g, h) := by
    have hm := congrArg ofMulCocycle₂.fst (map_mul s g h)
    rw [mul_fst, hsnd, hsnd] at hm
    exact hm
  rw [key, div_eq_mul_inv, inv_inv, smul_inv']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- If `H²(G, M)` vanishes, every extension of `G` by `M` inducing the given action splits. -/
theorem nonempty_splitting_of_subsingleton_H2
    (hsub : Subsingleton (H2 (Rep.ofMulDistribMulAction G M)))
    {E : Type} [Group E] (S : GroupExtension M E G)
    (hS : ∀ (g : G) (m : M), S.conjActHom g m = g • m) : Nonempty S.Splitting := by
  obtain σ := S.surjInvRightHom
  have hf : IsMulCocycle₂ (S.factorSet σ) := isMulCocycle₂_factorSet_of_conjActHom S hS σ
  have hzero : H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) = 0 :=
    hsub.elim _ _
  obtain ⟨x, hx⟩ := isMulCoboundary₂_of_mem_coboundaries₂ _ ((H2π_eq_zero_iff _).1 hzero)
  exact ⟨S.splittingOfIsMulCoboundary₂ σ x fun g h ↦ by rw [hS]; exact hx g h⟩

/-- `H²(G, M)` vanishes if and only if every extension of `G` by `M` inducing the given action of
`G` on `M` splits. -/
theorem forall_splits_iff_subsingleton_H2 :
    Subsingleton (H2 (Rep.ofMulDistribMulAction G M)) ↔
      ∀ (E : Type) (_ : Group E) (S : GroupExtension M E G),
        (∀ (g : G) (m : M), S.conjActHom g m = g • m) → Nonempty S.Splitting := by
  constructor
  · intro hsub E _ S hS
    exact nonempty_splitting_of_subsingleton_H2 hsub S hS
  · intro h
    have hzero : ∀ x : H2 (Rep.ofMulDistribMulAction G M), x = 0 := by
      intro x
      obtain ⟨f, hf, hx⟩ := exists_isMulCocycle₂_H2π_eq x
      obtain ⟨s⟩ := h (ofMulCocycle₂ hf) ofMulCocycle₂.instGroup
        (ofMulCocycle₂.toGroupExtension hf) fun g m ↦
          ofMulCocycle₂.conjActHom_toGroupExtension g m
      rw [← hx, H2π_eq_zero_iff]
      exact (coboundariesOfIsMulCoboundary₂ (isMulCoboundary₂_of_splitting s)).2
    exact ⟨fun a b ↦ by rw [hzero a, hzero b]⟩

end Universe

end groupCohomology
