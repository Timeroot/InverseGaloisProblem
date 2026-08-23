import Mathlib

/-!
# Galois descent for vector spaces

Let `L / K` be a finite Galois extension with group `G = Gal(L/K)`, and let `W` be an
`L`-vector space carrying an action of `G` by additive maps which is *semilinear*, in the
sense that `σ • (c • w) = σ c • (σ • w)` for `c : L` and `w : W`.  Speiser's theorem — the
additive form of Hilbert's Theorem 90 — says that `W` is obtained from its `K`-subspace of
invariants by extension of scalars.

The semilinearity condition is packaged as a `Prop`-valued mixin `IsSemilinearGaloisAction`
on top of Mathlib's `DistribMulAction Gal(L/K) W`.  This keeps the group action in the standard
`•` notation (so all of the `MulAction` and `Finset.smul_sum` API applies verbatim) while making
semilinearity inferable, so that the definitions below need not carry it as an explicit
hypothesis.

## Main results

* `InverseGalois.CFT.IsSemilinearGaloisAction`: the semilinearity mixin.
* `InverseGalois.CFT.invariants`: the `K`-subspace `W ^ G` of `G`-invariant vectors.
* `InverseGalois.CFT.average`: the averaged vector `∑ σ, σ • (c • w)`, together with
  `InverseGalois.CFT.average_mem_invariants`: it is `G`-invariant.
* `InverseGalois.CFT.span_invariants_eq_top`: the invariants span `W` over `L`.
* `InverseGalois.CFT.linearIndependent_of_mem_invariants`: a `K`-linearly independent family
  of invariant vectors is `L`-linearly independent.
* `InverseGalois.CFT.descentMap`: the natural `L`-linear map `L ⊗[K] W ^ G → W`.
* `InverseGalois.CFT.descentEquiv`: Galois descent, `L ⊗[K] W ^ G ≃ₗ[L] W`.
* `InverseGalois.CFT.finrank_invariants`: consequently `finrank K W ^ G = finrank L W`.
* `InverseGalois.CFT.baseChangeInvariantsEquiv`: in the split case `W = L ⊗[K] V`, the
  invariants are `1 ⊗ V`, so `(L ⊗[K] V) ^ G ≃ₗ[K] V`.
* `InverseGalois.CFT.invariantsSubalgebra` and `InverseGalois.CFT.descentAlgEquiv`: the same
  descent for a commutative `L`-algebra acted on by ring automorphisms,
  `L ⊗[K] A ^ G ≃ₐ[L] A`.

-/

namespace InverseGalois.CFT

open scoped TensorProduct

section Semilinear

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (W : Type*) [AddCommGroup W] [Module L W] [DistribMulAction Gal(L/K) W]

/-- An action of the Galois group `Gal(L/K)` on an `L`-module `W` is semilinear when
`σ • (c • w) = σ c • (σ • w)` for all scalars `c : L` and all vectors `w : W`. -/
class IsSemilinearGaloisAction : Prop where
  /-- The Galois action twists the `L`-scalars by the automorphism. -/
  smul_smul' (σ : Gal(L/K)) (c : L) (w : W) : σ • (c • w) = σ c • (σ • w)

variable {K L W}

/-- Semilinearity of the Galois action, in usable form. -/
theorem smul_smul_semilinear [IsSemilinearGaloisAction K L W] (σ : Gal(L/K)) (c : L) (w : W) :
    σ • (c • w) = σ c • (σ • w) :=
  IsSemilinearGaloisAction.smul_smul' σ c w

end Semilinear

section Invariants

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {W : Type*} [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W]
variable [DistribMulAction Gal(L/K) W] [IsSemilinearGaloisAction K L W]

/-- A semilinear Galois action is `K`-linear, since `K` is fixed pointwise. -/
theorem smul_comm_algebra (σ : Gal(L/K)) (a : K) (w : W) : σ • (a • w) = a • (σ • w) := by
  rw [← algebraMap_smul L a w, smul_smul_semilinear, AlgEquiv.commutes, algebraMap_smul]

variable (K L W)

/-- The `K`-subspace of vectors of `W` fixed by every element of `Gal(L/K)`.  It is a
`K`-subspace, not an `L`-subspace, because the action is only semilinear. -/
def invariants : Submodule K W where
  carrier := {w : W | ∀ σ : Gal(L/K), σ • w = w}
  add_mem' {x y} hx hy σ := by rw [smul_add, hx σ, hy σ]
  zero_mem' σ := smul_zero σ
  smul_mem' a w hw σ := by rw [smul_comm_algebra, hw]

variable {K L W}

@[simp]
theorem mem_invariants {w : W} : w ∈ invariants K L W ↔ ∀ σ : Gal(L/K), σ • w = w := Iff.rfl

variable (K L W)

/-- The natural `L`-linear map `L ⊗[K] W ^ G → W` sending `c ⊗ w` to `c • w`. -/
noncomputable def descentMap : L ⊗[K] (invariants K L W) →ₗ[L] W :=
  ((invariants K L W).subtype).liftBaseChange L

@[simp]
theorem descentMap_tmul (c : L) (w : invariants K L W) :
    descentMap K L W (c ⊗ₜ w) = c • (w : W) := rfl

end Invariants

section Average

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {W : Type*} [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W]
variable [DistribMulAction Gal(L/K) W] [IsSemilinearGaloisAction K L W]

variable (K L W)

/-- The average of `c • w` over the Galois group, `∑ σ, σ • (c • w)`. -/
noncomputable def average (c : L) (w : W) : W := ∑ σ : Gal(L/K), σ • (c • w)

variable {K L W}

omit [Module K W] [IsScalarTower K L W] in
/-- The averaged vector written with the scalars twisted out in front. -/
theorem average_eq (c : L) (w : W) : average K L W c w = ∑ σ : Gal(L/K), σ c • (σ • w) :=
  Finset.sum_congr rfl fun σ _ => smul_smul_semilinear σ c w

/-- Averaging over the Galois group produces invariant vectors. -/
theorem average_mem_invariants (c : L) (w : W) : average K L W c w ∈ invariants K L W := by
  intro τ
  rw [average, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [smul_smul]
  rfl

end Average

section Descent

/-- Dedekind's linear independence of characters, for the `K`-automorphisms of `L`. -/
theorem linearIndependent_aut (K L : Type*) [Field K] [Field L] [Algebra K L] :
    LinearIndependent L fun σ : Gal(L/K) => σ.toLinearMap :=
  (linearIndependent_toLinearMap K L L).comp (fun σ : Gal(L/K) => (σ : L →ₐ[K] L))
    fun _ _ hσ => AlgEquiv.ext fun x => DFunLike.ext_iff.1 hσ x

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {W : Type*} [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W]
variable [DistribMulAction Gal(L/K) W] [IsSemilinearGaloisAction K L W]

omit [IsGalois K L] in
/-- The invariants of a semilinear Galois action span the whole space over `L`. -/
theorem span_invariants_eq_top :
    Submodule.span L ((invariants K L W : Submodule K W) : Set W) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  by_contra hw
  obtain ⟨f, hfw, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := Submodule.span L
      ((invariants K L W : Submodule K W) : Set W)) hw inferInstance
  have hvanish : ∀ x ∈ invariants K L W, f x = 0 := by
    intro x hx
    have hmap : f x ∈ (Submodule.span L ((invariants K L W : Submodule K W) : Set W)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span hx)
    rw [hf, Submodule.mem_bot] at hmap
    exact hmap
  have hzero : ∑ σ : Gal(L/K), f (σ • w) • σ.toLinearMap = 0 := by
    ext c
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      AlgEquiv.toLinearMap_apply, smul_eq_mul, LinearMap.zero_apply]
    have hsum := hvanish _ (average_mem_invariants c w)
    rw [average_eq, map_sum] at hsum
    rw [← hsum]
    exact Finset.sum_congr rfl fun σ _ => by
      rw [LinearMap.map_smul f (σ c) (σ • w), smul_eq_mul, mul_comm]
  have hone := Fintype.linearIndependent_iff.mp (linearIndependent_aut K L)
    (fun σ => f (σ • w)) hzero 1
  rw [one_smul] at hone
  exact hfw hone

/-- A family of invariant vectors which is `K`-linearly independent is already `L`-linearly
independent.  This is Artin's argument on a shortest nontrivial relation. -/
theorem linearIndependent_of_mem_invariants {ι : Type*} {v : ι → W}
    (hv : ∀ i, v i ∈ invariants K L W) (hli : LinearIndependent K v) :
    LinearIndependent L v := by
  classical
  have key : ∀ n : ℕ, ∀ s : Finset ι, s.card ≤ n → ∀ g : ι → L,
      ∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs _ _ i hi
      rw [Nat.le_zero, Finset.card_eq_zero] at hs
      simp [hs] at hi
    | succ n ih =>
      intro s hs g hg i hi
      by_contra hgi
      set h : ι → L := fun k => (g i)⁻¹ * g k with hh
      have hhi : h i = 1 := by simp [hh, inv_mul_cancel₀ hgi]
      have hsum : ∑ k ∈ s, h k • v k = 0 := by
        simp only [hh, mul_smul]
        rw [← Finset.smul_sum, hg, smul_zero]
      have hfix : ∀ σ : Gal(L/K), ∀ k ∈ s, σ (h k) = h k := by
        intro σ k hk
        rcases eq_or_ne k i with rfl | hki
        · rw [hhi, map_one]
        · have htw : ∑ k ∈ s, σ (h k) • v k = 0 := by
            have hstep : ∑ k ∈ s, σ (h k) • v k = σ • ∑ k ∈ s, h k • v k := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun k _ => by
                rw [smul_smul_semilinear, hv k σ]
            rw [hstep, hsum, smul_zero]
          have h1 : ∑ k ∈ s, (σ (h k) - h k) • v k = 0 := by
            simp only [sub_smul, Finset.sum_sub_distrib, htw, hsum, sub_zero]
          have h2 : ∑ k ∈ s.erase i, (σ (h k) - h k) • v k = 0 := by
            rw [← Finset.sum_erase_add s _ hi, hhi, map_one, sub_self, zero_smul,
              add_zero] at h1
            exact h1
          have hcard : (s.erase i).card ≤ n := by
            rw [Finset.card_erase_of_mem hi]
            omega
          have hker := ih (s.erase i) hcard _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
          rwa [sub_eq_zero] at hker
      have hmem : ∀ k ∈ s, ∃ a : K, algebraMap K L a = h k := fun k hk =>
        (IsGalois.mem_range_algebraMap_iff_fixed (h k)).2 fun σ => hfix σ k hk
      set a : ι → K :=
        fun k => if hk : ∃ b : K, algebraMap K L b = h k then hk.choose else 0 with ha'
      have ha : ∀ k ∈ s, algebraMap K L (a k) = h k := by
        intro k hk
        rw [ha']
        simp only [dif_pos (hmem k hk)]
        exact (hmem k hk).choose_spec
      have hKsum : ∑ k ∈ s, a k • v k = 0 := by
        rw [← hsum]
        exact Finset.sum_congr rfl fun k hk => by rw [← ha k hk, algebraMap_smul]
      have hai := linearIndependent_iff'.mp hli s a hKsum i hi
      rw [← ha i hi, hai, map_zero] at hhi
      exact one_ne_zero hhi.symm
  rw [linearIndependent_iff']
  exact fun s g hg i hi => key s.card s le_rfl g hg i hi

variable (K L W)

omit [IsGalois K L] in
/-- The descent map is surjective, because the invariants span `W` over `L`. -/
theorem descentMap_surjective : Function.Surjective (descentMap K L W) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_invariants_eq_top (K := K) (L := L) (W := W),
    Submodule.span_le]
  rintro x hx
  exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp⟩

/-- The descent map is injective. -/
theorem descentMap_injective : Function.Injective (descentMap K L W) := by
  classical
  set b := Module.Basis.ofVectorSpace K (invariants K L W) with hb
  set B := b.baseChange (S := L) with hB
  have hliK : LinearIndependent K fun i => ((b i : invariants K L W) : W) :=
    b.linearIndependent.map' (invariants K L W).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent L (⇑(descentMap K L W) ∘ B) := by
    have hfun : ⇑(descentMap K L W) ∘ B = fun i => ((b i : invariants K L W) : W) := by
      funext i
      rw [Function.comp_apply, hB, Module.Basis.baseChange_apply, descentMap_tmul, one_smul]
    rw [hfun]
    exact linearIndependent_of_mem_invariants (fun i => (b i).2) hliK
  rw [linearIndependent_iff_injective_finsuppLinearCombination] at hli
  have key : ∀ z, Finsupp.linearCombination L (⇑(descentMap K L W) ∘ B) (B.repr z)
      = descentMap K L W z := by
    intro z
    rw [← Finsupp.apply_linearCombination, Module.Basis.linearCombination_repr]
  intro x y hxy
  refine B.repr.injective (hli ?_)
  rw [key, key, hxy]

/-- **Galois descent** (Speiser's theorem): an `L`-vector space with a semilinear action of
`Gal(L/K)` is the extension of scalars of its `K`-subspace of invariants. -/
noncomputable def descentEquiv : L ⊗[K] (invariants K L W) ≃ₗ[L] W :=
  LinearEquiv.ofBijective (descentMap K L W)
    ⟨descentMap_injective K L W, descentMap_surjective K L W⟩

@[simp]
theorem descentEquiv_tmul (c : L) (w : invariants K L W) :
    descentEquiv K L W (c ⊗ₜ w) = c • (w : W) := rfl

/-- The `K`-dimension of the invariants equals the `L`-dimension of the whole space. -/
theorem finrank_invariants :
    Module.finrank K (invariants K L W) = Module.finrank L W := by
  rw [← (descentEquiv K L W).finrank_eq, Module.finrank_baseChange]

end Descent

section BaseChange

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (V : Type*) [AddCommGroup V] [Module K V]

/-- On a base change `L ⊗[K] V`, the Galois action through the left tensor factor (which
Mathlib already supplies via `TensorProduct.leftDistribMulAction`) is semilinear. -/
instance isSemilinearGaloisAction_baseChange :
    IsSemilinearGaloisAction K L (L ⊗[K] V) where
  smul_smul' σ c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d v => simp [TensorProduct.smul_tmul', AlgEquiv.smul_def, smul_eq_mul]
    | add x y hx hy => simp only [smul_add, hx, hy]

/-- The canonical `K`-linear map from `V` to the Galois invariants of `L ⊗[K] V`. -/
def baseChangeInvariants : V →ₗ[K] invariants K L (L ⊗[K] V) :=
  LinearMap.codRestrict _ (TensorProduct.mk K L V 1) fun v σ => by
    simp [TensorProduct.smul_tmul']

@[simp]
theorem baseChangeInvariants_apply (v : V) :
    (baseChangeInvariants K L V v : L ⊗[K] V) = 1 ⊗ₜ v := rfl

/-- The canonical map from `V` into the invariants of `L ⊗[K] V` is injective. -/
theorem baseChangeInvariants_injective : Function.Injective (baseChangeInvariants K L V) := by
  classical
  set b := Module.Basis.ofVectorSpace K V with hb
  intro v v' hvv
  have hvv' : (1 : L) ⊗ₜ[K] v = 1 ⊗ₜ[K] v' := congrArg Subtype.val hvv
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  have := congrArg (fun x => (b.baseChange (S := L)).repr x i) hvv'
  simpa [Module.Basis.baseChange_repr_tmul, Algebra.smul_def,
    FaithfulSMul.algebraMap_injective K L |>.eq_iff] using this

/-- **Galois descent, base-change case**: the invariants of `L ⊗[K] V` under the Galois action
on the left factor are exactly the image of `V`. -/
noncomputable def baseChangeInvariantsEquiv [FiniteDimensional K L] [IsGalois K L]
    [FiniteDimensional K V] : invariants K L (L ⊗[K] V) ≃ₗ[K] V := by
  have hrank : Module.finrank K V = Module.finrank K (invariants K L (L ⊗[K] V)) := by
    rw [finrank_invariants, Module.finrank_baseChange]
  exact (LinearEquiv.ofBijective (baseChangeInvariants K L V)
    ⟨baseChangeInvariants_injective K L V,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1
        (baseChangeInvariants_injective K L V)⟩).symm

end BaseChange

section AlgebraDescent

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {A : Type*} [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
variable [MulSemiringAction Gal(L/K) A] [IsSemilinearGaloisAction K L A]

variable (K L A)

/-- The `K`-subalgebra of Galois-invariant elements of an `L`-algebra `A` on which `Gal(L/K)`
acts semilinearly by ring automorphisms. -/
def invariantsSubalgebra : Subalgebra K A where
  carrier := {a : A | ∀ σ : Gal(L/K), σ • a = a}
  mul_mem' {x y} hx hy σ := by rw [smul_mul', hx σ, hy σ]
  one_mem' σ := smul_one σ
  add_mem' {x y} hx hy σ := by rw [smul_add, hx σ, hy σ]
  zero_mem' σ := smul_zero σ
  algebraMap_mem' a σ := by
    rw [Algebra.algebraMap_eq_smul_one, smul_comm_algebra, smul_one]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The subalgebra of invariants and the submodule of invariants have the same elements. -/
theorem toSubmodule_invariantsSubalgebra :
    Subalgebra.toSubmodule (invariantsSubalgebra K L A) = invariants K L A := rfl

/-- The `K`-linear identification of the invariant subalgebra with the invariant submodule. -/
noncomputable def invariantsSubalgebraEquiv :
    invariantsSubalgebra K L A ≃ₗ[K] invariants K L A :=
  (Subalgebra.toSubmoduleEquiv (invariantsSubalgebra K L A)).symm.trans
    (LinearEquiv.ofEq _ _ (toSubmodule_invariantsSubalgebra K L A))

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem invariantsSubalgebraEquiv_apply (x : invariantsSubalgebra K L A) :
    (invariantsSubalgebraEquiv K L A x : A) = (x : A) := rfl

/-- The natural `L`-algebra map `L ⊗[K] A ^ G → A` sending `c ⊗ a` to `c • a`. -/
def descentAlgHom : L ⊗[K] (invariantsSubalgebra K L A) →ₐ[L] A :=
  Algebra.TensorProduct.lift (Algebra.ofId L A) (invariantsSubalgebra K L A).val
    fun _ _ => Commute.all _ _

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem descentAlgHom_tmul (c : L) (a : invariantsSubalgebra K L A) :
    descentAlgHom K L A (c ⊗ₜ a) = c • (a : A) := by
  rw [descentAlgHom, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

/-- The algebra descent map is bijective. -/
theorem descentAlgHom_bijective : Function.Bijective (descentAlgHom K L A) := by
  set e := TensorProduct.congr (LinearEquiv.refl K L) (invariantsSubalgebraEquiv K L A) with he
  have hmap : (descentAlgHom K L A).toLinearMap.restrictScalars K
      = ((descentMap K L A).restrictScalars K) ∘ₗ e.toLinearMap := by
    refine TensorProduct.ext' fun c a => ?_
    simp [he]
  have hfun : ∀ x, descentAlgHom K L A x = descentMap K L A (e x) := fun x =>
    congrFun (congrArg DFunLike.coe hmap) x
  have hbij : Function.Bijective fun x => descentMap K L A (e x) :=
    ⟨(descentMap_injective K L A).comp e.injective,
      (descentMap_surjective K L A).comp e.surjective⟩
  simpa only [funext hfun] using hbij

/-- **Galois descent for algebras**: a commutative `L`-algebra with a semilinear action of
`Gal(L/K)` by ring automorphisms is the base change of its `K`-subalgebra of invariants. -/
noncomputable def descentAlgEquiv : L ⊗[K] (invariantsSubalgebra K L A) ≃ₐ[L] A :=
  AlgEquiv.ofBijective (descentAlgHom K L A) (descentAlgHom_bijective K L A)

@[simp]
theorem descentAlgEquiv_tmul (c : L) (a : invariantsSubalgebra K L A) :
    descentAlgEquiv K L A (c ⊗ₜ a) = c • (a : A) := descentAlgHom_tmul K L A c a

end AlgebraDescent

end InverseGalois.CFT
