import Mathlib

/-!
# Tensor products of central simple algebras

Let `K` be a field. This file proves the two algebraic facts that make the set of
finite-dimensional central simple `K`-algebras into a monoid under `⊗[K]`, namely that a tensor
product of two central `K`-algebras is central, and that the tensor product of a *central* simple
`K`-algebra with an arbitrary simple `K`-algebra is simple.

The proofs are the classical ones. Fix a `K`-basis `𝔟` of `B`; then every element of `A ⊗[K] B`
has well-defined coordinates in `A` indexed by the basis (this is `TensorSimple.coeffEquiv`).
An element that commutes with `a ⊗ₜ 1` for every `a : A` has all of its coordinates in the centre
of `A`, hence, when `A` is central, is of the form `1 ⊗ₜ b`. Simplicity follows by picking a
nonzero element of a two-sided ideal whose coordinate support has minimal cardinality.

## Main results

* `TensorSimple.exists_one_tmul`: over a central `K`-algebra `A`, an element of `A ⊗[K] B`
  commuting with all `a ⊗ₜ 1` is of the form `1 ⊗ₜ b`.
* `Algebra.IsCentral.tensorProduct`: the tensor product of two central `K`-algebras is central.
* `IsSimpleRing.tensorProduct_of_isCentral`: if `A` is a central simple `K`-algebra and `B` is a
  simple `K`-algebra, then `A ⊗[K] B` is simple.
* `CSA.tensor`: the tensor product of two finite-dimensional central simple `K`-algebras, again
  as a finite-dimensional central simple `K`-algebra.
-/

universe u v w

open scoped TensorProduct

open Module

namespace TensorSimple

variable {K : Type u} {A : Type v} {B : Type w} {ι : Type*}
variable [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- The coordinates of an element of `A ⊗[K] B` relative to a `K`-basis `𝔟` of `B`: the element
`x` is the finite sum of the terms `coeffEquiv 𝔟 x j ⊗ₜ 𝔟 j`. -/
noncomputable def coeffEquiv (𝔟 : Basis ι K B) : A ⊗[K] B ≃ₗ[K] (ι →₀ A) :=
  letI := Classical.decEq ι
  (TensorProduct.congr (LinearEquiv.refl K A) 𝔟.repr).trans
    (TensorProduct.finsuppScalarRight K K A ι)

@[simp]
lemma coeffEquiv_tmul (𝔟 : Basis ι K B) (a : A) (b : B) (j : ι) :
    coeffEquiv 𝔟 (a ⊗ₜ[K] b) j = 𝔟.repr b j • a := by
  simp [coeffEquiv]

@[simp]
lemma coeffEquiv_symm_single (𝔟 : Basis ι K B) (j : ι) (a : A) :
    (coeffEquiv 𝔟).symm (Finsupp.single j a) = a ⊗ₜ[K] 𝔟 j := by
  simp [coeffEquiv]

/-- Left multiplication by `a ⊗ₜ 1` acts coordinatewise by left multiplication by `a`. -/
lemma coeffEquiv_mul_left (𝔟 : Basis ι K B) (a : A) (x : A ⊗[K] B) (j : ι) :
    coeffEquiv 𝔟 ((a ⊗ₜ[K] (1 : B)) * x) j = a * coeffEquiv 𝔟 x j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a' b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => simp [mul_add, hy, hz]

/-- Right multiplication by `a ⊗ₜ 1` acts coordinatewise by right multiplication by `a`. -/
lemma coeffEquiv_mul_right (𝔟 : Basis ι K B) (a : A) (x : A ⊗[K] B) (j : ι) :
    coeffEquiv 𝔟 (x * (a ⊗ₜ[K] (1 : B))) j = coeffEquiv 𝔟 x j * a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a' b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => simp [add_mul, hy, hz]

/-- Left multiplication by `a ⊗ₜ 1` does not enlarge the coordinate support. -/
lemma support_coeffEquiv_mul_left (𝔟 : Basis ι K B) (a : A) (x : A ⊗[K] B) :
    (coeffEquiv 𝔟 ((a ⊗ₜ[K] (1 : B)) * x)).support ⊆ (coeffEquiv 𝔟 x).support := by
  intro j hj
  simp only [Finsupp.mem_support_iff, coeffEquiv_mul_left] at hj ⊢
  intro h
  exact hj (by rw [h, mul_zero])

/-- Right multiplication by `a ⊗ₜ 1` does not enlarge the coordinate support. -/
lemma support_coeffEquiv_mul_right (𝔟 : Basis ι K B) (a : A) (x : A ⊗[K] B) :
    (coeffEquiv 𝔟 (x * (a ⊗ₜ[K] (1 : B)))).support ⊆ (coeffEquiv 𝔟 x).support := by
  intro j hj
  simp only [Finsupp.mem_support_iff, coeffEquiv_mul_right] at hj ⊢
  intro h
  exact hj (by rw [h, zero_mul])

/-- An element of `A ⊗[K] B` which commutes with every `a ⊗ₜ 1`, for `A` a central `K`-algebra,
lies in the image of `B`. -/
lemma exists_one_tmul [Algebra.IsCentral K A] (𝔟 : Basis ι K B) {x : A ⊗[K] B}
    (hx : ∀ a : A, (a ⊗ₜ[K] (1 : B)) * x = x * (a ⊗ₜ[K] (1 : B))) :
    ∃ b : B, x = (1 : A) ⊗ₜ[K] b := by
  have hcen : ∀ j, coeffEquiv 𝔟 x j ∈ Subalgebra.center K A := by
    intro j
    rw [Subalgebra.mem_center_iff]
    intro a
    have h := congrArg (fun y : A ⊗[K] B ↦ coeffEquiv 𝔟 y j) (hx a)
    simpa [coeffEquiv_mul_left, coeffEquiv_mul_right] using h
  choose c hc using fun j ↦ (Algebra.IsCentral.mem_center_iff K).1 (hcen j)
  refine ⟨∑ j ∈ (coeffEquiv 𝔟 x).support, c j • 𝔟 j, ?_⟩
  have hrepr : ∑ j ∈ (coeffEquiv 𝔟 x).support, Finsupp.single j (coeffEquiv 𝔟 x j) =
      coeffEquiv 𝔟 x := Finsupp.sum_single _
  calc x = (coeffEquiv 𝔟).symm (coeffEquiv 𝔟 x) := by simp
    _ = (coeffEquiv 𝔟).symm
          (∑ j ∈ (coeffEquiv 𝔟 x).support, Finsupp.single j (coeffEquiv 𝔟 x j)) := by rw [hrepr]
    _ = ∑ j ∈ (coeffEquiv 𝔟 x).support, (coeffEquiv 𝔟 x j) ⊗ₜ[K] 𝔟 j := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ ↦ coeffEquiv_symm_single 𝔟 j _
    _ = ∑ j ∈ (coeffEquiv 𝔟 x).support, (1 : A) ⊗ₜ[K] (c j • 𝔟 j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hc j, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    _ = (1 : A) ⊗ₜ[K] ∑ j ∈ (coeffEquiv 𝔟 x).support, c j • 𝔟 j := by
        rw [TensorProduct.tmul_sum]

end TensorSimple

open TensorSimple in
/-- The tensor product of two central algebras over a field is central. -/
instance Algebra.IsCentral.tensorProduct {K : Type u} {A : Type v} {B : Type w} [Field K]
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] [Algebra.IsCentral K A]
    [Algebra.IsCentral K B] : Algebra.IsCentral K (A ⊗[K] B) where
  out x hx := by
    rw [Algebra.mem_bot]
    rcases subsingleton_or_nontrivial A with hA | hA
    · have h1 : (1 : A ⊗[K] B) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0,
          TensorProduct.zero_tmul]
      have : Subsingleton (A ⊗[K] B) := subsingleton_of_zero_eq_one h1.symm
      exact ⟨0, Subsingleton.elim _ _⟩
    · rw [Subalgebra.mem_center_iff] at hx
      obtain ⟨b, rfl⟩ := exists_one_tmul (Module.Free.chooseBasis K B) fun a ↦ hx _
      have hbcen : b ∈ Subalgebra.center K B := by
        rw [Subalgebra.mem_center_iff]
        intro b'
        have h := hx ((1 : A) ⊗ₜ[K] b')
        simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
        exact Algebra.TensorProduct.includeRight_injective
          (FaithfulSMul.algebraMap_injective K A) h
      obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).1 hbcen
      refine ⟨k, ?_⟩
      rw [hk, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- The tensor product of a central simple algebra with a simple algebra over the same field is
simple. -/
theorem IsSimpleRing.tensorProduct_of_isCentral {K : Type u} {A : Type v} {B : Type w} [Field K]
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] [Algebra.IsCentral K A] [IsSimpleRing A]
    [IsSimpleRing B] : IsSimpleRing (A ⊗[K] B) := by
  classical
  have hAne : Nontrivial A := inferInstance
  have hBne : Nontrivial B := inferInstance
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective K A)
  have : Nontrivial (A ⊗[K] B) := hinj.nontrivial
  set 𝔟 : Basis (Module.Free.ChooseBasisIndex K B) K B := Module.Free.chooseBasis K B with h𝔟
  set e : A ⊗[K] B ≃ₗ[K] (Module.Free.ChooseBasisIndex K B →₀ A) :=
    TensorSimple.coeffEquiv 𝔟 with he
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ ?_
  rw [or_iff_not_imp_left, ← I.one_mem_iff]
  intro hI
  obtain ⟨y₀, hy₀I, hy₀⟩ : ∃ y ∈ I, y ≠ 0 :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal (A ⊗[K] B)) < I)
  -- pick a nonzero element of `I` whose coordinate support is as small as possible
  have hex : ∃ n : ℕ, ∃ y, y ∈ I ∧ y ≠ 0 ∧ (e y).support.card = n :=
    ⟨_, y₀, hy₀I, hy₀, rfl⟩
  obtain ⟨x, hxI, hx0, hxcard⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ I, y ≠ 0 → Nat.find hex ≤ (e y).support.card :=
    fun y hy hy0 ↦ Nat.find_min' hex ⟨y, hy, hy0, rfl⟩
  have hsne : (e x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun h ↦ hx0 (by simpa using congrArg e.symm h)
  obtain ⟨j₀, hj₀⟩ := hsne
  -- the `j₀`-th coordinates of elements of `I` supported inside `(e x).support` form an ideal
  set JA : TwoSidedIdeal A := TwoSidedIdeal.mk'
      {a : A | ∃ y ∈ I, (e y).support ⊆ (e x).support ∧ e y j₀ = a}
      ⟨0, I.zero_mem, by simp, by simp⟩
      (by
        rintro a a' ⟨y, hy, hys, rfl⟩ ⟨y', hy', hys', rfl⟩
        refine ⟨y + y', I.add_mem hy hy', ?_, by simp⟩
        rw [map_add]
        exact Finsupp.support_add.trans (Finset.union_subset hys hys'))
      (by
        rintro a ⟨y, hy, hys, rfl⟩
        exact ⟨-y, I.neg_mem hy, by simpa using (Finsupp.support_neg (e y)).le.trans hys, by simp⟩)
      (by
        rintro a' a ⟨y, hy, hys, rfl⟩
        refine ⟨(a' ⊗ₜ[K] (1 : B)) * y, I.mul_mem_left _ _ hy, ?_, ?_⟩
        · exact (TensorSimple.support_coeffEquiv_mul_left 𝔟 a' y).trans hys
        · rw [he]; exact TensorSimple.coeffEquiv_mul_left 𝔟 a' y j₀)
      (by
        rintro a a' ⟨y, hy, hys, rfl⟩
        refine ⟨y * (a' ⊗ₜ[K] (1 : B)), I.mul_mem_right _ _ hy, ?_, ?_⟩
        · exact (TensorSimple.support_coeffEquiv_mul_right 𝔟 a' y).trans hys
        · rw [he]; exact TensorSimple.coeffEquiv_mul_right 𝔟 a' y j₀) with hJA
  have ha₀ : e x j₀ ∈ JA := by
    rw [hJA, TwoSidedIdeal.mem_mk']
    exact ⟨x, hxI, subset_rfl, rfl⟩
  have ha₀ne : e x j₀ ≠ 0 := Finsupp.mem_support_iff.1 hj₀
  have h1JA : (1 : A) ∈ JA := IsSimpleRing.one_mem_of_ne_zero_mem JA ha₀ne ha₀
  rw [hJA, TwoSidedIdeal.mem_mk'] at h1JA
  obtain ⟨x', hx'I, hx's, hx'j₀⟩ := h1JA
  have hx'0 : x' ≠ 0 := by
    intro h
    rw [h] at hx'j₀
    simp at hx'j₀
  -- minimality forces `x'` to commute with the image of `A`
  have hcomm : ∀ a : A, (a ⊗ₜ[K] (1 : B)) * x' = x' * (a ⊗ₜ[K] (1 : B)) := by
    intro a
    set z := (a ⊗ₜ[K] (1 : B)) * x' - x' * (a ⊗ₜ[K] (1 : B)) with hz
    have hzI : z ∈ I := I.sub_mem (I.mul_mem_left _ _ hx'I) (I.mul_mem_right _ _ hx'I)
    have hzc : ∀ j, e z j = a * e x' j - e x' j * a := by
      intro j
      rw [hz, he]
      rw [map_sub, Finsupp.sub_apply, TensorSimple.coeffEquiv_mul_left,
        TensorSimple.coeffEquiv_mul_right]
    have hzsupp : (e z).support ⊆ (e x).support.erase j₀ := by
      intro j hj
      rw [Finsupp.mem_support_iff, hzc] at hj
      refine Finset.mem_erase.2 ⟨?_, hx's ?_⟩
      · rintro rfl
        exact hj (by rw [hx'j₀, mul_one, one_mul, sub_self])
      · rw [Finsupp.mem_support_iff]
        intro h
        exact hj (by rw [h, mul_zero, zero_mul, sub_self])
    have hzcard : (e z).support.card < Nat.find hex :=
      lt_of_le_of_lt (Finset.card_le_card hzsupp)
        (hxcard ▸ Finset.card_erase_lt_of_mem hj₀)
    have hz0 : z = 0 := by
      by_contra h
      exact absurd (hmin z hzI h) (not_le.2 hzcard)
    rwa [hz, sub_eq_zero] at hz0
  obtain ⟨b, hb⟩ := TensorSimple.exists_one_tmul 𝔟 hcomm
  have hbne : b ≠ 0 := by
    intro h
    rw [h, TensorProduct.tmul_zero] at hb
    exact hx'0 hb
  -- now use simplicity of `B`
  set JB : TwoSidedIdeal B := TwoSidedIdeal.mk'
      {b : B | (1 : A) ⊗ₜ[K] b ∈ I}
      (by simp)
      (by
        rintro b₁ b₂ h₁ h₂
        show (1 : A) ⊗ₜ[K] (b₁ + b₂) ∈ I
        rw [TensorProduct.tmul_add]
        exact I.add_mem h₁ h₂)
      (by
        rintro b₁ h₁
        show (1 : A) ⊗ₜ[K] (-b₁) ∈ I
        rw [TensorProduct.tmul_neg]
        exact I.neg_mem h₁)
      (by
        rintro b₁ b₂ h₂
        have := I.mul_mem_left ((1 : A) ⊗ₜ[K] b₁) _ h₂
        simpa [Algebra.TensorProduct.tmul_mul_tmul] using this)
      (by
        rintro b₁ b₂ h₁
        have := I.mul_mem_right _ ((1 : A) ⊗ₜ[K] b₂) h₁
        simpa [Algebra.TensorProduct.tmul_mul_tmul] using this) with hJB
  have hbJB : b ∈ JB := by
    rw [hJB, TwoSidedIdeal.mem_mk']
    show (1 : A) ⊗ₜ[K] b ∈ I
    rw [← hb]
    exact hx'I
  have h1JB : (1 : B) ∈ JB := IsSimpleRing.one_mem_of_ne_zero_mem JB hbne hbJB
  rw [hJB, TwoSidedIdeal.mem_mk'] at h1JB
  rwa [Algebra.TensorProduct.one_def]

variable {K : Type u} [Field K]

/-- The tensor product of two finite-dimensional central simple algebras over a field `K`, as a
finite-dimensional central simple algebra over `K`. -/
noncomputable def CSA.tensor (A B : CSA.{u, v} K) : CSA.{u, v} K where
  toAlgCat := AlgCat.of K (A ⊗[K] B)
  isSimple := IsSimpleRing.tensorProduct_of_isCentral
