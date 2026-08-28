/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerShrink

/-!
# The counting argument in a tensor product of two layers

The shrinking homomorphism attached to a vector of exponents multiplies the class of a layer word
by a monomial in those exponents, of degree at most one more than the level of the word.  A tensor
product of two layers is spanned by the tensors of two such classes, and on those the shrinking
homomorphism acts by the product of the two monomials, whose degree is bounded by the sum of the
two bounds.  The Chevalley–Warning count therefore applies to a tensor product of layers just as it
does to a single layer, with the degree bound added and the number of scalar equations multiplied.

The case needed later is the tensor product of the zeroth layer with a layer of arbitrary level and
a fixed module of coefficients, because that is what presents the first homology of the kernel of a
generic embedding problem.

## Main results

* `InverseGalois.Shafarevich.span_range_tmul_eq_top` — a tensor product is spanned by the tensors of
  two spanning families.
* `InverseGalois.Shafarevich.exists_ne_zero_forall_apply_eq_zero` — the counting argument in the
  abstract: given a spanning family on which the maps under consideration act by monomials of
  bounded degree, finitely many prescribed vectors are annihilated at once.
* `InverseGalois.Shafarevich.exists_layer_word_data` — the classes of the layer words provide such a
  family in a layer.
* `InverseGalois.Shafarevich.exists_ne_zero_forall_tensor_eq_zero` — **finitely many prescribed
  elements of the zeroth layer tensored with a layer and a module of coefficients are annihilated
  at once by a shrinking homomorphism.**

## Tags

Shafarevich's theorem, embedding problem, p-central series, Chevalley–Warning, tensor product
-/

open scoped TensorProduct

namespace InverseGalois.Shafarevich

/-! ### Spanning a tensor product -/

section Span

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **The tensors of two spanning families span the tensor product.** -/
theorem span_range_tmul_eq_top {ι κ : Type*} (u : ι → M) (w : κ → N)
    (hu : Submodule.span R (Set.range u) = ⊤) (hw : Submodule.span R (Set.range w) = ⊤) :
    Submodule.span R (Set.range fun q : ι × κ => u q.1 ⊗ₜ[R] w q.2) = ⊤ := by
  set V := Submodule.span R (Set.range fun q : ι × κ => u q.1 ⊗ₜ[R] w q.2) with hV
  have h1 : ∀ (i : ι) (y : N), u i ⊗ₜ[R] y ∈ V := by
    intro i y
    have hle : Submodule.span R (Set.range w)
        ≤ Submodule.comap (TensorProduct.mk R M N (u i)) V := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(i, k), rfl⟩
    exact hle (hw ▸ Submodule.mem_top)
  have h2 : ∀ (z : M) (y : N), z ⊗ₜ[R] y ∈ V := by
    intro z y
    have hle : Submodule.span R (Set.range u)
        ≤ Submodule.comap ((TensorProduct.mk R M N).flip y) V := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact h1 i y
    exact hle (hu ▸ Submodule.mem_top)
  refine Submodule.eq_top_iff'.2 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul z y => exact h2 z y
  | add z y hz hy => exact Submodule.add_mem _ hz hy

end Span

/-! ### The counting argument in the abstract -/

section Abstract

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {r d t : ℕ} {M W : Type*} [AddCommGroup M]
  [Module (ZMod ℓ) M] [AddCommGroup W] [Module (ZMod ℓ) W] [FiniteDimensional (ZMod ℓ) W]

/-- **The counting argument in the abstract.**  Suppose a family of vectors spans a space, and that
each map of a given family multiplies each of them by the value at the map's parameter of a
monomial attached to the vector, no monomial being constant and all of them of degree at most `d`.
Then some nonzero parameter gives a map annihilating finitely many prescribed vectors at once,
provided the number of variables exceeds `d` times the number of scalar equations involved. -/
theorem exists_ne_zero_forall_apply_eq_zero {Ω : Type*} (u : Ω → M) (u' : Ω → W)
    (μ : Ω → Multiset (Fin r)) (hspan : Submodule.span (ZMod ℓ) (Set.range u) = ⊤)
    (hμ0 : ∀ ω, μ ω ≠ 0) (hμd : ∀ ω, Multiset.card (μ ω) ≤ d)
    (Φ : (Fin r → ZMod ℓ) → M →ₗ[ZMod ℓ] W)
    (hΦ : ∀ a ω, Φ a (u ω) = ((μ ω).map a).prod • u' ω)
    (hr : d * (t * Module.finrank (ZMod ℓ) W) < r) (v : Fin t → M) :
    ∃ a : Fin r → ZMod ℓ, a ≠ 0 ∧ ∀ ν, Φ a (v ν) = 0 := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  have hmem : ∀ ν, v ν ∈ Submodule.span (ZMod ℓ) (Set.range u) := fun ν =>
    hspan ▸ Submodule.mem_top
  choose c hc using fun ν => Finsupp.mem_span_range_iff_exists_finsupp.mp (hmem ν)
  set s : Finset Ω := Finset.univ.biUnion fun ν => (c ν).support with hs
  have hsub : ∀ ν, (c ν).support ⊆ s := fun ν ω hω =>
    Finset.mem_biUnion.mpr ⟨ν, Finset.mem_univ ν, hω⟩
  have hcs : ∀ ν, ∑ ω ∈ s, c ν ω • u ω = v ν := by
    intro ν
    rw [← hc ν]
    exact (Finsupp.sum_of_support_subset (c ν) (hsub ν) (fun ω a => a • u ω)
      fun ω _ => zero_smul _ _).symm
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_sum_multiset_prod_smul_eq_zero
    (K := ZMod ℓ) (W := W) (μ := fun A : {ω : Ω // ω ∈ s} => μ A.1) (fun A => hμ0 A.1)
    (fun A => hμd A.1) hr fun ν A => c ν A.1 • u' A.1
  refine ⟨a, ha0, fun ν => ?_⟩
  calc Φ a (v ν) = Φ a (∑ ω ∈ s, c ν ω • u ω) := by rw [hcs ν]
    _ = ∑ ω ∈ s, c ν ω • Φ a (u ω) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun ω _ => map_smul _ _ _
    _ = ∑ ω ∈ s, c ν ω • (((μ ω).map a).prod • u' ω) :=
          Finset.sum_congr rfl fun ω _ => by rw [hΦ]
    _ = ∑ ω ∈ s, ((μ ω).map a).prod • (c ν ω • u' ω) :=
          Finset.sum_congr rfl fun ω _ => smul_comm _ _ _
    _ = ∑ A : {ω : Ω // ω ∈ s}, ((μ A.1).map a).prod • (c ν A.1 • u' A.1) :=
          (Finset.sum_coe_sort s _).symm
    _ = 0 := ha ν

end Abstract

/-! ### The layer words as a spanning family -/

section Words

variable {ι κ : Type*} {P Q : Type*} [Group P] [Group Q] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {r : ℕ}

/-- **The classes of the layer words of a given level form a spanning family of the layer on which
the shrinking homomorphisms act by monomials.** -/
theorem exists_layer_word_data {x : ι → P} (hx : Subgroup.closure (Set.range x) = ⊤) (y : κ → Q)
    (σ : ι → κ) (blk : ι → Fin r) (ψ : (Fin r → ℕ) → P →* Q)
    (hψ : ∀ a i, ψ a (x i) = y (σ i) ^ a (blk i)) (j : ℕ) :
    ∃ (u : LevelWord ι j → Layer ℓ P j) (u' : LevelWord ι j → Layer ℓ Q j),
      Submodule.span (ZMod ℓ) (Set.range u) = ⊤ ∧
        ∀ (a : Fin r → ZMod ℓ) (w : LevelWord ι j),
          layerLinear ℓ (ψ fun k => (a k).val) j (u w)
            = ((w.1.deg.map blk).map a).prod • u' w := by
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  have hgw : ∀ w : LevelWord ι j, w.1.eval ℓ x ∈ pCentral ℓ P j := fun w => by
    have h := LayerWord.eval_mem ℓ x w.1
    rwa [w.2] at h
  have hlev : ∀ w : LevelWord ι j, (w.1.map σ).level = j := fun w =>
    (LayerWord.level_map σ w.1).trans w.2
  have hmw : ∀ w : LevelWord ι j, (w.1.map σ).eval ℓ y ∈ pCentral ℓ Q j := fun w => by
    have h := LayerWord.eval_mem ℓ y (w.1.map σ)
    rwa [hlev w] at h
  have hrange : (Set.range fun w : LevelWord ι j => w.1.eval ℓ x)
      = {g : P | ∃ w : LayerWord ι, w.level = j ∧ w.eval ℓ x = g} := by
    ext g
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hsup : pCentral ℓ P j
      = Subgroup.closure (Set.range fun w : LevelWord ι j => w.1.eval ℓ x)
        ⊔ pCentral ℓ P (j + 1) := by
    rw [hrange]
    exact pCentral_eq_closure_eval_sup ℓ hx j
  refine ⟨fun w => layerMk (hgw w), fun w => layerMk (hmw w),
    span_layerMk_eq_top _ hgw hsup, fun a w => ?_⟩
  set b : Fin r → ℕ := fun k => (a k).val with hb
  have hkey : ψ b (w.1.eval ℓ x) ∈ pCentral ℓ Q j := map_mem_pCentral (ψ b) (hgw w)
  have h1 : ψ b (w.1.eval ℓ x) = w.1.eval ℓ fun i => y (σ i) ^ b (blk i) := by
    have hcomp : (ψ b : P → Q) ∘ x = fun i => y (σ i) ^ b (blk i) := funext fun i => hψ b i
    rw [LayerWord.map_eval, hcomp]
  have h2 := LayerWord.eval_comp_pow_div_mem ℓ σ y (fun i => b (blk i)) w.1
  rw [w.2] at h2
  have hmm : (w.1.deg.map fun i => b (blk i)) = (w.1.deg.map blk).map b := by
    rw [Multiset.map_map]
    rfl
  have h4 : layerMk hkey = ((w.1.deg.map blk).map b).prod • layerMk (hmw w) := by
    rw [← layerMk_pow (hmw w), layerMk_eq_iff, h1, ← hmm]
    exact h2
  rw [layerLinear_apply, layerMap_layerMk, h4]
  exact natCast_multiset_prod_smul (w.1.deg.map blk) a (layerMk (hmw w))

end Words

/-! ### The count in a tensor product of two layers -/

section Tensor

variable {ι κ : Type*} {P Q : Type*} [Group P] [Group Q] [Finite Q] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
  {r j t : ℕ}

/-- **Finitely many prescribed elements of the zeroth layer tensored with a layer and a module of
coefficients can be annihilated all at once.**  Two layer words multiply the class they carry by
monomials of degree at most one and at most `j + 1`, so the tensor of their classes is multiplied by
a monomial of degree at most `j + 2`, and the Chevalley–Warning count applies with that bound. -/
theorem exists_ne_zero_forall_tensor_eq_zero {x : ι → P}
    (hx : Subgroup.closure (Set.range x) = ⊤) (y : κ → Q) (σ : ι → κ) (blk : ι → Fin r)
    (ψ : (Fin r → ℕ) → P →* Q) (hψ : ∀ a i, ψ a (x i) = y (σ i) ^ a (blk i))
    (T : Type*) [AddCommGroup T] [Module (ZMod ℓ) T] [FiniteDimensional (ZMod ℓ) T]
    (hr : (j + 2) * (t * Module.finrank (ZMod ℓ)
      (Layer ℓ Q 0 ⊗[ZMod ℓ] (Layer ℓ Q j ⊗[ZMod ℓ] T))) < r)
    (v : Fin t → Layer ℓ P 0 ⊗[ZMod ℓ] (Layer ℓ P j ⊗[ZMod ℓ] T)) :
    ∃ a : Fin r → ZMod ℓ, a ≠ 0 ∧ ∀ ν,
      TensorProduct.map (layerLinear ℓ (ψ fun k => (a k).val) 0)
        (TensorProduct.map (layerLinear ℓ (ψ fun k => (a k).val) j) LinearMap.id) (v ν) = 0 := by
  classical
  obtain ⟨u₀, u₀', hspan₀, hmap₀⟩ := exists_layer_word_data (ℓ := ℓ) hx y σ blk ψ hψ 0
  obtain ⟨uj, uj', hspanj, hmapj⟩ := exists_layer_word_data (ℓ := ℓ) hx y σ blk ψ hψ j
  obtain ⟨dT, bT, -⟩ : ∃ (d : ℕ) (_ : Module.Basis (Fin d) (ZMod ℓ) T), True :=
    ⟨_, Module.finBasis (ZMod ℓ) T, trivial⟩
  have hspanI : Submodule.span (ZMod ℓ)
      (Set.range fun q : LevelWord ι j × Fin dT => uj q.1 ⊗ₜ[ZMod ℓ] bT q.2) = ⊤ :=
    span_range_tmul_eq_top uj bT hspanj bT.span_eq
  refine exists_ne_zero_forall_apply_eq_zero
    (Ω := LevelWord ι 0 × LevelWord ι j × Fin dT)
    (fun q => u₀ q.1 ⊗ₜ[ZMod ℓ] (uj q.2.1 ⊗ₜ[ZMod ℓ] bT q.2.2))
    (fun q => u₀' q.1 ⊗ₜ[ZMod ℓ] (uj' q.2.1 ⊗ₜ[ZMod ℓ] bT q.2.2))
    (fun q => q.1.1.deg.map blk + q.2.1.1.deg.map blk) ?_ ?_ ?_ (d := j + 2)
    (fun a => TensorProduct.map (layerLinear ℓ (ψ fun k => (a k).val) 0)
      (TensorProduct.map (layerLinear ℓ (ψ fun k => (a k).val) j) LinearMap.id)) ?_ hr v
  · exact span_range_tmul_eq_top (N := Layer ℓ P j ⊗[ZMod ℓ] T) u₀
      (fun q : LevelWord ι j × Fin dT => uj q.1 ⊗ₜ[ZMod ℓ] bT q.2) hspan₀ hspanI
  · intro q
    have h1 : Multiset.card (q.1.1.deg.map blk) ≠ 0 := by
      simpa using LayerWord.deg_ne_zero q.1.1
    simp only [ne_eq, ← Multiset.card_eq_zero, Multiset.card_add]
    omega
  · intro q
    have h1 := LayerWord.card_deg_le q.1.1
    have h2 := LayerWord.card_deg_le q.2.1.1
    rw [q.1.2] at h1
    rw [q.2.1.2] at h2
    simp only [Multiset.card_add, Multiset.card_map]
    omega
  · intro a q
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, hmap₀, hmapj, LinearMap.id_coe, id_eq,
      Multiset.map_add, Multiset.prod_add, ← TensorProduct.smul_tmul_smul,
      TensorProduct.smul_tmul']

end Tensor

/-! ### The generic instance -/

section GenericTensor

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and killing finitely many prescribed
elements of the zeroth layer tensored with a layer and a module of coefficients at once.**  The
number of scalar equations is the number of elements times the dimension of the target, and the
number of blocks has to exceed that, times two more than the level of the layer. -/
theorem exists_genericShrink_tensor_eq_zero {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t : ℕ} (T : Type*) [AddCommGroup T] [Module (ZMod ℓ) T] [Module.Finite (ZMod ℓ) T]
    (hr : (j + 2) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) 0 ⊗[ZMod ℓ]
      (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T))) < r)
    (v : Fin t → Layer ℓ (Generic U (r * n) S) 0 ⊗[ZMod ℓ]
      (Layer ℓ (Generic U (r * n) S) j ⊗[ZMod ℓ] T)) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, TensorProduct.map (layerLinear ℓ (genericShrink U r n S a) 0)
        (TensorProduct.map (layerLinear ℓ (genericShrink U r n S a) j) LinearMap.id) (v ν) = 0 := by
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_tensor_eq_zero (ℓ := ℓ)
    (x := fun w : Fin (r * n) × U => (QuotientGroup.mk (FreeGroup.of w) : Generic U (r * n) S))
    (closure_range_mk_of U (r * n) S)
    (fun w : Fin n × U => (QuotientGroup.mk (FreeGroup.of w) : Generic U n S))
    (fun w => ((finProdFinEquiv.symm w.1).2, w.2)) (fun w => (finProdFinEquiv.symm w.1).1)
    (fun b => genericShrink U r n S b)
    (fun b w => by rw [genericShrink_mk, shrinkHom_of, QuotientGroup.mk_pow]) T hr v
  obtain ⟨k, hk⟩ := Function.ne_iff.mp ha0
  refine ⟨fun i => (a i).val, genericShrink_surjective U r n S hS _ k ?_, ha⟩
  refine hℓ.out.coprime_iff_not_dvd.mpr fun hd => absurd (Nat.le_of_dvd ?_ hd) ?_
  · exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero (a k)).mpr hk)
  · exact not_le.mpr (ZMod.val_lt (a k))

end GenericTensor

end InverseGalois.Shafarevich
