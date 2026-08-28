/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.Layer
import InverseGalois.Solvable.Shafarevich.Shrink
import InverseGalois.Solvable.Shafarevich.ShrinkHom

/-!
# Killing finitely many obstructions in a layer

Here the three strands of the construction are tied together.  A homomorphism out of a group with
`r` blocks of generators, sending the generators of the `k`-th block to fixed powers `a k` of the
generators of a smaller group, carries a layer word of level `j` to the corresponding word
downstairs raised to a monomial in the exponents, of total degree at most `j + 1`.  The classes of
those words span the `j`-th layer, so the class of any prescribed element of the `j`-th term is
carried to a value of such a monomial form.  A Chevalley–Warning count then produces a nonzero
vector of exponents killing finitely many prescribed elements at once, and being nonzero it has a
coordinate prime to the characteristic, which is what makes the resulting homomorphism surjective.

## Main results

* `InverseGalois.Shafarevich.exists_ne_zero_forall_map_mem_pCentral` — **finitely many prescribed
  elements of the `j`-th term can be pushed into the `(j + 1)`-st all at once**, by a homomorphism
  attached to a nonzero vector of exponents, provided the number of blocks exceeds `j + 1` times
  the number of scalar equations involved.
* `InverseGalois.Shafarevich.exists_genericShrink_mem_pCentral` — the same for the shrinking
  homomorphism between generic operator groups, which is then surjective as well.
* `InverseGalois.Shafarevich.exists_genericShrink_rTensor_eq_zero` — the same again after extending
  the layer by a finite-dimensional module of coefficients, which multiplies the number of scalar
  equations by the dimension of that module.
* `InverseGalois.Shafarevich.layerMap_genericShrink_genericLayerRep` — the map of layers it induces
  respects the linear action of the operator group.

## Tags

Shafarevich's theorem, embedding problem, p-central series, Chevalley–Warning
-/

open scoped TensorProduct

namespace InverseGalois.Shafarevich

/-- The layer words of a prescribed level. -/
abbrev LevelWord (ι : Type*) (n : ℕ) : Type _ := {w : LayerWord ι // w.level = n}

/-! ### Reducing an exponent modulo `ℓ` -/

section Cast

variable {ℓ : ℕ} [NeZero ℓ] {W : Type*} [AddCommGroup W] [Module (ZMod ℓ) W] {α : Type*}

/-- A product of natural-number representatives acts as the product of the scalars they
represent. -/
theorem natCast_multiset_prod_smul (μ : Multiset α) (a : α → ZMod ℓ) (v : W) :
    (μ.map fun k => (a k).val).prod • v = (μ.map a).prod • v := by
  have h : (μ.map fun k => (((a k).val : ℕ) : ZMod ℓ)) = μ.map a :=
    Multiset.map_congr rfl fun k _ => by simp
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), Nat.cast_multiset_prod, Multiset.map_map]
  exact congrArg (· • v) (congrArg Multiset.prod h)

end Cast

/-! ### Coordinates in a tensor product -/

section Tensor

variable {R : Type*} [CommRing R] {M T : Type*} [AddCommGroup M] [Module R M] [AddCommGroup T]
  [Module R T] {d : ℕ}

/-- Read along a finite basis of the right-hand factor, an element of a tensor product is a sum of
pure tensors, one for each basis vector. -/
theorem exists_sum_tmul_basis (b : Module.Basis (Fin d) R T) (x : M ⊗[R] T) :
    ∃ w : Fin d → M, x = ∑ i, w i ⊗ₜ[R] b i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m t =>
    refine ⟨fun i => b.repr t i • m, ?_⟩
    calc m ⊗ₜ[R] t = m ⊗ₜ[R] ∑ i, b.repr t i • b i := by rw [b.sum_repr]
      _ = ∑ i, (b.repr t i • m) ⊗ₜ[R] b i := by
            rw [TensorProduct.tmul_sum]
            exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
  | add x y hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨w', rfl⟩ := hy
    exact ⟨w + w', by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩

end Tensor

/-! ### The counting argument in a layer -/

section Count

variable {ι κ : Type*} {P Q : Type*} [Group P] [Group Q] [Finite Q] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
  {r j t : ℕ}

/-- **Finitely many prescribed elements of the `j`-th term of the descending `p`-central series can
be pushed into the `(j + 1)`-st all at once.**  The homomorphisms available are indexed by vectors
of exponents, and send the `i`-th generator upstairs to a fixed power of the generator `σ i`
downstairs, the exponent depending only on the block `blk i`.  A vector of exponents doing the job
exists as soon as the number of blocks exceeds `j + 1` times the number of scalar equations
involved, and it may be taken nonzero. -/
theorem exists_ne_zero_forall_map_mem_pCentral {x : ι → P}
    (hx : Subgroup.closure (Set.range x) = ⊤) (y : κ → Q) (σ : ι → κ) (blk : ι → Fin r)
    (ψ : (Fin r → ℕ) → P →* Q) (hψ : ∀ a i, ψ a (x i) = y (σ i) ^ a (blk i))
    (hr : (j + 1) * (t * Module.finrank (ZMod ℓ) (Layer ℓ Q j)) < r)
    {z : Fin t → P} (hz : ∀ ν, z ν ∈ pCentral ℓ P j) :
    ∃ a : Fin r → ZMod ℓ, a ≠ 0 ∧
      ∀ ν, ψ (fun k => (a k).val) (z ν) ∈ pCentral ℓ Q (j + 1) := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  -- the values of the layer words of level `j`, upstairs and downstairs
  have hgw : ∀ w : LevelWord ι j, w.1.eval ℓ x ∈ pCentral ℓ P j := fun w => by
    have h := LayerWord.eval_mem ℓ x w.1
    rwa [w.2] at h
  have hlev : ∀ w : LevelWord ι j, (w.1.map σ).level = j := fun w =>
    (LayerWord.level_map σ w.1).trans w.2
  have hmw : ∀ w : LevelWord ι j, (w.1.map σ).eval ℓ y ∈ pCentral ℓ Q j := fun w => by
    have h := LayerWord.eval_mem ℓ y (w.1.map σ)
    rwa [hlev w] at h
  -- their classes span the layer upstairs
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
  have hspan := span_layerMk_eq_top (fun w : LevelWord ι j => w.1.eval ℓ x) hgw hsup
  -- so each prescribed element is a combination of finitely many of them
  have hmem : ∀ ν, layerMk (hz ν)
      ∈ Submodule.span (ZMod ℓ) (Set.range fun w : LevelWord ι j => layerMk (hgw w)) := by
    intro ν
    rw [hspan]
    exact Submodule.mem_top
  choose c hc using fun ν => Finsupp.mem_span_range_iff_exists_finsupp.mp (hmem ν)
  set s : Finset (LevelWord ι j) := Finset.univ.biUnion fun ν => (c ν).support with hs
  have hsub : ∀ ν, (c ν).support ⊆ s := fun ν w hw =>
    Finset.mem_biUnion.mpr ⟨ν, Finset.mem_univ ν, hw⟩
  have hcs : ∀ ν, ∑ w ∈ s, c ν w • layerMk (hgw w) = layerMk (hz ν) := by
    intro ν
    rw [← hc ν]
    exact (Finsupp.sum_of_support_subset (c ν) (hsub ν)
      (fun w a => a • layerMk (hgw w)) fun w _ => zero_smul _ _).symm
  -- the Chevalley–Warning count
  have hμ0 : ∀ A : {w : LevelWord ι j // w ∈ s}, A.1.1.deg.map blk ≠ 0 := by
    intro A
    simpa using LayerWord.deg_ne_zero A.1.1
  have hμs : ∀ A : {w : LevelWord ι j // w ∈ s}, Multiset.card (A.1.1.deg.map blk) ≤ j + 1 := by
    intro A
    have h := LayerWord.card_deg_le A.1.1
    rw [A.1.2] at h
    rwa [Multiset.card_map]
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_sum_multiset_prod_smul_eq_zero
    (K := ZMod ℓ) (W := Layer ℓ Q j) hμ0 hμs hr fun ν A => c ν A.1 • layerMk (hmw A.1)
  refine ⟨a, ha0, fun ν => ?_⟩
  set b : Fin r → ℕ := fun k => (a k).val with hb
  -- what the homomorphism does to the value of a single word
  have hkey : ∀ w : LevelWord ι j, ψ b (w.1.eval ℓ x) ∈ pCentral ℓ Q j := fun w =>
    map_mem_pCentral (ψ b) (hgw w)
  have hword : ∀ w : LevelWord ι j,
      layerMk (hkey w) = ((w.1.deg.map blk).map a).prod • layerMk (hmw w) := by
    intro w
    have h1 : ψ b (w.1.eval ℓ x) = w.1.eval ℓ fun i => y (σ i) ^ b (blk i) := by
      have hcomp : (ψ b : P → Q) ∘ x = fun i => y (σ i) ^ b (blk i) := funext fun i => hψ b i
      rw [LayerWord.map_eval, hcomp]
    have h2 := LayerWord.eval_comp_pow_div_mem ℓ σ y (fun i => b (blk i)) w.1
    rw [w.2] at h2
    have hmm : (w.1.deg.map fun i => b (blk i)) = (w.1.deg.map blk).map b := by
      rw [Multiset.map_map]
      rfl
    have h4 : layerMk (hkey w) = ((w.1.deg.map blk).map b).prod • layerMk (hmw w) := by
      rw [← layerMk_pow (hmw w), layerMk_eq_iff, h1, ← hmm]
      exact h2
    rw [h4]
    exact natCast_multiset_prod_smul (w.1.deg.map blk) a (layerMk (hmw w))
  -- and hence to the prescribed element
  have hfin : layerMk (map_mem_pCentral (ψ b) (hz ν)) = 0 :=
    calc layerMk (map_mem_pCentral (ψ b) (hz ν))
        = layerMap ℓ (ψ b) j (layerMk (hz ν)) := (layerMap_layerMk _ _).symm
      _ = layerMap ℓ (ψ b) j (∑ w ∈ s, c ν w • layerMk (hgw w)) := by rw [hcs ν]
      _ = ∑ w ∈ s, c ν w • layerMap ℓ (ψ b) j (layerMk (hgw w)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun w _ => layerMap_smul _ _ _
      _ = ∑ w ∈ s, c ν w • (((w.1.deg.map blk).map a).prod • layerMk (hmw w)) :=
            Finset.sum_congr rfl fun w _ => by rw [layerMap_layerMk, hword w]
      _ = ∑ w ∈ s, ((w.1.deg.map blk).map a).prod • (c ν w • layerMk (hmw w)) :=
            Finset.sum_congr rfl fun w _ => smul_comm _ _ _
      _ = ∑ A : {w : LevelWord ι j // w ∈ s},
            ((A.1.1.deg.map blk).map a).prod • (c ν A.1 • layerMk (hmw A.1)) :=
            (Finset.sum_coe_sort s _).symm
      _ = 0 := ha ν
  exact (layerMk_eq_zero_iff _).mp hfin

/-- The same count, phrased for prescribed elements of the layer itself rather than for elements of
the group. -/
theorem exists_ne_zero_forall_layerMap_eq_zero {x : ι → P}
    (hx : Subgroup.closure (Set.range x) = ⊤) (y : κ → Q) (σ : ι → κ) (blk : ι → Fin r)
    (ψ : (Fin r → ℕ) → P →* Q) (hψ : ∀ a i, ψ a (x i) = y (σ i) ^ a (blk i))
    (hr : (j + 1) * (t * Module.finrank (ZMod ℓ) (Layer ℓ Q j)) < r) (v : Fin t → Layer ℓ P j) :
    ∃ a : Fin r → ZMod ℓ, a ≠ 0 ∧
      ∀ ν, layerMap ℓ (ψ fun k => (a k).val) j (v ν) = 0 := by
  choose z hz hzv using fun ν => exists_layerMk (v ν)
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_map_mem_pCentral hx y σ blk ψ hψ hr hz
  refine ⟨a, ha0, fun ν => ?_⟩
  rw [← hzv ν, layerMap_layerMk, layerMk_eq_zero_iff]
  exact ha ν

end Count

/-! ### The generic instance -/

section Generic

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and killing finitely many prescribed
obstructions at once.**  Given finitely many elements of the `j`-th term of the descending
`ℓ`-central series of the generic operator group on `r` blocks of `n` letters, there is a vector of
exponents whose shrinking homomorphism is onto the generic operator group on `n` letters and pushes
all of them into the `(j + 1)`-st term, provided the number of blocks exceeds `j + 1` times the
number of scalar equations involved. -/
theorem exists_genericShrink_mem_pCentral {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t : ℕ}
    (hr : (j + 1) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    {z : Fin t → Generic U (r * n) S} (hz : ∀ ν, z ν ∈ pCentral ℓ (Generic U (r * n) S) j) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, genericShrink U r n S a (z ν) ∈ pCentral ℓ (Generic U n S) (j + 1) := by
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_map_mem_pCentral (ℓ := ℓ)
    (x := fun w : Fin (r * n) × U => (QuotientGroup.mk (FreeGroup.of w) : Generic U (r * n) S))
    (closure_range_mk_of U (r * n) S)
    (fun w : Fin n × U => (QuotientGroup.mk (FreeGroup.of w) : Generic U n S))
    (fun w => ((finProdFinEquiv.symm w.1).2, w.2)) (fun w => (finProdFinEquiv.symm w.1).1)
    (fun b => genericShrink U r n S b)
    (fun b w => by rw [genericShrink_mk, shrinkHom_of, QuotientGroup.mk_pow]) hr hz
  obtain ⟨k, hk⟩ := Function.ne_iff.mp ha0
  refine ⟨fun i => (a i).val, genericShrink_surjective U r n S hS _ k ?_, ha⟩
  refine hℓ.out.coprime_iff_not_dvd.mpr fun hd => absurd (Nat.le_of_dvd ?_ hd) ?_
  · exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero (a k)).mpr hk)
  · exact not_le.mpr (ZMod.val_lt (a k))

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and killing finitely many prescribed
elements of a layer at once.** -/
theorem exists_genericShrink_layerMap_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t : ℕ}
    (hr : (j + 1) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (v : Fin t → Layer ℓ (Generic U (r * n) S) j) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, layerMap ℓ (genericShrink U r n S a) j (v ν) = 0 := by
  choose z hz hzv using fun ν => exists_layerMk (v ν)
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_mem_pCentral U r n S hS hr hz
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hzv ν, layerMap_layerMk, layerMk_eq_zero_iff]
  exact ha ν

omit [Group U] in
/-- The same count for a family indexed by an arbitrary finite type. -/
theorem exists_genericShrink_forall_layerMap_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j : ℕ} {ι : Type*} [Finite ι]
    (hr : (j + 1) * (Nat.card ι * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (v : ι → Layer ℓ (Generic U (r * n) S) j) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, layerMap ℓ (genericShrink U r n S a) j (v ν) = 0 := by
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_layerMap_eq_zero U r n S hS hr
    (v ∘ (Finite.equivFin ι).symm)
  exact ⟨a, hsurj, fun ν => by simpa using ha (Finite.equivFin ι ν)⟩

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and killing finitely many prescribed
elements of a layer with coefficients at once.**  Extending the layer by a finite-dimensional
coefficient module multiplies the number of scalar equations by its dimension, which is again what
the bound on the number of blocks records. -/
theorem exists_genericShrink_rTensor_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S) {j t : ℕ}
    (T : Type*) [AddCommGroup T] [Module (ZMod ℓ) T] [Module.Finite (ZMod ℓ) T]
    (hr : (j + 1) * (t * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r)
    (v : Fin t → Layer ℓ (Generic U (r * n) S) j ⊗[ZMod ℓ] T) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, LinearMap.rTensor T (layerLinear ℓ (genericShrink U r n S a) j) (v ν) = 0 := by
  set d := Module.finrank (ZMod ℓ) T with hd
  choose w hw using fun ν => exists_sum_tmul_basis (Module.finBasis (ZMod ℓ) T) (v ν)
  have hr' : (j + 1) * (Nat.card (Fin t × Fin d)
      * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by
    refine lt_of_le_of_lt (le_of_eq ?_) hr
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin, Module.finrank_tensorProduct, ← hd]
    ring
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerMap_eq_zero U r n S hS hr'
    fun q : Fin t × Fin d => w q.1 q.2
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [hw ν, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.rTensor_tmul, layerLinear_apply, ha (ν, i), TensorProduct.zero_tmul]

/-! ### Equivariance -/

/-- **The operator group acts linearly on every layer of the generic operator group.** -/
def genericLayerRep (ℓ j : ℕ) : U →* Module.End (ZMod ℓ) (Layer ℓ (Generic U n S) j) :=
  (layerRep ℓ (Generic U n S) j).comp (genericAut U n S)

omit [Finite U] [Finite S] in
@[simp]
theorem genericLayerRep_apply (ℓ j : ℕ) (u : U) (v : Layer ℓ (Generic U n S) j) :
    genericLayerRep U n S ℓ j u v = layerMap ℓ (genericAut U n S u).toMonoidHom j v := rfl

omit [Finite U] [Finite S] in
/-- **The map of layers induced by a shrinking homomorphism is equivariant** for the action of the
operator group. -/
theorem layerMap_genericShrink_genericLayerRep (a : Fin r → ℕ) (ℓ j : ℕ) (u : U)
    (v : Layer ℓ (Generic U (r * n) S) j) :
    layerMap ℓ (genericShrink U r n S a) j (genericLayerRep U (r * n) S ℓ j u v)
      = genericLayerRep U n S ℓ j u (layerMap ℓ (genericShrink U r n S a) j v) :=
  layerMap_layerRep _ (genericShrink_comp_genericAut U r n S a u) v

end Generic

end InverseGalois.Shafarevich
