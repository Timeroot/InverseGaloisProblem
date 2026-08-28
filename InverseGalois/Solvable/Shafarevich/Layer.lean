/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.PCentralSpan

/-!
# The layers of the descending `p`-central series as vector spaces

Consecutive terms of the descending `p`-central series differ by a group that is abelian and killed
by `p`, so it is a vector space over `ZMod p`.  Realising it as the image of `pCentral p P n` in the
quotient by `pCentral p P (n + 1)` makes the comparison of two elements read as a membership in the
next term, which is the form in which every commutator estimate is available.

The counting argument of Shafarevich's construction takes place in this vector space, and the input
it needs is a spanning family.  One comes for free from the words that generate a layer: whenever a
family of elements of `pCentral p P n` generates it modulo the next term, the classes of those
elements span the layer.

## Main definitions

* `InverseGalois.Shafarevich.layerSub` — the `n`-th layer as a central subgroup of the quotient by
  the `(n + 1)`-st term.
* `InverseGalois.Shafarevich.Layer` — the same group written additively, a `ZMod p`-vector space.
* `InverseGalois.Shafarevich.layerMk` — the class of an element of the `n`-th term.
* `InverseGalois.Shafarevich.layerMap` — the map of layers induced by a homomorphism, and
  `InverseGalois.Shafarevich.layerLinear`, the same map read as a linear map.
* `InverseGalois.Shafarevich.layerRep` — the resulting linear action of the automorphism group of
  the group on each of its layers.

## Main results

* `InverseGalois.Shafarevich.layerMk_eq_iff` — two elements have the same class exactly when their
  quotient lies in the next term.
* `InverseGalois.Shafarevich.span_layerMk_eq_top` — **a family generating the `n`-th term modulo the
  next one spans the layer.**
* `InverseGalois.Shafarevich.layerMap_layerRep` — the map of layers induced by an equivariant
  homomorphism is equivariant.

## Tags

p-central series, elementary abelian, Shafarevich's theorem, embedding problem
-/

namespace InverseGalois.Shafarevich

/-! ### The layer as a central subgroup -/

section Sub

variable (p : ℕ) (P : Type*) [Group P] (n : ℕ)

/-- **The `n`-th layer of the descending `p`-central series**, as a subgroup of the quotient by the
next term.  It is central there and killed by `p`. -/
def layerSub : Subgroup (P ⧸ pCentral p P (n + 1)) :=
  (pCentral p P n).map (QuotientGroup.mk' (pCentral p P (n + 1)))

variable {p P n}

theorem mk_mem_layerSub {x : P} (hx : x ∈ pCentral p P n) :
    (QuotientGroup.mk x : P ⧸ pCentral p P (n + 1)) ∈ layerSub p P n :=
  ⟨x, hx, rfl⟩

theorem layerSub_le_center : layerSub p P n ≤ Subgroup.center (P ⧸ pCentral p P (n + 1)) :=
  map_pCentral_le_center p n

theorem pow_eq_one_of_mem_layerSub {y : P ⧸ pCentral p P (n + 1)} (hy : y ∈ layerSub p P n) :
    y ^ p = 1 := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact pow_mem_pCentral_succ p hx

variable (p P n)

instance : CommGroup ↥(layerSub p P n) :=
  { inferInstanceAs (Group ↥(layerSub p P n)) with
    mul_comm := fun y z =>
      Subtype.ext (Subgroup.mem_center_iff.mp (layerSub_le_center y.2) (z : _)).symm }

end Sub

/-! ### The layer as a vector space -/

section Layer

variable (p : ℕ) (P : Type*) [Group P] (n : ℕ)

/-- The `n`-th layer of the descending `p`-central series, written additively. -/
abbrev Layer : Type _ := Additive ↥(layerSub p P n)

variable {p P n}

/-- **The class of an element of the `n`-th term in the `n`-th layer.** -/
def layerMk {x : P} (hx : x ∈ pCentral p P n) : Layer p P n :=
  Additive.ofMul ⟨QuotientGroup.mk x, mk_mem_layerSub hx⟩

theorem layerMk_eq_iff {x y : P} (hx : x ∈ pCentral p P n) (hy : y ∈ pCentral p P n) :
    layerMk hx = layerMk hy ↔ x / y ∈ pCentral p P (n + 1) := by
  simp only [layerMk, Equiv.apply_eq_iff_eq, Subtype.mk.injEq]
  exact QuotientGroup.eq_iff_div_mem

theorem layerMk_one : layerMk (one_mem (pCentral p P n)) = 0 := rfl

theorem layerMk_mul {x y : P} (hx : x ∈ pCentral p P n) (hy : y ∈ pCentral p P n) :
    layerMk (mul_mem hx hy) = layerMk hx + layerMk hy := rfl

theorem layerMk_inv {x : P} (hx : x ∈ pCentral p P n) :
    layerMk (inv_mem hx) = -layerMk hx := rfl

theorem layerMk_pow {x : P} (hx : x ∈ pCentral p P n) (k : ℕ) :
    layerMk (pow_mem hx k) = k • layerMk hx := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : layerMk (pow_mem hx (k + 1)) = layerMk (pow_mem hx k) + layerMk hx := by
      rw [← layerMk_mul (pow_mem hx k) hx]
      congr 1
      exact pow_succ x k
    rw [h, ih, succ_nsmul]

theorem layerMk_eq_zero_iff {x : P} (hx : x ∈ pCentral p P n) :
    layerMk hx = 0 ↔ x ∈ pCentral p P (n + 1) := by
  rw [← layerMk_one (p := p) (P := P) (n := n), layerMk_eq_iff, div_one]

/-- Every element of a layer is the class of an element of the corresponding term. -/
theorem exists_layerMk (v : Layer p P n) :
    ∃ (x : P) (hx : x ∈ pCentral p P n), layerMk hx = v := by
  obtain ⟨x, hx, hxv⟩ := (Additive.toMul v).2
  exact ⟨x, hx, Additive.toMul.injective (Subtype.ext hxv)⟩

variable (p P n)

instance : Module (ZMod p) (Layer p P n) :=
  AddCommGroup.zmodModule fun v => by
    obtain ⟨x, hx, rfl⟩ := exists_layerMk v
    rw [← layerMk_pow hx p, layerMk_eq_zero_iff]
    exact pow_mem_pCentral_succ p hx

instance [Finite P] : Module.Finite (ZMod p) (Layer p P n) := Module.Finite.of_finite

end Layer

/-! ### Functoriality -/

section Map

variable {p : ℕ} {P Q : Type*} [Group P] [Group Q] {n : ℕ}

theorem map_mem_pCentral (f : P →* Q) {x : P} (hx : x ∈ pCentral p P n) :
    f x ∈ pCentral p Q n :=
  map_pCentral_le p f n ⟨x, hx, rfl⟩

/-- The homomorphism induced by `f` between the quotients by the `(n + 1)`-st terms. -/
def quotientMap (p : ℕ) (f : P →* Q) (n : ℕ) :
    P ⧸ pCentral p P (n + 1) →* Q ⧸ pCentral p Q (n + 1) :=
  QuotientGroup.map _ _ f (Subgroup.map_le_iff_le_comap.mp (map_pCentral_le p f (n + 1)))

@[simp]
theorem quotientMap_mk (f : P →* Q) (x : P) :
    quotientMap p f n (QuotientGroup.mk x) = QuotientGroup.mk (f x) := rfl

/-- The homomorphism induced by `f` between the `n`-th layers, multiplicatively. -/
def layerSubMap (p : ℕ) (f : P →* Q) (n : ℕ) : ↥(layerSub p P n) →* ↥(layerSub p Q n) :=
  MonoidHom.codRestrict ((quotientMap p f n).comp (layerSub p P n).subtype) _ <| by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨f x, map_mem_pCentral f hx, rfl⟩

/-- **The homomorphism induced by `f` between the `n`-th layers.** -/
def layerMap (p : ℕ) (f : P →* Q) (n : ℕ) : Layer p P n →+ Layer p Q n :=
  MonoidHom.toAdditive (layerSubMap p f n)

@[simp]
theorem layerMap_layerMk (f : P →* Q) {x : P} (hx : x ∈ pCentral p P n) :
    layerMap p f n (layerMk hx) = layerMk (map_mem_pCentral f hx) := rfl

theorem layerMap_smul (f : P →* Q) (c : ZMod p) (v : Layer p P n) :
    layerMap p f n (c • v) = c • layerMap p f n v :=
  ZMod.map_smul _ c v

/-- **The linear map of layers induced by a homomorphism.** -/
def layerLinear (p : ℕ) (f : P →* Q) (n : ℕ) : Layer p P n →ₗ[ZMod p] Layer p Q n where
  toFun := layerMap p f n
  map_add' := map_add _
  map_smul' := layerMap_smul f

@[simp]
theorem layerLinear_apply (f : P →* Q) (v : Layer p P n) :
    layerLinear p f n v = layerMap p f n v := rfl

@[simp]
theorem layerMap_id : layerMap p (MonoidHom.id P) n = AddMonoidHom.id (Layer p P n) := by
  ext v
  obtain ⟨x, hx, rfl⟩ := exists_layerMk v
  rfl

theorem layerMap_comp {R : Type*} [Group R] (g : Q →* R) (f : P →* Q) :
    layerMap p (g.comp f) n = (layerMap p g n).comp (layerMap p f n) := by
  ext v
  obtain ⟨x, hx, rfl⟩ := exists_layerMk v
  rfl

end Map

/-! ### The layer as a module over the operators -/

section Aut

variable {p : ℕ} {P Q : Type*} [Group P] [Group Q] {n : ℕ}

/-- The isomorphism of layers induced by an isomorphism of groups. -/
def layerCongr (p : ℕ) (e : P ≃* Q) (n : ℕ) : Layer p P n ≃+ Layer p Q n where
  toFun := layerMap p e.toMonoidHom n
  invFun := layerMap p e.symm.toMonoidHom n
  left_inv v := by
    rw [← AddMonoidHom.comp_apply, ← layerMap_comp,
      show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id P from
        MonoidHom.ext e.symm_apply_apply, layerMap_id, AddMonoidHom.id_apply]
  right_inv v := by
    rw [← AddMonoidHom.comp_apply, ← layerMap_comp,
      show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Q from
        MonoidHom.ext e.apply_symm_apply, layerMap_id, AddMonoidHom.id_apply]
  map_add' := map_add _

@[simp]
theorem layerCongr_apply (e : P ≃* Q) (v : Layer p P n) :
    layerCongr p e n v = layerMap p e.toMonoidHom n v := rfl

variable (p P n)

/-- **The layers of a group are representations of its automorphism group over `ZMod p`.**  Every
term of the descending `p`-central series is characteristic, so an automorphism of the group acts
linearly on every layer. -/
def layerRep : MulAut P →* Module.End (ZMod p) (Layer p P n) where
  toFun e := layerLinear p e.toMonoidHom n
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, hx, rfl⟩ := exists_layerMk v
    rfl
  map_mul' e e' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, hx, rfl⟩ := exists_layerMk v
    rfl

variable {p P n}

@[simp]
theorem layerRep_apply (e : MulAut P) (v : Layer p P n) :
    layerRep p P n e v = layerMap p e.toMonoidHom n v := rfl

/-- **The map of layers induced by an equivariant homomorphism is equivariant.** -/
theorem layerMap_layerRep (f : P →* Q) {e : MulAut P} {e' : MulAut Q}
    (h : f.comp e.toMonoidHom = e'.toMonoidHom.comp f) (v : Layer p P n) :
    layerMap p f n (layerRep p P n e v) = layerRep p Q n e' (layerMap p f n v) := by
  have h1 : layerMap p (f.comp e.toMonoidHom) n v = layerMap p (e'.toMonoidHom.comp f) n v := by
    rw [h]
  rw [layerMap_comp, layerMap_comp] at h1
  exact h1

end Aut

/-! ### Spanning the layer -/

section Span

variable {p : ℕ} {P : Type*} [Group P] {n : ℕ}

/-- **A family generating the `n`-th term of the descending `p`-central series modulo the next one
spans the `n`-th layer.** -/
theorem span_layerMk_eq_top {ι : Type*} (g : ι → P) (hg : ∀ i, g i ∈ pCentral p P n)
    (hsup : pCentral p P n = Subgroup.closure (Set.range g) ⊔ pCentral p P (n + 1)) :
    Submodule.span (ZMod p) (Set.range fun i => layerMk (hg i)) = ⊤ := by
  set T := Submodule.span (ZMod p) (Set.range fun i => layerMk (hg i))
  have hclosure : ∀ y ∈ Subgroup.closure (Set.range g),
      ∃ hy : y ∈ pCentral p P n, layerMk hy ∈ T := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨hg i, Submodule.subset_span ⟨i, rfl⟩⟩
    | one => exact ⟨one_mem _, by rw [layerMk_one]; exact zero_mem T⟩
    | mul z z' _ _ ihz ihz' =>
      obtain ⟨hz, hzT⟩ := ihz
      obtain ⟨hz', hz'T⟩ := ihz'
      exact ⟨mul_mem hz hz', by rw [layerMk_mul hz hz']; exact add_mem hzT hz'T⟩
    | inv z _ ihz =>
      obtain ⟨hz, hzT⟩ := ihz
      exact ⟨inv_mem hz, by rw [layerMk_inv hz]; exact neg_mem hzT⟩
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  obtain ⟨z, hz, rfl⟩ := exists_layerMk v
  have hz' : z ∈ Subgroup.closure (Set.range g) ⊔ pCentral p P (n + 1) := hsup ▸ hz
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hz'
  obtain ⟨y, hy, u, hu, rfl⟩ := hz'
  obtain ⟨hyn, hyT⟩ := hclosure y hy
  have hnorm : (pCentral p P (n + 1)).Normal := inferInstance
  have hdiv : y * u / y ∈ pCentral p P (n + 1) := by
    rw [div_eq_mul_inv]
    exact hnorm.conj_mem u hu y
  rwa [(layerMk_eq_iff hz hyn).mpr hdiv]

end Span

end InverseGalois.Shafarevich
