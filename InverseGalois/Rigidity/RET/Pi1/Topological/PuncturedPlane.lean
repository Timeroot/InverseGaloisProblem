/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Group
import InverseGalois.Rigidity.RET.Pi1.Topological.SphereBaseCase
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The fundamental group of the punctured plane

The complement of an `n`-element set of punctures in `ℂ` has free fundamental group on `n`
generators.  This is the analytic half of link **C**: combined with `Γ_r ≅ FreeGroup (Fin (r-1))`
it identifies the topological fundamental group of the `r`-punctured sphere (modelled as the plane
with `r - 1` punctures, the `r`-th puncture being `∞`) with the sphere presentation group `Γ_r`.

The proof is an induction on the number of punctures using the group-form Seifert–van Kampen
theorem `Rigidity.RET.VanKampen.coprodMulEquivPi1`.  After a linear change of coordinates the
punctures have pairwise distinct real parts, so a vertical line separates the rightmost puncture
from all the others; the two open half-planes it determines cover the punctured plane, and their
intersection is an open vertical strip missing every puncture, hence convex and simply connected.
One half-plane carries `n - 1` punctures (induction hypothesis) and the other exactly one
(`Complex.fundamentalGroupUnitsExp`), so `π₁` is the free product `F_{n-1} ∗ ℤ = F_n`.

Main results:

* `Monoid.Coprod.congr`, `Rigidity.RET.freeGroupCoprodEquiv` — the free product of free groups is
  free on the disjoint union of the bases;
* `Complex.leftHalfPlaneHomeo`, `Complex.rightHalfPlaneHomeo` — an open half-plane is homeomorphic
  to `ℂ`;
* `Rigidity.RET.pi1_compl_finset` — `π₁(ℂ ∖ S) ≅ FreeGroup (Fin S.card)`;
* `Rigidity.RET.pi1_compl_mulEquiv_sphereGroup` — `π₁(ℂ ∖ S) ≅ Γ_{S.card + 1}`.
-/

open scoped Multiplicative

universe u

namespace Monoid.Coprod

variable {M N M' N' : Type*} [Monoid M] [Monoid N] [Monoid M'] [Monoid N']

/-- **Functoriality of the binary free product in its factors.**  Isomorphisms of the two factors
induce an isomorphism of free products, acting factorwise. -/
def congr (e : M ≃* M') (f : N ≃* N') : Monoid.Coprod M N ≃* Monoid.Coprod M' N' where
  toFun := map e.toMonoidHom f.toMonoidHom
  invFun := map e.symm.toMonoidHom f.symm.toMonoidHom
  left_inv := by
    have h : (map e.symm.toMonoidHom f.symm.toMonoidHom).comp
        (map e.toMonoidHom f.toMonoidHom) = MonoidHom.id (Monoid.Coprod M N) :=
      hom_ext (MonoidHom.ext fun x => by simp [map_apply_inl])
        (MonoidHom.ext fun x => by simp [map_apply_inr])
    exact DFunLike.congr_fun h
  right_inv := by
    have h : (map e.toMonoidHom f.toMonoidHom).comp
        (map e.symm.toMonoidHom f.symm.toMonoidHom) = MonoidHom.id (Monoid.Coprod M' N') :=
      hom_ext (MonoidHom.ext fun x => by simp [map_apply_inl])
        (MonoidHom.ext fun x => by simp [map_apply_inr])
    exact DFunLike.congr_fun h
  map_mul' := map_mul _

end Monoid.Coprod

namespace Rigidity.RET

/-- **A free product of free groups is free.**  `F(α) ∗ F(β) ≅ F(α ⊕ β)`: both sides have the
universal property of the free group on the disjoint union of the two bases. -/
def freeGroupCoprodEquiv (α β : Type*) :
    Monoid.Coprod (FreeGroup α) (FreeGroup β) ≃* FreeGroup (α ⊕ β) where
  toFun := Monoid.Coprod.lift (FreeGroup.lift (fun a => FreeGroup.of (Sum.inl a)))
    (FreeGroup.lift (fun b => FreeGroup.of (Sum.inr b)))
  invFun := FreeGroup.lift
    (Sum.elim (fun a => Monoid.Coprod.inl (FreeGroup.of a))
      (fun b => Monoid.Coprod.inr (FreeGroup.of b)))
  left_inv := by
    have h : (FreeGroup.lift
        (Sum.elim (fun a => Monoid.Coprod.inl (FreeGroup.of a))
          (fun b => Monoid.Coprod.inr (FreeGroup.of b)))).comp
        (Monoid.Coprod.lift (FreeGroup.lift (fun a => FreeGroup.of (Sum.inl a)))
          (FreeGroup.lift (fun b => FreeGroup.of (Sum.inr b))))
        = MonoidHom.id (Monoid.Coprod (FreeGroup α) (FreeGroup β)) :=
      Monoid.Coprod.hom_ext (FreeGroup.ext_hom _ _ fun a => by simp)
        (FreeGroup.ext_hom _ _ fun b => by simp)
    exact DFunLike.congr_fun h
  right_inv := by
    have h : (Monoid.Coprod.lift (FreeGroup.lift (fun a => FreeGroup.of (Sum.inl a)))
        (FreeGroup.lift (fun b => FreeGroup.of (Sum.inr b)))).comp
        (FreeGroup.lift
          (Sum.elim (fun a => Monoid.Coprod.inl (FreeGroup.of a))
            (fun b => Monoid.Coprod.inr (FreeGroup.of b))))
        = MonoidHom.id (FreeGroup (α ⊕ β)) :=
      FreeGroup.ext_hom _ _ fun a => by cases a <;> simp
    exact DFunLike.congr_fun h
  map_mul' := map_mul _

/-- Adjoining one infinite-cyclic free factor to a free group of rank `n` gives the free group of
rank `n + 1`. -/
noncomputable def freeGroupCoprodIntEquiv (n : ℕ) :
    Monoid.Coprod (FreeGroup (Fin n)) (Multiplicative ℤ) ≃* FreeGroup (Fin (n + 1)) :=
  ((Monoid.Coprod.congr (MulEquiv.refl (FreeGroup (Fin n))) freeGroupFin1MulEquivInt.symm).trans
    (freeGroupCoprodEquiv (Fin n) (Fin 1))).trans (FreeGroup.freeGroupCongr finSumFinEquiv)

end Rigidity.RET

namespace Complex

/-- The coordinate map exhibiting the open half-plane `{z | z.re < c}` as a copy of `ℂ`: the
real part is stretched onto all of `ℝ` by `x ↦ log (c - x)` and the imaginary part is untouched. -/
noncomputable def leftHalfCoord (c : ℝ) (z : ℂ) : ℂ :=
  (Real.log (c - z.re) : ℂ) + (z.im : ℂ) * I

@[simp] theorem leftHalfCoord_re (c : ℝ) (z : ℂ) :
    (leftHalfCoord c z).re = Real.log (c - z.re) := by simp [leftHalfCoord]

@[simp] theorem leftHalfCoord_im (c : ℝ) (z : ℂ) : (leftHalfCoord c z).im = z.im := by
  simp [leftHalfCoord]

/-- The inverse coordinate map `ℂ → {z | z.re < c}`. -/
noncomputable def leftHalfCoordInv (c : ℝ) (w : ℂ) : ℂ :=
  ((c - Real.exp w.re : ℝ) : ℂ) + (w.im : ℂ) * I

@[simp] theorem leftHalfCoordInv_re (c : ℝ) (w : ℂ) :
    (leftHalfCoordInv c w).re = c - Real.exp w.re := by
  simp [leftHalfCoordInv, -Complex.ofReal_exp]

@[simp] theorem leftHalfCoordInv_im (c : ℝ) (w : ℂ) : (leftHalfCoordInv c w).im = w.im := by
  simp [leftHalfCoordInv]

theorem leftHalfCoordInv_mem (c : ℝ) (w : ℂ) : (leftHalfCoordInv c w).re < c := by
  simp only [leftHalfCoordInv_re]
  have := Real.exp_pos w.re
  linarith

theorem leftHalfCoordInv_leftHalfCoord {c : ℝ} {z : ℂ} (hz : z.re < c) :
    leftHalfCoordInv c (leftHalfCoord c z) = z := by
  apply Complex.ext <;> simp [Real.exp_log (by linarith : (0:ℝ) < c - z.re)]

theorem leftHalfCoord_leftHalfCoordInv (c : ℝ) (w : ℂ) :
    leftHalfCoord c (leftHalfCoordInv c w) = w := by
  apply Complex.ext <;> simp

/-- The left-half-plane coordinate is injective on the half-plane. -/
theorem leftHalfCoord_injOn (c : ℝ) : Set.InjOn (leftHalfCoord c) {z : ℂ | z.re < c} := by
  intro z hz w hw h
  rw [← leftHalfCoordInv_leftHalfCoord hz, ← leftHalfCoordInv_leftHalfCoord hw, h]

theorem continuous_leftHalfCoord (c : ℝ) :
    Continuous fun z : {z : ℂ // z.re < c} => leftHalfCoord c (z : ℂ) := by
  have hlog : Continuous fun z : {z : ℂ // z.re < c} => Real.log (c - (z : ℂ).re) :=
    Real.continuousOn_log.comp_continuous (by fun_prop) fun z => by
      have : (0:ℝ) < c - (z : ℂ).re := by have := z.2; simp at this; linarith
      simpa using ne_of_gt this
  unfold leftHalfCoord
  fun_prop

/-- **An open left half-plane is homeomorphic to the plane.** -/
noncomputable def leftHalfPlaneHomeo (c : ℝ) : {z : ℂ // z.re < c} ≃ₜ ℂ where
  toFun z := leftHalfCoord c (z : ℂ)
  invFun w := ⟨leftHalfCoordInv c w, leftHalfCoordInv_mem c w⟩
  left_inv z := Subtype.ext (leftHalfCoordInv_leftHalfCoord z.2)
  right_inv w := leftHalfCoord_leftHalfCoordInv c w
  continuous_toFun := continuous_leftHalfCoord c
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold leftHalfCoordInv
    fun_prop

@[simp] theorem leftHalfPlaneHomeo_apply (c : ℝ) (z : {z : ℂ // z.re < c}) :
    leftHalfPlaneHomeo c z = leftHalfCoord c (z : ℂ) := rfl

/-- **An open right half-plane is homeomorphic to the plane**, by reflecting it into a left
half-plane. -/
noncomputable def rightHalfPlaneHomeo (c : ℝ) : {z : ℂ // c < z.re} ≃ₜ ℂ :=
  ((Homeomorph.neg ℂ).subtype (q := fun z : ℂ => z.re < -c) (fun z => by
    show c < z.re ↔ (-z).re < -c
    simp only [neg_re]
    constructor <;> intro h <;> linarith)).trans (leftHalfPlaneHomeo (-c))

/-- The global coordinate underlying `rightHalfPlaneHomeo`. -/
noncomputable def rightHalfCoord (c : ℝ) (z : ℂ) : ℂ := leftHalfCoord (-c) (-z)

@[simp] theorem rightHalfPlaneHomeo_apply (c : ℝ) (z : {z : ℂ // c < z.re}) :
    rightHalfPlaneHomeo c z = rightHalfCoord c (z : ℂ) := rfl

theorem rightHalfCoord_injOn (c : ℝ) : Set.InjOn (rightHalfCoord c) {z : ℂ | c < z.re} := by
  intro z hz w hw h
  have hz' : (-z).re < -c := by simp only [neg_re]; simp at hz; linarith
  have hw' : (-w).re < -c := by simp only [neg_re]; simp at hw; linarith
  have := leftHalfCoord_injOn (-c) hz' hw' h
  simpa using congrArg Neg.neg this

end Complex

namespace Rigidity.RET

open Set Complex

section Subtypes

variable {X : Type*} [TopologicalSpace X]

/-- Two nested subtype conditions may be swapped. -/
def subtypeCommHomeo (p q : X → Prop) :
    {a : {x : X // p x} // q (a : X)} ≃ₜ {a : {x : X // q x} // p (a : X)} where
  toFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  invFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- A vacuous subtype condition may be dropped. -/
def subtypeAllHomeo {p : X → Prop} (h : ∀ x, p x) : {x : X // p x} ≃ₜ X where
  toFun := Subtype.val
  invFun x := ⟨x, h x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

end Subtypes

/-- **A punctured plane restricted to a planar region is a punctured plane.**  If `e` identifies a
subset `A ⊆ ℂ` with the whole plane and carries the punctures of `S` lying in `A` onto `T`, then the
part of `ℂ ∖ S` inside `A` is homeomorphic to `ℂ ∖ T`. -/
def puncturedRestrictHomeo {S T A : Set ℂ} (e : A ≃ₜ ℂ)
    (hT : ∀ a : A, (a : ℂ) ∉ S ↔ e a ∉ T) :
    {p : {z : ℂ // z ∉ S} // (p : ℂ) ∈ A} ≃ₜ {w : ℂ // w ∉ T} :=
  (subtypeCommHomeo (fun z : ℂ => z ∉ S) (fun z : ℂ => z ∈ A)).trans (e.subtype hT)

/-- `Pi1Free S n` records that the plane punctured along `S` has free fundamental group of rank
`n`, at every basepoint. -/
def Pi1Free (S : Set ℂ) (n : ℕ) : Prop :=
  ∀ (z₀ : ℂ) (hz₀ : z₀ ∉ S),
    Nonempty (FundamentalGroup {z : ℂ // z ∉ S} ⟨z₀, hz₀⟩ ≃* FreeGroup (Fin n))

/-- The complement of a countable set in the plane is path connected. -/
theorem pathConnectedSpace_punctured {S : Set ℂ} (hS : S.Countable) :
    PathConnectedSpace {z : ℂ // z ∉ S} := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  exact isPathConnected_iff_pathConnectedSpace.mp (hS.isPathConnected_compl_of_one_lt_rank hrank)

/-- Since the punctured plane is path connected, the rank computation at a single basepoint
suffices. -/
theorem pi1Free_of_basepoint {S : Set ℂ} (hS : S.Countable) {n : ℕ} {w : ℂ} (hw : w ∉ S)
    (h : Nonempty (FundamentalGroup {z : ℂ // z ∉ S} ⟨w, hw⟩ ≃* FreeGroup (Fin n))) :
    Pi1Free S n := by
  haveI := pathConnectedSpace_punctured hS
  intro z₀ hz₀
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    (X := {z : ℂ // z ∉ S}) ⟨z₀, hz₀⟩ ⟨w, hw⟩).trans h.some⟩

/-- A self-homeomorphism of the plane matching two puncture sets transports the rank
computation. -/
theorem Pi1Free.map {S T : Set ℂ} {n : ℕ} (e : ℂ ≃ₜ ℂ) (hST : ∀ z : ℂ, z ∈ S ↔ e z ∈ T)
    (h : Pi1Free T n) : Pi1Free S n := by
  intro z₀ hz₀
  have hiff : ∀ z : ℂ, z ∉ S ↔ e z ∉ T := fun z => not_congr (hST z)
  exact ⟨((e.subtype hiff).fundamentalGroupMulEquiv ⟨z₀, hz₀⟩).trans
    (h (e z₀) ((hiff z₀).1 hz₀)).some⟩

/-- The unpunctured plane, presented as a subtype. -/
def emptyPuncturedHomeo : {z : ℂ // z ∉ (∅ : Set ℂ)} ≃ₜ ℂ := subtypeAllHomeo fun _ => id

/-- **No punctures: the plane is simply connected.** -/
theorem pi1Free_empty : Pi1Free (∅ : Set ℂ) 0 := by
  intro z₀ hz₀
  exact ⟨(emptyPuncturedHomeo.fundamentalGroupMulEquiv ⟨z₀, hz₀⟩).trans mulEquivOfSubsingleton⟩

/-- **One puncture at the origin: the fundamental group is infinite cyclic.** -/
theorem pi1Free_zero : Pi1Free ({0} : Set ℂ) 1 := by
  refine pi1Free_of_basepoint (Set.countable_singleton 0) (w := Complex.exp 0)
    (by simp) ⟨?_⟩
  exact Complex.fundamentalGroupUnitsExp.trans freeGroupFin1MulEquivInt.symm

/-- **One puncture: the fundamental group is infinite cyclic.** -/
theorem pi1Free_singleton (q : ℂ) : Pi1Free ({q} : Set ℂ) 1 :=
  Pi1Free.map (Homeomorph.addRight (-q)) (fun z => by
    show z ∈ ({q} : Set ℂ) ↔ z + -q ∈ ({0} : Set ℂ)
    simp [Set.mem_singleton_iff, add_neg_eq_zero]) pi1Free_zero

/-- **A generic direction separates finitely many points.**  For a finite set of complex numbers
there is a nonzero `u` for which the real parts of `u · z` are pairwise distinct. -/
theorem exists_re_injOn (S : Finset ℂ) :
    ∃ u : ℂ, u ≠ 0 ∧ Set.InjOn (fun z : ℂ => (u * z).re) (S : Set ℂ) := by
  classical
  set B : Finset ℝ :=
    (S ×ˢ S).image (fun pq : ℂ × ℂ => (pq.1.re - pq.2.re) / (pq.1.im - pq.2.im)) with hB
  obtain ⟨t, ht⟩ := B.finite_toSet.infinite_compl.nonempty
  have hre : ∀ z : ℂ, ((1 + (t : ℂ) * Complex.I) * z).re = z.re - t * z.im := by
    intro z; simp [Complex.mul_re]
  refine ⟨1 + (t : ℂ) * Complex.I, ?_, ?_⟩
  · intro h
    have h1 : ((1 : ℂ) + (t : ℂ) * Complex.I).re = 0 := by rw [h]; simp
    simp [Complex.add_re, Complex.mul_re] at h1
  · intro z hz w hw hzw
    simp only [hre] at hzw
    by_cases him : z.im = w.im
    · exact Complex.ext (by rw [him] at hzw; linarith) him
    · exfalso
      apply ht
      have hne : z.im - w.im ≠ 0 := sub_ne_zero.mpr him
      rw [Finset.mem_coe, hB, Finset.mem_image]
      refine ⟨(z, w), Finset.mem_product.mpr ⟨Finset.mem_coe.mp hz, Finset.mem_coe.mp hw⟩, ?_⟩
      field_simp
      linear_combination hzw


/-- **Free product form of Seifert–van Kampen.**  If a space is covered by two open, path connected
sets with simply connected intersection, both containing the basepoint, and their fundamental groups
are free of ranks `m` and `k`, then the fundamental group of the whole space is free of rank
`m + k`. -/
theorem freeProduct_of_cover {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = Set.univ)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace ↥(U ∩ V)]
    {m k : ℕ}
    (hU : Nonempty (FundamentalGroup U ⟨x, hxU⟩ ≃* FreeGroup (Fin m)))
    (hV : Nonempty (FundamentalGroup V ⟨x, hxV⟩ ≃* FreeGroup (Fin k))) :
    Nonempty (FundamentalGroup X x ≃* FreeGroup (Fin (m + k))) :=
  ⟨(((Monoid.Coprod.congr hU.some hV.some).symm.trans
        (VanKampen.coprodMulEquivPi1 U V hxU hxV hUV hUopen hVopen)).symm.trans
      ((freeGroupCoprodEquiv (Fin m) (Fin k)).trans
        (FreeGroup.freeGroupCongr finSumFinEquiv)))⟩

/-- **Splitting a punctured plane along a vertical line.**  If no puncture has real part in
`[c', c]`, the two open half-planes `re < c` and `re > c'` cover the punctured plane, meet in a
convex (hence simply connected) strip, and are themselves punctured planes with puncture sets `TU`
and `TV` in the coordinates supplied by `leftHalfPlaneHomeo` and `rightHalfPlaneHomeo`.  Van Kampen
then adds the two ranks. -/
theorem pi1Free_of_split {S TU TV : Set ℂ} (hS : S.Countable)
    (hTU : TU.Countable) (hTV : TV.Countable) {c' c : ℝ} (hc'c : c' < c)
    (hstrip : ∀ q ∈ S, q.re < c' ∨ c < q.re)
    (hU : ∀ a : {z : ℂ // z.re < c}, (a : ℂ) ∉ S ↔ Complex.leftHalfPlaneHomeo c a ∉ TU)
    (hV : ∀ a : {z : ℂ // c' < z.re}, (a : ℂ) ∉ S ↔ Complex.rightHalfPlaneHomeo c' a ∉ TV)
    {m k : ℕ} (hm : Pi1Free TU m) (hk : Pi1Free TV k) :
    Pi1Free S (m + k) := by
  classical
  have hmid : (((c + c') / 2 : ℝ) : ℂ).re = (c + c') / 2 := Complex.ofReal_re _
  have hwS : (((c + c') / 2 : ℝ) : ℂ) ∉ S := by
    intro hmem
    rcases hstrip _ hmem with h | h <;> rw [hmid] at h <;> linarith
  refine pi1Free_of_basepoint hS hwS ?_
  set x : {z : ℂ // z ∉ S} := ⟨(((c + c') / 2 : ℝ) : ℂ), hwS⟩ with hxdef
  have hxU : x ∈ {w : {z : ℂ // z ∉ S} | (w : ℂ).re < c} := by
    show (((c + c') / 2 : ℝ) : ℂ).re < c
    rw [hmid]; linarith
  have hxV : x ∈ {w : {z : ℂ // z ∉ S} | c' < (w : ℂ).re} := by
    show c' < (((c + c') / 2 : ℝ) : ℂ).re
    rw [hmid]; linarith
  have hUopen : IsOpen {w : {z : ℂ // z ∉ S} | (w : ℂ).re < c} :=
    (isOpen_lt Complex.continuous_re continuous_const).preimage continuous_subtype_val
  have hVopen : IsOpen {w : {z : ℂ // z ∉ S} | c' < (w : ℂ).re} :=
    (isOpen_lt continuous_const Complex.continuous_re).preimage continuous_subtype_val
  have hUV : {w : {z : ℂ // z ∉ S} | (w : ℂ).re < c} ∪
      {w : {z : ℂ // z ∉ S} | c' < (w : ℂ).re} = Set.univ := by
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : (w : ℂ).re < c
    · exact Or.inl h
    · push_neg at h; exact Or.inr (by linarith)
  -- the two half-planes are punctured planes
  have EU : ({w : {z : ℂ // z ∉ S} | (w : ℂ).re < c} : Set {z : ℂ // z ∉ S}) ≃ₜ
      {z : ℂ // z ∉ TU} :=
    puncturedRestrictHomeo (A := {z : ℂ | z.re < c}) (Complex.leftHalfPlaneHomeo c) hU
  have EV : ({w : {z : ℂ // z ∉ S} | c' < (w : ℂ).re} : Set {z : ℂ // z ∉ S}) ≃ₜ
      {z : ℂ // z ∉ TV} :=
    puncturedRestrictHomeo (A := {z : ℂ | c' < z.re}) (Complex.rightHalfPlaneHomeo c') hV
  haveI : PathConnectedSpace ({w : {z : ℂ // z ∉ S} | (w : ℂ).re < c} : Set {z : ℂ // z ∉ S}) := by
    haveI := pathConnectedSpace_punctured hTU
    exact EU.symm.surjective.pathConnectedSpace EU.symm.continuous
  haveI : PathConnectedSpace ({w : {z : ℂ // z ∉ S} | c' < (w : ℂ).re} : Set {z : ℂ // z ∉ S}) := by
    haveI := pathConnectedSpace_punctured hTV
    exact EV.symm.surjective.pathConnectedSpace EV.symm.continuous
  -- the overlap is a convex strip
  have hOverlapNone : ∀ b : ({z : ℂ | z.re < c} ∩ {z : ℂ | c' < z.re} : Set ℂ), (b : ℂ) ∉ S := by
    rintro ⟨b, hb1, hb2⟩ hb
    simp only [Set.mem_setOf_eq] at hb1 hb2
    rcases hstrip _ hb with h | h <;> linarith
  have EW : (({w : {z : ℂ // z ∉ S} | (w : ℂ).re < c} ∩
      {w : {z : ℂ // z ∉ S} | c' < (w : ℂ).re} : Set {z : ℂ // z ∉ S})) ≃ₜ
      ({z : ℂ | z.re < c} ∩ {z : ℂ | c' < z.re} : Set ℂ) :=
    (subtypeCommHomeo (fun z : ℂ => z ∉ S)
      (fun z : ℂ => z ∈ ({z : ℂ | z.re < c} ∩ {z : ℂ | c' < z.re} : Set ℂ))).trans
      (subtypeAllHomeo hOverlapNone)
  haveI : ContractibleSpace ({z : ℂ | z.re < c} ∩ {z : ℂ | c' < z.re} : Set ℂ) :=
    Convex.contractibleSpace ((convex_halfSpace_re_lt c).inter (convex_halfSpace_re_gt c'))
      ⟨(((c + c') / 2 : ℝ) : ℂ), by
        refine ⟨?_, ?_⟩ <;> simp only [Set.mem_setOf_eq, hmid] <;> linarith⟩
  haveI : ContractibleSpace (({w : {z : ℂ // z ∉ S} | (w : ℂ).re < c} ∩
      {w : {z : ℂ // z ∉ S} | c' < (w : ℂ).re} : Set {z : ℂ // z ∉ S})) := EW.contractibleSpace
  refine freeProduct_of_cover hUopen hVopen hUV hxU hxV ?_ ?_
  · exact ⟨(EU.fundamentalGroupMulEquiv ⟨x, hxU⟩).trans (hm _ (EU ⟨x, hxU⟩).2).some⟩
  · exact ⟨(EV.fundamentalGroupMulEquiv ⟨x, hxV⟩).trans (hk _ (EV ⟨x, hxV⟩).2).some⟩

/-- **Induction step.**  A plane punctured at `n + 1` points with pairwise distinct real parts is
split by a vertical line just to the left of the rightmost puncture: the left piece is a plane
punctured at the remaining `n` points, the right piece a plane punctured at one point. -/
theorem pi1Free_step {n : ℕ} (ih : ∀ S : Finset ℂ, S.card = n → Pi1Free (S : Set ℂ) n)
    (S : Finset ℂ) (hcard : S.card = n + 1) (hinj : Set.InjOn Complex.re (S : Set ℂ)) :
    Pi1Free (S : Set ℂ) (n + 1) := by
  classical
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hpS, hpmax⟩ := S.exists_max_image Complex.re hSne
  have hS'card : (S.erase p).card = n := by
    rw [Finset.card_erase_of_mem hpS, hcard]
    omega
  have hS'sub : ∀ q ∈ S.erase p, q ∈ S := fun q hq => Finset.mem_of_mem_erase hq
  -- an abscissa `d` bounding all the other punctures, strictly left of `p`
  obtain ⟨d, hdS', hdlt⟩ : ∃ d : ℝ, (∀ q ∈ S.erase p, q.re ≤ d) ∧ d < p.re := by
    refine ⟨(insert (p.re - 1) ((S.erase p).image Complex.re)).max'
        ⟨p.re - 1, Finset.mem_insert_self _ _⟩,
      fun q hq => Finset.le_max' _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)), ?_⟩
    have hmem := Finset.max'_mem (insert (p.re - 1) ((S.erase p).image Complex.re))
      ⟨p.re - 1, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]; linarith
    · obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp h
      rw [← hq']
      refine lt_of_le_of_ne (hpmax q (hS'sub q hq)) (fun hc => ?_)
      exact (Finset.ne_of_mem_erase hq)
        (hinj (Finset.mem_coe.mpr (hS'sub q hq)) (Finset.mem_coe.mpr hpS) hc)
  obtain ⟨c', c, hdc', hc'c, hcp⟩ : ∃ c' c : ℝ, d < c' ∧ c' < c ∧ c < p.re :=
    ⟨d + (p.re - d) / 3, d + 2 * (p.re - d) / 3, by linarith, by linarith, by linarith⟩
  have hstrip : ∀ q ∈ (S : Set ℂ), q.re < c' ∨ c < q.re := by
    intro q hq
    by_cases h : q = p
    · exact Or.inr (by rw [h]; exact hcp)
    · exact Or.inl (lt_of_le_of_lt
        (hdS' q (Finset.mem_erase.mpr ⟨h, Finset.mem_coe.mp hq⟩)) hdc')
  -- the left piece is a plane punctured at the images of the remaining punctures
  have hinjOn : Set.InjOn (Complex.leftHalfCoord c) ((S.erase p : Finset ℂ) : Set ℂ) := by
    refine (Complex.leftHalfCoord_injOn c).mono fun q hq => ?_
    exact lt_of_le_of_lt (hdS' q (Finset.mem_coe.mp hq)) (by linarith)
  have hTUcard : ((S.erase p).image (Complex.leftHalfCoord c)).card = n := by
    rw [Finset.card_image_of_injOn hinjOn, hS'card]
  refine pi1Free_of_split (S := (S : Set ℂ))
    (TU := (((S.erase p).image (Complex.leftHalfCoord c) : Finset ℂ) : Set ℂ))
    (TV := ({Complex.rightHalfCoord c' p} : Set ℂ))
    S.finite_toSet.countable (Finset.finite_toSet _).countable (Set.countable_singleton _)
    hc'c hstrip ?_ ?_ (ih _ hTUcard) (pi1Free_singleton _)
  · rintro ⟨a, ha⟩
    refine not_congr ?_
    rw [Complex.leftHalfPlaneHomeo_apply]
    simp only [Finset.mem_coe, Finset.mem_image]
    constructor
    · intro haS
      have hane : a ≠ p := fun h => by rw [h] at ha; linarith
      exact ⟨a, Finset.mem_erase.mpr ⟨hane, Finset.mem_coe.mp haS⟩, rfl⟩
    · rintro ⟨q, hq, hqa⟩
      have hqc : q.re < c := lt_of_le_of_lt (hdS' q hq) (by linarith)
      have hqa' : q = a := Complex.leftHalfCoord_injOn c hqc ha hqa
      rw [← hqa']
      exact hS'sub q hq
  · rintro ⟨a, ha⟩
    refine not_congr ?_
    rw [Complex.rightHalfPlaneHomeo_apply]
    simp only [Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · intro haS
      have hap : a = p := by
        by_contra hne
        have := hdS' a (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp haS⟩)
        linarith
      rw [hap]
    · intro h
      have hp' : c' < p.re := by linarith
      rw [Complex.rightHalfCoord_injOn c' ha hp' h]
      exact hpS

/-- **The fundamental group of a plane punctured at `n` points is free of rank `n`.** -/
theorem pi1Free_of_card : ∀ (n : ℕ) (S : Finset ℂ), S.card = n → Pi1Free (S : Set ℂ) n := by
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero] at hS
    subst hS
    simpa using pi1Free_empty
  | succ n ih =>
    intro S hS
    obtain ⟨u, hu, hinj⟩ := exists_re_injOn S
    have hTcard : (S.image (fun z => u * z)).card = n + 1 := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ hu), hS]
    have hTinj : Set.InjOn Complex.re ((S.image (fun z => u * z) : Finset ℂ) : Set ℂ) := by
      intro x hx y hy hxy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact congrArg (fun w => u * w)
        (hinj (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy') hxy)
    refine Pi1Free.map (Homeomorph.mulLeft₀ u hu) (fun z => ?_)
      (pi1Free_step ih _ hTcard hTinj)
    show z ∈ (S : Set ℂ) ↔ u * z ∈ ((S.image (fun z => u * z) : Finset ℂ) : Set ℂ)
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨w, hw, hwz⟩ => by
      rwa [mul_right_injective₀ hu hwz] at hw⟩

/-- **The fundamental group of `ℂ` minus a finite set `S` is free of rank `S.card`.** -/
theorem pi1_compl_finset (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ)) :
    Nonempty (FundamentalGroup {z : ℂ // z ∉ (S : Set ℂ)} ⟨z₀, hz₀⟩ ≃* FreeGroup (Fin S.card)) :=
  pi1Free_of_card S.card S rfl z₀ hz₀

/-- **Link C, general `r`.**  The `r`-punctured sphere, modelled as the plane punctured at
`r - 1 = S.card` points (the last puncture being `∞`), has fundamental group the sphere
presentation group `Γ_r`. -/
theorem pi1_compl_mulEquiv_sphereGroup (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ)) :
    Nonempty (FundamentalGroup {z : ℂ // z ∉ (S : Set ℂ)} ⟨z₀, hz₀⟩ ≃*
      SphereGroup (S.card + 1)) :=
  ⟨(pi1_compl_finset S z₀ hz₀).some.trans
    (sphereGroup_mulEquiv_free (r := S.card + 1) (by omega)).some.symm⟩

end Rigidity.RET
