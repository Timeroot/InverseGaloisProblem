/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Herbrand

/-!
# Shapiro's lemma for a cyclic group

A module over a subgroup of a cyclic group induces one over the whole group: if `τ` is an
automorphism of `B` of order dividing `m`, the induced module is the group of `d`-tuples of
elements of `B`, cyclically permuted by an automorphism `σ` whose `d`-th power applies `τ` in every
coordinate.  Then `σ` has order dividing `d * m`, and Shapiro's lemma says that the Tate groups of
the induced module are those of `B` itself.

Both isomorphisms are given by explicit maps.  A fixed point of `σ` is a constant tuple whose value
is fixed by `τ`, so evaluation at the coordinate `0` identifies the fixed points of the two modules;
under it the norm of `σ` becomes the norm of `τ` applied to the sum of the coordinates, which gives
the upper Tate group.  For the lower one the sum of the coordinates is the right map: it carries
the norm-zero tuples to the norm-zero elements and the differences to the differences, and the
tuple supported at `0` is a section of it.

Both statements are needed for the local decomposition of the ideles of a cyclic extension, where
the places above a fixed place of the base field form a single orbit and so contribute an induced
module; Shapiro's lemma replaces that contribution by the local module at one place.

## Main definitions

* `InverseGalois.CFT.indAut`: the automorphism of the induced module.
* `InverseGalois.CFT.tateH0IndEquiv`, `InverseGalois.CFT.tateHm1IndEquiv`: **Shapiro's lemma**, the
  Tate groups of the induced module are those of the original module.

## Main results

* `InverseGalois.CFT.normHom_mul`: the norm of a composite order factors through the norm of the
  intermediate one.
* `InverseGalois.CFT.pow_card_indAut_apply`: the `d`-th power of the induced automorphism applies
  `τ` in every coordinate.
* `InverseGalois.CFT.herbrand_indAut`: **the Herbrand quotient of an induced module is that of the
  module it is induced from.**

## Tags

Tate cohomology, Shapiro's lemma, induced module, Herbrand quotient
-/

namespace InverseGalois.CFT

/-! ### Splitting the norm along a factorisation of the order -/

section NormMul

variable {M : Type*} [AddCommGroup M]

/-- Applying a sum of powers of `σ` means applying the two powers in turn. -/
theorem pow_add_apply (σ : M ≃+ M) (a b : ℕ) (x : M) :
    (σ ^ (a + b)) x = (σ ^ a) ((σ ^ b) x) := by
  rw [pow_add]
  rfl

/-- **The norm of a composite order factors.**  Summing over `d * m` powers of `σ` is summing over
`m` powers of `σ ^ d` after summing over `d` powers of `σ`. -/
theorem normHom_mul (σ : M ≃+ M) (d m : ℕ) (x : M) :
    normHom σ (d * m) x = normHom (σ ^ d) m (normHom σ d x) := by
  induction m with
  | zero => simp [normHom_apply]
  | succ m ih =>
    have hstep : normHom σ (d * m + d) x
        = normHom σ (d * m) x + (σ ^ (d * m)) (normHom σ d x) := by
      rw [normHom_apply, normHom_apply, normHom_apply, Finset.sum_range_add, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [pow_add_apply]
    rw [Nat.mul_succ, hstep, ih, normHom_apply (σ ^ d) (m + 1), Finset.sum_range_succ,
      normHom_apply (σ ^ d) m, ← pow_mul]

end NormMul

/-! ### Arithmetic of the cyclic index set -/

section Index

variable (d : ℕ) [NeZero d]

/-- The predecessor of the order, as a residue, is `-1`. -/
theorem natCast_pred_eq_neg_one : ((d - 1 : ℕ) : ZMod d) = -1 := by
  have h1 : ((d - 1 : ℕ) + 1 : ℕ) = d := by have := NeZero.ne d; omega
  have h2 : ((((d - 1 : ℕ) + 1 : ℕ) : ℕ) : ZMod d) = ((d : ℕ) : ZMod d) := by rw [h1]
  rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h2
  linear_combination h2

/-- The value of `-1` is the predecessor of the order. -/
theorem val_neg_one_zmod : (-1 : ZMod d).val = d - 1 := by
  rw [← natCast_pred_eq_neg_one d,
    ZMod.val_cast_of_lt (by have := NeZero.ne d; omega : d - 1 < d)]

variable {d}

omit [NeZero d] in
/-- A residue strictly below the last one is not `-1`. -/
theorem natCast_ne_neg_one {k : ℕ} (hk : k + 1 < d) : (k : ZMod d) ≠ -1 := by
  intro h
  have h0 : ((k + 1 : ℕ) : ZMod d) = 0 := by
    rw [Nat.cast_add, Nat.cast_one, h]
    ring
  have hdvd : d ∣ (k + 1) := (ZMod.natCast_eq_zero_iff _ _).mp h0
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The value of a residue other than `-1` has a successor below the order. -/
theorem val_add_one_lt_of_ne {i : ZMod d} (h : i ≠ -1) : i.val + 1 < d := by
  rcases Nat.lt_or_ge (i.val + 1) d with h1 | h1
  · exact h1
  · refine absurd ?_ h
    have hv : i.val = d - 1 := by have := ZMod.val_lt i; omega
    rw [← ZMod.natCast_rightInverse i, hv, natCast_pred_eq_neg_one]

/-- The value of the successor of a residue other than `-1`. -/
theorem val_add_one_of_ne {i : ZMod d} (h : i ≠ -1) : (i + 1).val = i.val + 1 := by
  have hc : ((i.val + 1 : ℕ) : ZMod d) = i + 1 := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_rightInverse i]
  rw [← hc, ZMod.val_cast_of_lt (val_add_one_lt_of_ne h)]

/-- A sum over the residues is a sum over an initial segment of the naturals. -/
theorem sum_range_natCast {A : Type*} [AddCommMonoid A] (g : ZMod d → A) :
    ∑ r ∈ Finset.range d, g (r : ZMod d) = ∑ i, g i := by
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod d)) (Finset.range d) := by
    intro x hx y hy h
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    rw [← ZMod.val_cast_of_lt hx, ← ZMod.val_cast_of_lt hy]
    exact congrArg ZMod.val h
  rw [← Finset.sum_image hinj]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
  exact ⟨i.val, ZMod.val_lt i, ZMod.natCast_rightInverse i⟩

end Index

/-! ### The induced module -/

variable {B : Type*} [AddCommGroup B] (τ : B ≃+ B)

/-- The automorphism applied at one coordinate of the induced module: the identity everywhere
except at the last coordinate, where it is `τ`. -/
def indTwist {d : ℕ} (i : ZMod d) : B ≃+ B := if i = -1 then τ else 1

@[simp]
theorem indTwist_neg_one (d : ℕ) : indTwist τ (-1 : ZMod d) = τ := if_pos rfl

theorem indTwist_of_ne {d : ℕ} {i : ZMod d} (h : i ≠ -1) : indTwist τ i = 1 := if_neg h

/-- **The automorphism of the induced module.**  It shifts the coordinates cyclically and applies
`τ` on passing the last one. -/
def indAut (τ : B ≃+ B) (d : ℕ) : (ZMod d → B) ≃+ (ZMod d → B) where
  toFun f i := indTwist τ i (f (i + 1))
  invFun f i := (indTwist τ (i - 1)).symm (f (i - 1))
  left_inv f := funext fun i => by
    simp only [sub_add_cancel, AddEquiv.symm_apply_apply]
  right_inv f := funext fun i => by
    simp only [add_sub_cancel_right, AddEquiv.apply_symm_apply]
  map_add' f g := funext fun i => map_add _ _ _

theorem indAut_apply {d : ℕ} (f : ZMod d → B) (i : ZMod d) :
    indAut τ d f i = indTwist τ i (f (i + 1)) := rfl

/-! ### Powers of the induced automorphism -/

variable {d : ℕ}

/-- **Away from the last coordinate the induced automorphism is a plain shift.** -/
theorem pow_indAut_apply (f : ZMod d → B) : ∀ (r : ℕ) (i : ZMod d),
    (∀ k : ℕ, k < r → i + (k : ZMod d) ≠ -1) → ((indAut τ d) ^ r) f i = f (i + r) := by
  intro r
  induction r with
  | zero => intro i _; simp
  | succ r ih =>
    intro i h
    have h0 : i ≠ -1 := by
      have := h 0 (Nat.succ_pos r)
      simpa using this
    have hstep : ∀ k : ℕ, k < r → (i + 1) + (k : ZMod d) ≠ -1 := by
      intro k hk
      have := h (k + 1) (by omega)
      rw [Nat.cast_add, Nat.cast_one] at this
      intro hcon
      exact this (by rw [← hcon]; ring)
    rw [pow_succ_apply, indAut_apply, indTwist_of_ne τ h0, ih (i + 1) hstep]
    show f (i + 1 + (r : ZMod d)) = f (i + ((r + 1 : ℕ) : ZMod d))
    congr 1
    push_cast
    ring

variable [NeZero d]

omit [NeZero d] in
/-- The powers of the induced automorphism read off the coordinates one by one. -/
theorem pow_indAut_apply_zero (r : ℕ) (hr : r < d) (f : ZMod d → B) :
    ((indAut τ d) ^ r) f 0 = f r := by
  have h := pow_indAut_apply τ f r 0 fun k hk => by
    rw [zero_add]
    exact natCast_ne_neg_one (by omega)
  rw [zero_add] at h
  exact h

/-- **The `d`-th power of the induced automorphism applies `τ` in every coordinate.** -/
theorem pow_card_indAut_apply (f : ZMod d → B) (i : ZMod d) :
    ((indAut τ d) ^ d) f i = τ (f i) := by
  set j := (-1 - i).val with hj
  have hjd : j < d := ZMod.val_lt _
  have hij : i + (j : ZMod d) = -1 := by
    rw [hj, ZMod.natCast_rightInverse (-1 - i)]
    ring
  have hsplit : d = j + (1 + (d - j - 1)) := by omega
  have hlast : ((d - j - 1 : ℕ) : ZMod d) = i := by
    have h1 : ((d - j - 1) + j + 1 : ℕ) = d := by omega
    have h2 : ((((d - j - 1) + j + 1 : ℕ) : ℕ) : ZMod d) = ((d : ℕ) : ZMod d) := by rw [h1]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h2
    linear_combination h2 - hij
  have hnowrap : ∀ k : ℕ, k < j → i + (k : ZMod d) ≠ -1 := by
    intro k hk hcon
    have hkj : (k : ZMod d) = (j : ZMod d) := by
      have : i + (k : ZMod d) = i + (j : ZMod d) := by rw [hcon, hij]
      exact add_left_cancel this
    rw [← ZMod.val_cast_of_lt (show k < d by omega), ← ZMod.val_cast_of_lt hjd, hkj] at hk
    omega
  have hpow : ((indAut τ d) ^ d) f i = ((indAut τ d) ^ (j + (1 + (d - j - 1)))) f i :=
    congrArg (fun k => ((indAut τ d) ^ k) f i) hsplit
  rw [hpow, pow_add_apply, pow_indAut_apply τ _ j i hnowrap, hij, pow_add_apply, pow_one,
    indAut_apply, indTwist_neg_one, neg_add_cancel,
    pow_indAut_apply_zero τ (d - j - 1) (by omega), hlast]

/-- The powers of the `d`-th power of the induced automorphism apply powers of `τ`. -/
theorem pow_pow_card_indAut_apply (j : ℕ) (f : ZMod d → B) (i : ZMod d) :
    ((((indAut τ d) ^ d) ^ j) f) i = (τ ^ j) (f i) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ_apply, pow_card_indAut_apply, ih, pow_succ_apply]

/-- **The induced automorphism has order dividing `d * m`.** -/
theorem indAut_pow_eq_one {m : ℕ} (hτ : τ ^ m = 1) : (indAut τ d) ^ (d * m) = 1 := by
  refine AddEquiv.ext fun f => funext fun i => ?_
  rw [pow_mul, pow_pow_card_indAut_apply, hτ]
  rfl

/-! ### The fixed points of the induced automorphism -/

/-- **A fixed tuple is constant.** -/
theorem apply_eq_apply_zero_of_indAut_eq {f : ZMod d → B} (hf : indAut τ d f = f) (i : ZMod d) :
    f i = f 0 := by
  have h : ∀ r : ℕ, ((indAut τ d) ^ r) f = f := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => rw [pow_succ_apply, ih, hf]
  have h0 := pow_indAut_apply_zero τ i.val (ZMod.val_lt i) f
  rw [h i.val, ZMod.natCast_rightInverse i] at h0
  exact h0.symm

/-- The common value of a fixed tuple is fixed by `τ`. -/
theorem tau_apply_zero_of_indAut_eq {f : ZMod d → B} (hf : indAut τ d f = f) : τ (f 0) = f 0 := by
  have h1 : indAut τ d f (-1) = f (-1) := by rw [hf]
  rw [indAut_apply, indTwist_neg_one, neg_add_cancel] at h1
  rw [h1, apply_eq_apply_zero_of_indAut_eq τ hf]

omit [NeZero d] in
/-- **A constant tuple with a `τ`-fixed value is fixed.** -/
theorem indAut_const {b : B} (hb : τ b = b) :
    indAut τ d (fun _ => b) = (fun _ => b) := by
  funext i
  rw [indAut_apply]
  by_cases h : i = -1
  · rw [h, indTwist_neg_one]; exact hb
  · rw [indTwist_of_ne τ h]; rfl

/-- A fixed tuple is determined by its value at the coordinate `0`. -/
theorem eq_of_indAut_eq_of_apply_zero_eq {f g : ZMod d → B} (hf : indAut τ d f = f)
    (hg : indAut τ d g = g) (h : f 0 = g 0) : f = g :=
  funext fun i => by
    rw [apply_eq_apply_zero_of_indAut_eq τ hf, apply_eq_apply_zero_of_indAut_eq τ hg, h]

/-! ### The sum of the coordinates and the tuple supported at zero -/

variable (d)

/-- **The sum of the coordinates of a tuple.** -/
def indSum : (ZMod d → B) →+ B where
  toFun f := ∑ i, f i
  map_zero' := Finset.sum_const_zero
  map_add' _ _ := Finset.sum_add_distrib

theorem indSum_apply (f : ZMod d → B) : indSum d f = ∑ i, f i := rfl

/-- **The tuple supported at the coordinate `0`.** -/
def indSingle : B →+ (ZMod d → B) := AddMonoidHom.single (fun _ : ZMod d => B) 0

omit [NeZero d] in
theorem indSingle_apply (b : B) (i : ZMod d) :
    indSingle d b i = (Pi.single (0 : ZMod d) b : ZMod d → B) i := rfl

@[simp]
theorem indSum_indSingle (b : B) : indSum d (indSingle d b) = b := by
  rw [indSum_apply]
  simp only [indSingle_apply]
  exact Fintype.sum_pi_single' (0 : ZMod d) b

variable {d}

/-- **The sum of the coordinates turns the norm of the induced automorphism into the norm of
`τ`.** -/
theorem normHom_indAut_apply_zero (m : ℕ) (f : ZMod d → B) :
    normHom (indAut τ d) (d * m) f 0 = normHom τ m (indSum d f) := by
  have key : ∀ g : ZMod d → B, normHom ((indAut τ d) ^ d) m g 0 = normHom τ m (g 0) := by
    intro g
    rw [normHom_apply, normHom_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => pow_pow_card_indAut_apply τ j g 0
  have key2 : normHom (indAut τ d) d f 0 = indSum d f := by
    rw [normHom_apply, Finset.sum_apply, indSum_apply, ← sum_range_natCast]
    exact Finset.sum_congr rfl fun r hr =>
      pow_indAut_apply_zero τ r (Finset.mem_range.mp hr) f
  rw [normHom_mul, key, key2]

/-- **The sum of the coordinates turns a difference into a difference.** -/
theorem indSum_sigmaSubOne (g : ZMod d → B) :
    indSum d (sigmaSubOne (indAut τ d) g) = τ (g 0) - g 0 := by
  have hbij : ∑ i : ZMod d, g (i + 1) = ∑ i, g i :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod d)) _ _ fun _ => rfl
  have hdiff : ∑ i : ZMod d, (indAut τ d g i - g (i + 1)) = τ (g 0) - g 0 := by
    rw [Finset.sum_eq_single (-1 : ZMod d)]
    · rw [indAut_apply, indTwist_neg_one, neg_add_cancel]
    · intro i _ hi
      rw [indAut_apply, indTwist_of_ne τ hi]
      exact sub_self _
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsum : ∑ i : ZMod d, indAut τ d g i = (∑ i, g i) + (τ (g 0) - g 0) := by
    rw [← hbij, ← hdiff, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by abel
  show ∑ i, (indAut τ d g - g) i = τ (g 0) - g 0
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib, hsum]
  abel

/-! ### The retraction onto the tuple supported at zero -/

/-- The tuple whose difference under the induced automorphism corrects an arbitrary tuple to the
one supported at the coordinate `0`. -/
def indRetract (f : ZMod d → B) : ZMod d → B := fun i =>
  (∑ r ∈ Finset.range i.val, f (r : ZMod d)) - (if i = 0 then 0 else indSum d f)

theorem indRetract_zero (f : ZMod d → B) : indRetract f (0 : ZMod d) = 0 := by
  rw [indRetract]
  simp

/-- **Every tuple differs from the tuple supported at `0` with the same coordinate sum by a
difference.** -/
theorem sigmaSubOne_indRetract (f : ZMod d → B) :
    sigmaSubOne (indAut τ d) (indRetract f) = f - indSingle d (indSum d f) := by
  have hQ : indSum d f = ∑ r ∈ Finset.range d, f (r : ZMod d) := by
    rw [indSum_apply, ← sum_range_natCast]
  funext i
  show indAut τ d (indRetract f) i - indRetract f i = f i - indSingle d (indSum d f) i
  rw [indAut_apply, indSingle_apply]
  by_cases hi : i = -1
  · subst hi
    rw [indTwist_neg_one, neg_add_cancel, indRetract_zero, map_zero]
    by_cases hd : (-1 : ZMod d) = 0
    · have hd1 : d = 1 := by
        have h0 : ((1 : ℕ) : ZMod d) = 0 := by
          rw [Nat.cast_one]
          linear_combination -hd
        have := Nat.le_of_dvd Nat.one_pos ((ZMod.natCast_eq_zero_iff _ _).mp h0)
        have := NeZero.ne d
        omega
      have hrange : Finset.range d = {0} := by rw [hd1]; exact Finset.range_one
      have hsum : indSum d f = f 0 := by
        rw [hQ, hrange, Finset.sum_singleton, Nat.cast_zero]
      rw [hd, indRetract_zero, Pi.single_eq_same, hsum]
      abel
    · have hd1 : (d - 1) + 1 = d := by have := NeZero.ne d; omega
      have hsplit : (∑ r ∈ Finset.range ((d - 1) + 1), f (r : ZMod d))
          = (∑ r ∈ Finset.range (d - 1), f (r : ZMod d)) + f (-1) := by
        rw [Finset.sum_range_succ, natCast_pred_eq_neg_one]
      rw [hd1] at hsplit
      rw [indRetract, if_neg hd, val_neg_one_zmod d, hQ, Pi.single_eq_of_ne hd, hsplit]
      abel
  · rw [indTwist_of_ne τ hi]
    show indRetract f (i + 1) - indRetract f i
        = f i - (Pi.single (0 : ZMod d) (indSum d f) : ZMod d → B) i
    have hne0 : i + 1 ≠ 0 := fun h => hi (by linear_combination h)
    rw [indRetract, indRetract, if_neg hne0, val_add_one_of_ne hi, Finset.sum_range_succ,
      ZMod.natCast_rightInverse i]
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos rfl, Pi.single_eq_same]
      abel
    · rw [if_neg hi0, Pi.single_eq_of_ne hi0]
      abel

/-- The tuple supported at `0` with a difference as value is itself a difference. -/
theorem exists_sigmaSubOne_eq_indSingle (b : B) :
    ∃ g, sigmaSubOne (indAut τ d) g = indSingle d (τ b - b) := by
  obtain ⟨g, hg⟩ : ∃ g, sigmaSubOne (indAut τ d) g
      = sigmaSubOne (indAut τ d) (fun _ => b)
        - indSingle d (indSum d (sigmaSubOne (indAut τ d) (fun _ => b))) :=
    ⟨indRetract (sigmaSubOne (indAut τ d) fun _ => b), sigmaSubOne_indRetract τ _⟩
  rw [indSum_sigmaSubOne] at hg
  exact ⟨(fun _ => b) - g, by rw [map_sub, hg]; abel⟩

/-! ### Shapiro's lemma for the upper Tate group -/

variable (m : ℕ)

/-- Evaluation at the coordinate `0`, restricted to the fixed points. -/
def indEvalKer : (sigmaSubOne (indAut τ d)).ker →+ (sigmaSubOne τ).ker :=
  AddMonoidHom.codRestrict
    ((Pi.evalAddMonoidHom (fun _ : ZMod d => B) 0).comp (sigmaSubOne (indAut τ d)).ker.subtype)
    _ fun x => (mem_ker_sigmaSubOne_iff τ _).mpr
      (tau_apply_zero_of_indAut_eq τ ((mem_ker_sigmaSubOne_iff _ _).mp x.2))

/-- **The comparison map on the upper Tate group**, induced by evaluation at the coordinate
`0`. -/
noncomputable def tateH0IndHom : tateH0 (indAut τ d) (d * m) →+ tateH0 τ m :=
  QuotientAddGroup.map _ _ (indEvalKer τ) <| by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨indSum d y, by rw [← normHom_indAut_apply_zero, hy]; rfl⟩

theorem tateH0IndHom_mk (f : ZMod d → B) (hf : indAut τ d f = f) :
    tateH0IndHom τ m (tateH0.mk (indAut τ d) (d * m) f hf)
      = tateH0.mk τ m (f 0) (tau_apply_zero_of_indAut_eq τ hf) := rfl

theorem tateH0IndHom_surjective : Function.Surjective (tateH0IndHom (d := d) τ m) := by
  intro c
  obtain ⟨b, hb, rfl⟩ := tateH0.mk_surjective c
  exact ⟨tateH0.mk (indAut τ d) (d * m) (fun _ => b) (indAut_const τ hb), rfl⟩

theorem tateH0IndHom_injective (hτ : τ ^ m = 1) :
    Function.Injective (tateH0IndHom (d := d) τ m) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, hf, rfl⟩ := tateH0.mk_surjective c
  rw [tateH0IndHom_mk, tateH0.mk_eq_zero_iff] at hc
  obtain ⟨b, hb⟩ := hc
  refine (tateH0.mk_eq_zero_iff _ _).mpr ⟨indSingle d b, ?_⟩
  refine eq_of_indAut_eq_of_apply_zero_eq τ ?_ hf ?_
  · exact (mem_ker_sigmaSubOne_iff _ _).mp
      (range_normHom_le_ker_sigmaSubOne _ (indAut_pow_eq_one τ hτ) ⟨indSingle d b, rfl⟩)
  · rw [normHom_indAut_apply_zero, indSum_indSingle, hb]

/-- **Shapiro's lemma for the upper Tate group.** -/
noncomputable def tateH0IndEquiv (hτ : τ ^ m = 1) :
    tateH0 (indAut τ d) (d * m) ≃+ tateH0 τ m :=
  AddEquiv.ofBijective _ ⟨tateH0IndHom_injective τ m hτ, tateH0IndHom_surjective τ m⟩

theorem card_tateH0_indAut (hτ : τ ^ m = 1) :
    Nat.card (tateH0 (indAut τ d) (d * m)) = Nat.card (tateH0 τ m) :=
  Nat.card_congr (tateH0IndEquiv τ m hτ).toEquiv

/-! ### Shapiro's lemma for the lower Tate group -/

/-- The sum of the coordinates, restricted to the tuples of norm zero. -/
noncomputable def indSumKer :
    (normHom (indAut τ d) (d * m)).ker →+ (normHom τ m).ker :=
  AddMonoidHom.codRestrict ((indSum d).comp (normHom (indAut τ d) (d * m)).ker.subtype) _
    fun x => AddMonoidHom.mem_ker.mpr <| by
      show normHom τ m (indSum d (x : ZMod d → B)) = 0
      rw [← normHom_indAut_apply_zero, AddMonoidHom.mem_ker.mp x.2]
      rfl

/-- **The comparison map on the lower Tate group**, induced by the sum of the coordinates. -/
noncomputable def tateHm1IndHom : tateHm1 (indAut τ d) (d * m) →+ tateHm1 τ m :=
  QuotientAddGroup.map _ _ (indSumKer τ m) <| by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨y 0, ?_⟩
    have hy' : sigmaSubOne (indAut τ d) y = x := hy
    show sigmaSubOne τ (y 0) = indSum d x
    rw [sigmaSubOne_apply, ← indSum_sigmaSubOne, hy']

theorem tateHm1IndHom_mk (f : ZMod d → B) (hf : normHom (indAut τ d) (d * m) f = 0) :
    tateHm1IndHom τ m (tateHm1.mk (indAut τ d) (d * m) f hf)
      = tateHm1.mk τ m (indSum d f)
        (by rw [← normHom_indAut_apply_zero, hf]; rfl) := rfl

/-- The tuple supported at `0` with a norm-zero value has norm zero. -/
theorem normHom_indSingle_eq_zero (hτ : τ ^ m = 1) {b : B} (hb : normHom τ m b = 0) :
    normHom (indAut τ d) (d * m) (indSingle d b) = 0 := by
  refine eq_of_indAut_eq_of_apply_zero_eq τ ?_ ?_ ?_
  · exact (mem_ker_sigmaSubOne_iff _ _).mp
      (range_normHom_le_ker_sigmaSubOne _ (indAut_pow_eq_one τ hτ) ⟨indSingle d b, rfl⟩)
  · exact indAut_const τ (map_zero τ)
  · rw [normHom_indAut_apply_zero, indSum_indSingle, hb]
    rfl

theorem tateHm1IndHom_surjective (hτ : τ ^ m = 1) :
    Function.Surjective (tateHm1IndHom (d := d) τ m) := by
  intro c
  obtain ⟨b, hb, rfl⟩ := tateHm1.mk_surjective c
  refine ⟨tateHm1.mk (indAut τ d) (d * m) (indSingle d b) (normHom_indSingle_eq_zero τ m hτ hb), ?_⟩
  rw [tateHm1IndHom_mk]
  congr 1
  exact indSum_indSingle d b

theorem tateHm1IndHom_injective : Function.Injective (tateHm1IndHom (d := d) τ m) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, hf, rfl⟩ := tateHm1.mk_surjective c
  rw [tateHm1IndHom_mk, tateHm1.mk_eq_zero_iff] at hc
  obtain ⟨b, hb⟩ := hc
  obtain ⟨g, hg⟩ := exists_sigmaSubOne_eq_indSingle τ (d := d) b
  refine (tateHm1.mk_eq_zero_iff _ _).mpr ⟨indRetract f + g, ?_⟩
  have h1 := sigmaSubOne_indRetract τ f
  rw [hb] at hg
  show sigmaSubOne (indAut τ d) (indRetract f + g) = f
  rw [map_add, h1, hg]
  abel

/-- **Shapiro's lemma for the lower Tate group.** -/
noncomputable def tateHm1IndEquiv (hτ : τ ^ m = 1) :
    tateHm1 (indAut τ d) (d * m) ≃+ tateHm1 τ m :=
  AddEquiv.ofBijective _ ⟨tateHm1IndHom_injective τ m, tateHm1IndHom_surjective τ m hτ⟩

theorem card_tateHm1_indAut (hτ : τ ^ m = 1) :
    Nat.card (tateHm1 (indAut τ d) (d * m)) = Nat.card (tateHm1 τ m) :=
  Nat.card_congr (tateHm1IndEquiv τ m hτ).toEquiv

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient of an induced module is that of the module it is induced from.** -/
theorem herbrand_indAut (hτ : τ ^ m = 1) :
    herbrand (indAut τ d) (d * m) = herbrand τ m := by
  rw [herbrand, herbrand, card_tateH0_indAut τ m hτ, card_tateHm1_indAut τ m hτ]

end InverseGalois.CFT
