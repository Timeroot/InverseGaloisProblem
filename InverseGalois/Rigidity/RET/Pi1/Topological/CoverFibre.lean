/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.ConvexHomotopy

/-!
# The fibres of the cover attached to a monodromy homomorphism

A homomorphism `φ` from the loops of a region `X` of the plane, based at `x₀`, to a group `H`
determines a covering space of `X` with deck group `H`.  Its fibre over a point `x` is built here,
before any topology: it is the set of *equivariant labels*

```
s : (paths from x₀ to x, up to homotopy) → H,     s (g ∗ q) = φ g * s q,
```

one label for each homotopy class of paths reaching `x`, changing by `φ g` when the path is
prepended with a loop `g`.  A single label determines all of them, so the fibre is a copy of `H`
once `x` can be reached from `x₀` at all, and it is empty otherwise; the point of the description
is that it is canonical — no path from `x₀` to `x` has to be chosen — so the fibres over the
various points can be compared without a choice, and the comparison is transitive on the nose.

That comparison is `MonodromyData.restrict`: a homotopy class `c` of paths from `y` to `x` carries
a label over `x` to a label over `y`, by prepending `c`.  Composing paths composes restrictions,
and the constant path restricts to nothing at all, so `restrict` is a functor from the fundamental
groupoid to sets, and each `restrict c` is a bijection.

The classes that will be used to glue the fibres into a space are those of the straight segments
inside a *flat piece* of `X` — a convex open subset.  Two paths inside a convex set with the same
endpoints are homotopic, so the segment class does not depend on the path chosen, and segment
classes inside one flat piece compose.  That is the whole of the local structure of the cover.

## Main definitions

* `Rigidity.RET.IsFlat` — a convex open subset of a region of the plane.
* `Rigidity.RET.segClass` — the homotopy class of the straight segment inside a flat piece.
* `Rigidity.RET.MonodromyData` — a homomorphism from the loops at `x₀` to a group `H`.
* `Rigidity.RET.MonodromyData.Fib` — the fibre of the associated cover, as equivariant labels.
* `Rigidity.RET.MonodromyData.restrict` — transport of labels along a homotopy class of paths.
* `Rigidity.RET.MonodromyData.Total` — the total space of the associated cover, as a bare type.

## Main results

* `Rigidity.RET.eq_segClass_of_mem` — any path inside a flat piece has the segment class.
* `Rigidity.RET.segClass_trans` — segment classes inside one flat piece compose.
* `Rigidity.RET.MonodromyData.restrict_restrict` — transport is functorial.
* `Rigidity.RET.MonodromyData.restrictEquiv` — transport along a class is a bijection.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Flat pieces of a region -/

/-- A **flat piece** of a region `X` of the plane: a convex open subset of it.  Paths inside a flat
piece are determined up to homotopy by their endpoints. -/
structure IsFlat (X K : Set ℂ) : Prop where
  /-- a flat piece is open. -/
  isOpen : IsOpen K
  /-- a flat piece is convex. -/
  isSegClosed : IsSegClosed K
  /-- a flat piece is contained in the region. -/
  subset : K ⊆ X

/-- The intersection of two flat pieces is flat. -/
theorem IsFlat.inter {X K L : Set ℂ} (hK : IsFlat X K) (hL : IsFlat X L) : IsFlat X (K ∩ L) where
  isOpen := hK.isOpen.inter hL.isOpen
  isSegClosed := fun a ha b hb =>
    Set.subset_inter (hK.isSegClosed a ha.1 b hb.1) (hL.isSegClosed a ha.2 b hb.2)
  subset := (Set.inter_subset_left).trans hK.subset

/-- A flat piece of a subregion is a flat piece of the region. -/
theorem IsFlat.mono {X Y K : Set ℂ} (hK : IsFlat Y K) (hYX : Y ⊆ X) : IsFlat X K where
  isOpen := hK.isOpen
  isSegClosed := hK.isSegClosed
  subset := hK.subset.trans hYX

/-- **Every point of an open region lies in a flat piece of it** — a small disc. -/
theorem exists_isFlat_mem {X : Set ℂ} (hX : IsOpen X) {z : ℂ} (hz : z ∈ X) :
    ∃ K, IsFlat X K ∧ z ∈ K := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hX z hz
  exact ⟨Metric.ball z ρ,
    { isOpen := Metric.isOpen_ball
      isSegClosed := isSegClosed_iff_convex.mpr (convex_ball z ρ)
      subset := hsub },
    Metric.mem_ball_self hρ⟩

/-! ### The class of a straight segment inside a flat piece -/

/-- **The homotopy class of the straight segment** between two points of a flat piece of `X`, read
as a path of `X`. -/
def segClass {X K : Set ℂ} (hK : IsFlat X K) {a b : ↥X}
    (ha : (a : ℂ) ∈ K) (hb : (b : ℂ) ∈ K) : Path.Homotopic.Quotient a b :=
  Path.Homotopic.Quotient.mk (segPath a b ((hK.isSegClosed _ ha _ hb).trans hK.subset))

/-- **Any path inside a flat piece has the segment class**: a convex set is simply connected, so
two paths of `X` running inside it with the same endpoints are homotopic. -/
theorem eq_segClass_of_mem {X K : Set ℂ} (hK : IsFlat X K) {a b : ↥X}
    (ha : (a : ℂ) ∈ K) (hb : (b : ℂ) ∈ K) (p : Path a b) (hp : ∀ t, (p t : ℂ) ∈ K) :
    Path.Homotopic.Quotient.mk p = segClass hK ha hb :=
  Path.Homotopic.Quotient.eq.mpr
    (homotopic_of_mem_convex hK.isSegClosed hK.subset p _ hp fun t =>
      hK.isSegClosed _ ha _ hb (mem_seg_segPath _ t))

/-- The segment class from a point to itself is the constant class. -/
@[simp] theorem segClass_self {X K : Set ℂ} (hK : IsFlat X K) {a : ↥X} (ha : (a : ℂ) ∈ K) :
    segClass hK ha ha = Path.Homotopic.Quotient.refl a := by
  rw [← Path.Homotopic.Quotient.mk_refl]
  exact (eq_segClass_of_mem hK ha ha (Path.refl a) fun _ => by simpa using ha).symm

/-- **Segment classes inside one flat piece compose.** -/
theorem segClass_trans {X K : Set ℂ} (hK : IsFlat X K) {a b c : ↥X}
    (ha : (a : ℂ) ∈ K) (hb : (b : ℂ) ∈ K) (hc : (c : ℂ) ∈ K) :
    (segClass hK ha hb).trans (segClass hK hb hc) = segClass hK ha hc := by
  rw [segClass, segClass, ← Path.Homotopic.Quotient.mk_trans]
  refine eq_segClass_of_mem hK ha hc _ fun t => ?_
  rw [Path.trans_apply]
  split
  · exact hK.isSegClosed _ ha _ hb (mem_seg_segPath _ _)
  · exact hK.isSegClosed _ hb _ hc (mem_seg_segPath _ _)

/-- A segment class inside a smaller flat piece is the segment class inside a bigger one. -/
theorem segClass_mono {X K L : Set ℂ} (hK : IsFlat X K) (hL : IsFlat X L) (hKL : K ⊆ L) {a b : ↥X}
    (ha : (a : ℂ) ∈ K) (hb : (b : ℂ) ∈ K) :
    segClass hK ha hb = segClass hL (hKL ha) (hKL hb) :=
  (eq_segClass_of_mem hL (hKL ha) (hKL hb) _ fun t =>
    hKL (hK.isSegClosed _ ha _ hb (mem_seg_segPath _ t))).symm

/-! ### Monodromy data and its fibres -/

variable {X : Set ℂ}

/-- **A monodromy homomorphism**: a map from the homotopy classes of loops of `X` at `x₀` to a
group `H`, turning concatenation into multiplication.

The group of loops is used in its raw form — homotopy classes of paths from `x₀` to itself, with
concatenation — rather than through `FundamentalGroup`, so that no convention about the order of
composition has to be fixed before the cover is built. -/
structure MonodromyData (x₀ : ↥X) (H : Type*) [Group H] where
  /-- the region is open, so that every point of it lies in a flat piece. -/
  isOpen_region : IsOpen X
  /-- the value of the monodromy on a loop. -/
  toFun : Path.Homotopic.Quotient x₀ x₀ → H
  /-- concatenation of loops goes to multiplication. -/
  map_trans' : ∀ a b, toFun (a.trans b) = toFun a * toFun b

namespace MonodromyData

variable {x₀ : ↥X} {H : Type*} [Group H] (D : MonodromyData x₀ H)

@[simp] theorem map_trans (a b : Path.Homotopic.Quotient x₀ x₀) :
    D.toFun (a.trans b) = D.toFun a * D.toFun b := D.map_trans' a b

@[simp] theorem map_refl : D.toFun (Path.Homotopic.Quotient.refl x₀) = 1 := by
  have h := D.map_trans (Path.Homotopic.Quotient.refl x₀) (Path.Homotopic.Quotient.refl x₀)
  rw [Path.Homotopic.Quotient.refl_trans] at h
  exact mul_left_cancel (a := D.toFun (Path.Homotopic.Quotient.refl x₀)) (by rw [mul_one]; exact h.symm)

@[simp] theorem map_symm (a : Path.Homotopic.Quotient x₀ x₀) :
    D.toFun a.symm = (D.toFun a)⁻¹ := by
  have h := D.map_trans a a.symm
  rw [Path.Homotopic.Quotient.trans_symm, D.map_refl] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- **The fibre of the cover over `x`**: an equivariant labelling of the homotopy classes of paths
from the base point to `x` by elements of `H`.

Prepending a loop `g` to a path multiplies the label on the left by `φ g`.  A label at one path
therefore determines the labels at all of them, so the fibre is a copy of `H` as soon as `x` can be
joined to the base point, and is empty otherwise. -/
def Fib (x : ↥X) : Type _ :=
  {s : Path.Homotopic.Quotient x₀ x → H //
    ∀ (g : Path.Homotopic.Quotient x₀ x₀) (q : Path.Homotopic.Quotient x₀ x),
      s (g.trans q) = D.toFun g * s q}

instance (x : ↥X) : CoeFun (D.Fib x) fun _ => Path.Homotopic.Quotient x₀ x → H :=
  ⟨fun s => s.1⟩

@[ext] theorem Fib.ext {x : ↥X} {s t : D.Fib x} (h : ∀ q, s.1 q = t.1 q) : s = t :=
  Subtype.ext (funext h)

/-- **The total space of the cover**, as a bare type: a point of `X` together with a label of the
paths reaching it. -/
def Total : Type _ := Σ x : ↥X, D.Fib x

/-- The projection of the total space to the region. -/
def proj : D.Total → ↥X := Sigma.fst

@[simp] theorem proj_mk (x : ↥X) (s : D.Fib x) : D.proj ⟨x, s⟩ = x := rfl

/-- **Transport of labels along a homotopy class of paths**: a class `c` of paths from `y` to `x`
carries a label over `x` to a label over `y`, by prepending `c` to the path being labelled. -/
def restrict {x y : ↥X} (c : Path.Homotopic.Quotient y x) (s : D.Fib x) : D.Fib y :=
  ⟨fun q => s.1 (q.trans c), fun g q => by
    show s.1 ((g.trans q).trans c) = D.toFun g * s.1 (q.trans c)
    rw [Path.Homotopic.Quotient.trans_assoc]
    exact s.2 g (q.trans c)⟩

@[simp] theorem restrict_apply {x y : ↥X} (c : Path.Homotopic.Quotient y x) (s : D.Fib x)
    (q : Path.Homotopic.Quotient x₀ y) : (D.restrict c s).1 q = s.1 (q.trans c) := rfl

/-- **Transport is functorial**: transporting along `c` and then along `c'` is transporting along
the concatenation. -/
@[simp] theorem restrict_restrict {x y z : ↥X} (c : Path.Homotopic.Quotient z y)
    (c' : Path.Homotopic.Quotient y x) (s : D.Fib x) :
    D.restrict c (D.restrict c' s) = D.restrict (c.trans c') s := by
  ext q
  simp [Path.Homotopic.Quotient.trans_assoc]

/-- Transporting along the constant path does nothing. -/
@[simp] theorem restrict_refl {x : ↥X} (s : D.Fib x) :
    D.restrict (Path.Homotopic.Quotient.refl x) s = s := by
  ext q
  simp

/-- **Transport along a homotopy class is a bijection of fibres**, with the reverse class as
inverse. -/
def restrictEquiv {x y : ↥X} (c : Path.Homotopic.Quotient y x) : D.Fib x ≃ D.Fib y where
  toFun := D.restrict c
  invFun := D.restrict c.symm
  left_inv s := by
    rw [D.restrict_restrict, Path.Homotopic.Quotient.symm_trans, D.restrict_refl]
  right_inv s := by
    rw [D.restrict_restrict, Path.Homotopic.Quotient.trans_symm, D.restrict_refl]

@[simp] theorem restrictEquiv_apply {x y : ↥X} (c : Path.Homotopic.Quotient y x) (s : D.Fib x) :
    D.restrictEquiv c s = D.restrict c s := rfl

theorem restrict_injective {x y : ↥X} (c : Path.Homotopic.Quotient y x) :
    Function.Injective (D.restrict (x := x) (y := y) c) := (D.restrictEquiv c).injective

/-- A label is determined by its value at a single path. -/
theorem Fib.eq_of_apply_eq {x : ↥X} {s t : D.Fib x} (q : Path.Homotopic.Quotient x₀ x)
    (h : s.1 q = t.1 q) : s = t := by
  ext q'
  have hq : (q'.trans q.symm).trans q = q' := by
    rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  rw [← hq, s.2, t.2, h]

/-! ### The fibre over a point joined to the base point -/

/-- **The label of the paths reaching `x` prescribed at one of them.**  Reading a path `q` against
a fixed path `q₀` gives a loop, and the monodromy of that loop is the change of label. -/
def Fib.of {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) (h : H) : D.Fib x :=
  ⟨fun q => D.toFun (q.trans q₀.symm) * h, fun g q => by
    show D.toFun ((g.trans q).trans q₀.symm) * h = D.toFun g * (D.toFun (q.trans q₀.symm) * h)
    rw [Path.Homotopic.Quotient.trans_assoc, D.map_trans, mul_assoc]⟩

@[simp] theorem Fib.of_apply_self {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) (h : H) :
    (Fib.of D q₀ h).1 q₀ = h := by
  show D.toFun (q₀.trans q₀.symm) * h = h
  rw [Path.Homotopic.Quotient.trans_symm, D.map_refl, one_mul]

/-- **The fibre over a point joined to the base point is a copy of `H`**, once a path to that point
is chosen: a label is exactly its value at the chosen path. -/
def fibEquiv {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) : D.Fib x ≃ H where
  toFun s := s.1 q₀
  invFun h := Fib.of D q₀ h
  left_inv s := Fib.eq_of_apply_eq D q₀ (Fib.of_apply_self D q₀ (s.1 q₀))
  right_inv h := Fib.of_apply_self D q₀ h

@[simp] theorem fibEquiv_apply {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) (s : D.Fib x) :
    D.fibEquiv q₀ s = s.1 q₀ := rfl

theorem Fib.nonempty {x : ↥X} (q₀ : Path.Homotopic.Quotient x₀ x) : Nonempty (D.Fib x) :=
  ⟨Fib.of D q₀ 1⟩

end MonodromyData

end Rigidity.RET

end
