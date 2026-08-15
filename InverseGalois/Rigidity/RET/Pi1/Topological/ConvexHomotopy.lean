/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill

/-!
# Homotopies built from straight lines

Comparing two explicit paths of a region of the plane is easiest when the segment joining them,
point by point, stays inside the region: the straight-line homotopy then does the whole job.  Two
situations of that kind are set up here.

The first is a convex subset: two paths of the region that both run inside a common convex subset
and share their endpoints are homotopic, because a convex set is contractible and hence simply
connected.  The second is a region obtained by removing a single point `s`: the straight-line
homotopy between two paths avoids `s` as soon as, at each time, the two points are seen from `s`
in directions making a positive inner product, since two vectors with positive inner product never
straddle the origin.

Along with these come the straight path between two points of a region, and the description of its
image as a segment.

Segments and convexity are spelled out here in terms of the multiplication of the plane rather than
through the scalar action of the reals, and convexity is carried by the predicate `IsSegClosed`.
The two descriptions agree, but the plane carries several syntactically distinct actions of the
reals, and a statement mentioning one of them is painful to use next to a statement mentioning
another.

## Main results

* `Rigidity.RET.seg`, `Rigidity.RET.IsSegClosed` — the segment between two points of the plane and
  the sets closed under forming segments, both written multiplicatively.
* `Rigidity.RET.isSegClosed_iff_convex` — those sets are exactly the convex ones.
* `Rigidity.RET.homotopic_of_mem_convex` — two paths of a region running inside a common convex
  subset, with the same endpoints, are homotopic.
* `Rigidity.RET.homotopic_refl_of_mem_convex` — a loop running inside a convex subset is
  nullhomotopic.
* `Rigidity.RET.segPath` — the straight path between two points of a region.
* `Rigidity.RET.notMem_seg_of_re_pos` — two vectors with positive inner product do not straddle
  the origin.
* `Rigidity.RET.homotopic_of_re_pos` — two paths never pointing in opposite directions as seen
  from `s` are homotopic in a region avoiding `s`.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Segments and convexity, written multiplicatively -/

/-- The closed segment of the plane between two points. -/
def seg (a b : ℂ) : Set ℂ := {z | ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ z = a + (t : ℂ) * (b - a)}

/-- A subset of the plane is **segment closed** when it contains the segment between any two of
its points. -/
def IsSegClosed (K : Set ℂ) : Prop := ∀ a ∈ K, ∀ b ∈ K, seg a b ⊆ K

theorem seg_eq_segment (a b : ℂ) : seg a b = segment ℝ a b := by
  ext z
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    ring
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    refine ⟨v, ⟨hv, by linarith⟩, ?_⟩
    have hu' : u = 1 - v := by linarith
    simp only [Complex.real_smul, hu']
    push_cast
    ring

theorem left_mem_seg (a b : ℂ) : a ∈ seg a b := ⟨0, by norm_num, by simp⟩

theorem right_mem_seg (a b : ℂ) : b ∈ seg a b := ⟨1, by norm_num, by push_cast; ring⟩

theorem seg_symm (a b : ℂ) : seg a b = seg b a := by
  rw [seg_eq_segment, seg_eq_segment, segment_symm]

theorem isSegClosed_iff_convex {K : Set ℂ} : IsSegClosed K ↔ Convex ℝ K := by
  constructor
  · intro h a ha b hb u v hu hv huv
    have hv1 : v ≤ 1 := by linarith
    refine h a ha b hb ⟨v, ⟨hv, hv1⟩, ?_⟩
    have hu' : u = 1 - v := by linarith
    simp only [Complex.real_smul, hu']
    push_cast
    ring
  · intro h a ha b hb
    rw [seg_eq_segment]
    exact h.segment_subset ha hb

theorem IsSegClosed.convex {K : Set ℂ} (h : IsSegClosed K) : Convex ℝ K :=
  isSegClosed_iff_convex.mp h

theorem isSegClosed_seg (a b : ℂ) : IsSegClosed (seg a b) := by
  rw [isSegClosed_iff_convex, seg_eq_segment]
  exact convex_segment a b

/-- A point of a segment cuts it into two shorter segments. -/
theorem seg_subset_left {a b c : ℂ} (hb : b ∈ seg a c) : seg a b ⊆ seg a c :=
  isSegClosed_seg a c a (left_mem_seg a c) b hb

/-- A point of a segment cuts it into two shorter segments. -/
theorem seg_subset_right {a b c : ℂ} (hb : b ∈ seg a c) : seg b c ⊆ seg a c :=
  isSegClosed_seg a c b hb c (right_mem_seg a c)

/-! ### Paths inside a convex subset -/

/-- A path of a region of the plane which runs inside a subset of it, read as a path of that
subset. -/
def pathRestrictSet {X K : Set ℂ} {a b : ↥X} (p : Path a b) (hp : ∀ t, (p t : ℂ) ∈ K) :
    Path (⟨(a : ℂ), by simpa using hp 0⟩ : ↥K) ⟨(b : ℂ), by simpa using hp 1⟩ where
  toFun t := ⟨(p t : ℂ), hp t⟩
  continuous_toFun := (continuous_subtype_val.comp p.continuous).subtype_mk _
  source' := by simp
  target' := by simp

/-- **Two paths of a region of the plane which run inside a common convex subset and share their
endpoints are homotopic.**  A convex set is contractible, hence simply connected, so the two paths
are already homotopic inside it. -/
theorem homotopic_of_mem_convex {X K : Set ℂ} (hK : IsSegClosed K) (hKX : K ⊆ X)
    {a b : ↥X} (p q : Path a b) (hp : ∀ t, (p t : ℂ) ∈ K) (hq : ∀ t, (q t : ℂ) ∈ K) :
    p.Homotopic q := by
  haveI : ContractibleSpace ↥K := hK.convex.contractibleSpace ⟨(a : ℂ), by simpa using hp 0⟩
  have hpq : (pathRestrictSet p hp).Homotopic (pathRestrictSet q hq) :=
    SimplyConnectedSpace.paths_homotopic _ _
  simpa using hpq.map (subsetIncl hKX)

/-- **A loop of a region of the plane which runs inside a convex subset is nullhomotopic.** -/
theorem homotopic_refl_of_mem_convex {X K : Set ℂ} (hK : IsSegClosed K) (hKX : K ⊆ X)
    {a : ↥X} (p : Path a a) (hp : ∀ t, (p t : ℂ) ∈ K) : p.Homotopic (Path.refl a) :=
  homotopic_of_mem_convex hK hKX p (Path.refl a) hp fun _ => by simpa using hp 0

/-! ### Straight segments -/

/-- The straight path between two points of a region of the plane, along a segment contained in
it. -/
def segPath {X : Set ℂ} (a b : ↥X) (h : seg (a : ℂ) (b : ℂ) ⊆ X) : Path a b where
  toFun t := ⟨(a : ℂ) + (((t : ℝ)) : ℂ) * ((b : ℂ) - (a : ℂ)), h ⟨(t : ℝ), t.2, rfl⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_const.add (Continuous.mul ?_ continuous_const)) _
    exact Complex.continuous_ofReal.comp continuous_subtype_val
  source' := by
    refine Subtype.ext ?_
    simp
  target' := by
    refine Subtype.ext ?_
    show (a : ℂ) + (((1 : I) : ℝ) : ℂ) * ((b : ℂ) - (a : ℂ)) = (b : ℂ)
    norm_num

@[simp] theorem coe_segPath {X : Set ℂ} (a b : ↥X) (h : seg (a : ℂ) (b : ℂ) ⊆ X) (t : I) :
    ((segPath a b h t : ↥X) : ℂ) = (a : ℂ) + (((t : ℝ)) : ℂ) * ((b : ℂ) - (a : ℂ)) := rfl

theorem mem_seg_segPath {X : Set ℂ} {a b : ↥X} (h : seg (a : ℂ) (b : ℂ) ⊆ X) (t : I) :
    ((segPath a b h t : ↥X) : ℂ) ∈ seg (a : ℂ) (b : ℂ) := ⟨(t : ℝ), t.2, rfl⟩

/-! ### The straight-line homotopy away from a point -/

/-- **Two vectors making a positive inner product do not straddle the origin.** -/
theorem notMem_seg_of_re_pos {z w : ℂ} (h : 0 < (z * (starRingEnd ℂ) w).re) :
    (0 : ℂ) ∉ seg z w := by
  rintro ⟨t, ⟨ht0, ht1⟩, hzero⟩
  have key : (z + (t : ℂ) * (w - z)) * (starRingEnd ℂ) w
      = ((1 - t : ℝ) : ℂ) * (z * (starRingEnd ℂ) w) + (t : ℂ) * (Complex.normSq w : ℂ) := by
    rw [← Complex.mul_conj]
    push_cast
    ring
  rw [← hzero, zero_mul] at key
  have hre : 0 = (1 - t) * (z * (starRingEnd ℂ) w).re + t * Complex.normSq w := by
    have := congrArg Complex.re key
    simpa using this
  rcases eq_or_lt_of_le ht1 with ht | ht
  · -- `t = 1`: the second vector is the origin, so the inner product vanishes
    have hw : w = 0 := by
      have : (0 : ℂ) = w := by rw [hzero, ht]; push_cast; ring
      exact this.symm
    rw [hw] at h
    simp at h
  · nlinarith [Complex.normSq_nonneg w]

/-- **Two paths which never point in opposite directions as seen from `s` are homotopic in a
region avoiding `s`.**  The straight-line homotopy between them cannot cross `s`. -/
theorem homotopic_of_re_pos {X K : Set ℂ} (hK : IsSegClosed K) {s : ℂ} (hKX : K \ {s} ⊆ X)
    {a b : ↥X} (p q : Path a b) (hp : ∀ t, (p t : ℂ) ∈ K) (hq : ∀ t, (q t : ℂ) ∈ K)
    (hpos : ∀ t, 0 < (((p t : ℂ) - s) * (starRingEnd ℂ) ((q t : ℂ) - s)).re) :
    p.Homotopic q := by
  have hmem : ∀ (u t : I), ((p t : ↥X) : ℂ) + ((u : ℝ) : ℂ) * (((q t : ↥X) : ℂ)
      - ((p t : ↥X) : ℂ)) ∈ X := by
    intro u t
    refine hKX ⟨hK _ (hp t) _ (hq t) ⟨(u : ℝ), u.2, rfl⟩, ?_⟩
    intro hs
    simp only [Set.mem_singleton_iff] at hs
    refine notMem_seg_of_re_pos (hpos t) ⟨(u : ℝ), u.2, ?_⟩
    linear_combination -hs
  refine ⟨{ toFun := fun v => ⟨((p v.2 : ↥X) : ℂ)
              + ((v.1 : ℝ) : ℂ) * (((q v.2 : ↥X) : ℂ) - ((p v.2 : ↥X) : ℂ)), hmem v.1 v.2⟩
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · refine Continuous.subtype_mk (Continuous.add ?_ (Continuous.mul ?_ (Continuous.sub ?_ ?_))) _
    · exact continuous_subtype_val.comp (p.continuous.comp continuous_snd)
    · exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    · exact continuous_subtype_val.comp (q.continuous.comp continuous_snd)
    · exact continuous_subtype_val.comp (p.continuous.comp continuous_snd)
  · intro t
    refine Subtype.ext ?_
    simp
  · intro t
    refine Subtype.ext ?_
    show ((p t : ↥X) : ℂ) + (((1 : I) : ℝ) : ℂ) * (((q t : ↥X) : ℂ) - ((p t : ↥X) : ℂ))
      = ((q t : ↥X) : ℂ)
    norm_num
  · rintro u x (rfl | rfl) <;>
    · refine Subtype.ext ?_
      simp only [Path.source, Path.target, ContinuousMap.coe_mk, Path.coe_toContinuousMap]
      ring

end Rigidity.RET

end
