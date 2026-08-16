/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverFibre

/-!
# The covering space attached to a monodromy homomorphism

The fibres of the cover attached to a monodromy homomorphism `φ` are the equivariant labels of
`RET/Pi1/Topological/CoverFibre.lean`.  They are glued into a space here, and the projection to the
region is shown to be a covering map.

The gluing is the obvious one: over a flat piece `K` — a convex open subset of the region — a label
over one point of `K` determines a label over each other point of `K`, by transport along the
straight segment joining them, and the resulting family is declared open.  These *sheets* are a
basis of a topology, because the intersection of two flat pieces is flat and two sheets that meet
over a flat piece agree over the whole of it: transporting twice along segments of one flat piece
is transporting once, since a convex set is simply connected.

Over a flat piece the total space is then the product of the piece with a single fibre, by
transport, and that product decomposition is a homeomorphism because a locally constant map to a
discrete space is continuous.  Every point of an open region lies in a flat piece, so the
projection is a covering map with fibre the labels.

## Main definitions

* `Rigidity.RET.MonodromyData.sheet` — the family of labels over a flat piece obtained by
  transporting one of them.
* `Rigidity.RET.MonodromyData.instTopologicalSpaceTotal` — the topology of the total space.
* `Rigidity.RET.MonodromyData.flatHomeomorph` — the product decomposition over a flat piece.

## Main results

* `Rigidity.RET.MonodromyData.isTopologicalBasis_sheets` — the sheets are a basis.
* `Rigidity.RET.MonodromyData.continuous_proj` — the projection is continuous.
* `Rigidity.RET.MonodromyData.isEvenlyCovered_fib` — a flat piece is evenly covered.
* `Rigidity.RET.MonodromyData.isCoveringMap_proj` — the projection is a covering map.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET.MonodromyData

variable {X : Set ℂ} {x₀ : ↥X} {H : Type*} [Group H] (D : MonodromyData x₀ H)

/-! ### Sheets -/

/-- **The sheet of a label over a flat piece**: the labels obtained from `s` by transport along the
straight segments of `K`, one over each point of `K`. -/
def sheet {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K) (s : D.Fib x) :
    Set D.Total :=
  {y | ∃ hy : ((y.1 : ↥X) : ℂ) ∈ K, y.2 = D.restrict (segClass hK hy hx) s}

theorem mem_sheet_iff {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K) (s : D.Fib x)
    (y : D.Total) :
    y ∈ D.sheet hK hx s ↔ ∃ hy : ((y.1 : ↥X) : ℂ) ∈ K, y.2 = D.restrict (segClass hK hy hx) s :=
  Iff.rfl

theorem mk_mem_sheet {K : Set ℂ} (hK : IsFlat X K) {x y : ↥X} (hx : (x : ℂ) ∈ K)
    (hy : (y : ℂ) ∈ K) (s : D.Fib x) :
    (⟨y, D.restrict (segClass hK hy hx) s⟩ : D.Total) ∈ D.sheet hK hx s := ⟨hy, rfl⟩

theorem self_mem_sheet {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K) (s : D.Fib x) :
    (⟨x, s⟩ : D.Total) ∈ D.sheet hK hx s := by
  refine ⟨hx, ?_⟩
  rw [segClass_self, D.restrict_refl]

/-- The label of a point of a sheet, read off the label the sheet was built from. -/
theorem snd_eq_of_mem_sheet {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K)
    (s : D.Fib x) {y : D.Total} (hy : y ∈ D.sheet hK hx s) (hyK : ((y.1 : ↥X) : ℂ) ∈ K) :
    y.2 = D.restrict (segClass hK hyK hx) s := hy.choose_spec

/-- **A sheet is determined by any one of its points.** -/
theorem sheet_eq_of_mem {K : Set ℂ} (hK : IsFlat X K) {x y : ↥X} (hx : (x : ℂ) ∈ K)
    (hy : (y : ℂ) ∈ K) (s : D.Fib x) (t : D.Fib y)
    (h : (⟨y, t⟩ : D.Total) ∈ D.sheet hK hx s) : D.sheet hK hy t = D.sheet hK hx s := by
  have ht : t = D.restrict (segClass hK hy hx) s := D.snd_eq_of_mem_sheet hK hx s h hy
  refine Set.ext fun z => ⟨?_, ?_⟩
  · rintro ⟨hz, hz2⟩
    refine ⟨hz, ?_⟩
    rw [hz2, ht, D.restrict_restrict, segClass_trans]
  · rintro ⟨hz, hz2⟩
    refine ⟨hz, ?_⟩
    rw [hz2, ht, D.restrict_restrict, segClass_trans]

/-- A sheet over a smaller flat piece sits inside the sheet over a bigger one. -/
theorem sheet_subset_sheet {K L : Set ℂ} (hK : IsFlat X K) (hL : IsFlat X L) (hKL : K ⊆ L)
    {x : ↥X} (hx : (x : ℂ) ∈ K) (s : D.Fib x) :
    D.sheet hK hx s ⊆ D.sheet hL (hKL hx) s := by
  rintro y ⟨hy, hy2⟩
  exact ⟨hKL hy, by rw [hy2, segClass_mono hK hL hKL hy hx]⟩

/-! ### The topology of the total space -/

/-- The sheets over the flat pieces of the region. -/
def sheets : Set (Set D.Total) :=
  {U | ∃ (K : Set ℂ) (hK : IsFlat X K) (x : ↥X) (hx : (x : ℂ) ∈ K) (s : D.Fib x),
    U = D.sheet hK hx s}

theorem sheet_mem_sheets {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K)
    (s : D.Fib x) : D.sheet hK hx s ∈ D.sheets := ⟨K, hK, x, hx, s, rfl⟩

/-- The topology of the total space: the sheets are a basis. -/
instance instTopologicalSpaceTotal : TopologicalSpace D.Total :=
  TopologicalSpace.generateFrom D.sheets

/-- The fibres carry the discrete topology. -/
instance instTopologicalSpaceFib (x : ↥X) : TopologicalSpace (D.Fib x) := ⊥

instance instDiscreteTopologyFib (x : ↥X) : DiscreteTopology (D.Fib x) := ⟨rfl⟩

theorem isOpen_sheet {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K) (s : D.Fib x) :
    IsOpen (D.sheet hK hx s) :=
  TopologicalSpace.GenerateOpen.basic _ (D.sheet_mem_sheets hK hx s)

/-- **The sheets are a topological basis of the total space.** -/
theorem isTopologicalBasis_sheets : TopologicalSpace.IsTopologicalBasis D.sheets where
  exists_subset_inter := by
    rintro _ ⟨K, hK, x, hx, s, rfl⟩ _ ⟨L, hL, y, hy, t, rfl⟩ z ⟨hz₁, hz₂⟩
    obtain ⟨hzK, -⟩ := id hz₁
    obtain ⟨hzL, -⟩ := id hz₂
    refine ⟨D.sheet (hK.inter hL) ⟨hzK, hzL⟩ z.2, D.sheet_mem_sheets _ _ _, ?_, ?_⟩
    · have := D.self_mem_sheet (hK.inter hL) (x := z.1) ⟨hzK, hzL⟩ z.2
      simpa using this
    · refine Set.subset_inter ?_ ?_
      · refine (D.sheet_subset_sheet (hK.inter hL) hK Set.inter_subset_left ⟨hzK, hzL⟩ z.2).trans ?_
        exact le_of_eq (D.sheet_eq_of_mem hK hx hzK s z.2 (by simpa using hz₁))
      · refine (D.sheet_subset_sheet (hK.inter hL) hL Set.inter_subset_right ⟨hzK, hzL⟩ z.2).trans ?_
        exact le_of_eq (D.sheet_eq_of_mem hL hy hzL t z.2 (by simpa using hz₂))
  sUnion_eq := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨K, hK, hyK⟩ := exists_isFlat_mem D.isOpen_region (y.1).2
    exact ⟨_, D.sheet_mem_sheets hK hyK y.2, by simpa using D.self_mem_sheet hK hyK y.2⟩
  eq_generateFrom := rfl

/-! ### The projection is continuous -/

/-- **A sheet through a point of the total space, inside a prescribed open set of the region.** -/
theorem exists_sheet_subset_preimage {W : Set ↥X} (hW : IsOpen W) (y : D.Total) (hy : y.1 ∈ W) :
    ∃ (K : Set ℂ) (hK : IsFlat X K) (hyK : ((y.1 : ↥X) : ℂ) ∈ K),
      D.sheet hK hyK y.2 ⊆ D.proj ⁻¹' W := by
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.mp hW
  obtain ⟨K, hK, hyK⟩ :=
    exists_isFlat_mem (D.isOpen_region.inter hW') ⟨(y.1).2, hy⟩
  refine ⟨K, hK.mono Set.inter_subset_left, hyK, ?_⟩
  rintro z ⟨hz, -⟩
  exact (hK.subset hz).2

theorem continuous_proj : Continuous D.proj := by
  refine continuous_def.mpr fun W hW => ?_
  refine isOpen_iff_forall_mem_open.mpr fun y hy => ?_
  obtain ⟨K, hK, hyK, hsub⟩ := D.exists_sheet_subset_preimage hW y hy
  exact ⟨_, hsub, D.isOpen_sheet hK hyK y.2, by simpa using D.self_mem_sheet hK hyK y.2⟩

/-! ### The product decomposition over a flat piece -/

section Flat

variable {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K)

include hK in
/-- The part of the region cut out by a flat piece. -/
theorem isOpen_baseSet : IsOpen (Subtype.val ⁻¹' K : Set ↥X) :=
  hK.isOpen.preimage continuous_subtype_val

include hK in
theorem isOpen_proj_preimage : IsOpen (D.proj ⁻¹' (Subtype.val ⁻¹' K : Set ↥X)) :=
  (isOpen_baseSet hK).preimage D.continuous_proj

/-- **Reading a point of the total space over a flat piece as a label over a fixed point of that
piece**, by transport along the straight segment. -/
def flatLabel (y : D.proj ⁻¹' (Subtype.val ⁻¹' K : Set ↥X)) : D.Fib x :=
  D.restrict (segClass hK hx (y.2 : ((y.1).1 : ℂ) ∈ K)) (y.1).2

include hK hx in
/-- The label read over a fixed point of a flat piece is constant on each sheet, hence continuous
into the discrete fibre. -/
theorem continuous_flatLabel : Continuous (D.flatLabel hK hx) := by
  refine continuous_def.mpr fun V _ => ?_
  refine isOpen_iff_forall_mem_open.mpr fun y hy => ?_
  have hyK : ((y.1).1 : ℂ) ∈ K := y.2
  refine ⟨Subtype.val ⁻¹' D.sheet hK hyK (y.1).2,
    ?_, (D.isOpen_sheet hK hyK (y.1).2).preimage continuous_subtype_val, ?_⟩
  · rintro z hz
    have hzK : ((z.1).1 : ℂ) ∈ K := z.2
    have hz2 : (z.1).2 = D.restrict (segClass hK hzK hyK) (y.1).2 :=
      D.snd_eq_of_mem_sheet hK hyK (y.1).2 hz hzK
    have : D.flatLabel hK hx z = D.flatLabel hK hx y := by
      show D.restrict (segClass hK hx hzK) (z.1).2 = D.restrict (segClass hK hx hyK) (y.1).2
      rw [hz2, D.restrict_restrict, segClass_trans]
    rw [Set.mem_preimage, this]
    exact hy
  · exact D.self_mem_sheet hK hyK (y.1).2

/-- **Spreading a label over a fixed point of a flat piece across the whole piece.** -/
def flatSection (z : (Subtype.val ⁻¹' K : Set ↥X)) (e : D.Fib x) : D.Total :=
  ⟨z.1, D.restrict (segClass hK (z.2 : ((z.1 : ↥X) : ℂ) ∈ K) hx) e⟩

include hK hx in
theorem continuous_flatSection :
    Continuous fun p : (Subtype.val ⁻¹' K : Set ↥X) × D.Fib x => D.flatSection hK hx p.1 p.2 := by
  refine continuous_def.mpr fun U hU => ?_
  refine isOpen_iff_forall_mem_open.mpr fun p hp => ?_
  obtain ⟨L, hL, z, hzL, t, hLsub, hmem⟩ :
      ∃ (L : Set ℂ) (hL : IsFlat X L) (z : ↥X) (hzL : (z : ℂ) ∈ L) (t : D.Fib z),
        D.sheet hL hzL t ⊆ U ∧ D.flatSection hK hx p.1 p.2 ∈ D.sheet hL hzL t := by
    obtain ⟨V, hV, hpV, hVU⟩ := (D.isTopologicalBasis_sheets).exists_subset_of_mem_open hp hU
    obtain ⟨L, hL, z, hzL, t, rfl⟩ := hV
    exact ⟨L, hL, z, hzL, t, hVU, hpV⟩
  set p0 : ↥X := (p.1 : ↥X)
  have hp0K : (p0 : ℂ) ∈ K := p.1.2
  have hp0L : (p0 : ℂ) ∈ L := hmem.choose
  have hp0eq : D.restrict (segClass hK hp0K hx) p.2 = D.restrict (segClass hL hp0L hzL) t :=
    hmem.choose_spec
  refine ⟨(fun q : (Subtype.val ⁻¹' K : Set ↥X) × D.Fib x => ((q.1 : ↥X) : ℂ)) ⁻¹' (K ∩ L) ∩
      (fun q : (Subtype.val ⁻¹' K : Set ↥X) × D.Fib x => q.2) ⁻¹' {p.2}, ?_, ?_, ?_⟩
  · rintro q ⟨hq, hq2⟩
    refine hLsub ⟨hq.2, ?_⟩
    have hqK : ((q.1 : ↥X) : ℂ) ∈ K := q.1.2
    have hmid : segClass (hK.inter hL) ⟨hq.1, hq.2⟩ (⟨hp0K, hp0L⟩ : (p0 : ℂ) ∈ K ∩ L)
        = segClass hK hqK hp0K :=
      (segClass_mono (hK.inter hL) hK Set.inter_subset_left _ _)
    have hmid' : segClass (hK.inter hL) ⟨hq.1, hq.2⟩ (⟨hp0K, hp0L⟩ : (p0 : ℂ) ∈ K ∩ L)
        = segClass hL hq.2 hp0L :=
      (segClass_mono (hK.inter hL) hL Set.inter_subset_right _ _)
    show D.restrict (segClass hK hqK hx) q.2 = D.restrict (segClass hL hq.2 hzL) t
    have hq2' : q.2 = p.2 := hq2
    rw [hq2', ← segClass_trans hK hqK hp0K hx, ← D.restrict_restrict, hp0eq,
      D.restrict_restrict, ← hmid, hmid', segClass_trans]
  · exact ((hK.isOpen.inter hL.isOpen).preimage
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst)).inter
      (isOpen_discrete _ |>.preimage continuous_snd)
  · exact ⟨⟨hp0K, hp0L⟩, rfl⟩

include hK hx in
/-- **Over a flat piece the total space is the product of the piece with one fibre.** -/
def flatHomeomorph :
    (D.proj ⁻¹' (Subtype.val ⁻¹' K : Set ↥X)) ≃ₜ (Subtype.val ⁻¹' K : Set ↥X) × D.Fib x where
  toFun y := (⟨(y.1).1, y.2⟩, D.flatLabel hK hx y)
  invFun p := ⟨D.flatSection hK hx p.1 p.2, p.1.2⟩
  left_inv y := by
    have hyK : ((y.1).1 : ℂ) ∈ K := y.2
    refine Subtype.ext ?_
    refine Sigma.ext rfl ?_
    show HEq (D.restrict (segClass hK hyK hx) (D.restrict (segClass hK hx hyK) (y.1).2)) (y.1).2
    rw [D.restrict_restrict, segClass_trans, segClass_self, D.restrict_refl]
  right_inv p := by
    have hpK : ((p.1 : ↥X) : ℂ) ∈ K := p.1.2
    refine Prod.ext (Subtype.ext rfl) ?_
    show D.restrict (segClass hK hx hpK) (D.restrict (segClass hK hpK hx) p.2) = p.2
    rw [D.restrict_restrict, segClass_trans, segClass_self, D.restrict_refl]
  continuous_toFun :=
    ((D.continuous_proj.comp continuous_subtype_val).subtype_mk _).prodMk
      (D.continuous_flatLabel hK hx)
  continuous_invFun := (D.continuous_flatSection hK hx).subtype_mk _

include hK hx in
/-- **A flat piece is evenly covered.** -/
theorem isEvenlyCovered_of_isFlat : IsEvenlyCovered D.proj x (D.Fib x) :=
  ⟨inferInstance, Subtype.val ⁻¹' K, hx, isOpen_baseSet hK, D.isOpen_proj_preimage hK,
    D.flatHomeomorph hK hx, fun _ => rfl⟩

end Flat

/-- **Every point of the region is evenly covered.** -/
theorem isEvenlyCovered_fib (x : ↥X) : IsEvenlyCovered D.proj x (D.Fib x) := by
  obtain ⟨K, hK, hxK⟩ := exists_isFlat_mem D.isOpen_region x.2
  exact D.isEvenlyCovered_of_isFlat hK hxK

/-- **The projection of the cover attached to a monodromy homomorphism is a covering map.** -/
theorem isCoveringMap_proj : IsCoveringMap D.proj := fun x =>
  (D.isEvenlyCovered_fib x).to_isEvenlyCovered_preimage

end Rigidity.RET.MonodromyData

end
