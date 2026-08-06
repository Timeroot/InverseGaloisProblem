/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Uniqueness
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Subdivision2D
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Seifert–van Kampen: the existence half and the pushout

The pushout universal property has two halves.  `VanKampen/Uniqueness.lean` proved the
**uniqueness** half (`functor_ext_of_restrictions`): a functor out of `π(X)` is pinned by its two
restrictions.  This file supplies the **existence** half and assembles the two into the pushout.

The existence half is `exists_descended_functor`: given a category `H` and functors
`u : π(U) ⥤ H`, `v : π(V) ⥤ H` that agree after restriction to `π(U ∩ V)`, there is a functor
`F : π(X) ⥤ H` restricting to `u` on `π(U)` and to `v` on `π(V)`.  On objects `F` sends a point to
`u` or `v` according to which cover element contains it (well-defined on the overlap by the
agreement hypothesis).  On a morphism `⟦γ⟧` one subdivides `γ` into pieces each supported in a
single cover element (`Generation.lean` / `Bridge.lean`), maps each piece by `u` or `v`, and
composes; the value is independent of the subdivision and of the homotopy class of `γ` — the latter
via the two-dimensional grid subdivision of a homotopy (`Subdivision2D.lean`), crossing the square
one cell at a time.

Combining existence and uniqueness gives the pushout: `desc` is the descended functor and the
mediating functor is unique by `functor_ext_of_restrictions`.

## Main declarations

* `Rigidity.RET.VanKampen.exists_descended_functor` — the existence half of the universal property.
* `Rigidity.RET.VanKampen.isPushout` — the Seifert–van Kampen square is a pushout in `Grpd`.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits FundamentalGroupoid Set unitInterval

namespace Rigidity.RET.VanKampen

variable {X : Type u} [TopologicalSpace X] (U V : Set X)

/-- **Object part of the descended functor.**  A point of `X` is sent to its `u`-image if it lies
in `U`, otherwise to its `v`-image (the cover `X = U ∪ V` guarantees one of the two).  On the
overlap `U ∩ V` the two choices agree, by the object part of the compatibility hypothesis. -/
noncomputable def descObj (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H) (x : X) : H :=
  letI : Decidable (x ∈ U) := Classical.dec _
  if h : x ∈ U then u.obj ⟨⟨x, h⟩⟩
  else v.obj ⟨⟨x, by
    have hx : x ∈ U ∪ V := by rw [hUV]; exact mem_univ x
    exact hx.resolve_left h⟩⟩

/-- On `U`, the descended object map is `u`. -/
theorem descObj_of_mem_U (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H) (x : X) (h : x ∈ U) :
    descObj U V hUV u v x = u.obj ⟨⟨x, h⟩⟩ := by
  simp only [descObj, dif_pos h]

/-- On `V`, the descended object map is `v` — including on the overlap, where the compatibility
hypothesis `huv` forces `u` and `v` to agree. -/
theorem descObj_of_mem_V (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    (x : X) (h : x ∈ V) :
    descObj U V hUV u v x = v.obj ⟨⟨x, h⟩⟩ := by
  by_cases hU : x ∈ U
  · rw [descObj_of_mem_U U V hUV u v x hU]
    have hobj := Functor.congr_obj huv (⟨⟨x, ⟨hU, h⟩⟩⟩ : FundamentalGroupoid (U ∩ V : Set X))
    simpa [FundamentalGroupoid.map, inclUW, inclVW, Set.inclusion] using hobj
  · simp only [descObj, dif_neg hU]

/-- Lift a path `γ : Path a b` whose range lies in a subset `s` to a path in the subspace `↥s`;
pushing the lift forward along the inclusion `s ↪ X` recovers `γ` (`liftPath_map`). -/
def liftPath (s : Set X) {a b : X} (γ : Path a b) (h : range γ ⊆ s)
    (ha : a ∈ s) (hb : b ∈ s) : Path (⟨a, ha⟩ : s) (⟨b, hb⟩ : s) where
  toFun t := ⟨γ t, h ⟨t, rfl⟩⟩
  continuous_toFun := (map_continuous γ).subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp] theorem liftPath_map (s : Set X) {a b : X} (γ : Path a b) (h : range γ ⊆ s)
    (ha : a ∈ s) (hb : b ∈ s) :
    (liftPath s γ h ha hb).map continuous_subtype_val = γ := by
  ext t; rfl

@[simp] theorem liftPath_apply (s : Set X) {a b : X} (γ : Path a b) (h : range γ ⊆ s)
    (ha : a ∈ s) (hb : b ∈ s) (t : I) : ((liftPath s γ h ha hb t : s) : X) = γ t := rfl

/-- The lift of a concatenation is the concatenation of the lifts: as paths in the subspace `↥s`
they are equal, since both send `t` to `(p.trans q) t`. -/
theorem liftPath_trans (s : Set X) {a b c : X} (p : Path a b) (q : Path b c)
    (hp : range p ⊆ s) (hq : range q ⊆ s) (hpq : range (p.trans q) ⊆ s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    (liftPath s p hp ha hb).trans (liftPath s q hq hb hc)
      = liftPath s (p.trans q) hpq ha hc := by
  ext t
  show (((liftPath s p hp ha hb).trans (liftPath s q hq hb hc)) t : X) = (p.trans q) t
  rw [Path.trans_apply, Path.trans_apply]
  split <;> rfl

/-- **Lifting a homotopy into a subspace.**  A homotopy `F` between paths `p`, `q : Path a b` whose
total image lies in a subset `s` lifts to a homotopy between the lifted paths in the subspace `↥s`;
the lift is `F` with values corestricted to `s`. -/
def liftHomotopy (s : Set X) {a b : X} {p q : Path a b} (F : p.Homotopy q)
    (hs : ∀ y, F y ∈ s) (hp : range p ⊆ s) (hq : range q ⊆ s) (ha : a ∈ s) (hb : b ∈ s) :
    (liftPath s p hp ha hb).Homotopy (liftPath s q hq ha hb) where
  toContinuousMap := ⟨fun y => ⟨F y, hs y⟩, (map_continuous F).subtype_mk _⟩
  map_zero_left y := Subtype.ext (F.map_zero_left y)
  map_one_left y := Subtype.ext (F.map_one_left y)
  prop' t x hx := Subtype.ext (F.prop t x hx)

/-- The homotopy-class version of `liftHomotopy`: if `p` and `q` are joined by a homotopy staying in
`s`, their lifts to `↥s` have the same class in `π(s)`. -/
theorem liftPath_mk_eq_of_homotopy (s : Set X) {a b : X} {p q : Path a b} (F : p.Homotopy q)
    (hs : ∀ y, F y ∈ s) (hp : range p ⊆ s) (hq : range q ⊆ s) (ha : a ∈ s) (hb : b ∈ s) :
    (⟦liftPath s p hp ha hb⟧ : Path.Homotopic.Quotient (⟨a, ha⟩ : s) ⟨b, hb⟩)
      = ⟦liftPath s q hq ha hb⟧ :=
  Quotient.sound ⟨liftHomotopy s F hs hp hq ha hb⟩

/-- Lifting commutes with taking subpaths: the lift of a subpath of `γ` is the corresponding subpath
of the lift of `γ` (both send `s` to `⟨γ (subpathAux t₀ t₁ s), _⟩`). -/
theorem liftPath_subpath (s : Set X) {a b : X} (γ : Path a b) (hγ : range γ ⊆ s)
    (ha : a ∈ s) (hb : b ∈ s) (t₀ t₁ : I) (hsub : range (γ.subpath t₀ t₁) ⊆ s)
    (ha' : γ t₀ ∈ s) (hb' : γ t₁ ∈ s) :
    liftPath s (γ.subpath t₀ t₁) hsub ha' hb'
      = (liftPath s γ hγ ha hb).subpath t₀ t₁ := by
  ext s'; rfl

/-- **Local descended morphism (via `U`).**  The value the descended functor must take on a path
`γ` lying entirely in `U`: lift `γ` into `π(U)`, apply `u`, and reconcile the endpoints with the
`descObj` object map via the `eqToHom` bookkeeping. -/
noncomputable def descLocU (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U) (ha : a ∈ U) (hb : b ∈ U) :
    descObj U V hUV u v a ⟶ descObj U V hUV u v b :=
  eqToHom (descObj_of_mem_U U V hUV u v a ha) ≫
    u.map ⟦liftPath U γ hγ ha hb⟧ ≫
    eqToHom (descObj_of_mem_U U V hUV u v b hb).symm

/-- **Local descended morphism (via `V`).**  As `descLocU`, for a path `γ` lying entirely in `V`. -/
noncomputable def descLocV (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ V) (ha : a ∈ V) (hb : b ∈ V) :
    descObj U V hUV u v a ⟶ descObj U V hUV u v b :=
  eqToHom (descObj_of_mem_V U V hUV u v huv a ha) ≫
    v.map ⟦liftPath V γ hγ ha hb⟧ ≫
    eqToHom (descObj_of_mem_V U V hUV u v huv b hb).symm

/-- **Overlap agreement.**  A path lying in *both* cover elements gets the same local descended
morphism whether computed through `u` or through `v` — this is exactly where the compatibility
hypothesis `huv` is used, and it is what makes switching sides at a partition point legitimate. -/
theorem descLocU_eq_descLocV (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hU : range γ ⊆ U) (hV : range γ ⊆ V) :
    descLocU U V hUV u v γ hU (hU ⟨0, γ.source⟩) (hU ⟨1, γ.target⟩)
      = descLocV U V hUV u v huv γ hV (hV ⟨0, γ.source⟩) (hV ⟨1, γ.target⟩) := by
  have hW : range γ ⊆ (U ∩ V : Set X) := subset_inter hU hV
  have haW : a ∈ (U ∩ V : Set X) := hW ⟨0, γ.source⟩
  have hbW : b ∈ (U ∩ V : Set X) := hW ⟨1, γ.target⟩
  set δ : (⟨⟨a, haW⟩⟩ : FundamentalGroupoid (U ∩ V : Set X)) ⟶ ⟨⟨b, hbW⟩⟩ :=
    ⟦liftPath (U ∩ V : Set X) γ hW haW hbW⟧ with hδ
  -- pushing `δ` into `π(U)` (resp. `π(V)`) recovers the `U`- (resp. `V`-) lift of `γ`
  have eqU : (FundamentalGroupoid.map (inclUW U V)).map δ
      = (⟦liftPath U γ hU (hU ⟨0, γ.source⟩) (hU ⟨1, γ.target⟩)⟧
        : (⟨⟨a, hU ⟨0, γ.source⟩⟩⟩ : FundamentalGroupoid U) ⟶ ⟨⟨b, hU ⟨1, γ.target⟩⟩⟩) := by
    rw [hδ]
    show (⟦(liftPath (U ∩ V : Set X) γ hW haW hbW).map (inclUW U V).continuous⟧
        : Path.Homotopic.Quotient _ _) = ⟦liftPath U γ hU _ _⟧
    congr 1
  have eqV : (FundamentalGroupoid.map (inclVW U V)).map δ
      = (⟦liftPath V γ hV (hV ⟨0, γ.source⟩) (hV ⟨1, γ.target⟩)⟧
        : (⟨⟨a, hV ⟨0, γ.source⟩⟩⟩ : FundamentalGroupoid V) ⟶ ⟨⟨b, hV ⟨1, γ.target⟩⟩⟩) := by
    rw [hδ]
    show (⟦(liftPath (U ∩ V : Set X) γ hW haW hbW).map (inclVW U V).continuous⟧
        : Path.Homotopic.Quotient _ _) = ⟦liftPath V γ hV _ _⟧
    congr 1
  have key := Functor.congr_hom huv δ
  simp only [Functor.comp_map, eqU, eqV] at key
  simp only [descLocU, descLocV]
  rw [key]
  simp [eqToHom_trans, Category.assoc]

/-- **Same-side concatenation law (via `U`).**  The local descended morphism of a concatenation of
two paths in `U` is the composite of their local descended morphisms.  This is functoriality of `u`
together with `⟦liftPath (p.trans q)⟧ = ⟦liftPath p⟧ ≫ ⟦liftPath q⟧`; it is what makes the descended
morphism independent of a refinement of the subdivision. -/
theorem descLocU_trans (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    {a b c : X} (p : Path a b) (q : Path b c)
    (hp : range p ⊆ U) (hq : range q ⊆ U) (hpq : range (p.trans q) ⊆ U)
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) :
    descLocU U V hUV u v (p.trans q) hpq ha hc
      = descLocU U V hUV u v p hp ha hb ≫ descLocU U V hUV u v q hq hb hc := by
  have hcls :
      (⟦liftPath U p hp ha hb⟧ ≫ ⟦liftPath U q hq hb hc⟧ :
        (⟨⟨a, ha⟩⟩ : FundamentalGroupoid U) ⟶ ⟨⟨c, hc⟩⟩)
      = ⟦liftPath U (p.trans q) hpq ha hc⟧ := by
    rw [FundamentalGroupoid.comp_eq, ← liftPath_trans U p q hp hq hpq ha hb hc]
    exact (Path.Homotopic.Quotient.mk_trans _ _).symm
  simp only [descLocU]
  rw [← hcls, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Same-side concatenation law (via `V`).**  As `descLocU_trans`, for paths lying in `V`. -/
theorem descLocV_trans (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b c : X} (p : Path a b) (q : Path b c)
    (hp : range p ⊆ V) (hq : range q ⊆ V) (hpq : range (p.trans q) ⊆ V)
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) :
    descLocV U V hUV u v huv (p.trans q) hpq ha hc
      = descLocV U V hUV u v huv p hp ha hb ≫ descLocV U V hUV u v huv q hq hb hc := by
  have hcls :
      (⟦liftPath V p hp ha hb⟧ ≫ ⟦liftPath V q hq hb hc⟧ :
        (⟨⟨a, ha⟩⟩ : FundamentalGroupoid V) ⟶ ⟨⟨c, hc⟩⟩)
      = ⟦liftPath V (p.trans q) hpq ha hc⟧ := by
    rw [FundamentalGroupoid.comp_eq, ← liftPath_trans V p q hp hq hpq ha hb hc]
    exact (Path.Homotopic.Quotient.mk_trans _ _).symm
  simp only [descLocV]
  rw [← hcls, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The range of a subpath is contained in any set containing the range of the whole path. -/
theorem subpath_range_subset (s : Set X) {a b : X} (γ : Path a b) (h : range γ ⊆ s) (t₀ t₁ : I) :
    range (γ.subpath t₀ t₁) ⊆ s := by
  rw [Path.range_subpath]; exact (image_subset_range γ _).trans h

/-- **Subpath of a subpath.**  `subpath` composes affinely: taking the `σ₀`–`σ₁` subpath of the
`t₀`–`t₁` subpath of `γ` is the subpath of `γ` between the reparametrized endpoints.  This is the
affinity of `subpathAux` in its endpoint arguments. -/
theorem subpath_subpath {a b : X} (γ : Path a b) (t₀ t₁ σ₀ σ₁ : I) :
    (γ.subpath t₀ t₁).subpath σ₀ σ₁
      = γ.subpath (Path.subpathAux t₀ t₁ σ₀) (Path.subpathAux t₀ t₁ σ₁) := by
  ext s
  show (γ.subpath t₀ t₁) (Path.subpathAux σ₀ σ₁ s)
    = γ (Path.subpathAux (Path.subpathAux t₀ t₁ σ₀) (Path.subpathAux t₀ t₁ σ₁) s)
  show γ (Path.subpathAux t₀ t₁ (Path.subpathAux σ₀ σ₁ s))
    = γ (Path.subpathAux (Path.subpathAux t₀ t₁ σ₀) (Path.subpathAux t₀ t₁ σ₁) s)
  congr 1
  apply Subtype.ext
  simp only [Path.subpathAux]
  ring

/-- The range of a subpath, as an image of the closed interval between its endpoints. -/
theorem range_subpath_uIcc {a b : X} (γ : Path a b) (t₀ t₁ : I) :
    range (γ.subpath t₀ t₁) = γ '' Set.uIcc t₀ t₁ := Path.range_subpath γ t₀ t₁

/-- **Subpath additivity (via `U`).**  For a path `γ` lying entirely in `U`, the local descended
morphism of a subpath splits at any interior parameter.  Proved by lifting `γ` to `↥U` *once* and
using Mathlib's `subpathTransSubpath` there, so no ambient homotopy-image bound is needed. -/
theorem descLocU_subpath_additive (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U) (t₀ t₁ t₂ : I) :
    descLocU U V hUV u v (γ.subpath t₀ t₂) (subpath_range_subset U γ hγ t₀ t₂)
        (hγ (mem_range_self t₀)) (hγ (mem_range_self t₂))
      = descLocU U V hUV u v (γ.subpath t₀ t₁) (subpath_range_subset U γ hγ t₀ t₁)
          (hγ (mem_range_self t₀)) (hγ (mem_range_self t₁))
        ≫ descLocU U V hUV u v (γ.subpath t₁ t₂) (subpath_range_subset U γ hγ t₁ t₂)
          (hγ (mem_range_self t₁)) (hγ (mem_range_self t₂)) := by
  have m0 : γ t₀ ∈ U := hγ (mem_range_self t₀)
  have m1 : γ t₁ ∈ U := hγ (mem_range_self t₁)
  have m2 : γ t₂ ∈ U := hγ (mem_range_self t₂)
  have h0m : a ∈ U := hγ ⟨0, γ.source⟩
  have h1m : b ∈ U := hγ ⟨1, γ.target⟩
  have hcls :
      (⟦liftPath U (γ.subpath t₀ t₁) (subpath_range_subset U γ hγ t₀ t₁) m0 m1⟧
          ≫ ⟦liftPath U (γ.subpath t₁ t₂) (subpath_range_subset U γ hγ t₁ t₂) m1 m2⟧
        : (⟨⟨γ t₀, m0⟩⟩ : FundamentalGroupoid U) ⟶ ⟨⟨γ t₂, m2⟩⟩)
      = ⟦liftPath U (γ.subpath t₀ t₂) (subpath_range_subset U γ hγ t₀ t₂) m0 m2⟧ := by
    rw [FundamentalGroupoid.comp_eq]
    exact Quotient.sound ⟨Path.Homotopy.subpathTransSubpath (liftPath U γ hγ h0m h1m) t₀ t₁ t₂⟩
  simp only [descLocU]
  rw [← hcls, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Subpath additivity (via `V`).**  As `descLocU_subpath_additive`, for a path lying in `V`. -/
theorem descLocV_subpath_additive (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ V) (t₀ t₁ t₂ : I) :
    descLocV U V hUV u v huv (γ.subpath t₀ t₂) (subpath_range_subset V γ hγ t₀ t₂)
        (hγ (mem_range_self t₀)) (hγ (mem_range_self t₂))
      = descLocV U V hUV u v huv (γ.subpath t₀ t₁) (subpath_range_subset V γ hγ t₀ t₁)
          (hγ (mem_range_self t₀)) (hγ (mem_range_self t₁))
        ≫ descLocV U V hUV u v huv (γ.subpath t₁ t₂) (subpath_range_subset V γ hγ t₁ t₂)
          (hγ (mem_range_self t₁)) (hγ (mem_range_self t₂)) := by
  have m0 : γ t₀ ∈ V := hγ (mem_range_self t₀)
  have m1 : γ t₁ ∈ V := hγ (mem_range_self t₁)
  have m2 : γ t₂ ∈ V := hγ (mem_range_self t₂)
  have h0m : a ∈ V := hγ ⟨0, γ.source⟩
  have h1m : b ∈ V := hγ ⟨1, γ.target⟩
  have hcls :
      (⟦liftPath V (γ.subpath t₀ t₁) (subpath_range_subset V γ hγ t₀ t₁) m0 m1⟧
          ≫ ⟦liftPath V (γ.subpath t₁ t₂) (subpath_range_subset V γ hγ t₁ t₂) m1 m2⟧
        : (⟨⟨γ t₀, m0⟩⟩ : FundamentalGroupoid V) ⟶ ⟨⟨γ t₂, m2⟩⟩)
      = ⟦liftPath V (γ.subpath t₀ t₂) (subpath_range_subset V γ hγ t₀ t₂) m0 m2⟧ := by
    rw [FundamentalGroupoid.comp_eq]
    exact Quotient.sound ⟨Path.Homotopy.subpathTransSubpath (liftPath V γ hγ h0m h1m) t₀ t₁ t₂⟩
  simp only [descLocV]
  rw [← hcls, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Existence of an interior parameter.**  If `x₀ ≤ x₁ ≤ x₂` in the unit interval, there is a
parameter `σ` with `subpathAux x₀ x₂ σ = x₁`: the affine reparametrization of `[x₀, x₂]` hitting the
interior point `x₁`.  (When `x₀ = x₂` the endpoints coincide and any `σ` works.) -/
theorem subpathAux_mid_exists (x₀ x₁ x₂ : I) (h01 : x₀ ≤ x₁) (h12 : x₁ ≤ x₂) :
    ∃ σ₁ : I, Path.subpathAux x₀ x₂ σ₁ = x₁ := by
  have h01' : (x₀ : ℝ) ≤ x₁ := Subtype.coe_le_coe.2 h01
  have h12' : (x₁ : ℝ) ≤ x₂ := Subtype.coe_le_coe.2 h12
  rcases eq_or_lt_of_le (h01.trans h12) with heq | hlt
  · subst heq
    have hx1 : x₁ = x₀ := le_antisymm h12 h01
    refine ⟨0, ?_⟩
    rw [hx1]
    apply Subtype.ext
    simp [Path.subpathAux]
  · have hlt' : (x₀ : ℝ) < x₂ := Subtype.coe_lt_coe.2 hlt
    have hd : (0 : ℝ) < (x₂ : ℝ) - x₀ := by linarith
    refine ⟨⟨((x₁ : ℝ) - x₀) / ((x₂ : ℝ) - x₀), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hd.le
    · rw [div_le_one hd]; linarith
    · apply Subtype.ext
      simp only [Path.subpathAux]
      field_simp
      ring

/-- **Span additivity (via `U`).**  For any path `γ`, if the *spanning* subpath `γ.subpath x₀ x₂`
lies in `U` and `x₀ ≤ x₁ ≤ x₂`, the local descended morphism splits at the interior ambient point
`x₁`.  Unlike `descLocU_subpath_additive` this only needs the span (not all of `γ`) in `U`: it is
`descLocU_subpath_additive` applied to the span, reparametrized to hit `x₁`. -/
theorem descLocU_span_additive (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    {a b : X} (γ : Path a b) (x₀ x₁ x₂ : I) (h01 : x₀ ≤ x₁) (h12 : x₁ ≤ x₂)
    (hr02 : range (γ.subpath x₀ x₂) ⊆ U)
    (hr01 : range (γ.subpath x₀ x₁) ⊆ U) (hr12 : range (γ.subpath x₁ x₂) ⊆ U)
    (m0 : γ x₀ ∈ U) (m1 : γ x₁ ∈ U) (m2 : γ x₂ ∈ U) :
    descLocU U V hUV u v (γ.subpath x₀ x₂) hr02 m0 m2
      = descLocU U V hUV u v (γ.subpath x₀ x₁) hr01 m0 m1
        ≫ descLocU U V hUV u v (γ.subpath x₁ x₂) hr12 m1 m2 := by
  obtain ⟨σ₁, hσ⟩ := subpathAux_mid_exists x₀ x₁ x₂ h01 h12
  have hσr : (1 - (σ₁ : ℝ)) * x₀ + σ₁ * x₂ = x₁ := by
    have := congrArg (Subtype.val) hσ
    simpa [Path.subpathAux] using this
  -- the affine composite identity: reparametrizing the span by `subpathAux 0 σ₁` gives `subpath x₀ x₁`
  have aux01 : ∀ s : I,
      (Path.subpathAux x₀ x₂ (Path.subpathAux 0 σ₁ s) : ℝ) = (Path.subpathAux x₀ x₁ s : ℝ) := by
    intro s
    simp only [Path.subpathAux, Set.Icc.coe_zero]
    linear_combination (s : ℝ) * hσr
  have aux12 : ∀ s : I,
      (Path.subpathAux x₀ x₂ (Path.subpathAux σ₁ 1 s) : ℝ) = (Path.subpathAux x₁ x₂ s : ℝ) := by
    intro s
    simp only [Path.subpathAux, Set.Icc.coe_one]
    linear_combination (1 - (s : ℝ)) * hσr
  set Γ : Path (⟨γ x₀, m0⟩ : U) (⟨γ x₂, m2⟩ : U) := liftPath U (γ.subpath x₀ x₂) hr02 m0 m2 with hΓ
  set A : Path (⟨γ x₀, m0⟩ : U) (⟨γ x₁, m1⟩ : U) := liftPath U (γ.subpath x₀ x₁) hr01 m0 m1 with hA
  set B : Path (⟨γ x₁, m1⟩ : U) (⟨γ x₂, m2⟩ : U) := liftPath U (γ.subpath x₁ x₂) hr12 m1 m2 with hB
  -- pointwise agreement of the lifted pieces with subpaths of the lifted span
  have hAeq : ∀ s, (A s : X) = ((Γ.subpath 0 σ₁) s : X) := by
    intro s
    show (γ.subpath x₀ x₁ s : X) = (γ.subpath x₀ x₂ (Path.subpathAux 0 σ₁ s) : X)
    show γ (Path.subpathAux x₀ x₁ s) = γ (Path.subpathAux x₀ x₂ (Path.subpathAux 0 σ₁ s))
    congr 1; exact Subtype.ext (aux01 s).symm
  have hBeq : ∀ s, (B s : X) = ((Γ.subpath σ₁ 1) s : X) := by
    intro s
    show (γ.subpath x₁ x₂ s : X) = (γ.subpath x₀ x₂ (Path.subpathAux σ₁ 1 s) : X)
    show γ (Path.subpathAux x₁ x₂ s) = γ (Path.subpathAux x₀ x₂ (Path.subpathAux σ₁ 1 s))
    congr 1; exact Subtype.ext (aux12 s).symm
  have hΓeq : ∀ s, (Γ s : X) = ((Γ.subpath 0 1) s : X) := by
    intro s
    show (γ.subpath x₀ x₂ s : X) = (γ.subpath x₀ x₂ (Path.subpathAux 0 1 s) : X)
    congr 1
    apply Subtype.ext
    simp [Path.subpathAux]
  -- the key class equality in `π(U)`
  have hcls :
      (⟦A⟧ ≫ ⟦B⟧ : (⟨⟨γ x₀, m0⟩⟩ : FundamentalGroupoid U) ⟶ ⟨⟨γ x₂, m2⟩⟩) = ⟦Γ⟧ := by
    rw [FundamentalGroupoid.comp_eq]
    show (⟦A.trans B⟧ : Path.Homotopic.Quotient _ _) = ⟦Γ⟧
    have hAB : ∀ s, (A.trans B) s
        = ((Γ.subpath 0 σ₁).trans (Γ.subpath σ₁ 1)) s := by
      intro s
      apply Subtype.ext
      simp only [Path.trans_apply]
      split_ifs
      · exact hAeq _
      · exact hBeq _
    have key1 : HEq (⟦A.trans B⟧ : Path.Homotopic.Quotient (⟨γ x₀, m0⟩ : U) ⟨γ x₂, m2⟩)
        (⟦(Γ.subpath 0 σ₁).trans (Γ.subpath σ₁ 1)⟧ :
          Path.Homotopic.Quotient (Γ 0) (Γ 1)) :=
      Path.Homotopic.hpath_hext hAB
    have key2 : (⟦(Γ.subpath 0 σ₁).trans (Γ.subpath σ₁ 1)⟧ :
          Path.Homotopic.Quotient (Γ 0) (Γ 1))
        = ⟦Γ.subpath 0 1⟧ :=
      Quotient.sound ⟨Path.Homotopy.subpathTransSubpath Γ 0 σ₁ 1⟩
    have key3 : HEq (⟦Γ.subpath 0 1⟧ : Path.Homotopic.Quotient (Γ 0) (Γ 1))
        (⟦Γ⟧ : Path.Homotopic.Quotient (⟨γ x₀, m0⟩ : U) ⟨γ x₂, m2⟩) :=
      Path.Homotopic.hpath_hext (fun s => Subtype.ext (hΓeq s).symm)
    exact eq_of_heq (key1.trans ((heq_of_eq key2).trans key3))
  simp only [descLocU, ← hΓ, ← hA, ← hB]
  rw [← hcls, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Span additivity (via `V`).**  As `descLocU_span_additive`, for a spanning subpath lying in
`V`: the local descended morphism of `γ.subpath x₀ x₂` splits at the interior ambient point `x₁`. -/
theorem descLocV_span_additive (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ x₂ : I) (h01 : x₀ ≤ x₁) (h12 : x₁ ≤ x₂)
    (hr02 : range (γ.subpath x₀ x₂) ⊆ V)
    (hr01 : range (γ.subpath x₀ x₁) ⊆ V) (hr12 : range (γ.subpath x₁ x₂) ⊆ V)
    (m0 : γ x₀ ∈ V) (m1 : γ x₁ ∈ V) (m2 : γ x₂ ∈ V) :
    descLocV U V hUV u v huv (γ.subpath x₀ x₂) hr02 m0 m2
      = descLocV U V hUV u v huv (γ.subpath x₀ x₁) hr01 m0 m1
        ≫ descLocV U V hUV u v huv (γ.subpath x₁ x₂) hr12 m1 m2 := by
  obtain ⟨σ₁, hσ⟩ := subpathAux_mid_exists x₀ x₁ x₂ h01 h12
  have hσr : (1 - (σ₁ : ℝ)) * x₀ + σ₁ * x₂ = x₁ := by
    have := congrArg (Subtype.val) hσ
    simpa [Path.subpathAux] using this
  have aux01 : ∀ s : I,
      (Path.subpathAux x₀ x₂ (Path.subpathAux 0 σ₁ s) : ℝ) = (Path.subpathAux x₀ x₁ s : ℝ) := by
    intro s
    simp only [Path.subpathAux, Set.Icc.coe_zero]
    linear_combination (s : ℝ) * hσr
  have aux12 : ∀ s : I,
      (Path.subpathAux x₀ x₂ (Path.subpathAux σ₁ 1 s) : ℝ) = (Path.subpathAux x₁ x₂ s : ℝ) := by
    intro s
    simp only [Path.subpathAux, Set.Icc.coe_one]
    linear_combination (1 - (s : ℝ)) * hσr
  set Γ : Path (⟨γ x₀, m0⟩ : V) (⟨γ x₂, m2⟩ : V) := liftPath V (γ.subpath x₀ x₂) hr02 m0 m2 with hΓ
  set A : Path (⟨γ x₀, m0⟩ : V) (⟨γ x₁, m1⟩ : V) := liftPath V (γ.subpath x₀ x₁) hr01 m0 m1 with hA
  set B : Path (⟨γ x₁, m1⟩ : V) (⟨γ x₂, m2⟩ : V) := liftPath V (γ.subpath x₁ x₂) hr12 m1 m2 with hB
  have hAeq : ∀ s, (A s : X) = ((Γ.subpath 0 σ₁) s : X) := by
    intro s
    show (γ.subpath x₀ x₁ s : X) = (γ.subpath x₀ x₂ (Path.subpathAux 0 σ₁ s) : X)
    show γ (Path.subpathAux x₀ x₁ s) = γ (Path.subpathAux x₀ x₂ (Path.subpathAux 0 σ₁ s))
    congr 1; exact Subtype.ext (aux01 s).symm
  have hBeq : ∀ s, (B s : X) = ((Γ.subpath σ₁ 1) s : X) := by
    intro s
    show (γ.subpath x₁ x₂ s : X) = (γ.subpath x₀ x₂ (Path.subpathAux σ₁ 1 s) : X)
    show γ (Path.subpathAux x₁ x₂ s) = γ (Path.subpathAux x₀ x₂ (Path.subpathAux σ₁ 1 s))
    congr 1; exact Subtype.ext (aux12 s).symm
  have hΓeq : ∀ s, (Γ s : X) = ((Γ.subpath 0 1) s : X) := by
    intro s
    show (γ.subpath x₀ x₂ s : X) = (γ.subpath x₀ x₂ (Path.subpathAux 0 1 s) : X)
    congr 1
    apply Subtype.ext
    simp [Path.subpathAux]
  have hcls :
      (⟦A⟧ ≫ ⟦B⟧ : (⟨⟨γ x₀, m0⟩⟩ : FundamentalGroupoid V) ⟶ ⟨⟨γ x₂, m2⟩⟩) = ⟦Γ⟧ := by
    rw [FundamentalGroupoid.comp_eq]
    show (⟦A.trans B⟧ : Path.Homotopic.Quotient _ _) = ⟦Γ⟧
    have hAB : ∀ s, (A.trans B) s
        = ((Γ.subpath 0 σ₁).trans (Γ.subpath σ₁ 1)) s := by
      intro s
      apply Subtype.ext
      simp only [Path.trans_apply]
      split_ifs
      · exact hAeq _
      · exact hBeq _
    have key1 : HEq (⟦A.trans B⟧ : Path.Homotopic.Quotient (⟨γ x₀, m0⟩ : V) ⟨γ x₂, m2⟩)
        (⟦(Γ.subpath 0 σ₁).trans (Γ.subpath σ₁ 1)⟧ :
          Path.Homotopic.Quotient (Γ 0) (Γ 1)) :=
      Path.Homotopic.hpath_hext hAB
    have key2 : (⟦(Γ.subpath 0 σ₁).trans (Γ.subpath σ₁ 1)⟧ :
          Path.Homotopic.Quotient (Γ 0) (Γ 1))
        = ⟦Γ.subpath 0 1⟧ :=
      Quotient.sound ⟨Path.Homotopy.subpathTransSubpath Γ 0 σ₁ 1⟩
    have key3 : HEq (⟦Γ.subpath 0 1⟧ : Path.Homotopic.Quotient (Γ 0) (Γ 1))
        (⟦Γ⟧ : Path.Homotopic.Quotient (⟨γ x₀, m0⟩ : V) ⟨γ x₂, m2⟩) :=
      Path.Homotopic.hpath_hext (fun s => Subtype.ext (hΓeq s).symm)
    exact eq_of_heq (key1.trans ((heq_of_eq key2).trans key3))
  simp only [descLocV, ← hΓ, ← hA, ← hB]
  rw [← hcls, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The local descended morphism of a constant path is the identity. -/
theorem descLocU_refl (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (x : X) (hx : x ∈ U) (hr : range (Path.refl x) ⊆ U) :
    descLocU U V hUV u v (Path.refl x) hr hx hx = 𝟙 (descObj U V hUV u v x) := by
  simp only [descLocU]
  have hlift : liftPath U (Path.refl x) hr hx hx = Path.refl (⟨x, hx⟩ : ↥U) := by ext s; rfl
  have hid : (⟦liftPath U (Path.refl x) hr hx hx⟧
        : (⟨⟨x, hx⟩⟩ : FundamentalGroupoid U) ⟶ (⟨⟨x, hx⟩⟩ : FundamentalGroupoid U))
      = 𝟙 (⟨⟨x, hx⟩⟩ : FundamentalGroupoid U) := by
    rw [hlift, FundamentalGroupoid.id_eq_path_refl]
  rw [hid, u.map_id]
  simp

/-- The local descended morphism (via `V`) of a constant path is the identity. -/
theorem descLocV_refl (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    (x : X) (hx : x ∈ V) (hr : range (Path.refl x) ⊆ V) :
    descLocV U V hUV u v huv (Path.refl x) hr hx hx = 𝟙 (descObj U V hUV u v x) := by
  simp only [descLocV]
  have hlift : liftPath V (Path.refl x) hr hx hx = Path.refl (⟨x, hx⟩ : ↥V) := by ext s; rfl
  have hid : (⟦liftPath V (Path.refl x) hr hx hx⟧
        : (⟨⟨x, hx⟩⟩ : FundamentalGroupoid V) ⟶ (⟨⟨x, hx⟩⟩ : FundamentalGroupoid V))
      = 𝟙 (⟨⟨x, hx⟩⟩ : FundamentalGroupoid V) := by
    rw [hlift, FundamentalGroupoid.id_eq_path_refl]
  rw [hid, v.map_id]
  simp

/-- **Homotopy invariance of the local descended morphism (via `U`).**  Two paths in `U` that are
homotopic through a homotopy staying in `U` have the same `U`-local descended morphism, because their
lifts to `↥U` are homotopic, hence have equal class in `π(U)`. -/
theorem descLocU_hom_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    {a b : X} (p q : Path a b) (hp : range p ⊆ U) (hq : range q ⊆ U) (ha : a ∈ U) (hb : b ∈ U)
    (F : p.Homotopy q) (hF : ∀ y, F y ∈ U) :
    descLocU U V hUV u v p hp ha hb = descLocU U V hUV u v q hq ha hb := by
  simp only [descLocU]
  rw [liftPath_mk_eq_of_homotopy U F hF hp hq ha hb]

/-- **Homotopy invariance of the local descended morphism (via `V`).**  As `descLocU_hom_congr`. -/
theorem descLocV_hom_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (p q : Path a b) (hp : range p ⊆ V) (hq : range q ⊆ V) (ha : a ∈ V) (hb : b ∈ V)
    (F : p.Homotopy q) (hF : ∀ y, F y ∈ V) :
    descLocV U V hUV u v huv p hp ha hb = descLocV U V hUV u v huv q hq ha hb := by
  simp only [descLocV]
  rw [liftPath_mk_eq_of_homotopy V F hF hp hq ha hb]

/-- The range of a finite concatenation lies in a set `s` as soon as the first basepoint does and
every piece does. -/
theorem range_concat_subset (s : Set X) {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (hp0 : p 0 ∈ s)
    (hF : ∀ k, range (F k) ⊆ s) : range (Path.concat p F) ⊆ s := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    exact Set.range_subset_iff.2 (fun _ => hp0)
  | succ n ih =>
    rw [Path.concat_succ, Path.trans_range]
    refine Set.union_subset (ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp0
      (fun k => hF k.castSucc)) (hF (Fin.last n))

/-- **Local descended morphism of a single cover-supported path.**  A path lying in `U` *or* in `V`
gets a descended morphism: computed through `u` if it lies in `U`, otherwise through `v`.  The two
recipes agree on the overlap (`descLocU_eq_descLocV`), so the choice is immaterial — recorded by the
computation lemmas `descPiece_eq_U` / `descPiece_eq_V`. -/
noncomputable def descPiece (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U ∨ range γ ⊆ V) :
    descObj U V hUV u v a ⟶ descObj U V hUV u v b :=
  letI : Decidable (range γ ⊆ U) := Classical.dec _
  if h : range γ ⊆ U then
    descLocU U V hUV u v γ h (h ⟨0, γ.source⟩) (h ⟨1, γ.target⟩)
  else
    have hV : range γ ⊆ V := hγ.resolve_left h
    descLocV U V hUV u v huv γ hV (hV ⟨0, γ.source⟩) (hV ⟨1, γ.target⟩)

/-- When the path lies in `U`, `descPiece` is the `U`-local morphism. -/
theorem descPiece_eq_U (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U ∨ range γ ⊆ V) (hU : range γ ⊆ U) :
    descPiece U V hUV u v huv γ hγ
      = descLocU U V hUV u v γ hU (hU ⟨0, γ.source⟩) (hU ⟨1, γ.target⟩) := by
  simp only [descPiece, dif_pos hU]

/-- When the path lies in `V`, `descPiece` is the `V`-local morphism — even if it also lies in `U`,
by overlap agreement. -/
theorem descPiece_eq_V (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U ∨ range γ ⊆ V) (hV : range γ ⊆ V) :
    descPiece U V hUV u v huv γ hγ
      = descLocV U V hUV u v huv γ hV (hV ⟨0, γ.source⟩) (hV ⟨1, γ.target⟩) := by
  by_cases hU : range γ ⊆ U
  · rw [descPiece_eq_U U V hUV u v huv γ hγ hU]
    exact descLocU_eq_descLocV U V hUV u v huv γ hU hV
  · simp only [descPiece, dif_neg hU]

/-- **Descended morphism of a subdivided path.**  Given a finite concatenation of paths
`F 0, F 1, …, F (m-1)` (with matching endpoints `p 0, …, p m`), each supported in a single cover
element, its descended morphism is the composite of the `descPiece`s.  This is the value the
descended functor takes on a cover-adapted subdivision; independence of the subdivision is
`descChain`'s refinement invariance. -/
noncomputable def descChain (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v) :
    {m : ℕ} → (p : Fin (m + 1) → X) →
      (F : (k : Fin m) → Path (p k.castSucc) (p k.succ)) →
      (∀ k, range (F k) ⊆ U ∨ range (F k) ⊆ V) →
      (descObj U V hUV u v (p 0) ⟶ descObj U V hUV u v (p (Fin.last m)))
  | 0, p, _, _ => 𝟙 (descObj U V hUV u v (p 0))
  | m + 1, p, F, hF =>
      descChain hUV u v huv (p ∘ Fin.castSucc) (fun k => F k.castSucc)
          (fun k => hF k.castSucc) ≫
        descPiece U V hUV u v huv (F (Fin.last m)) (hF (Fin.last m))

@[simp] theorem descChain_zero (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    (p : Fin 1 → X) (F : (k : Fin 0) → Path (p k.castSucc) (p k.succ))
    (hF : ∀ k, range (F k) ⊆ U ∨ range (F k) ⊆ V) :
    descChain U V hUV u v huv p F hF = 𝟙 (descObj U V hUV u v (p 0)) := rfl

theorem descChain_succ (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {m : ℕ} (p : Fin (m + 2) → X) (F : (k : Fin (m + 1)) → Path (p k.castSucc) (p k.succ))
    (hF : ∀ k, range (F k) ⊆ U ∨ range (F k) ⊆ V) :
    descChain U V hUV u v huv p F hF
      = descChain U V hUV u v huv (p ∘ Fin.castSucc) (fun k => F k.castSucc)
          (fun k => hF k.castSucc) ≫
        descPiece U V hUV u v huv (F (Fin.last m)) (hF (Fin.last m)) := rfl

/-- **Congruence of `descLocU` along an equality of paths.**  The trailing membership/range
arguments are propositions, so proof irrelevance makes the two sides agree once the paths do. -/
theorem descLocU_path_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    {a b : X} {p q : Path a b} (hpq : p = q)
    (hp : range p ⊆ U) (ha : a ∈ U) (hb : b ∈ U) :
    descLocU U V hUV u v p hp ha hb = descLocU U V hUV u v q (hpq ▸ hp) ha hb := by
  subst hpq; rfl

/-- **Congruence of `descLocV` along an equality of paths.**  As `descLocU_path_congr`. -/
theorem descLocV_path_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} {p q : Path a b} (hpq : p = q)
    (hp : range p ⊆ V) (ha : a ∈ V) (hb : b ∈ V) :
    descLocV U V hUV u v huv p hp ha hb = descLocV U V hUV u v huv q (hpq ▸ hp) ha hb := by
  subst hpq; rfl

/-- **`I`-indexed descended chain.**  The `descChain` over the subpaths cut out by a partition
`t : Fin (n+1) → I` of the parameter interval, packaged so that it is indexed by the partition `t`
itself (a *non-dependent* `Fin`-tuple).  This makes the reindexing lemmas — congruence along an
equality of partitions, back-insertion (`snoc`) — clean, avoiding dependent rewrites of the
underlying cell family. -/
noncomputable def descChainI (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 1) → I)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descObj U V hUV u v (γ (t 0)) ⟶ descObj U V hUV u v (γ (t (Fin.last n))) :=
  descChain U V hUV u v huv (γ ∘ t)
    (fun k : Fin n => γ.subpath (t k.castSucc) (t k.succ)) hcov

/-- A one-cell `descChainI` is the identity. -/
theorem descChainI_zero (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (t : Fin 1 → I)
    (hcov : ∀ k : Fin 0, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChainI U V hUV u v huv γ t hcov = 𝟙 (descObj U V hUV u v (γ (t 0))) := rfl

/-- **Congruence of `descChainI` along an equality of partitions.**  Two equal partitions give the
same chain, up to the endpoint recasts forced by the (propositional) equality of endpoints. -/
theorem descChainI_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n : ℕ} {t t' : Fin (n + 1) → I} (ht : t = t')
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
    (hcov' : ∀ k : Fin n, range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ U ∨
                 range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ V) :
    descChainI U V hUV u v huv γ t hcov
      = eqToHom (congrArg (fun r : Fin (n + 1) → I => descObj U V hUV u v (γ (r 0))) ht)
        ≫ descChainI U V hUV u v huv γ t' hcov'
        ≫ eqToHom (congrArg (fun r : Fin (n + 1) → I =>
            descObj U V hUV u v (γ (r (Fin.last n)))) ht.symm) := by
  subst ht
  simp

/-- **Back-peeling a `descChainI`.**  A partition with at least two cells splits off its last cell:
the chain equals the chain of the first `n` cells composed with the `descPiece` of the last cell.
Definitional (`descChain`'s recursion peels from the back). -/
theorem descChainI_succ (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 2) → I)
    (hcov : ∀ k : Fin (n + 1), range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChainI U V hUV u v huv γ t hcov
      = descChainI U V hUV u v huv γ (t ∘ Fin.castSucc) (fun k => hcov k.castSucc)
        ≫ descPiece U V hUV u v huv
            (γ.subpath (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1)))) (hcov (Fin.last n)) :=
  rfl

/-- The local descended morphism of a constant path is the identity — `descPiece` form. -/
theorem descPiece_refl (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    (x : X) (hcov : range (Path.refl x) ⊆ U ∨ range (Path.refl x) ⊆ V) :
    descPiece U V hUV u v huv (Path.refl x) hcov = 𝟙 (descObj U V hUV u v x) := by
  by_cases hU : range (Path.refl x) ⊆ U
  · rw [descPiece_eq_U U V hUV u v huv (Path.refl x) hcov hU]
    exact descLocU_refl U V hUV u v x (hU ⟨0, (Path.refl x).source⟩) hU
  · have hV : range (Path.refl x) ⊆ V := hcov.resolve_left hU
    rw [descPiece_eq_V U V hUV u v huv (Path.refl x) hcov hV]
    exact descLocV_refl U V hUV u v huv x (hV ⟨0, (Path.refl x).source⟩) hV

/-- **Congruence of `descPiece` along an equality of paths.** -/
theorem descPiece_path_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} {p q : Path a b} (hpq : p = q)
    (hcov : range p ⊆ U ∨ range p ⊆ V) :
    descPiece U V hUV u v huv p hcov = descPiece U V hUV u v huv q (hpq ▸ hcov) := by
  subst hpq; rfl

/-- **A subpath with (propositionally) equal endpoints has `descPiece` an identity recast.** -/
theorem descPiece_subpath_const (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (c c' : I) (hcc : c = c')
    (hcov : range (γ.subpath c c') ⊆ U ∨ range (γ.subpath c c') ⊆ V) :
    descPiece U V hUV u v huv (γ.subpath c c') hcov
      = eqToHom (congrArg (descObj U V hUV u v) (congrArg γ hcc)) := by
  subst hcc
  rw [descPiece_path_congr U V hUV u v huv (Path.subpath_self γ c) hcov,
    descPiece_refl U V hUV u v huv (γ c)]
  simp

/-- **Endpoint congruence of `descPiece` for a subpath.**  Moving the subpath endpoints along
propositional equalities `x₀ = x₀'`, `x₁ = x₁'` changes `descPiece` only by the forced `eqToHom`
endpoint recasts (the endpoint *types* `descObj (γ x₀)`, `descObj (γ x₁)` themselves move). -/
theorem descPiece_subpath_endpoint_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ x₀' x₁' : I) (h0 : x₀ = x₀') (h1 : x₁ = x₁')
    (hcov : range (γ.subpath x₀ x₁) ⊆ U ∨ range (γ.subpath x₀ x₁) ⊆ V)
    (hcov' : range (γ.subpath x₀' x₁') ⊆ U ∨ range (γ.subpath x₀' x₁') ⊆ V) :
    descPiece U V hUV u v huv (γ.subpath x₀ x₁) hcov
      = eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) h0)
        ≫ descPiece U V hUV u v huv (γ.subpath x₀' x₁') hcov'
        ≫ eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) h1.symm) := by
  subst h0; subst h1; simp

/-- Range monotonicity of subpaths: a subpath over a smaller parameter interval has smaller range. -/
theorem range_subpath_mono {a b : X} (γ : Path a b) {x₀ x₁ y₀ y₁ : I}
    (h : Set.uIcc x₀ x₁ ⊆ Set.uIcc y₀ y₁) :
    range (γ.subpath x₀ x₁) ⊆ range (γ.subpath y₀ y₁) := by
  rw [range_subpath_uIcc, range_subpath_uIcc]
  exact Set.image_mono h

/-- **Span additivity (`descPiece` form).**  A spanning subpath `γ.subpath x₀ x₂` (lying in a single
cover element) splits at any interior ambient point `x₁` (`x₀ ≤ x₁ ≤ x₂`), whichever cover element it
lands in. -/
theorem descPiece_span_additive (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ x₂ : I) (h01 : x₀ ≤ x₁) (h12 : x₁ ≤ x₂)
    (hcov02 : range (γ.subpath x₀ x₂) ⊆ U ∨ range (γ.subpath x₀ x₂) ⊆ V)
    (hcov01 : range (γ.subpath x₀ x₁) ⊆ U ∨ range (γ.subpath x₀ x₁) ⊆ V)
    (hcov12 : range (γ.subpath x₁ x₂) ⊆ U ∨ range (γ.subpath x₁ x₂) ⊆ V) :
    descPiece U V hUV u v huv (γ.subpath x₀ x₂) hcov02
      = descPiece U V hUV u v huv (γ.subpath x₀ x₁) hcov01
        ≫ descPiece U V hUV u v huv (γ.subpath x₁ x₂) hcov12 := by
  have hx1mem : x₁ ∈ Set.uIcc x₀ x₂ := Set.mem_uIcc.2 (Or.inl ⟨h01, h12⟩)
  have huIcc01 : Set.uIcc x₀ x₁ ⊆ Set.uIcc x₀ x₂ :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc hx1mem
  have huIcc12 : Set.uIcc x₁ x₂ ⊆ Set.uIcc x₀ x₂ :=
    Set.uIcc_subset_uIcc hx1mem Set.right_mem_uIcc
  by_cases hU : range (γ.subpath x₀ x₂) ⊆ U
  · have hU01 : range (γ.subpath x₀ x₁) ⊆ U := (range_subpath_mono γ huIcc01).trans hU
    have hU12 : range (γ.subpath x₁ x₂) ⊆ U := (range_subpath_mono γ huIcc12).trans hU
    rw [descPiece_eq_U U V hUV u v huv (γ.subpath x₀ x₂) hcov02 hU,
        descPiece_eq_U U V hUV u v huv (γ.subpath x₀ x₁) hcov01 hU01,
        descPiece_eq_U U V hUV u v huv (γ.subpath x₁ x₂) hcov12 hU12]
    exact descLocU_span_additive U V hUV u v γ x₀ x₁ x₂ h01 h12 _ _ _ _ _ _
  · have hV02 : range (γ.subpath x₀ x₂) ⊆ V := hcov02.resolve_left hU
    have hV01 : range (γ.subpath x₀ x₁) ⊆ V := (range_subpath_mono γ huIcc01).trans hV02
    have hV12 : range (γ.subpath x₁ x₂) ⊆ V := (range_subpath_mono γ huIcc12).trans hV02
    rw [descPiece_eq_V U V hUV u v huv (γ.subpath x₀ x₂) hcov02 hV02,
        descPiece_eq_V U V hUV u v huv (γ.subpath x₀ x₁) hcov01 hV01,
        descPiece_eq_V U V hUV u v huv (γ.subpath x₁ x₂) hcov12 hV12]
    exact descLocV_span_additive U V hUV u v huv γ x₀ x₁ x₂ h01 h12 _ _ _ _ _ _

/-- **Back-insertion (`snoc`) of a partition point.**  Appending a final partition point `y` to a
partition `t` appends one `descPiece` for the new last cell.  The core morphism is definitional
(`Fin.snoc t y ∘ Fin.castSucc` reduces to `t`); the endpoint recasts bridge `Fin.snoc t y` at `0`
and `Fin.last` to `t 0` and `y`. -/
theorem descChainI_snoc (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 1) → I) (y : I)
    (hcovS : ∀ k : Fin (n + 1),
        range (γ.subpath ((Fin.snoc t y : Fin (n + 2) → I) k.castSucc)
          ((Fin.snoc t y : Fin (n + 2) → I) k.succ)) ⊆ U ∨
        range (γ.subpath ((Fin.snoc t y : Fin (n + 2) → I) k.castSucc)
          ((Fin.snoc t y : Fin (n + 2) → I) k.succ)) ⊆ V)
    (hcovt : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
    (hcovlast : range (γ.subpath (t (Fin.last n)) y) ⊆ U ∨
                range (γ.subpath (t (Fin.last n)) y) ⊆ V) :
    descChainI U V hUV u v huv γ (Fin.snoc t y) hcovS
      = eqToHom (congrArg (fun z => descObj U V hUV u v (γ z))
            (show (Fin.snoc t y : Fin (n + 2) → I) 0 = t 0 by
              rw [← Fin.castSucc_zero, Fin.snoc_castSucc]))
        ≫ descChainI U V hUV u v huv γ t hcovt
        ≫ descPiece U V hUV u v huv (γ.subpath (t (Fin.last n)) y) hcovlast
        ≫ eqToHom (congrArg (fun z => descObj U V hUV u v (γ z))
            (show y = (Fin.snoc t y : Fin (n + 2) → I) (Fin.last (n + 1)) by
              rw [Fin.snoc_last])) := by
  have hcs : (Fin.snoc t y : Fin (n + 2) → I) ∘ Fin.castSucc = t := Fin.snoc_comp_castSucc
  have he0 : (Fin.snoc t y : Fin (n + 2) → I) (Fin.castSucc (Fin.last n)) = t (Fin.last n) := by
    rw [Fin.snoc_castSucc]
  have he1 : (Fin.snoc t y : Fin (n + 2) → I) (Fin.last (n + 1)) = y := by rw [Fin.snoc_last]
  rw [descChainI_succ U V hUV u v huv γ (Fin.snoc t y) hcovS,
      descPiece_subpath_endpoint_congr U V hUV u v huv γ
        ((Fin.snoc t y : Fin (n + 2) → I) (Fin.castSucc (Fin.last n)))
        ((Fin.snoc t y : Fin (n + 2) → I) (Fin.last (n + 1)))
        (t (Fin.last n)) y he0 he1 (hcovS (Fin.last n)) hcovlast,
      descChainI_congr U V hUV u v huv γ hcs (fun k => hcovS k.castSucc) hcovt]
  simp

/-- **A constant partition gives an identity chain.**  If every partition point coincides (`s i = s
0`), then every cell is a constant subpath, so the whole `descChainI` collapses to the `eqToHom`
endpoint recast. -/
theorem descChainI_const (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) :
    ∀ {m : ℕ} (s : Fin (m + 1) → I) (hconst0 : ∀ i, s i = s 0)
      (hcov : ∀ k : Fin m, range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ U ∨
                 range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ V),
      descChainI U V hUV u v huv γ s hcov
        = eqToHom (congrArg (fun z => descObj U V hUV u v (γ z))
            (show s 0 = s (Fin.last m) from (hconst0 (Fin.last m)).symm)) := by
  intro m
  induction m with
  | zero =>
    intro s hconst hcov
    rw [descChainI_zero]
    simp
  | succ m ih =>
    intro s hconst hcov
    have hconst' : ∀ i, (s ∘ Fin.castSucc) i = (s ∘ Fin.castSucc) 0 := by
      intro i
      simp only [Function.comp_apply]
      rw [hconst (Fin.castSucc i), hconst (Fin.castSucc 0)]
    rw [descChainI_succ U V hUV u v huv γ s hcov,
        ih (s ∘ Fin.castSucc) hconst' (fun k => hcov k.castSucc),
        descPiece_subpath_const U V hUV u v huv γ (s (Fin.castSucc (Fin.last m)))
          (s (Fin.last (m + 1)))
          (show s (Fin.castSucc (Fin.last m)) = s (Fin.last (m + 1)) by
            rw [hconst (Fin.castSucc (Fin.last m)), hconst (Fin.last (m + 1))])
          (hcov (Fin.last m))]
    simp

/-- **Descended chain over a sub-interval, with a fixed source/target type.**  A partition `t` of a
sub-interval `[x₀, x₁]` (with `t 0 = x₀`, `t (last) = x₁`) yields a morphism
`descObj (γ x₀) ⟶ descObj (γ x₁)`, with the endpoint identifications folded in as `eqToHom`.  The
fixed source/target — depending only on `x₀`, `x₁`, not on `t` — is what makes subdivision
independence a plain equality of morphisms (`descSpan_indep`). -/
noncomputable def descSpan (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ : I) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = x₀) (h1 : t (Fin.last n) = x₁)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descObj U V hUV u v (γ x₀) ⟶ descObj U V hUV u v (γ x₁) :=
  eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) h0.symm)
    ≫ descChainI U V hUV u v huv γ t hcov
    ≫ eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) h1)

/-- **Back-peeling `descSpan`.**  A span with at least one cell splits off its last cell as a
`descPiece`, the head being the span over the first `n` cells. -/
theorem descSpan_succ (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ : I) {n : ℕ} (t : Fin (n + 2) → I)
    (h0 : t 0 = x₀) (h1 : t (Fin.last (n + 1)) = x₁)
    (hcov : ∀ k : Fin (n + 1), range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descSpan U V hUV u v huv γ x₀ x₁ t h0 h1 hcov
      = descSpan U V hUV u v huv γ x₀ (t (Fin.castSucc (Fin.last n))) (t ∘ Fin.castSucc)
          (by simpa [Fin.castSucc_zero] using h0) rfl (fun k => hcov k.castSucc)
        ≫ descPiece U V hUV u v huv
            (γ.subpath (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1)))) (hcov (Fin.last n))
        ≫ eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) h1) := by
  simp only [descSpan]
  rw [descChainI_succ U V hUV u v huv γ t hcov]
  simp

/-- **`snoc` form of `descSpan`.**  Appending a final partition point `y` (the new right endpoint)
appends one `descPiece` for the last cell; the head is the span over the original partition. -/
theorem descSpan_snoc (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ : I) {n : ℕ} (r : Fin (n + 1) → I) (y : I) (h0 : r 0 = x₀)
    (hcovS : ∀ k : Fin (n + 1),
        range (γ.subpath ((Fin.snoc r y : Fin (n + 2) → I) k.castSucc)
          ((Fin.snoc r y : Fin (n + 2) → I) k.succ)) ⊆ U ∨
        range (γ.subpath ((Fin.snoc r y : Fin (n + 2) → I) k.castSucc)
          ((Fin.snoc r y : Fin (n + 2) → I) k.succ)) ⊆ V)
    (hcovr : ∀ k : Fin n, range (γ.subpath (r k.castSucc) (r k.succ)) ⊆ U ∨
                 range (γ.subpath (r k.castSucc) (r k.succ)) ⊆ V)
    (hcovlast : range (γ.subpath (r (Fin.last n)) y) ⊆ U ∨
                range (γ.subpath (r (Fin.last n)) y) ⊆ V) :
    descSpan U V hUV u v huv γ x₀ y (Fin.snoc r y)
        (by rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h0) (by rw [Fin.snoc_last]) hcovS
      = descSpan U V hUV u v huv γ x₀ (r (Fin.last n)) r h0 rfl hcovr
        ≫ descPiece U V hUV u v huv (γ.subpath (r (Fin.last n)) y) hcovlast := by
  simp only [descSpan]
  rw [descChainI_snoc U V hUV u v huv γ r y hcovS hcovr hcovlast]
  simp

/-- **Normalised back-peel of `descSpan`.**  A span with at least one cell equals the span over its
first `n` cells followed by a single `descPiece` over the final cell `[a_t, x₁]`, where the right
endpoint is the *actual* endpoint `x₁` (not the raw partition value).  This normalised form is the
workhorse for the subdivision-independence induction. -/
theorem descSpan_peel_last (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ : I) {n : ℕ} (t : Fin (n + 2) → I)
    (h0 : t 0 = x₀) (h1 : t (Fin.last (n + 1)) = x₁)
    (hcov : ∀ k : Fin (n + 1), range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
    (hlast : range (γ.subpath (t (Fin.castSucc (Fin.last n))) x₁) ⊆ U ∨
             range (γ.subpath (t (Fin.castSucc (Fin.last n))) x₁) ⊆ V) :
    descSpan U V hUV u v huv γ x₀ x₁ t h0 h1 hcov
      = descSpan U V hUV u v huv γ x₀ (t (Fin.castSucc (Fin.last n))) (t ∘ Fin.castSucc)
          (by simpa [Fin.castSucc_zero] using h0) rfl (fun k => hcov k.castSucc)
        ≫ descPiece U V hUV u v huv (γ.subpath (t (Fin.castSucc (Fin.last n))) x₁) hlast := by
  rw [descSpan_succ U V hUV u v huv γ x₀ x₁ t h0 h1 hcov,
      descPiece_subpath_endpoint_congr U V hUV u v huv γ
        (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1)))
        (t (Fin.castSucc (Fin.last n))) x₁ rfl h1 (hcov (Fin.last n)) hlast]
  simp

/-- **Recasting the target endpoint of a `descSpan`.**  Post-composing a span with the `eqToHom`
that moves its right endpoint along `x₁ = x₁'` is the same span with the moved endpoint. -/
theorem descSpan_recast_target (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ x₁' : I) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = x₀) (h1 : t (Fin.last n) = x₁)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
    (he : x₁ = x₁') :
    descSpan U V hUV u v huv γ x₀ x₁ t h0 h1 hcov
        ≫ eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) he)
      = descSpan U V hUV u v huv γ x₀ x₁' t h0 (h1.trans he) hcov := by
  subst he
  simp [descSpan]

/-- **Monotone `snoc`.**  Appending a value `y ≥ r (last)` to a monotone family keeps it monotone. -/
theorem monotone_snoc {n : ℕ} {r : Fin (n + 1) → I} {y : I}
    (hr : Monotone r) (hy : r (Fin.last n) ≤ y) : Monotone (Fin.snoc r y : Fin (n + 2) → I) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hr (Fin.castSucc_le_castSucc_iff.mp hij)
    · rw [Fin.snoc_castSucc, Fin.snoc_last]
      exact (hr (Fin.le_last i')).trans hy
  · have hj : j = Fin.last (n + 1) := le_antisymm (Fin.le_last j) hij
    exact le_of_eq (congrArg (Fin.snoc r y) hj.symm)

/-- **A constant span is the identity.**  A monotone partition of a degenerate interval `[x₀, x₀]`
gives a span equal to the identity morphism (every cell is a constant subpath). -/
theorem descSpan_eq_of_const (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ : I) {m : ℕ} (s : Fin (m + 1) → I)
    (hmono : Monotone s) (h0 : s 0 = x₀) (h1 : s (Fin.last m) = x₀)
    (hcov : ∀ k : Fin m, range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ U ∨
                 range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ V) :
    descSpan U V hUV u v huv γ x₀ x₀ s h0 h1 hcov = 𝟙 (descObj U V hUV u v (γ x₀)) := by
  have hconst : ∀ i, s i = s 0 := by
    intro i
    have hs0 : s 0 = s (Fin.last m) := by rw [h0, h1]
    refine le_antisymm ?_ (hmono (Fin.zero_le i))
    rw [hs0]; exact hmono (Fin.le_last i)
  simp only [descSpan]
  rw [descChainI_const U V hUV u v huv γ s hconst hcov]
  simp

/-- **Subdivision independence of `descSpan`.**  Two monotone partitions of the same interval
`[x₀, x₁]` produce the same span.  Proved by strong induction on the total number of cells `n + m`,
by a two-pointer comparison of the two second-to-last partition points: peel both last cells when
they agree, otherwise split the longer one's last cell at the shorter one's second-to-last point and
refold via `snoc`. -/
theorem descSpan_indep (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) :
    ∀ (N : ℕ) (x₀ x₁ : I) {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I)
      (_htmono : Monotone t) (_hsmono : Monotone s)
      (h0t : t 0 = x₀) (h1t : t (Fin.last n) = x₁)
      (h0s : s 0 = x₀) (h1s : s (Fin.last m) = x₁)
      (hcovt : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
      (hcovs : ∀ k : Fin m, range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ U ∨
                 range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ V),
      n + m ≤ N →
      descSpan U V hUV u v huv γ x₀ x₁ t h0t h1t hcovt
        = descSpan U V hUV u v huv γ x₀ x₁ s h0s h1s hcovs := by
  intro N
  induction N with
  | zero =>
    intro x₀ x₁ n m t s htmono hsmono h0t h1t h0s h1s hcovt hcovs hNle
    obtain ⟨hn, hm⟩ := Nat.add_eq_zero_iff.mp (Nat.le_zero.mp hNle)
    subst hn; subst hm
    have hx : x₀ = x₁ := by rw [← h0t, ← h1t]; congr 1
    subst hx
    rw [descSpan_eq_of_const U V hUV u v huv γ x₀ t htmono h0t h1t hcovt,
        descSpan_eq_of_const U V hUV u v huv γ x₀ s hsmono h0s h1s hcovs]
  | succ N ih =>
    intro x₀ x₁ n m t s htmono hsmono h0t h1t h0s h1s hcovt hcovs hNle
    rcases n with _ | n'
    · have hx : x₀ = x₁ := by rw [← h0t, ← h1t]; congr 1
      subst hx
      rw [descSpan_eq_of_const U V hUV u v huv γ x₀ t htmono h0t h1t hcovt,
          descSpan_eq_of_const U V hUV u v huv γ x₀ s hsmono h0s h1s hcovs]
    · rcases m with _ | m'
      · have hx : x₀ = x₁ := by rw [← h0s, ← h1s]; congr 1
        subst hx
        rw [descSpan_eq_of_const U V hUV u v huv γ x₀ t htmono h0t h1t hcovt,
            descSpan_eq_of_const U V hUV u v huv γ x₀ s hsmono h0s h1s hcovs]
      · -- Main case: both partitions have ≥ 1 cell.
        have htmono' : Monotone (t ∘ Fin.castSucc) :=
          fun i j hij => htmono (Fin.castSucc_le_castSucc_iff.mpr hij)
        have hsmono' : Monotone (s ∘ Fin.castSucc) :=
          fun i j hij => hsmono (Fin.castSucc_le_castSucc_iff.mpr hij)
        have h0t' : (t ∘ Fin.castSucc) 0 = x₀ := by simpa [Fin.castSucc_zero] using h0t
        have h0s' : (s ∘ Fin.castSucc) 0 = x₀ := by simpa [Fin.castSucc_zero] using h0s
        have ha_t_le : t (Fin.castSucc (Fin.last n')) ≤ x₁ := by
          rw [← h1t]; exact htmono (Fin.le_last _)
        have ha_s_le : s (Fin.castSucc (Fin.last m')) ≤ x₁ := by
          rw [← h1s]; exact hsmono (Fin.le_last _)
        have hlast_t : range (γ.subpath (t (Fin.castSucc (Fin.last n'))) x₁) ⊆ U ∨
                       range (γ.subpath (t (Fin.castSucc (Fin.last n'))) x₁) ⊆ V := by
          have h := hcovt (Fin.last n'); rwa [Fin.succ_last, h1t] at h
        have hlast_s : range (γ.subpath (s (Fin.castSucc (Fin.last m'))) x₁) ⊆ U ∨
                       range (γ.subpath (s (Fin.castSucc (Fin.last m'))) x₁) ⊆ V := by
          have h := hcovs (Fin.last m'); rwa [Fin.succ_last, h1s] at h
        rcases lt_trichotomy (t (Fin.castSucc (Fin.last n')))
            (s (Fin.castSucc (Fin.last m'))) with hlt | heq | hgt
        · -- a_t < a_s : split t's last cell at a_s.
          have hcov_ats : range (γ.subpath (t (Fin.castSucc (Fin.last n')))
                (s (Fin.castSucc (Fin.last m')))) ⊆ U ∨
              range (γ.subpath (t (Fin.castSucc (Fin.last n')))
                (s (Fin.castSucc (Fin.last m')))) ⊆ V := by
            have hsub : Set.uIcc (t (Fin.castSucc (Fin.last n'))) (s (Fin.castSucc (Fin.last m')))
                ⊆ Set.uIcc (t (Fin.castSucc (Fin.last n'))) x₁ :=
              Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hlt.le, ha_s_le⟩))
            exact hlast_t.imp (fun h => (range_subpath_mono γ hsub).trans h)
              (fun h => (range_subpath_mono γ hsub).trans h)
          have h0snoc : (Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m'))) :
              Fin (n' + 2) → I) 0 = x₀ := by
            rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h0t'
          have h1snoc : (Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m'))) :
              Fin (n' + 2) → I) (Fin.last (n' + 1)) = s (Fin.castSucc (Fin.last m')) := by
            rw [Fin.snoc_last]
          have hmono_snoc : Monotone (Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m'))) :
              Fin (n' + 2) → I) := monotone_snoc htmono' hlt.le
          have hcovS : ∀ k : Fin (n' + 1),
              range (γ.subpath ((Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m'))) :
                  Fin (n' + 2) → I) k.castSucc)
                ((Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m'))) :
                  Fin (n' + 2) → I) k.succ)) ⊆ U ∨
              range (γ.subpath ((Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m'))) :
                  Fin (n' + 2) → I) k.castSucc)
                ((Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m'))) :
                  Fin (n' + 2) → I) k.succ)) ⊆ V := by
            intro k
            refine Fin.lastCases ?_ ?_ k
            · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]; exact hcov_ats
            · intro j
              rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
              exact hcovt j.castSucc
          have hkey : descSpan U V hUV u v huv γ x₀ (t (Fin.castSucc (Fin.last n')))
                (t ∘ Fin.castSucc) (by simpa [Fin.castSucc_zero] using h0t) rfl
                (fun k => hcovt k.castSucc)
              ≫ descPiece U V hUV u v huv (γ.subpath (t (Fin.castSucc (Fin.last n')))
                  (s (Fin.castSucc (Fin.last m')))) hcov_ats
              = descSpan U V hUV u v huv γ x₀ (s (Fin.castSucc (Fin.last m')))
                  (s ∘ Fin.castSucc) (by simpa [Fin.castSucc_zero] using h0s) rfl
                  (fun k => hcovs k.castSucc) :=
            (descSpan_snoc U V hUV u v huv γ x₀ (t ∘ Fin.castSucc)
                (s (Fin.castSucc (Fin.last m'))) h0t' hcovS (fun k => hcovt k.castSucc)
                hcov_ats).symm.trans
              (ih x₀ (s (Fin.castSucc (Fin.last m')))
                (Fin.snoc (t ∘ Fin.castSucc) (s (Fin.castSucc (Fin.last m')))) (s ∘ Fin.castSucc)
                hmono_snoc hsmono' h0snoc h1snoc h0s' rfl hcovS (fun k => hcovs k.castSucc)
                (by omega))
          rw [descSpan_peel_last U V hUV u v huv γ x₀ x₁ t h0t h1t hcovt hlast_t,
              descSpan_peel_last U V hUV u v huv γ x₀ x₁ s h0s h1s hcovs hlast_s,
              descPiece_span_additive U V hUV u v huv γ (t (Fin.castSucc (Fin.last n')))
                (s (Fin.castSucc (Fin.last m'))) x₁ hlt.le ha_s_le hlast_t hcov_ats hlast_s,
              ← Category.assoc, hkey]
        · -- a_t = a_s : peel both, align endpoints.
          rw [descSpan_peel_last U V hUV u v huv γ x₀ x₁ t h0t h1t hcovt hlast_t,
              descSpan_peel_last U V hUV u v huv γ x₀ x₁ s h0s h1s hcovs hlast_s]
          have hh : descSpan U V hUV u v huv γ x₀ (t (Fin.castSucc (Fin.last n')))
                (t ∘ Fin.castSucc) (by simpa [Fin.castSucc_zero] using h0t) rfl
                (fun k => hcovt k.castSucc)
              = descSpan U V hUV u v huv γ x₀ (s (Fin.castSucc (Fin.last m')))
                  (s ∘ Fin.castSucc) (by simpa [Fin.castSucc_zero] using h0s) rfl
                  (fun k => hcovs k.castSucc)
                ≫ eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) heq.symm) := by
            rw [descSpan_recast_target U V hUV u v huv γ x₀ (s (Fin.castSucc (Fin.last m')))
                  (t (Fin.castSucc (Fin.last n'))) (s ∘ Fin.castSucc) h0s' rfl
                  (fun k => hcovs k.castSucc) heq.symm]
            exact ih x₀ (t (Fin.castSucc (Fin.last n'))) (t ∘ Fin.castSucc) (s ∘ Fin.castSucc)
              htmono' hsmono' h0t' rfl h0s' heq.symm (fun k => hcovt k.castSucc)
              (fun k => hcovs k.castSucc) (by omega)
          rw [hh, Category.assoc]
          congr 1
          rw [descPiece_subpath_endpoint_congr U V hUV u v huv γ (s (Fin.castSucc (Fin.last m')))
                x₁ (t (Fin.castSucc (Fin.last n'))) x₁ heq.symm rfl hlast_s hlast_t]
          simp
        · -- a_s < a_t : split s's last cell at a_t.
          have hcov_sat : range (γ.subpath (s (Fin.castSucc (Fin.last m')))
                (t (Fin.castSucc (Fin.last n')))) ⊆ U ∨
              range (γ.subpath (s (Fin.castSucc (Fin.last m')))
                (t (Fin.castSucc (Fin.last n')))) ⊆ V := by
            have hsub : Set.uIcc (s (Fin.castSucc (Fin.last m'))) (t (Fin.castSucc (Fin.last n')))
                ⊆ Set.uIcc (s (Fin.castSucc (Fin.last m'))) x₁ :=
              Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hgt.le, ha_t_le⟩))
            exact hlast_s.imp (fun h => (range_subpath_mono γ hsub).trans h)
              (fun h => (range_subpath_mono γ hsub).trans h)
          have h0snoc' : (Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n'))) :
              Fin (m' + 2) → I) 0 = x₀ := by
            rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h0s'
          have h1snoc' : (Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n'))) :
              Fin (m' + 2) → I) (Fin.last (m' + 1)) = t (Fin.castSucc (Fin.last n')) := by
            rw [Fin.snoc_last]
          have hmono_snoc' : Monotone (Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n'))) :
              Fin (m' + 2) → I) := monotone_snoc hsmono' hgt.le
          have hcovS' : ∀ k : Fin (m' + 1),
              range (γ.subpath ((Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n'))) :
                  Fin (m' + 2) → I) k.castSucc)
                ((Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n'))) :
                  Fin (m' + 2) → I) k.succ)) ⊆ U ∨
              range (γ.subpath ((Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n'))) :
                  Fin (m' + 2) → I) k.castSucc)
                ((Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n'))) :
                  Fin (m' + 2) → I) k.succ)) ⊆ V := by
            intro k
            refine Fin.lastCases ?_ ?_ k
            · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]; exact hcov_sat
            · intro j
              rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
              exact hcovs j.castSucc
          have hkey : descSpan U V hUV u v huv γ x₀ (s (Fin.castSucc (Fin.last m')))
                (s ∘ Fin.castSucc) (by simpa [Fin.castSucc_zero] using h0s) rfl
                (fun k => hcovs k.castSucc)
              ≫ descPiece U V hUV u v huv (γ.subpath (s (Fin.castSucc (Fin.last m')))
                  (t (Fin.castSucc (Fin.last n')))) hcov_sat
              = descSpan U V hUV u v huv γ x₀ (t (Fin.castSucc (Fin.last n')))
                  (t ∘ Fin.castSucc) (by simpa [Fin.castSucc_zero] using h0t) rfl
                  (fun k => hcovt k.castSucc) :=
            (descSpan_snoc U V hUV u v huv γ x₀ (s ∘ Fin.castSucc)
                (t (Fin.castSucc (Fin.last n'))) h0s' hcovS' (fun k => hcovs k.castSucc)
                hcov_sat).symm.trans
              (ih x₀ (t (Fin.castSucc (Fin.last n')))
                (Fin.snoc (s ∘ Fin.castSucc) (t (Fin.castSucc (Fin.last n')))) (t ∘ Fin.castSucc)
                hmono_snoc' htmono' h0snoc' h1snoc' h0t' rfl hcovS' (fun k => hcovt k.castSucc)
                (by omega))
          rw [descSpan_peel_last U V hUV u v huv γ x₀ x₁ t h0t h1t hcovt hlast_t,
              descSpan_peel_last U V hUV u v huv γ x₀ x₁ s h0s h1s hcovs hlast_s,
              descPiece_span_additive U V hUV u v huv γ (s (Fin.castSucc (Fin.last m')))
                (t (Fin.castSucc (Fin.last n'))) x₁ hgt.le ha_t_le hlast_s hcov_sat hlast_t,
              ← Category.assoc, hkey]

/-- **Telescoping a chain that lies entirely in `U`.**  When every piece of a finite concatenation
lands in `U`, its `descChain` equals the single `U`-local descended morphism of the whole
concatenation.  Proved by induction, using `descPiece_eq_U` on the last piece and the same-side
concatenation law `descLocU_trans`. -/
theorem descChain_eq_descLocU_concat (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {n : ℕ} (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (hp0 : p 0 ∈ U) (hplast : p (Fin.last n) ∈ U) (hFU : ∀ k, range (F k) ⊆ U)
    (hcov : ∀ k, range (F k) ⊆ U ∨ range (F k) ⊆ V) :
    descChain U V hUV u v huv p F hcov
      = descLocU U V hUV u v (Path.concat p F) (range_concat_subset U p F hp0 hFU) hp0 hplast := by
  induction n with
  | zero =>
    rw [descChain_zero, descLocU_path_congr U V hUV u v (Path.concat_zero p F)
      (range_concat_subset U p F hp0 hFU) hp0 hplast]
    exact (descLocU_refl U V hUV u v (p 0) hp0 _).symm
  | succ n ih =>
    have hmid : (p ∘ Fin.castSucc) (Fin.last n) ∈ U :=
      hFU (Fin.last n) ⟨0, (F (Fin.last n)).source⟩
    rw [descChain_succ,
      ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp0 hmid
        (fun k => hFU k.castSucc) (fun k => hcov k.castSucc),
      descPiece_eq_U U V hUV u v huv (F (Fin.last n)) (hcov (Fin.last n)) (hFU (Fin.last n))]
    symm
    calc descLocU U V hUV u v (Path.concat p F) (range_concat_subset U p F hp0 hFU) hp0 hplast
        = descLocU U V hUV u v
            ((Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)).trans (F (Fin.last n)))
            (Path.concat_succ p F ▸ range_concat_subset U p F hp0 hFU) hp0 hplast :=
          descLocU_path_congr U V hUV u v (Path.concat_succ p F)
            (range_concat_subset U p F hp0 hFU) hp0 hplast
      _ = descLocU U V hUV u v (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc))
              (range_concat_subset U (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp0
                (fun k => hFU k.castSucc)) hp0 hmid
            ≫ descLocU U V hUV u v (F (Fin.last n)) (hFU (Fin.last n))
              (hFU (Fin.last n) ⟨0, (F (Fin.last n)).source⟩)
              (hFU (Fin.last n) ⟨1, (F (Fin.last n)).target⟩) :=
          descLocU_trans U V hUV u v (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc))
            (F (Fin.last n))
            (range_concat_subset U (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp0
              (fun k => hFU k.castSucc)) (hFU (Fin.last n))
            (Path.concat_succ p F ▸ range_concat_subset U p F hp0 hFU) hp0 hmid hplast

/-- **Telescoping a chain that lies entirely in `V`.**  As `descChain_eq_descLocU_concat`. -/
theorem descChain_eq_descLocV_concat (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {n : ℕ} (p : Fin (n + 1) → X) (F : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (hp0 : p 0 ∈ V) (hplast : p (Fin.last n) ∈ V) (hFV : ∀ k, range (F k) ⊆ V)
    (hcov : ∀ k, range (F k) ⊆ U ∨ range (F k) ⊆ V) :
    descChain U V hUV u v huv p F hcov
      = descLocV U V hUV u v huv (Path.concat p F) (range_concat_subset V p F hp0 hFV) hp0 hplast := by
  induction n with
  | zero =>
    rw [descChain_zero, descLocV_path_congr U V hUV u v huv (Path.concat_zero p F)
      (range_concat_subset V p F hp0 hFV) hp0 hplast]
    exact (descLocV_refl U V hUV u v huv (p 0) hp0 _).symm
  | succ n ih =>
    have hmid : (p ∘ Fin.castSucc) (Fin.last n) ∈ V :=
      hFV (Fin.last n) ⟨0, (F (Fin.last n)).source⟩
    rw [descChain_succ,
      ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp0 hmid
        (fun k => hFV k.castSucc) (fun k => hcov k.castSucc),
      descPiece_eq_V U V hUV u v huv (F (Fin.last n)) (hcov (Fin.last n)) (hFV (Fin.last n))]
    symm
    calc descLocV U V hUV u v huv (Path.concat p F) (range_concat_subset V p F hp0 hFV) hp0 hplast
        = descLocV U V hUV u v huv
            ((Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)).trans (F (Fin.last n)))
            (Path.concat_succ p F ▸ range_concat_subset V p F hp0 hFV) hp0 hplast :=
          descLocV_path_congr U V hUV u v huv (Path.concat_succ p F)
            (range_concat_subset V p F hp0 hFV) hp0 hplast
      _ = descLocV U V hUV u v huv (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc))
              (range_concat_subset V (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp0
                (fun k => hFV k.castSucc)) hp0 hmid
            ≫ descLocV U V hUV u v huv (F (Fin.last n)) (hFV (Fin.last n))
              (hFV (Fin.last n) ⟨0, (F (Fin.last n)).source⟩)
              (hFV (Fin.last n) ⟨1, (F (Fin.last n)).target⟩) :=
          descLocV_trans U V hUV u v huv (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc))
            (F (Fin.last n))
            (range_concat_subset V (p ∘ Fin.castSucc) (fun k => F k.castSucc) hp0
              (fun k => hFV k.castSucc)) (hFV (Fin.last n))
            (Path.concat_succ p F ▸ range_concat_subset V p F hp0 hFV) hp0 hmid hplast

/-- **A chain of subpaths of a single path in `U` telescopes to the whole subpath.**  When `γ` lies
in `U`, the `descChain` over the subpaths cut out by a partition `t` equals the single `U`-local
descended morphism of `γ.subpath (t 0) (t last)` — proved by induction using subpath additivity.
This is the exact-equality reconciliation that avoids any ambient homotopy. -/
theorem descChain_subpath_eq_descLocU (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U) {n : ℕ} (t : Fin (n + 1) → I)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChain U V hUV u v huv (γ ∘ t) (fun k => γ.subpath (t k.castSucc) (t k.succ)) hcov
      = descLocU U V hUV u v (γ.subpath (t 0) (t (Fin.last n)))
          (subpath_range_subset U γ hγ (t 0) (t (Fin.last n)))
          (hγ (mem_range_self (t 0))) (hγ (mem_range_self (t (Fin.last n)))) := by
  induction n with
  | zero =>
    rw [descChain_zero]
    have heq : γ.subpath (t 0) (t (Fin.last 0)) = Path.refl (γ (t 0)) := Path.subpath_self γ (t 0)
    rw [descLocU_path_congr U V hUV u v heq (subpath_range_subset U γ hγ (t 0) (t (Fin.last 0)))
      (hγ (mem_range_self (t 0))) (hγ (mem_range_self (t (Fin.last 0))))]
    exact (descLocU_refl U V hUV u v (γ (t 0)) (hγ (mem_range_self (t 0))) _).symm
  | succ n ih =>
    rw [descChain_succ,
      descPiece_eq_U U V hUV u v huv (γ.subpath (t (Fin.last n).castSucc) (t (Fin.last n).succ))
        (hcov (Fin.last n)) (subpath_range_subset U γ hγ _ _),
      descLocU_subpath_additive U V hUV u v γ hγ (t 0) (t (Fin.last n).castSucc)
        (t (Fin.last (n + 1)))]
    congr 1
    exact ih (t ∘ Fin.castSucc) (fun k => hcov k.castSucc)

/-- **A chain of subpaths of a single path in `V` telescopes to the whole subpath.**  As
`descChain_subpath_eq_descLocU`. -/
theorem descChain_subpath_eq_descLocV (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ V) {n : ℕ} (t : Fin (n + 1) → I)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChain U V hUV u v huv (γ ∘ t) (fun k => γ.subpath (t k.castSucc) (t k.succ)) hcov
      = descLocV U V hUV u v huv (γ.subpath (t 0) (t (Fin.last n)))
          (subpath_range_subset V γ hγ (t 0) (t (Fin.last n)))
          (hγ (mem_range_self (t 0))) (hγ (mem_range_self (t (Fin.last n)))) := by
  induction n with
  | zero =>
    rw [descChain_zero]
    have heq : γ.subpath (t 0) (t (Fin.last 0)) = Path.refl (γ (t 0)) := Path.subpath_self γ (t 0)
    rw [descLocV_path_congr U V hUV u v huv heq (subpath_range_subset V γ hγ (t 0) (t (Fin.last 0)))
      (hγ (mem_range_self (t 0))) (hγ (mem_range_self (t (Fin.last 0))))]
    exact (descLocV_refl U V hUV u v huv (γ (t 0)) (hγ (mem_range_self (t 0))) _).symm
  | succ n ih =>
    rw [descChain_succ,
      descPiece_eq_V U V hUV u v huv (γ.subpath (t (Fin.last n).castSucc) (t (Fin.last n).succ))
        (hcov (Fin.last n)) (subpath_range_subset V γ hγ _ _),
      descLocV_subpath_additive U V hUV u v huv γ hγ (t 0) (t (Fin.last n).castSucc)
        (t (Fin.last (n + 1)))]
    congr 1
    exact ih (t ∘ Fin.castSucc) (fun k => hcov k.castSucc)

/-- **Descended morphism of a path from an explicit subdivision.**  For a cover-adapted partition
`t` of `[0,1]` (with `t 0 = 0`, `t last = 1`), the descended morphism `descObj a ⟶ descObj b` is
the chain of `descPiece`s of the subpaths, with the endpoint identifications `γ (t 0) = a`,
`γ (t last) = b` folded in. -/
noncomputable def descChainPath (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descObj U V hUV u v a ⟶ descObj U V hUV u v b :=
  eqToHom (congrArg (descObj U V hUV u v)
      (show a = (γ ∘ t) 0 by simp only [Function.comp_apply, h0, γ.source])) ≫
    descChain U V hUV u v huv (γ ∘ t)
      (fun k : Fin n => γ.subpath (t k.castSucc) (t k.succ)) hcov ≫
    eqToHom (congrArg (descObj U V hUV u v)
      (show (γ ∘ t) (Fin.last n) = b by simp only [Function.comp_apply, h1, γ.target]))

/-- **A cover-adapted subdivision of a path lying in `U` computes its `U`-local morphism.**  When
the whole path `γ` lies in `U`, its `descChainPath` (for any endpoint-normalized partition) equals
the single `U`-local descended morphism `descLocU γ` — the pieces telescope
(`descChain_subpath_eq_descLocU`) and the endpoint recasts cancel. -/
theorem descChainPath_eq_descLocU (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChainPath U V hUV u v huv γ t h0 h1 hcov
      = descLocU U V hUV u v γ hγ (hγ ⟨0, γ.source⟩) (hγ ⟨1, γ.target⟩) := by
  have hpt0 : γ (t 0) = a := by rw [h0]; exact γ.source
  have hpt1 : γ (t (Fin.last n)) = b := by rw [h1]; exact γ.target
  have M0 : γ (t 0) ∈ U := hγ (mem_range_self (t 0))
  have Mlast : γ (t (Fin.last n)) ∈ U := hγ (mem_range_self (t (Fin.last n)))
  have ho0 : (⟨⟨γ (t 0), M0⟩⟩ : FundamentalGroupoid U) = ⟨⟨a, hγ ⟨0, γ.source⟩⟩⟩ := by
    congr 1; exact Subtype.ext hpt0
  have ho1 : (⟨⟨γ (t (Fin.last n)), Mlast⟩⟩ : FundamentalGroupoid U) = ⟨⟨b, hγ ⟨1, γ.target⟩⟩⟩ := by
    congr 1; exact Subtype.ext hpt1
  -- Reparametrization at the level of homotopy classes in `π(U)`: the full subpath (endpoints
  -- normalized to `0`, `1`) has the same class as `γ` itself, up to the endpoint recasts.
  have hcls :
      (⟦liftPath U (γ.subpath (t 0) (t (Fin.last n)))
            (subpath_range_subset U γ hγ (t 0) (t (Fin.last n))) M0 Mlast⟧
        : (⟨⟨γ (t 0), M0⟩⟩ : FundamentalGroupoid U) ⟶ ⟨⟨γ (t (Fin.last n)), Mlast⟩⟩)
      = eqToHom ho0
          ≫ (⟦liftPath U γ hγ (hγ ⟨0, γ.source⟩) (hγ ⟨1, γ.target⟩)⟧
              : (⟨⟨a, hγ ⟨0, γ.source⟩⟩⟩ : FundamentalGroupoid U) ⟶ ⟨⟨b, hγ ⟨1, γ.target⟩⟩⟩)
          ≫ eqToHom ho1.symm := by
    refine (conj_eqToHom_iff_heq _ _ ho0 ho1).2 ?_
    apply Path.Homotopic.hpath_hext
    intro s
    apply Subtype.ext
    simp only [liftPath_apply, Path.subpath, Path.coe_mk_mk, Function.comp_apply, h0, h1]
    congr 1
    apply Subtype.ext
    simp [Path.subpathAux]
  unfold descChainPath
  rw [descChain_subpath_eq_descLocU U V hUV u v huv γ hγ t hcov]
  simp only [descLocU]
  rw [hcls, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **A cover-adapted subdivision of a path lying in `V` computes its `V`-local morphism.**  As
`descChainPath_eq_descLocU`. -/
theorem descChainPath_eq_descLocV (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ V) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChainPath U V hUV u v huv γ t h0 h1 hcov
      = descLocV U V hUV u v huv γ hγ (hγ ⟨0, γ.source⟩) (hγ ⟨1, γ.target⟩) := by
  have hpt0 : γ (t 0) = a := by rw [h0]; exact γ.source
  have hpt1 : γ (t (Fin.last n)) = b := by rw [h1]; exact γ.target
  have M0 : γ (t 0) ∈ V := hγ (mem_range_self (t 0))
  have Mlast : γ (t (Fin.last n)) ∈ V := hγ (mem_range_self (t (Fin.last n)))
  have ho0 : (⟨⟨γ (t 0), M0⟩⟩ : FundamentalGroupoid V) = ⟨⟨a, hγ ⟨0, γ.source⟩⟩⟩ := by
    congr 1; exact Subtype.ext hpt0
  have ho1 : (⟨⟨γ (t (Fin.last n)), Mlast⟩⟩ : FundamentalGroupoid V) = ⟨⟨b, hγ ⟨1, γ.target⟩⟩⟩ := by
    congr 1; exact Subtype.ext hpt1
  have hcls :
      (⟦liftPath V (γ.subpath (t 0) (t (Fin.last n)))
            (subpath_range_subset V γ hγ (t 0) (t (Fin.last n))) M0 Mlast⟧
        : (⟨⟨γ (t 0), M0⟩⟩ : FundamentalGroupoid V) ⟶ ⟨⟨γ (t (Fin.last n)), Mlast⟩⟩)
      = eqToHom ho0
          ≫ (⟦liftPath V γ hγ (hγ ⟨0, γ.source⟩) (hγ ⟨1, γ.target⟩)⟧
              : (⟨⟨a, hγ ⟨0, γ.source⟩⟩⟩ : FundamentalGroupoid V) ⟶ ⟨⟨b, hγ ⟨1, γ.target⟩⟩⟩)
          ≫ eqToHom ho1.symm := by
    refine (conj_eqToHom_iff_heq _ _ ho0 ho1).2 ?_
    apply Path.Homotopic.hpath_hext
    intro s
    apply Subtype.ext
    simp only [liftPath_apply, Path.subpath, Path.coe_mk_mk, Function.comp_apply, h0, h1]
    congr 1
    apply Subtype.ext
    simp [Path.subpathAux]
  unfold descChainPath
  rw [descChain_subpath_eq_descLocV U V hUV u v huv γ hγ t hcov]
  simp only [descLocV]
  rw [hcls, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **Bridge: `descChainPath` is a `descSpan`.**  The descended chain over a full partition of
`[0, 1]` is exactly the span from `0` to `1`, conjugated by the fixed endpoint recasts
`descObj a ↔ descObj (γ 0)` and `descObj (γ 1) ↔ descObj b` — recasts that depend only on `γ`, not
on the partition.  This is what reduces subdivision independence for `descChainPath` to the span
form `descSpan_indep`. -/
theorem descChainPath_eq_span (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChainPath U V hUV u v huv γ t h0 h1 hcov
      = eqToHom (congrArg (descObj U V hUV u v) γ.source.symm)
        ≫ descSpan U V hUV u v huv γ 0 1 t h0 h1 hcov
        ≫ eqToHom (congrArg (descObj U V hUV u v) γ.target) := by
  simp only [descChainPath, descSpan, descChainI, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

/-- **Subdivision independence for `descChainPath`.**  Any two *monotone* cover-adapted subdivisions
of `[0, 1]` compute the same descended chain.  Both reduce (via `descChainPath_eq_span`) to a
`descSpan` conjugated by the same endpoint recasts, and the two spans are equal by `descSpan_indep`. -/
theorem descChainPath_indep (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I)
    (htmono : Monotone t) (hsmono : Monotone s)
    (h0t : t 0 = 0) (h1t : t (Fin.last n) = 1) (h0s : s 0 = 0) (h1s : s (Fin.last m) = 1)
    (hcovt : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
    (hcovs : ∀ k : Fin m, range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ U ∨
                 range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ V) :
    descChainPath U V hUV u v huv γ t h0t h1t hcovt
      = descChainPath U V hUV u v huv γ s h0s h1s hcovs := by
  rw [descChainPath_eq_span U V hUV u v huv γ t h0t h1t hcovt,
      descChainPath_eq_span U V hUV u v huv γ s h0s h1s hcovs,
      descSpan_indep U V hUV u v huv γ (n + m) 0 1 t s htmono hsmono h0t h1t h0s h1s
        hcovt hcovs (le_refl _)]

/-- **Descended morphism of a path.**  Chooses a cover-adapted subdivision (`exists_subpath_cover`)
and takes its `descChainPath`.  Independence of the choice is `descHom_eq_descChainPath`. -/
noncomputable def descHom (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) : descObj U V hUV u v a ⟶ descObj U V hUV u v b :=
  descChainPath U V hUV u v huv γ
    (exists_subpath_cover U V hUopen hVopen hUV γ).choose_spec.choose
    (exists_subpath_cover U V hUopen hVopen hUV γ).choose_spec.choose_spec.1
    (exists_subpath_cover U V hUopen hVopen hUV γ).choose_spec.choose_spec.2.1
    (exists_subpath_cover U V hUopen hVopen hUV γ).choose_spec.choose_spec.2.2.2

/-- **Subdivision independence.**  The descended morphism of a path is independent of the chosen
cover-adapted subdivision: any subdivision computes the same value as `descHom`.  This is proved by
passing to a common refinement, using that splitting a piece at an interior point factors the
`descPiece` (via `subpathTransSubpath` inside a single cover element and functoriality of `u`/`v`)
and the same-side concatenation laws `descLocU_trans` / `descLocV_trans`. -/
theorem descHom_eq_descChainPath (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) {n : ℕ} (t : Fin (n + 1) → I) (htmono : Monotone t)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChainPath U V hUV u v huv γ t h0 h1 hcov
      = descHom U V hUopen hVopen hUV u v huv γ := by
  unfold descHom
  exact descChainPath_indep U V hUV u v huv γ t _ htmono
    (exists_subpath_cover U V hUopen hVopen hUV γ).choose_spec.choose_spec.2.2.1
    h0 h1 _ _ hcov _

/-! ### Reparametrization toolkit for multiplicativity

The halving maps `halfL x = x/2`, `halfR x = (x+1)/2` rescale the parameter interval onto the two
halves `[0, 1/2]`, `[1/2, 1]`.  They convert a subpath of `p.trans q` on a half-cell into the
corresponding subpath of `p` (resp. `q`); the combined partition `pcat` glues a partition of `p`
and a partition of `q` into one partition of `p.trans q`. -/

/-- Rescale `[0,1]` onto `[0, 1/2]`. -/
noncomputable def halfL (x : I) : I := ⟨(x : ℝ) / 2,
  Set.mem_Icc.mpr ⟨by have := unitInterval.nonneg x; linarith,
    by have := unitInterval.le_one x; linarith⟩⟩

/-- Rescale `[0,1]` onto `[1/2, 1]`. -/
noncomputable def halfR (x : I) : I := ⟨((x : ℝ) + 1) / 2,
  Set.mem_Icc.mpr ⟨by have := unitInterval.nonneg x; linarith,
    by have := unitInterval.le_one x; linarith⟩⟩

@[simp] theorem coe_halfL (x : I) : (halfL x : ℝ) = (x : ℝ) / 2 := rfl
@[simp] theorem coe_halfR (x : I) : (halfR x : ℝ) = ((x : ℝ) + 1) / 2 := rfl

theorem coe_halfL_le_half (x : I) : (halfL x : ℝ) ≤ 1 / 2 := by
  simp only [coe_halfL]; have := unitInterval.le_one x; linarith
theorem half_le_coe_halfR (x : I) : 1 / 2 ≤ (halfR x : ℝ) := by
  simp only [coe_halfR]; have := unitInterval.nonneg x; linarith

theorem halfL_zero : halfL 0 = 0 := by apply Subtype.ext; simp
theorem halfL_one : halfL 1 = ⟨1 / 2, by norm_num⟩ := by apply Subtype.ext; simp
theorem halfR_zero : halfR 0 = ⟨1 / 2, by norm_num⟩ := by apply Subtype.ext; simp
theorem halfR_one : halfR 1 = 1 := by apply Subtype.ext; simp

/-- On the left half, `p.trans q` reparametrizes to `p`. -/
theorem trans_halfL {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x : I) : (p.trans q) (halfL x) = p x := by
  rw [Path.trans_apply, dif_pos (coe_halfL_le_half x)]
  congr 1; apply Subtype.ext; simp only [coe_halfL]; ring

/-- On the right half, `p.trans q` reparametrizes to `q`. -/
theorem trans_halfR {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x : I) : (p.trans q) (halfR x) = q x := by
  rcases eq_or_lt_of_le (half_le_coe_halfR x) with heq | hlt
  · have hx0 : x = 0 := by
      simp only [coe_halfR] at heq
      apply Subtype.ext; simpa using (by linarith : (x : ℝ) = 0)
    subst hx0
    have he : halfR (0 : I) = ⟨1 / 2, by norm_num⟩ := by apply Subtype.ext; simp [coe_halfR]
    rw [he, Path.trans_apply, dif_pos (by norm_num), q.source]
    convert p.target using 2; norm_num
  · rw [Path.trans_apply, dif_neg (not_le.mpr hlt)]
    congr 1; apply Subtype.ext; simp only [coe_halfR]; ring

theorem subpathAux_halfL (a b s : I) :
    Path.subpathAux (halfL a) (halfL b) s = halfL (Path.subpathAux a b s) := by
  apply Subtype.ext; simp only [Path.subpathAux, coe_halfL]; ring

theorem subpathAux_halfR (a b s : I) :
    Path.subpathAux (halfR a) (halfR b) s = halfR (Path.subpathAux a b s) := by
  apply Subtype.ext; simp only [Path.subpathAux, coe_halfR]; ring

/-- Two paths with (propositionally) equal endpoints that agree pointwise are heterogeneously
equal. -/
theorem path_heq_of_ends {Y : Type*} [TopologicalSpace Y] {a1 b1 a2 b2 : Y}
    (P1 : Path a1 b1) (P2 : Path a2 b2) (ha : a1 = a2) (hb : b1 = b2)
    (h : ∀ s, P1 s = P2 s) : HEq P1 P2 := by
  subst ha; subst hb; rw [heq_eq_eq]; ext s; exact h s

/-- The left-scaled subpath of `p.trans q` is (heterogeneously) the subpath of `p`. -/
theorem trans_subpath_halfL {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x₀ x₁ : I) :
    HEq ((p.trans q).subpath (halfL x₀) (halfL x₁)) (p.subpath x₀ x₁) := by
  apply path_heq_of_ends
  · exact trans_halfL p q x₀
  · exact trans_halfL p q x₁
  · intro s
    simp only [Path.subpath, Path.coe_mk_mk, Function.comp_apply]
    rw [subpathAux_halfL, trans_halfL]

/-- The right-scaled subpath of `p.trans q` is (heterogeneously) the subpath of `q`. -/
theorem trans_subpath_halfR {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x₀ x₁ : I) :
    HEq ((p.trans q).subpath (halfR x₀) (halfR x₁)) (q.subpath x₀ x₁) := by
  apply path_heq_of_ends
  · exact trans_halfR p q x₀
  · exact trans_halfR p q x₁
  · intro s
    simp only [Path.subpath, Path.coe_mk_mk, Function.comp_apply]
    rw [subpathAux_halfR, trans_halfR]

/-- **Combined partition.**  Glue a partition `t` of `[0, 1/2]` (via `halfL`) and a partition `s` of
`[1/2, 1]` (via `halfR`) into a single partition of `[0, 1]` with `n + m` cells. -/
noncomputable def pcat {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I) :
    Fin (n + m + 1) → I :=
  show Fin (n + (m + 1)) → I from Fin.append (fun i : Fin n => t i.castSucc) s

theorem pcat_snoc {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I) (y : I) :
    pcat t (Fin.snoc s y) = Fin.snoc (pcat t s) y := by
  unfold pcat; exact Fin.append_snoc (fun i : Fin n => t i.castSucc) s y

theorem pcat_zero {n m : ℕ} (hn : 0 < n) (t : Fin (n + 1) → I) (s : Fin (m + 1) → I) :
    pcat t s 0 = t 0 := by
  unfold pcat
  rw [show (0 : Fin (n + (m + 1))) = Fin.castAdd (m + 1) (⟨0, hn⟩ : Fin n) from Fin.ext rfl,
    Fin.append_left]
  congr 1

theorem pcat_last {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I) :
    pcat t s (Fin.last (n + m)) = s (Fin.last m) := by
  unfold pcat
  rw [show (Fin.last (n + m) : Fin (n + (m + 1))) = Fin.natAdd n (Fin.last m) from
    Fin.ext (by simp), Fin.append_right]

theorem pcat_apply {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I)
    (i : Fin (n + (m + 1))) :
    pcat t s i = if h : (i : ℕ) < n then t ⟨i, by omega⟩ else s ⟨(i : ℕ) - n, by omega⟩ := by
  by_cases h : (i : ℕ) < n
  · rw [dif_pos h]
    have hv : pcat t s i = t (⟨(i : ℕ), h⟩ : Fin n).castSucc := by
      unfold pcat
      conv_lhs => rw [show i = Fin.castAdd (m + 1) (⟨(i : ℕ), h⟩ : Fin n) from Fin.ext rfl]
      rw [Fin.append_left]
    rw [hv]; congr 1
  · rw [dif_neg h]
    have hv : pcat t s i = s (⟨(i : ℕ) - n, by omega⟩ : Fin (m + 1)) := by
      unfold pcat
      conv_lhs => rw [show i = Fin.natAdd n (⟨(i : ℕ) - n, by omega⟩ : Fin (m + 1)) from
        Fin.ext (by simp; omega)]
      rw [Fin.append_right]
    rw [hv]

theorem pcat_mono {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I)
    (ht : Monotone t) (hs : Monotone s) (hmid : t (Fin.last n) = s 0) :
    Monotone (pcat t s) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  simp only [pcat_apply, Fin.val_castSucc, Fin.val_succ]
  by_cases h1 : (i : ℕ) < n
  · by_cases h2 : (i : ℕ) + 1 < n
    · rw [dif_pos h1, dif_pos h2]; exact ht (Fin.mk_le_mk.mpr (by omega))
    · rw [dif_pos h1, dif_neg h2]
      calc t ⟨(i : ℕ), by omega⟩ ≤ t (Fin.last n) := ht (Fin.le_last _)
        _ = s 0 := hmid
        _ ≤ s ⟨(i : ℕ) + 1 - n, by omega⟩ := hs (Fin.zero_le _)
  · rw [dif_neg h1, dif_neg (by omega : ¬ (i : ℕ) + 1 < n)]
    exact hs (Fin.mk_le_mk.mpr (by omega))

/-! ### The square lemma

A continuous map `S : I × I → X` whose image lies in a single cover element has four boundary
edges; going up the left edge and then across the top is homotopic, *inside the square*, to going
across the bottom and then up the right edge.  Pushing that homotopy through `S` keeps it inside
the cover element, so the two routes have the same descended morphism.  This is the single cell of
the grid crossing that proves homotopy invariance. -/

/-- The left edge of the unit square, from `(0, 0)` to `(1, 0)`. -/
def sqLeft : Path ((0, 0) : I × I) ((1, 0) : I × I) where
  toFun y := (y, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The top edge of the unit square, from `(1, 0)` to `(1, 1)`. -/
def sqTop : Path ((1, 0) : I × I) ((1, 1) : I × I) where
  toFun x := (1, x)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The bottom edge of the unit square, from `(0, 0)` to `(0, 1)`. -/
def sqBot : Path ((0, 0) : I × I) ((0, 1) : I × I) where
  toFun x := (0, x)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The right edge of the unit square, from `(0, 1)` to `(1, 1)`. -/
def sqRight : Path ((0, 1) : I × I) ((1, 1) : I × I) where
  toFun y := (y, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- Any two paths across the square with the same endpoints are homotopic: `I × I` is a product of
convex sets, hence contractible, hence simply connected. -/
theorem sq_paths_homotopic (p q : Path ((0, 0) : I × I) ((1, 1) : I × I)) : p.Homotopic q := by
  haveI : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  exact SimplyConnectedSpace.paths_homotopic p q

/-- The left-then-top route across the square is homotopic to the bottom-then-right route. -/
theorem sq_route_homotopic :
    (sqLeft.trans sqTop).Homotopic (sqBot.trans sqRight) :=
  sq_paths_homotopic _ _

/-- **The square lemma.**  Let `S : I × I → X` have image inside a single cover element and let
`bot`, `top` (the horizontal edges, traced in the second coordinate) and `lef`, `rig` (the vertical
edges, traced in the first coordinate) be paths tracing its boundary.  Then left-then-top and
bottom-then-right have the same descended morphism. -/
theorem descPiece_square (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    (S : C(I × I, X)) (hS : range S ⊆ U ∨ range S ⊆ V)
    {p₀₀ p₀₁ p₁₀ p₁₁ : X}
    (bot : Path p₀₀ p₀₁) (top : Path p₁₀ p₁₁) (lef : Path p₀₀ p₁₀) (rig : Path p₀₁ p₁₁)
    (hbot : ∀ x, bot x = S (0, x)) (htop : ∀ x, top x = S (1, x))
    (hlef : ∀ y, lef y = S (y, 0)) (hrig : ∀ y, rig y = S (y, 1))
    (hcb : range bot ⊆ U ∨ range bot ⊆ V) (hct : range top ⊆ U ∨ range top ⊆ V)
    (hcl : range lef ⊆ U ∨ range lef ⊆ V) (hcr : range rig ⊆ U ∨ range rig ⊆ V) :
    descPiece U V hUV u v huv lef hcl ≫ descPiece U V hUV u v huv top hct
      = descPiece U V hUV u v huv bot hcb ≫ descPiece U V hUV u v huv rig hcr := by
  -- Every edge factors through `S`, so it has range inside `range S`.
  have rb : range bot ⊆ range S := by rintro _ ⟨x, rfl⟩; exact ⟨(0, x), (hbot x).symm⟩
  have rt : range top ⊆ range S := by rintro _ ⟨x, rfl⟩; exact ⟨(1, x), (htop x).symm⟩
  have rl : range lef ⊆ range S := by rintro _ ⟨y, rfl⟩; exact ⟨(y, 0), (hlef y).symm⟩
  have rr : range rig ⊆ range S := by rintro _ ⟨y, rfl⟩; exact ⟨(y, 1), (hrig y).symm⟩
  -- Normalize the corners so that all four paths live between the corner values of `S`.
  have e00 : p₀₀ = S (0, 0) := bot.source.symm.trans (hbot 0)
  have e01 : p₀₁ = S (0, 1) := bot.target.symm.trans (hbot 1)
  have e10 : p₁₀ = S (1, 0) := top.source.symm.trans (htop 0)
  have e11 : p₁₁ = S (1, 1) := top.target.symm.trans (htop 1)
  subst e00; subst e01; subst e10; subst e11
  -- The two routes are the images of the two square routes under `S`.
  have hLT : lef.trans top = (sqLeft.trans sqTop).map S.continuous := by
    ext x
    simp only [Path.trans_apply, Path.map_coe, Function.comp_apply]
    split_ifs with hx
    · exact hlef _
    · exact htop _
  have hBR : bot.trans rig = (sqBot.trans sqRight).map S.continuous := by
    ext x
    simp only [Path.trans_apply, Path.map_coe, Function.comp_apply]
    split_ifs with hx
    · exact hbot _
    · exact hrig _
  obtain ⟨G⟩ := sq_route_homotopic
  have hGrange : ∀ y, (G.map S) y ∈ range S := fun y => ⟨G y, rfl⟩
  rcases hS with hSU | hSV
  · -- everything lies in `U`
    have bU := rb.trans hSU
    have tU := rt.trans hSU
    have lU := rl.trans hSU
    have rU := rr.trans hSU
    have ltU : range (lef.trans top) ⊆ U := by
      rw [Path.trans_range]; exact union_subset lU tU
    have brU : range (bot.trans rig) ⊆ U := by
      rw [Path.trans_range]; exact union_subset bU rU
    rw [descPiece_eq_U U V hUV u v huv lef hcl lU, descPiece_eq_U U V hUV u v huv top hct tU,
      descPiece_eq_U U V hUV u v huv bot hcb bU, descPiece_eq_U U V hUV u v huv rig hcr rU,
      ← descLocU_trans U V hUV u v lef top lU tU ltU _ _ _,
      ← descLocU_trans U V hUV u v bot rig bU rU brU _ _ _,
      descLocU_path_congr U V hUV u v hLT ltU _ _,
      descLocU_path_congr U V hUV u v hBR brU _ _]
    exact descLocU_hom_congr U V hUV u v _ _ _ _ _ _ (G.map S) fun y => hSU (hGrange y)
  · -- everything lies in `V`
    have bV := rb.trans hSV
    have tV := rt.trans hSV
    have lV := rl.trans hSV
    have rV := rr.trans hSV
    have ltV : range (lef.trans top) ⊆ V := by
      rw [Path.trans_range]; exact union_subset lV tV
    have brV : range (bot.trans rig) ⊆ V := by
      rw [Path.trans_range]; exact union_subset bV rV
    rw [descPiece_eq_V U V hUV u v huv lef hcl lV, descPiece_eq_V U V hUV u v huv top hct tV,
      descPiece_eq_V U V hUV u v huv bot hcb bV, descPiece_eq_V U V hUV u v huv rig hcr rV,
      ← descLocV_trans U V hUV u v huv lef top lV tV ltV _ _ _,
      ← descLocV_trans U V hUV u v huv bot rig bV rV brV _ _ _,
      descLocV_path_congr U V hUV u v huv hLT ltV _ _,
      descLocV_path_congr U V hUV u v huv hBR brV _ _]
    exact descLocV_hom_congr U V hUV u v huv _ _ _ _ _ _ (G.map S) fun y => hSV (hGrange y)

/-! ### The ladder

A purely formal consequence of the square lemma: two chains of the same length joined by vertical
connectors, all of whose elementary squares commute, satisfy `first connector ≫ top chain =
bottom chain ≫ last connector`. -/

/-- **Ladder lemma.**  Given two chains `F` (along vertices `P`) and `G` (along vertices `Q`) of
the same length, connected by vertical paths `W i : Path (P i) (Q i)` whose elementary squares all
commute, the two ways around the whole ladder agree. -/
theorem descChain_ladder (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v) :
    ∀ {k : ℕ} (P Q : Fin (k + 1) → X)
      (F : (i : Fin k) → Path (P i.castSucc) (P i.succ))
      (G : (i : Fin k) → Path (Q i.castSucc) (Q i.succ))
      (W : (i : Fin (k + 1)) → Path (P i) (Q i))
      (hF : ∀ i, range (F i) ⊆ U ∨ range (F i) ⊆ V)
      (hG : ∀ i, range (G i) ⊆ U ∨ range (G i) ⊆ V)
      (hW : ∀ i, range (W i) ⊆ U ∨ range (W i) ⊆ V),
      (∀ i : Fin k, descPiece U V hUV u v huv (W i.castSucc) (hW i.castSucc)
            ≫ descPiece U V hUV u v huv (G i) (hG i)
          = descPiece U V hUV u v huv (F i) (hF i)
            ≫ descPiece U V hUV u v huv (W i.succ) (hW i.succ)) →
      descPiece U V hUV u v huv (W 0) (hW 0) ≫ descChain U V hUV u v huv Q G hG
        = descChain U V hUV u v huv P F hF
          ≫ descPiece U V hUV u v huv (W (Fin.last k)) (hW (Fin.last k)) := by
  intro k
  induction k with
  | zero =>
    intro P Q F G W hF hG hW _
    simp
  | succ k ih =>
    intro P Q F G W hF hG hW hsq
    have hih := ih (P ∘ Fin.castSucc) (Q ∘ Fin.castSucc) (fun i => F i.castSucc)
      (fun i => G i.castSucc) (fun i => W i.castSucc) (fun i => hF i.castSucc)
      (fun i => hG i.castSucc) (fun i => hW i.castSucc) (fun i => hsq i.castSucc)
    simp only [Fin.castSucc_zero] at hih
    rw [descChain_succ U V hUV u v huv P F hF, descChain_succ U V hUV u v huv Q G hG,
      ← Category.assoc, hih, Category.assoc, hsq (Fin.last k), ← Category.assoc]
    rfl

/-! ### Slices of a homotopy, and the grid partition -/

/-- The horizontal slice of a path homotopy at height `y`: the path `x ↦ Hm (y, x)`. -/
def homRow {a b : X} {γ γ' : Path a b} (Hm : γ.Homotopy γ') (y : I) : Path a b where
  toFun x := Hm (y, x)
  continuous_toFun := (map_continuous Hm).comp (by fun_prop)
  source' := Hm.source y
  target' := Hm.target y

/-- The vertical slice of a path homotopy at parameter `x`: the path `y ↦ Hm (y, x)`. -/
def homCol {a b : X} {γ γ' : Path a b} (Hm : γ.Homotopy γ') (x : I) : Path (γ x) (γ' x) where
  toFun y := Hm (y, x)
  continuous_toFun := (map_continuous Hm).comp (by fun_prop)
  source' := Hm.map_zero_left x
  target' := Hm.map_one_left x

/-- The bottom slice of a homotopy is its source path. -/
theorem homRow_zero {a b : X} {γ γ' : Path a b} (Hm : γ.Homotopy γ') : homRow Hm 0 = γ := by
  ext x; exact Hm.map_zero_left x

/-- The top slice of a homotopy is its target path. -/
theorem homRow_one {a b : X} {γ γ' : Path a b} (Hm : γ.Homotopy γ') : homRow Hm 1 = γ' := by
  ext x; exact Hm.map_one_left x

/-- The initial segment `t 0, …, t N` of an eventually-constant partition, as a `Fin`-tuple. -/
def gridPart (t : ℕ → I) (N : ℕ) : Fin (N + 1) → I := fun i => t (i : ℕ)

/-- The interpolation map `s ↦ (1 - s) t₀ + s t₁` is continuous. -/
theorem continuous_subpathAux (x y : I) : Continuous (Path.subpathAux x y) :=
  Path.subpathAux_continuous.comp (by fun_prop : Continuous fun s : I => (x, y, s))

/-- The interpolation map lands in the interval it interpolates. -/
theorem subpathAux_mem_Icc {x y : I} (hxy : x ≤ y) (s : I) : Path.subpathAux x y s ∈ Icc x y := by
  have hs : Path.subpathAux x y s ∈ range (Path.subpathAux x y) := mem_range_self s
  rwa [Path.range_subpathAux, uIcc_of_le hxy] at hs

/-- A path that is constant as a map has an `eqToHom` for its `descPiece`. -/
theorem descPiece_const (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {x y : X} (p : Path x y) (hp : ∀ s, p s = x)
    (hcov : range p ⊆ U ∨ range p ⊆ V) :
    descPiece U V hUV u v huv p hcov
      = eqToHom (congrArg (descObj U V hUV u v) ((hp 1).symm.trans p.target)) := by
  have hxy : x = y := (hp 1).symm.trans p.target
  subst hxy
  have hrefl : p = Path.refl x := by ext s; exact hp s
  rw [descPiece_path_congr U V hUV u v huv hrefl hcov, descPiece_refl]
  simp

/-- **Congruence of `descChainPath` along an equality of paths.** -/
theorem descChainPath_congr_path (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} {γ δ : Path a b} (hγδ : γ = δ) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
    (hcov' : ∀ k : Fin n, range (δ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (δ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descChainPath U V hUV u v huv γ t h0 h1 hcov
      = descChainPath U V hUV u v huv δ t h0 h1 hcov' := by
  subst hγδ; rfl

/-- **Homotopy invariance.**  Endpoint-homotopic paths have the same descended morphism.  This is
the two-dimensional grid subdivision of the homotopy (`Subdivision2D.lean`): the homotopy square is
chopped into cells each carried into a single cover element, and crossing one cell at a time replaces
a path by a homotopic one whose descended morphism agrees, since inside one cover element the
descended morphism is `u`- (or `v`-) functorial and a cell homotopy lifts to that subspace. -/
theorem descHom_homotopic (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ γ' : Path a b) (h : γ.Homotopic γ') :
    descHom U V hUopen hVopen hUV u v huv γ = descHom U V hUopen hVopen hUV u v huv γ' := by
  obtain ⟨Hm⟩ := h
  -- The homotopy as a bundled continuous map on the square, and its grid subdivision.
  set SH : C(I × I, X) := ⟨fun z => Hm z, map_continuous Hm⟩ with hSHdef
  obtain ⟨t, N, ht0, htN, htmono, hcell⟩ := exists_grid_cover U V hUopen hVopen hUV SH
  have hgp0 : gridPart t N 0 = 0 := ht0
  have hgpN : gridPart t N (Fin.last N) = 1 := htN N le_rfl
  have hgpmono : Monotone (gridPart t N) := fun i j hij => htmono hij
  -- Every horizontal edge of the grid lies in a single cover element.
  have hcovRow : ∀ (m : ℕ) (k : Fin N),
      range ((homRow Hm (t m)).subpath (gridPart t N k.castSucc) (gridPart t N k.succ)) ⊆ U ∨
      range ((homRow Hm (t m)).subpath (gridPart t N k.castSucc) (gridPart t N k.succ)) ⊆ V := by
    intro m k
    have hsub : range ((homRow Hm (t m)).subpath (gridPart t N k.castSucc) (gridPart t N k.succ))
        ⊆ SH '' (Icc (t m) (t (m + 1)) ×ˢ Icc (t (k : ℕ)) (t ((k : ℕ) + 1))) := by
      rw [Path.range_subpath_of_le _ _ _ (hgpmono (Fin.castSucc_lt_succ (i := k)).le)]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(t m, x), ⟨⟨le_rfl, htmono (by omega : m ≤ m + 1)⟩, hx⟩, rfl⟩
    rcases hcell m (k : ℕ) with hU | hV
    · exact Or.inl (hsub.trans hU)
    · exact Or.inr (hsub.trans hV)
  -- Every vertical edge of the grid lies in a single cover element.
  have hcovCol : ∀ (m : ℕ) (j : Fin (N + 1)),
      range ((homCol Hm (gridPart t N j)).subpath (t m) (t (m + 1))) ⊆ U ∨
      range ((homCol Hm (gridPart t N j)).subpath (t m) (t (m + 1))) ⊆ V := by
    intro m j
    have hsub : range ((homCol Hm (gridPart t N j)).subpath (t m) (t (m + 1)))
        ⊆ SH '' (Icc (t m) (t (m + 1)) ×ˢ Icc (t (j : ℕ)) (t ((j : ℕ) + 1))) := by
      rw [Path.range_subpath_of_le _ _ _ (htmono (by omega : m ≤ m + 1))]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨(y, gridPart t N j), ⟨hy, ⟨le_rfl, htmono (by omega : (j : ℕ) ≤ (j : ℕ) + 1)⟩⟩, rfl⟩
    rcases hcell m (j : ℕ) with hU | hV
    · exact Or.inl (hsub.trans hU)
    · exact Or.inr (hsub.trans hV)
  -- Crossing one row of the grid does not change the descended morphism.
  have hstep : ∀ m : ℕ,
      descChainPath U V hUV u v huv (homRow Hm (t m)) (gridPart t N) hgp0 hgpN (hcovRow m)
        = descChainPath U V hUV u v huv (homRow Hm (t (m + 1))) (gridPart t N) hgp0 hgpN
            (hcovRow (m + 1)) := by
    intro m
    -- Each elementary cell square commutes.
    have hsq : ∀ j : Fin N,
        descPiece U V hUV u v huv
              ((homCol Hm (gridPart t N j.castSucc)).subpath (t m) (t (m + 1)))
              (hcovCol m j.castSucc)
            ≫ descPiece U V hUV u v huv
              ((homRow Hm (t (m + 1))).subpath (gridPart t N j.castSucc) (gridPart t N j.succ))
              (hcovRow (m + 1) j)
          = descPiece U V hUV u v huv
              ((homRow Hm (t m)).subpath (gridPart t N j.castSucc) (gridPart t N j.succ))
              (hcovRow m j)
            ≫ descPiece U V hUV u v huv
              ((homCol Hm (gridPart t N j.succ)).subpath (t m) (t (m + 1)))
              (hcovCol m j.succ) := by
      intro j
      -- The cell, reparametrized to the unit square.
      set cellMap : C(I × I, I × I) :=
        ⟨fun z => (Path.subpathAux (t m) (t (m + 1)) z.1,
                   Path.subpathAux (gridPart t N j.castSucc) (gridPart t N j.succ) z.2),
         ((continuous_subpathAux _ _).comp continuous_fst).prodMk
           ((continuous_subpathAux _ _).comp continuous_snd)⟩ with hcellMap
      have hScell : range (SH.comp cellMap)
          ⊆ SH '' (Icc (t m) (t (m + 1)) ×ˢ Icc (t (j : ℕ)) (t ((j : ℕ) + 1))) := by
        rintro _ ⟨z, rfl⟩
        exact ⟨cellMap z, ⟨subpathAux_mem_Icc (htmono (Nat.le_succ m)) z.1,
          subpathAux_mem_Icc (htmono (Nat.le_succ (j : ℕ))) z.2⟩, rfl⟩
      have hS : range (SH.comp cellMap) ⊆ U ∨ range (SH.comp cellMap) ⊆ V := by
        rcases hcell m (j : ℕ) with hU | hV
        · exact Or.inl (hScell.trans hU)
        · exact Or.inr (hScell.trans hV)
      refine descPiece_square U V hUV u v huv (SH.comp cellMap) hS _ _ _ _ ?_ ?_ ?_ ?_ _ _ _ _
      · intro x
        show Hm (t m, Path.subpathAux (gridPart t N j.castSucc) (gridPart t N j.succ) x)
            = Hm (Path.subpathAux (t m) (t (m + 1)) 0,
                  Path.subpathAux (gridPart t N j.castSucc) (gridPart t N j.succ) x)
        rw [Path.subpathAux_zero]
      · intro x
        show Hm (t (m + 1), Path.subpathAux (gridPart t N j.castSucc) (gridPart t N j.succ) x)
            = Hm (Path.subpathAux (t m) (t (m + 1)) 1,
                  Path.subpathAux (gridPart t N j.castSucc) (gridPart t N j.succ) x)
        rw [Path.subpathAux_one]
      · intro y
        show Hm (Path.subpathAux (t m) (t (m + 1)) y, gridPart t N j.castSucc)
            = Hm (Path.subpathAux (t m) (t (m + 1)) y,
                  Path.subpathAux (gridPart t N j.castSucc) (gridPart t N j.succ) 0)
        rw [Path.subpathAux_zero]
      · intro y
        show Hm (Path.subpathAux (t m) (t (m + 1)) y, gridPart t N j.succ)
            = Hm (Path.subpathAux (t m) (t (m + 1)) y,
                  Path.subpathAux (gridPart t N j.castSucc) (gridPart t N j.succ) 1)
        rw [Path.subpathAux_one]
    have hladder := descChain_ladder U V hUV u v huv
      (⇑(homRow Hm (t m)) ∘ gridPart t N)
      (⇑(homRow Hm (t (m + 1))) ∘ gridPart t N)
      (fun j : Fin N =>
        (homRow Hm (t m)).subpath (gridPart t N j.castSucc) (gridPart t N j.succ))
      (fun j : Fin N =>
        (homRow Hm (t (m + 1))).subpath (gridPart t N j.castSucc) (gridPart t N j.succ))
      (fun j : Fin (N + 1) => (homCol Hm (gridPart t N j)).subpath (t m) (t (m + 1)))
      (hcovRow m) (hcovRow (m + 1)) (hcovCol m) hsq
    -- The two outer connectors are constant paths, hence `eqToHom`s.
    have hconst0 : ∀ s : I,
        ((homCol Hm (gridPart t N 0)).subpath (t m) (t (m + 1))) s
          = (⇑(homRow Hm (t m)) ∘ gridPart t N) 0 := by
      intro s
      show Hm (Path.subpathAux (t m) (t (m + 1)) s, gridPart t N 0) = Hm (t m, gridPart t N 0)
      rw [hgp0, Hm.source, Hm.source]
    have hconst1 : ∀ s : I,
        ((homCol Hm (gridPart t N (Fin.last N))).subpath (t m) (t (m + 1))) s
          = (⇑(homRow Hm (t m)) ∘ gridPart t N) (Fin.last N) := by
      intro s
      show Hm (Path.subpathAux (t m) (t (m + 1)) s, gridPart t N (Fin.last N))
          = Hm (t m, gridPart t N (Fin.last N))
      rw [hgpN, Hm.target, Hm.target]
    have d0 : (⇑(homRow Hm (t m)) ∘ gridPart t N) 0
            = (⇑(homRow Hm (t (m + 1))) ∘ gridPart t N) 0 := by
      show Hm (t m, gridPart t N 0) = Hm (t (m + 1), gridPart t N 0)
      rw [hgp0, Hm.source, Hm.source]
    have d1 : (⇑(homRow Hm (t m)) ∘ gridPart t N) (Fin.last N)
            = (⇑(homRow Hm (t (m + 1))) ∘ gridPart t N) (Fin.last N) := by
      show Hm (t m, gridPart t N (Fin.last N)) = Hm (t (m + 1), gridPart t N (Fin.last N))
      rw [hgpN, Hm.target, Hm.target]
    have hw0 : descPiece U V hUV u v huv
          ((homCol Hm (gridPart t N 0)).subpath (t m) (t (m + 1))) (hcovCol m 0)
        = eqToHom (congrArg (descObj U V hUV u v) d0) :=
      descPiece_const U V hUV u v huv _ hconst0 (hcovCol m 0)
    have hw1 : descPiece U V hUV u v huv
          ((homCol Hm (gridPart t N (Fin.last N))).subpath (t m) (t (m + 1)))
          (hcovCol m (Fin.last N))
        = eqToHom (congrArg (descObj U V hUV u v) d1) :=
      descPiece_const U V hUV u v huv _ hconst1 (hcovCol m (Fin.last N))
    rw [hw0, hw1] at hladder
    have hB : descChain U V hUV u v huv (⇑(homRow Hm (t (m + 1))) ∘ gridPart t N)
          (fun j : Fin N =>
            (homRow Hm (t (m + 1))).subpath (gridPart t N j.castSucc) (gridPart t N j.succ))
          (hcovRow (m + 1))
        = eqToHom (congrArg (descObj U V hUV u v) d0).symm
          ≫ descChain U V hUV u v huv (⇑(homRow Hm (t m)) ∘ gridPart t N)
              (fun j : Fin N =>
                (homRow Hm (t m)).subpath (gridPart t N j.castSucc) (gridPart t N j.succ))
              (hcovRow m)
          ≫ eqToHom (congrArg (descObj U V hUV u v) d1) := by
      rw [← hladder]; simp
    simp only [descChainPath]
    rw [hB]
    simp
  -- Iterate the row crossing from row `0` to row `N`.
  have hRowAll : ∀ m : ℕ,
      descChainPath U V hUV u v huv (homRow Hm (t 0)) (gridPart t N) hgp0 hgpN (hcovRow 0)
        = descChainPath U V hUV u v huv (homRow Hm (t m)) (gridPart t N) hgp0 hgpN
            (hcovRow m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [ih, hstep m]
  have hγ0 : homRow Hm (t 0) = γ := by rw [ht0]; exact homRow_zero Hm
  have hγ1 : homRow Hm (t N) = γ' := by rw [htN N le_rfl]; exact homRow_one Hm
  have hcovγ : ∀ k : Fin N,
      range (γ.subpath (gridPart t N k.castSucc) (gridPart t N k.succ)) ⊆ U ∨
      range (γ.subpath (gridPart t N k.castSucc) (gridPart t N k.succ)) ⊆ V := by
    rw [← hγ0]; exact hcovRow 0
  have hcovγ' : ∀ k : Fin N,
      range (γ'.subpath (gridPart t N k.castSucc) (gridPart t N k.succ)) ⊆ U ∨
      range (γ'.subpath (gridPart t N k.castSucc) (gridPart t N k.succ)) ⊆ V := by
    rw [← hγ1]; exact hcovRow N
  calc descHom U V hUopen hVopen hUV u v huv γ
      = descChainPath U V hUV u v huv γ (gridPart t N) hgp0 hgpN hcovγ :=
        (descHom_eq_descChainPath U V hUopen hVopen hUV u v huv γ (gridPart t N) hgpmono
          hgp0 hgpN hcovγ).symm
    _ = descChainPath U V hUV u v huv (homRow Hm (t 0)) (gridPart t N) hgp0 hgpN (hcovRow 0) :=
        descChainPath_congr_path U V hUV u v huv hγ0.symm (gridPart t N) hgp0 hgpN hcovγ
          (hcovRow 0)
    _ = descChainPath U V hUV u v huv (homRow Hm (t N)) (gridPart t N) hgp0 hgpN (hcovRow N) :=
        hRowAll N
    _ = descChainPath U V hUV u v huv γ' (gridPart t N) hgp0 hgpN hcovγ' :=
        descChainPath_congr_path U V hUV u v huv hγ1 (gridPart t N) hgp0 hgpN (hcovRow N) hcovγ'
    _ = descHom U V hUopen hVopen hUV u v huv γ' :=
        descHom_eq_descChainPath U V hUopen hVopen hUV u v huv γ' (gridPart t N) hgpmono
          hgp0 hgpN hcovγ'

/-- **Partition congruence for `descSpan`.**  Equal partitions give equal spans (the endpoint
proofs are propositions). -/
theorem descSpan_partition_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₁ : I) {n : ℕ} {t t' : Fin (n + 1) → I} (ht : t = t')
    (h0 : t 0 = x₀) (h1 : t (Fin.last n) = x₁)
    (hcov : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V)
    (h0' : t' 0 = x₀) (h1' : t' (Fin.last n) = x₁)
    (hcov' : ∀ k : Fin n, range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ U ∨
                 range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ V) :
    descSpan U V hUV u v huv γ x₀ x₁ t h0 h1 hcov
      = descSpan U V hUV u v huv γ x₀ x₁ t' h0' h1' hcov' := by
  subst ht; rfl

/-- Restricting a combined partition to its first cells drops the last cell of the right block. -/
theorem pcat_comp_castSucc {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1 + 1) → I) :
    pcat t s ∘ Fin.castSucc = pcat t (s ∘ Fin.castSucc) := by
  funext i
  simp only [Function.comp_apply, pcat_apply, Fin.val_castSucc]
  by_cases hi : (i : ℕ) < n
  · rw [dif_pos hi, dif_pos hi]
  · rw [dif_neg hi, dif_neg hi]
    congr 1

/-- **Congruence of `descChain` along an equality of vertex families and an `HEq` of cell
families.**  Two cell families that agree heterogeneously (their endpoints move only along the
propositional vertex equality) produce the same chain, up to the forced endpoint recasts. -/
theorem descChain_path_congr (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {m : ℕ} {P P' : Fin (m + 1) → X} (hP : P = P')
    (F : (k : Fin m) → Path (P k.castSucc) (P k.succ))
    (F' : (k : Fin m) → Path (P' k.castSucc) (P' k.succ))
    (hF : ∀ k, HEq (F k) (F' k))
    (hcov : ∀ k, range (F k) ⊆ U ∨ range (F k) ⊆ V)
    (hcov' : ∀ k, range (F' k) ⊆ U ∨ range (F' k) ⊆ V) :
    descChain U V hUV u v huv P F hcov
      = eqToHom (congrArg (fun r : Fin (m + 1) → X => descObj U V hUV u v (r 0)) hP)
        ≫ descChain U V hUV u v huv P' F' hcov'
        ≫ eqToHom (congrArg (fun r : Fin (m + 1) → X => descObj U V hUV u v (r (Fin.last m)))
            hP.symm) := by
  subst hP
  have hFF : F = F' := funext fun k => eq_of_heq (hF k)
  subst hFF
  simp

/-- **Recasting the source endpoint of a `descPiece`.**  Moving the subpath source along a
propositional equality `x₀ = x₀'` changes `descPiece` only by the forced `eqToHom` on the left. -/
theorem descPiece_recast_source (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ x₀' x₁ : I) (h0 : x₀ = x₀')
    (hcov : range (γ.subpath x₀ x₁) ⊆ U ∨ range (γ.subpath x₀ x₁) ⊆ V)
    (hcov' : range (γ.subpath x₀' x₁) ⊆ U ∨ range (γ.subpath x₀' x₁) ⊆ V) :
    descPiece U V hUV u v huv (γ.subpath x₀ x₁) hcov
      = eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) h0)
        ≫ descPiece U V hUV u v huv (γ.subpath x₀' x₁) hcov' := by
  subst h0; simp

/-- **Concatenation additivity of `descSpan`.**  A span over a glued partition `pcat t s` factors as
the span over `t` followed by the span over `s`.  This is the span-level statement of
multiplicativity, proved by back-peeling the right block one cell at a time. -/
theorem descSpan_append (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (x₀ : I) {n : ℕ} (t : Fin (n + 1) → I) (h0t : t 0 = x₀)
    (hcovt : ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    ∀ {m : ℕ} (s : Fin (m + 1) → I) (h0s : s 0 = t (Fin.last n))
      (hcovs : ∀ k : Fin m, range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ U ∨
                   range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ V)
      (hcovW : ∀ k : Fin (n + m),
          range (γ.subpath ((pcat t s) k.castSucc) ((pcat t s) k.succ)) ⊆ U ∨
          range (γ.subpath ((pcat t s) k.castSucc) ((pcat t s) k.succ)) ⊆ V)
      (h0W : (pcat t s) 0 = x₀),
      descSpan U V hUV u v huv γ x₀ (s (Fin.last m)) (pcat t s) h0W (pcat_last t s) hcovW
        = descSpan U V hUV u v huv γ x₀ (t (Fin.last n)) t h0t rfl hcovt
          ≫ descSpan U V hUV u v huv γ (t (Fin.last n)) (s (Fin.last m)) s h0s rfl hcovs := by
  intro m
  induction m with
  | zero =>
    intro s h0s hcovs hcovW h0W
    have hpcat : pcat t s = t := by
      funext i
      rw [pcat_apply]
      by_cases hi : (i : ℕ) < n
      · rw [dif_pos hi]
      · rw [dif_neg hi]
        have hlt := i.isLt
        have hin : (i : ℕ) = n := by omega
        have hi_last : i = Fin.last n := Fin.ext (by rw [Fin.val_last]; exact hin)
        have e1 : (⟨(i : ℕ) - n, by omega⟩ : Fin (0 + 1)) = (0 : Fin (0 + 1)) :=
          Fin.ext (by simp only [Fin.val_zero]; omega)
        rw [e1, h0s, hi_last]
    have hmid : t (Fin.last n) = s (Fin.last 0) := by
      rw [show s (Fin.last 0) = s 0 from congrArg s (Fin.ext rfl)]; exact h0s.symm
    have hR2 : descSpan U V hUV u v huv γ (t (Fin.last n)) (s (Fin.last 0)) s h0s rfl hcovs
        = eqToHom (congrArg (fun z => descObj U V hUV u v (γ z)) hmid) := by
      rw [descSpan, descChainI_zero U V hUV u v huv γ s hcovs]
      simp
    rw [hR2,
        descSpan_recast_target U V hUV u v huv γ x₀ (t (Fin.last n)) (s (Fin.last 0)) t
          h0t rfl hcovt hmid,
        descSpan_partition_congr U V hUV u v huv γ x₀ (s (Fin.last 0)) hpcat h0W (pcat_last t s)
          hcovW h0t hmid hcovt]
  | succ m ih =>
    intro s h0s hcovs hcovW h0W
    haveI : NeZero (n + (m + 1)) := ⟨by omega⟩
    -- the last cell of `s`, in its two index forms
    have hlasts : range (γ.subpath (s (Fin.castSucc (Fin.last m))) (s (Fin.last (m + 1)))) ⊆ U ∨
                  range (γ.subpath (s (Fin.castSucc (Fin.last m))) (s (Fin.last (m + 1)))) ⊆ V := by
      have h := hcovs (Fin.last m)
      rwa [Fin.succ_last] at h
    -- the penultimate value of the glued partition equals the second-to-last value of `s`
    have hmidpt : (pcat t s) (Fin.castSucc (Fin.last (n + m))) = s (Fin.castSucc (Fin.last m)) := by
      rw [pcat_apply, dif_neg (by simp only [Fin.val_castSucc, Fin.val_last]; omega :
          ¬ ((Fin.castSucc (Fin.last (n + m)) : Fin (n + (m + 1 + 1))) : ℕ) < n)]
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_last]
      omega
    have hlastW : range (γ.subpath ((pcat t s) (Fin.castSucc (Fin.last (n + m))))
            (s (Fin.last (m + 1)))) ⊆ U ∨
          range (γ.subpath ((pcat t s) (Fin.castSucc (Fin.last (n + m))))
            (s (Fin.last (m + 1)))) ⊆ V := by
      rw [hmidpt]; exact hlasts
    -- endpoint / cover data for the inductive hypothesis, restricted to `s ∘ castSucc`
    have h0s' : (s ∘ Fin.castSucc) 0 = t (Fin.last n) := by
      simp only [Function.comp_apply, Fin.castSucc_zero]; exact h0s
    have hcovs' : ∀ k : Fin m,
        range (γ.subpath ((s ∘ Fin.castSucc) k.castSucc) ((s ∘ Fin.castSucc) k.succ)) ⊆ U ∨
        range (γ.subpath ((s ∘ Fin.castSucc) k.castSucc) ((s ∘ Fin.castSucc) k.succ)) ⊆ V :=
      fun k => hcovs k.castSucc
    have hcovW' : ∀ k : Fin (n + m),
        range (γ.subpath ((pcat t (s ∘ Fin.castSucc)) k.castSucc)
          ((pcat t (s ∘ Fin.castSucc)) k.succ)) ⊆ U ∨
        range (γ.subpath ((pcat t (s ∘ Fin.castSucc)) k.castSucc)
          ((pcat t (s ∘ Fin.castSucc)) k.succ)) ⊆ V := by
      intro k
      rw [← pcat_comp_castSucc t s]
      exact hcovW k.castSucc
    have h0W' : (pcat t (s ∘ Fin.castSucc)) 0 = x₀ := by
      rw [← pcat_comp_castSucc t s, Function.comp_apply, Fin.castSucc_zero]; exact h0W
    have B : (pcat t (s ∘ Fin.castSucc)) (Fin.last (n + m)) = s (Fin.castSucc (Fin.last m)) :=
      pcat_last t (s ∘ Fin.castSucc)
    -- factor the right span (over `s`) : peel its last cell
    have hRHS_eq : descSpan U V hUV u v huv γ (t (Fin.last n)) (s (Fin.last (m + 1))) s h0s rfl hcovs
        = descSpan U V hUV u v huv γ (t (Fin.last n)) (s (Fin.castSucc (Fin.last m)))
            (s ∘ Fin.castSucc) h0s' rfl hcovs'
          ≫ descPiece U V hUV u v huv
              (γ.subpath (s (Fin.castSucc (Fin.last m))) (s (Fin.last (m + 1)))) hlasts := by
      rw [descSpan_peel_last U V hUV u v huv γ (t (Fin.last n)) (s (Fin.last (m + 1))) s h0s rfl
        hcovs hlasts]
    -- factor the glued span : peel its last cell, then reparametrise the head to `pcat t (s∘cs)`
    have hLHS_eq : descSpan U V hUV u v huv γ x₀ (s (Fin.last (m + 1))) (pcat t s) h0W
          (pcat_last t s) hcovW
        = descSpan (n := n + m) U V hUV u v huv γ x₀ (s (Fin.castSucc (Fin.last m)))
            (pcat t (s ∘ Fin.castSucc)) h0W' B hcovW'
          ≫ descPiece U V hUV u v huv
              (γ.subpath (s (Fin.castSucc (Fin.last m))) (s (Fin.last (m + 1)))) hlasts := by
      rw [descSpan_peel_last (n := n + m) U V hUV u v huv γ x₀ (s (Fin.last (m + 1)))
            (pcat (m := m + 1) t s) h0W (pcat_last t s) hcovW hlastW,
          descSpan_partition_congr (n := n + m) (t := (pcat t s) ∘ Fin.castSucc)
            (t' := pcat t (s ∘ Fin.castSucc)) U V hUV u v huv γ x₀
            ((pcat t s) (Fin.castSucc (Fin.last (n + m)))) (pcat_comp_castSucc t s) _ _ _ h0W'
            (B.trans hmidpt.symm) hcovW',
          descPiece_recast_source U V hUV u v huv γ
            ((pcat t s) (Fin.castSucc (Fin.last (n + m)))) (s (Fin.castSucc (Fin.last m)))
            (s (Fin.last (m + 1))) hmidpt hlastW hlasts,
          ← Category.assoc,
          descSpan_recast_target (n := n + m) U V hUV u v huv γ x₀
            ((pcat t s) (Fin.castSucc (Fin.last (n + m)))) (s (Fin.castSucc (Fin.last m)))
            (pcat t (s ∘ Fin.castSucc)) h0W' (B.trans hmidpt.symm) hcovW' hmidpt]
    rw [hLHS_eq, hRHS_eq, ← Category.assoc]
    exact congrArg
      (· ≫ descPiece U V hUV u v huv
          (γ.subpath (s (Fin.castSucc (Fin.last m))) (s (Fin.last (m + 1)))) hlasts)
      (ih (s ∘ Fin.castSucc) h0s' hcovs' hcovW' h0W')

/-- The left halving map is monotone. -/
theorem monotone_halfL : Monotone halfL := by
  intro x y h
  rw [← Subtype.coe_le_coe] at h ⊢
  simp only [coe_halfL]
  linarith

/-- The right halving map is monotone. -/
theorem monotone_halfR : Monotone halfR := by
  intro x y h
  rw [← Subtype.coe_le_coe] at h ⊢
  simp only [coe_halfR]
  linarith

/-- On the left half, a subpath of `p.trans q` *is* the corresponding subpath of `p`, as a map. -/
theorem coe_trans_subpath_halfL {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x₀ x₁ : I) :
    ⇑((p.trans q).subpath (halfL x₀) (halfL x₁)) = ⇑(p.subpath x₀ x₁) := by
  funext z
  simp only [Path.subpath, Path.coe_mk_mk, Function.comp_apply]
  rw [subpathAux_halfL, trans_halfL]

/-- On the right half, a subpath of `p.trans q` *is* the corresponding subpath of `q`, as a map. -/
theorem coe_trans_subpath_halfR {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x₀ x₁ : I) :
    ⇑((p.trans q).subpath (halfR x₀) (halfR x₁)) = ⇑(q.subpath x₀ x₁) := by
  funext z
  simp only [Path.subpath, Path.coe_mk_mk, Function.comp_apply]
  rw [subpathAux_halfR, trans_halfR]

/-- Ranges agree on the left half. -/
theorem range_trans_subpath_halfL {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x₀ x₁ : I) :
    range ((p.trans q).subpath (halfL x₀) (halfL x₁)) = range (p.subpath x₀ x₁) := by
  rw [coe_trans_subpath_halfL]

/-- Ranges agree on the right half. -/
theorem range_trans_subpath_halfR {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (x₀ x₁ : I) :
    range ((p.trans q).subpath (halfR x₀) (halfR x₁)) = range (q.subpath x₀ x₁) := by
  rw [coe_trans_subpath_halfR]

/-- **Cells of a combined partition.**  When the two blocks meet (`t (last n) = s 0`), every cell of
`pcat t s` is a cell of `t` or a cell of `s`. -/
theorem pcat_cell {n m : ℕ} (t : Fin (n + 1) → I) (s : Fin (m + 1) → I)
    (hmid : t (Fin.last n) = s 0) (k : Fin (n + m)) :
    (∃ j : Fin n, pcat t s k.castSucc = t j.castSucc ∧ pcat t s k.succ = t j.succ) ∨
    (∃ j : Fin m, pcat t s k.castSucc = s j.castSucc ∧ pcat t s k.succ = s j.succ) := by
  have hk' := k.isLt
  by_cases hk : (k : ℕ) < n
  · refine Or.inl ⟨⟨(k : ℕ), hk⟩, ?_, ?_⟩
    · rw [pcat_apply, dif_pos (by simp only [Fin.val_castSucc]; exact hk)]
      exact congrArg t (Fin.ext (by simp))
    · rw [pcat_apply]
      by_cases hk1 : (k : ℕ) + 1 < n
      · rw [dif_pos (by simp only [Fin.val_succ]; exact hk1)]
        exact congrArg t (Fin.ext (by simp))
      · rw [dif_neg (by simp only [Fin.val_succ]; exact hk1),
            show (⟨(k : ℕ), hk⟩ : Fin n).succ = Fin.last n from
              Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega),
            hmid]
        exact congrArg s (Fin.ext (by simp only [Fin.val_succ, Fin.val_zero]; omega))
  · refine Or.inr ⟨⟨(k : ℕ) - n, by omega⟩, ?_, ?_⟩
    · rw [pcat_apply, dif_neg (by simp only [Fin.val_castSucc]; exact hk)]
      exact congrArg s (Fin.ext (by simp))
    · rw [pcat_apply, dif_neg (by simp only [Fin.val_succ]; omega)]
      exact congrArg s (Fin.ext (by simp only [Fin.val_succ, Fin.val_succ]; omega))

/-- **Reparametrization of a span.**  If `φ : I → I` carries the path `γ` onto the path `δ` — both
pointwise and on subpaths — then the span of `γ` over the reparametrized partition `φ ∘ t` is the
span of `δ` over `t`, conjugated by the endpoint identifications. -/
theorem descSpan_reparam (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b a' b' : X} (γ : Path a b) (δ : Path a' b') (φ : I → I)
    (hφ : ∀ x : I, γ (φ x) = δ x)
    (hsub : ∀ x y : I, ⇑(γ.subpath (φ x) (φ y)) = ⇑(δ.subpath x y))
    (x₀ x₁ y₀ y₁ : I) {n : ℕ} (t : Fin (n + 1) → I)
    (h0 : t 0 = x₀) (h1 : t (Fin.last n) = x₁)
    (hy0 : (φ ∘ t) 0 = y₀) (hy1 : (φ ∘ t) (Fin.last n) = y₁)
    (hey0 : γ y₀ = δ x₀) (hey1 : γ y₁ = δ x₁)
    (hcovγ : ∀ k : Fin n, range (γ.subpath ((φ ∘ t) k.castSucc) ((φ ∘ t) k.succ)) ⊆ U ∨
                 range (γ.subpath ((φ ∘ t) k.castSucc) ((φ ∘ t) k.succ)) ⊆ V)
    (hcovδ : ∀ k : Fin n, range (δ.subpath (t k.castSucc) (t k.succ)) ⊆ U ∨
                 range (δ.subpath (t k.castSucc) (t k.succ)) ⊆ V) :
    descSpan U V hUV u v huv γ y₀ y₁ (φ ∘ t) hy0 hy1 hcovγ
      = eqToHom (congrArg (descObj U V hUV u v) hey0)
        ≫ descSpan U V hUV u v huv δ x₀ x₁ t h0 h1 hcovδ
        ≫ eqToHom (congrArg (descObj U V hUV u v) hey1.symm) := by
  have hP : γ ∘ (φ ∘ t) = δ ∘ t := funext fun i => hφ (t i)
  have hF : ∀ k : Fin n, HEq (γ.subpath ((φ ∘ t) k.castSucc) ((φ ∘ t) k.succ))
      (δ.subpath (t k.castSucc) (t k.succ)) := fun k =>
    path_heq_of_ends _ _ (hφ _) (hφ _) fun z => congrFun (hsub (t k.castSucc) (t k.succ)) z
  simp only [descSpan, descChainI]
  rw [descChain_path_congr U V hUV u v huv hP
      (fun k : Fin n => γ.subpath ((φ ∘ t) k.castSucc) ((φ ∘ t) k.succ))
      (fun k : Fin n => δ.subpath (t k.castSucc) (t k.succ)) hF hcovγ hcovδ]
  simp

/-- The descended morphism is multiplicative on concatenation of paths. -/
theorem descHom_trans (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b c : X} (p : Path a b) (q : Path b c) :
    descHom U V hUopen hVopen hUV u v huv (p.trans q)
      = descHom U V hUopen hVopen hUV u v huv p ≫ descHom U V hUopen hVopen hUV u v huv q := by
  obtain ⟨n, t, h0t, h1t, htmono, hcovt⟩ := exists_subpath_cover U V hUopen hVopen hUV p
  obtain ⟨m, s, h0s, h1s, hsmono, hcovs⟩ := exists_subpath_cover U V hUopen hVopen hUV q
  -- a genuine subdivision has at least one cell
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have h01 : (0 : I) = 1 :=
        h0t.symm.trans ((congrArg t (Fin.ext rfl : (0 : Fin (0 + 1)) = Fin.last 0)).trans h1t)
      have hval := congrArg Subtype.val h01
      simp at hval
    · exact hpos
  -- the two rescaled partitions, and the glued partition of `p.trans q`
  have hmid : (halfL ∘ t) (Fin.last n) = (halfR ∘ s) 0 := by
    simp only [Function.comp_apply, h1t, h0s, halfL_one, halfR_zero]
  have h0L : (halfL ∘ t) 0 = 0 := by
    simp only [Function.comp_apply, h0t, halfL_zero]
  have hWlast : (halfR ∘ s) (Fin.last m) = 1 := by
    simp only [Function.comp_apply, h1s, halfR_one]
  have hW0 : pcat (halfL ∘ t) (halfR ∘ s) 0 = 0 := (pcat_zero hn _ _).trans h0L
  have hW1 : pcat (halfL ∘ t) (halfR ∘ s) (Fin.last (n + m)) = 1 :=
    (pcat_last _ _).trans hWlast
  have hWmono : Monotone (pcat (halfL ∘ t) (halfR ∘ s)) :=
    pcat_mono _ _ (monotone_halfL.comp htmono) (monotone_halfR.comp hsmono) hmid
  -- cover-adaptedness of each block, and of the glued partition
  have hcovL : ∀ k : Fin n,
      range ((p.trans q).subpath ((halfL ∘ t) k.castSucc) ((halfL ∘ t) k.succ)) ⊆ U ∨
      range ((p.trans q).subpath ((halfL ∘ t) k.castSucc) ((halfL ∘ t) k.succ)) ⊆ V := by
    intro k
    simpa only [Function.comp_apply, range_trans_subpath_halfL] using hcovt k
  have hcovR : ∀ k : Fin m,
      range ((p.trans q).subpath ((halfR ∘ s) k.castSucc) ((halfR ∘ s) k.succ)) ⊆ U ∨
      range ((p.trans q).subpath ((halfR ∘ s) k.castSucc) ((halfR ∘ s) k.succ)) ⊆ V := by
    intro k
    simpa only [Function.comp_apply, range_trans_subpath_halfR] using hcovs k
  have hcovW : ∀ k : Fin (n + m),
      range ((p.trans q).subpath (pcat (halfL ∘ t) (halfR ∘ s) k.castSucc)
        (pcat (halfL ∘ t) (halfR ∘ s) k.succ)) ⊆ U ∨
      range ((p.trans q).subpath (pcat (halfL ∘ t) (halfR ∘ s) k.castSucc)
        (pcat (halfL ∘ t) (halfR ∘ s) k.succ)) ⊆ V := by
    intro k
    rcases pcat_cell (halfL ∘ t) (halfR ∘ s) hmid k with ⟨j, e1, e2⟩ | ⟨j, e1, e2⟩
    · rw [e1, e2]; exact hcovL j
    · rw [e1, e2]; exact hcovR j
  -- endpoint identifications for the two halves
  have hey1L : (p.trans q) ((halfL ∘ t) (Fin.last n)) = p 1 := by
    simp only [Function.comp_apply, h1t]; exact trans_halfL p q 1
  have hey0L : (p.trans q) (0 : I) = p 0 := (p.trans q).source.trans p.source.symm
  have hey0R : (p.trans q) ((halfL ∘ t) (Fin.last n)) = q 0 :=
    hey1L.trans (p.target.trans q.source.symm)
  have hey1R : (p.trans q) ((halfR ∘ s) (Fin.last m)) = q 1 := by
    simp only [Function.comp_apply, h1s]; exact trans_halfR p q 1
  -- split the glued span into the two blocks, then reparametrize each block
  have hA := (descSpan_recast_target U V hUV u v huv (p.trans q) 0
      ((halfR ∘ s) (Fin.last m)) 1 (pcat (halfL ∘ t) (halfR ∘ s)) hW0 (pcat_last _ _) hcovW
      hWlast).symm
  have hB := descSpan_append U V hUV u v huv (p.trans q) 0 (halfL ∘ t) h0L hcovL
      (halfR ∘ s) hmid.symm hcovR hcovW hW0
  have hC := descSpan_reparam U V hUV u v huv (p.trans q) p halfL (trans_halfL p q)
      (coe_trans_subpath_halfL p q) 0 1 0 ((halfL ∘ t) (Fin.last n)) t h0t h1t h0L rfl
      hey0L hey1L hcovL hcovt
  have hD := descSpan_reparam U V hUV u v huv (p.trans q) q halfR (trans_halfR p q)
      (coe_trans_subpath_halfR p q) 0 1 ((halfL ∘ t) (Fin.last n)) ((halfR ∘ s) (Fin.last m)) s
      h0s h1s hmid.symm rfl hey0R hey1R hcovR hcovs
  rw [← descHom_eq_descChainPath U V hUopen hVopen hUV u v huv (p.trans q) _ hWmono hW0 hW1 hcovW,
      ← descHom_eq_descChainPath U V hUopen hVopen hUV u v huv p t htmono h0t h1t hcovt,
      ← descHom_eq_descChainPath U V hUopen hVopen hUV u v huv q s hsmono h0s h1s hcovs,
      descChainPath_eq_span U V hUV u v huv (p.trans q) _ hW0 hW1 hcovW,
      descChainPath_eq_span U V hUV u v huv p t h0t h1t hcovt,
      descChainPath_eq_span U V hUV u v huv q s h0s h1s hcovs,
      hA, hB, hC, hD]
  simp

/-- For a path lying entirely in `U`, the descended morphism is its `U`-local morphism. -/
theorem descHom_eq_descLocU (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ U) :
    descHom U V hUopen hVopen hUV u v huv γ
      = descLocU U V hUV u v γ hγ (hγ ⟨0, γ.source⟩) (hγ ⟨1, γ.target⟩) := by
  unfold descHom
  exact descChainPath_eq_descLocU U V hUV u v huv γ hγ _ _ _ _

/-- For a path lying entirely in `V`, the descended morphism is its `V`-local morphism. -/
theorem descHom_eq_descLocV (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v)
    {a b : X} (γ : Path a b) (hγ : range γ ⊆ V) :
    descHom U V hUopen hVopen hUV u v huv γ
      = descLocV U V hUV u v huv γ hγ (hγ ⟨0, γ.source⟩) (hγ ⟨1, γ.target⟩) := by
  unfold descHom
  exact descChainPath_eq_descLocV U V hUV u v huv γ hγ _ _ _ _

/-- The descended morphism of the constant path is the identity. -/
theorem descHom_refl (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : U ∪ V = univ)
    {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v) (x : X) :
    descHom U V hUopen hVopen hUV u v huv (Path.refl x) = 𝟙 (descObj U V hUV u v x) := by
  have hx : x ∈ U ∪ V := by rw [hUV]; exact mem_univ x
  rcases hx with hU | hV
  · have hr : range (Path.refl x) ⊆ U := by
      rw [Path.refl_range]; exact Set.singleton_subset_iff.2 hU
    rw [descHom_eq_descLocU U V hUopen hVopen hUV u v huv (Path.refl x) hr]
    exact descLocU_refl U V hUV u v x hU hr
  · have hr : range (Path.refl x) ⊆ V := by
      rw [Path.refl_range]; exact Set.singleton_subset_iff.2 hV
    rw [descHom_eq_descLocV U V hUopen hVopen hUV u v huv (Path.refl x) hr]
    exact descLocV_refl U V hUV u v huv x hV hr

/-- **Seifert–van Kampen, existence half.**  For an open cover `X = U ∪ V` and a category `H`, any
pair of functors `u : π(U) ⥤ H`, `v : π(V) ⥤ H` agreeing after restriction along the inclusions of
`π(U ∩ V)` descends to a functor `F : π(X) ⥤ H` restricting to `u` on `π(U)` and to `v` on `π(V)`.

The functor is built by subdividing paths into cover-supported pieces (`Generation.lean`) and
mapping each piece by `u` or `v`; well-definedness up to homotopy is the two-dimensional grid
subdivision of `Subdivision2D.lean`. -/
theorem exists_descended_functor (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUV : U ∪ V = univ) {H : Type v} [Category.{w} H]
    (u : FundamentalGroupoid U ⥤ H) (v : FundamentalGroupoid V ⥤ H)
    (huv : FundamentalGroupoid.map (inclUW U V) ⋙ u
         = FundamentalGroupoid.map (inclVW U V) ⋙ v) :
    ∃ F : FundamentalGroupoid X ⥤ H,
      FundamentalGroupoid.map (inclUX U) ⋙ F = u ∧
      FundamentalGroupoid.map (inclVX V) ⋙ F = v := by
  -- Assemble the descended functor from `descHom`.
  refine ⟨{
      obj := fun x => descObj U V hUV u v x.as
      map := fun {x y} f => Quotient.liftOn f
          (fun γ => descHom U V hUopen hVopen hUV u v huv γ)
          (fun γ γ' h => descHom_homotopic U V hUopen hVopen hUV u v huv γ γ' h)
      map_id := ?_
      map_comp := ?_ }, ?_, ?_⟩
  · -- `F.map (𝟙 x) = 𝟙 (F.obj x)`
    intro x
    rw [FundamentalGroupoid.id_eq_path_refl]
    exact descHom_refl U V hUopen hVopen hUV u v huv x.as
  · -- `F.map (f ≫ g) = F.map f ≫ F.map g`
    intro x y z f g
    induction f using Quotient.inductionOn with
    | h p =>
      induction g using Quotient.inductionOn with
      | h q =>
        show descHom U V hUopen hVopen hUV u v huv (p.trans q)
          = descHom U V hUopen hVopen hUV u v huv p ≫ descHom U V hUopen hVopen hUV u v huv q
        exact descHom_trans U V hUopen hVopen hUV u v huv p q
  · -- `map (inclUX U) ⋙ F = u`
    refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y δ => ?_)
    · exact descObj_of_mem_U U V hUV u v x.as.1 x.as.2
    · induction δ using Quotient.inductionOn with
      | h ρ =>
        have hrng : range (ρ.map continuous_subtype_val) ⊆ U := by
          rintro _ ⟨s, rfl⟩; exact (ρ s).2
        have hlift : ∀ (ha : (↑x.as : X) ∈ U) (hb : (↑y.as : X) ∈ U),
            liftPath U (ρ.map continuous_subtype_val) hrng ha hb = ρ :=
          fun _ _ => by ext t; rfl
        show descHom U V hUopen hVopen hUV u v huv (ρ.map continuous_subtype_val)
          = eqToHom _ ≫ u.map ⟦ρ⟧ ≫ eqToHom _
        rw [descHom_eq_descLocU U V hUopen hVopen hUV u v huv (ρ.map continuous_subtype_val) hrng]
        simp only [descLocU, hlift]
  · -- `map (inclVX V) ⋙ F = v`
    refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y δ => ?_)
    · exact descObj_of_mem_V U V hUV u v huv x.as.1 x.as.2
    · induction δ using Quotient.inductionOn with
      | h ρ =>
        have hrng : range (ρ.map continuous_subtype_val) ⊆ V := by
          rintro _ ⟨s, rfl⟩; exact (ρ s).2
        have hlift : ∀ (ha : (↑x.as : X) ∈ V) (hb : (↑y.as : X) ∈ V),
            liftPath V (ρ.map continuous_subtype_val) hrng ha hb = ρ :=
          fun _ _ => by ext t; rfl
        show descHom U V hUopen hVopen hUV u v huv (ρ.map continuous_subtype_val)
          = eqToHom _ ≫ v.map ⟦ρ⟧ ≫ eqToHom _
        rw [descHom_eq_descLocV U V hUopen hVopen hUV u v huv (ρ.map continuous_subtype_val) hrng]
        simp only [descLocV, hlift]

/-- **Seifert–van Kampen (groupoid form).**  For an open cover `X = U ∪ V`, the fundamental
groupoid of `X` is the pushout of `π(U)` and `π(V)` over `π(U ∩ V)` in the category `Grpd` of
groupoids.  Existence of the mediating functor is `exists_descended_functor`; its uniqueness is
`functor_ext_of_restrictions`. -/
theorem isPushout (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) :
    IsPushout (mapUW U V) (mapVW U V) (mapUX U) (mapVX V) := by
  refine IsPushout.of_isColimit
    (PushoutCocone.isColimitAux'
      (PushoutCocone.mk (mapUX U) (mapVX V) (commSq U V).w) (fun s => ?_))
  -- `s` is a competing cocone: functors `s.inl : π(U) ⥤ s.pt`, `s.inr : π(V) ⥤ s.pt` that
  -- agree after restriction to `π(U ∩ V)`.
  have hcond : FundamentalGroupoid.map (inclUW U V) ⋙ s.inl
      = FundamentalGroupoid.map (inclVW U V) ⋙ s.inr := by
    have h := s.condition
    simpa [mapUW, mapVW, Grpd.comp_eq_comp] using h
  -- The goal is `Type`-valued (a `Subtype`), so extract the functor with `Exists.choose`.
  set hex := exists_descended_functor U V hU hV hUV s.inl s.inr hcond with hexdef
  set F := hex.choose with hFdef
  have hFU : FundamentalGroupoid.map (inclUX U) ⋙ F = s.inl := hex.choose_spec.1
  have hFV : FundamentalGroupoid.map (inclVX V) ⋙ F = s.inr := hex.choose_spec.2
  refine ⟨F, ?_, ?_, ?_⟩
  · -- `mapUX U ≫ F = s.inl`
    simpa [mapUX, Grpd.comp_eq_comp] using hFU
  · -- `mapVX V ≫ F = s.inr`
    simpa [mapVX, Grpd.comp_eq_comp] using hFV
  · -- uniqueness of the mediating functor, from `functor_ext_of_restrictions`
    intro m hmU hmV
    have huEq : FundamentalGroupoid.map (inclUX U) ⋙ m
        = FundamentalGroupoid.map (inclUX U) ⋙ F := by
      have h1 : FundamentalGroupoid.map (inclUX U) ⋙ m = s.inl := by
        simpa [mapUX, Grpd.comp_eq_comp] using hmU
      rw [h1, ← hFU]
    have hvEq : FundamentalGroupoid.map (inclVX V) ⋙ m
        = FundamentalGroupoid.map (inclVX V) ⋙ F := by
      have h1 : FundamentalGroupoid.map (inclVX V) ⋙ m = s.inr := by
        simpa [mapVX, Grpd.comp_eq_comp] using hmV
      rw [h1, ← hFV]
    exact functor_ext_of_restrictions m F U V hU hV hUV huEq hvEq

end Rigidity.RET.VanKampen
