/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Coinduced

/-!
# A coinduced module and the local conditions inherited by the subgroup

Restriction to a subgroup of a subgroup is restriction to the ambient group read through the
inclusion, so a class which dies on a subgroup dies on every subgroup of it.  Shapiro's map is
restriction to the subgroup one coinduces from followed by evaluation at the neutral element, and
both of those commute with restricting further.

So suppose every member of a family of subgroups of the subgroup one coinduces from is contained in
a member of a family of subgroups of the whole group.  Then Shapiro's map carries the classes
trivial on the second family to classes trivial on the first, and being injective it leaves nothing
behind: a coinduced module has no everywhere locally trivial class as soon as the module one
coinduces has none for the family the subgroup inherits.

Over a number field the family is the decomposition subgroups, and the subgroups a finite extension
inherits from them are again decomposition subgroups, of that extension.  So the local-global
obstruction of a module coinduced from a finite extension is the obstruction of the extension
itself, which is Shapiro's lemma for the everywhere locally trivial classes.  This is a mechanism
for vanishing quite different from asking the coefficients to be cohomologically trivial: it works
for the trivial module coinduced from the whole group, which is never free.

## Main definitions

* `InverseGalois.CFT.subgroupInclusion`: the inclusion of a subgroup of a subgroup into a subgroup
  of the ambient group containing it.

## Main results

* `InverseGalois.CFT.resH1_resH1_eq_one_of_le`, `InverseGalois.CFT.resH2_resH2_eq_one_of_le`: a
  class which dies on a subgroup dies on every subgroup of it.
* `InverseGalois.CFT.sha1_smoothCoind_eq_bot_of_sha1`,
  `InverseGalois.CFT.sha2_smoothCoind_eq_bot_of_sha2`: **a coinduced module has no everywhere
  locally trivial class**, in either degree, as soon as the module one coinduces has none for the
  family of subgroups the subgroup inherits.
* `InverseGalois.CFT.sha1_smoothCoind_eq_bot_of_comap`,
  `InverseGalois.CFT.sha2_smoothCoind_eq_bot_of_comap`: the same for the family cut out on the
  subgroup by meeting it with the subgroups of the ambient family.

## Tags

profinite group, Galois cohomology, coinduced module, Shapiro's lemma, local-global principle
-/

namespace InverseGalois.CFT

/-! ### Restriction to a subgroup of a subgroup -/

section Inclusion

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G}

/-- **The inclusion of a subgroup of a subgroup** into a subgroup of the ambient group containing
it. -/
def subgroupInclusion (D' : Subgroup ↥H) {D : Subgroup G}
    (hle : ∀ x : ↥D', ((x : ↥H) : G) ∈ D) : ↥D' →* ↥D where
  toFun x := ⟨((x : ↥H) : G), hle x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inclusion of a subgroup of a subgroup is continuous. -/
theorem continuous_subgroupInclusion (D' : Subgroup ↥H) {D : Subgroup G}
    (hle : ∀ x : ↥D', ((x : ↥H) : G) ∈ D) : Continuous (subgroupInclusion D' hle) :=
  Continuous.subtype_mk ((continuous_subtype H).comp (continuous_subtype D')) _

variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- **A class of the first cohomology which dies on a subgroup dies on every subgroup of it.** -/
theorem resH1_resH1_eq_one_of_le (D' : Subgroup ↥H) {D : Subgroup G}
    (hle : ∀ x : ↥D', ((x : ↥H) : G) ∈ D) {c : SmoothH1 G M} (h : resH1 D c = 1) :
    resH1 D' (resH1 H c) = 1 := by
  have key : resH1 D' (resH1 H c)
      = comapH1 (subgroupInclusion D' hle) (fun _ _ => rfl)
        (isSmoothHom_of_continuous (continuous_subgroupInclusion D' hle)) (resH1 D c) := by
    obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective c
    rfl
  rw [key, h, _root_.map_one]

/-- **A class of the second cohomology which dies on a subgroup dies on every subgroup of it.** -/
theorem resH2_resH2_eq_one_of_le (D' : Subgroup ↥H) {D : Subgroup G}
    (hle : ∀ x : ↥D', ((x : ↥H) : G) ∈ D) {c : SmoothH2 G M} (h : resH2 D c = 1) :
    resH2 D' (resH2 H c) = 1 := by
  have key : resH2 D' (resH2 H c)
      = comapH2 (subgroupInclusion D' hle) (fun _ _ => rfl)
        (isSmoothHom_of_continuous (continuous_subgroupInclusion D' hle)) (resH2 D c) := by
    obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective c
    rfl
  rw [key, h, _root_.map_one]

end Inclusion

/-! ### The everywhere locally trivial classes of a coinduced module -/

section Coind

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) (M : Type*) [CommGroup M]
  [MulDistribMulAction ↥H M]

/-- **Shapiro's map commutes with restricting further**, both of its two steps being composition
of the cocycle with something. -/
theorem resH1_smoothShapiroH1 (D' : Subgroup ↥H) (c : SmoothH1 G ↥(smoothCoind H M)) :
    resH1 D' (smoothShapiroH1 H M c)
      = coeffH1 (smoothCoindEval H M) (fun (g : ↥D') f => smoothCoindEval_smul (g : ↥H) f)
        (resH1 D' (resH1 H c)) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective c
  rfl

/-- **Shapiro's map commutes with restricting further**, both of its two steps being composition
of the cocycle with something. -/
theorem resH2_smoothShapiroH2 (D' : Subgroup ↥H) (c : SmoothH2 G ↥(smoothCoind H M)) :
    resH2 D' (smoothShapiroH2 H M c)
      = coeffH2 (smoothCoindEval H M) (fun (g : ↥D') f => smoothCoindEval_smul (g : ↥H) f)
        (resH2 D' (resH2 H c)) := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective c
  rfl

variable {H M}

/-- **A coinduced module has no everywhere locally trivial class in the first cohomology** as soon
as the module one coinduces has none for the family of subgroups the subgroup inherits.  Shapiro's
map sends a class trivial on the ambient family to a class trivial on the inherited one, because
each member of the inherited family sits inside a member of the ambient one; and Shapiro's map is
injective in this degree with no hypothesis at all. -/
theorem sha1_smoothCoind_eq_bot_of_sha1 {S : Set (Subgroup G)} {S' : Set (Subgroup ↥H)}
    (hS' : ∀ D' ∈ S', ∃ D ∈ S, ∀ x : ↥D', ((x : ↥H) : G) ∈ D) (hM : sha1 M S' = ⊥) :
    sha1 ↥(smoothCoind H M) S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
  refine (injective_iff_map_eq_one _).1 smoothShapiroH1_injective c ?_
  refine (Subgroup.eq_bot_iff_forall _).1 hM _ (mem_sha1.2 fun D' hD' => ?_)
  obtain ⟨D, hD, hle⟩ := hS' D' hD'
  rw [resH1_smoothShapiroH1 H M D' c,
    resH1_resH1_eq_one_of_le D' hle (mem_sha1.1 hc D hD), _root_.map_one]

/-- **A coinduced module has no everywhere locally trivial class in the second cohomology** as soon
as the module one coinduces has none for the family of subgroups the subgroup inherits.  Shapiro's
map sends a class trivial on the ambient family to a class trivial on the inherited one, because
each member of the inherited family sits inside a member of the ambient one; and Shapiro's map is
injective in this degree for a normal subgroup with an open normal core. -/
theorem sha2_smoothCoind_eq_bot_of_sha2 [H.Normal] (hcore : HasOpenNormalCore H)
    {S : Set (Subgroup G)} {S' : Set (Subgroup ↥H)}
    (hS' : ∀ D' ∈ S', ∃ D ∈ S, ∀ x : ↥D', ((x : ↥H) : G) ∈ D) (hM : sha2 M S' = ⊥) :
    sha2 ↥(smoothCoind H M) S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
  refine (injective_iff_map_eq_one _).1 (smoothShapiroH2_injective hcore) c ?_
  refine (Subgroup.eq_bot_iff_forall _).1 hM _ (mem_sha2.2 fun D' hD' => ?_)
  obtain ⟨D, hD, hle⟩ := hS' D' hD'
  rw [resH2_smoothShapiroH2 H M D' c,
    resH2_resH2_eq_one_of_le D' hle (mem_sha2.1 hc D hD), _root_.map_one]

omit [TopologicalSpace G] in
/-- The family a subgroup inherits by meeting a family of subgroups of the ambient group. -/
theorem exists_mem_of_mem_image_comap {S : Set (Subgroup G)} {D' : Subgroup ↥H}
    (hD' : D' ∈ (fun D : Subgroup G => D.comap H.subtype) '' S) :
    ∃ D ∈ S, ∀ x : ↥D', ((x : ↥H) : G) ∈ D := by
  obtain ⟨D, hD, rfl⟩ := hD'
  exact ⟨D, hD, fun x => x.2⟩

/-- **A coinduced module has no everywhere locally trivial class in the first cohomology** as soon
as the module one coinduces has none for the subgroups cut out on the subgroup by the family. -/
theorem sha1_smoothCoind_eq_bot_of_comap {S : Set (Subgroup G)}
    (hM : sha1 M ((fun D : Subgroup G => D.comap H.subtype) '' S) = ⊥) :
    sha1 ↥(smoothCoind H M) S = ⊥ :=
  sha1_smoothCoind_eq_bot_of_sha1 (fun _ hD' => exists_mem_of_mem_image_comap hD') hM

/-- **A coinduced module has no everywhere locally trivial class in the second cohomology** as soon
as the module one coinduces has none for the subgroups cut out on the subgroup by the family. -/
theorem sha2_smoothCoind_eq_bot_of_comap [H.Normal] (hcore : HasOpenNormalCore H)
    {S : Set (Subgroup G)}
    (hM : sha2 M ((fun D : Subgroup G => D.comap H.subtype) '' S) = ⊥) :
    sha2 ↥(smoothCoind H M) S = ⊥ :=
  sha2_smoothCoind_eq_bot_of_sha2 hcore (fun _ hD' => exists_mem_of_mem_image_comap hD') hM

end Coind

end InverseGalois.CFT
