/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.GenerationGroup

/-!
# Filling in a puncture is surjective on fundamental groups

Removing punctures from the plane can only lose loops, never gain them: if `T ⊆ S` are finite sets
of punctures, every loop in `ℂ ∖ T` is homotopic to one avoiding `S` as well, so the inclusion
`ℂ ∖ S ↪ ℂ ∖ T` induces a **surjection** of fundamental groups.

One puncture is filled in at a time.  Around the puncture `s` being filled in take a disc small
enough to miss the other punctures; the disc and the complement of `s` cover `ℂ ∖ T`, they overlap
in a punctured disc, and all three are path connected.  Seifert–van Kampen in its generation form
(`Rigidity.RET.VanKampen.closure_range_pi1_union_of_pathConnected`, which asks nothing of the
overlap beyond path connectedness) then writes every loop in terms of loops in the disc — which are
null-homotopic, the disc being convex — and loops missing `s`.

## Main results

* `Rigidity.RET.isPathConnected_ball_diff_singleton` — a punctured disc in `ℂ` is path connected.
* `Rigidity.RET.surjective_pi1Punct_erase` — filling in one puncture is surjective on `π₁`.
* `Rigidity.RET.surjective_pi1Punct` — filling in any set of punctures is surjective on `π₁`.
-/

universe u v

open CategoryTheory Set FundamentalGroupoid

noncomputable section

namespace Rigidity.RET

/-! ### Moving the basepoint of a surjectivity statement -/

/-- **A functor of groupoids surjective on one vertex group is surjective on any vertex group
connected to it.**  Conjugating by the connecting morphism and its image moves a preimage from one
basepoint to the other. -/
theorem surjective_mapEnd_of_hom {C : Type*} [Groupoid.{v} C] {D : Type*} [Groupoid.{v} D]
    (F : C ⥤ D) {c₀ c₁ : C} (d : c₀ ⟶ c₁) (h : Function.Surjective (F.mapEnd c₁)) :
    Function.Surjective (F.mapEnd c₀) := by
  intro α
  obtain ⟨γ, hγ⟩ := h (Groupoid.inv (F.map d) ≫ α ≫ F.map d)
  have hγ' : F.map γ = Groupoid.inv (F.map d) ≫ α ≫ F.map d := hγ
  refine ⟨d ≫ γ ≫ Groupoid.inv d, ?_⟩
  show F.map (d ≫ γ ≫ Groupoid.inv d) = α
  simp only [Groupoid.inv_eq_inv, Functor.map_comp, Functor.map_inv] at hγ' ⊢
  rw [hγ']
  simp

/-! ### The inclusion of a more punctured plane into a less punctured one -/

/-- The inclusion `ℂ ∖ S ↪ ℂ ∖ T` for `T ⊆ S`. -/
def punctureIncl {S T : Set ℂ} (h : T ⊆ S) :
    C({z : ℂ // z ∉ S}, {z : ℂ // z ∉ T}) :=
  ⟨fun p => ⟨p.1, fun hc => p.2 (h hc)⟩, continuous_subtype_val.subtype_mk _⟩

/-- The homomorphism `π₁(ℂ ∖ S) → π₁(ℂ ∖ T)` induced by the inclusion, for `T ⊆ S`. -/
def pi1Punct {S T : Set ℂ} (h : T ⊆ S) {z₀ : ℂ} (hz₀ : z₀ ∉ S) :
    FundamentalGroup {z : ℂ // z ∉ S} ⟨z₀, hz₀⟩ →*
      FundamentalGroup {z : ℂ // z ∉ T} ⟨z₀, fun hc => hz₀ (h hc)⟩ :=
  FundamentalGroup.map (punctureIncl h) ⟨z₀, hz₀⟩

/-! ### A punctured disc is path connected -/

/-- **A disc with its centre removed is path connected.**  It is the image of the path connected
set `(0, r) × ℝ` of polar coordinates under `(ρ, θ) ↦ s + ρ e^{iθ}`. -/
theorem isPathConnected_ball_diff_singleton (s : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball s r \ {s}) := by
  have hconv : Convex ℝ ((Set.Ioo 0 r) ×ˢ (Set.univ : Set ℝ)) :=
    (convex_Ioo 0 r).prod convex_univ
  have hne : ((Set.Ioo 0 r) ×ˢ (Set.univ : Set ℝ)).Nonempty :=
    ⟨(r / 2, 0), ⟨by constructor <;> linarith, Set.mem_univ _⟩⟩
  have hpc := (hconv.isPathConnected hne).image
    (f := fun p : ℝ × ℝ => s + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
    (by fun_prop)
  have himg : (fun p : ℝ × ℝ => s + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
      ((Set.Ioo 0 r) ×ˢ (Set.univ : Set ℝ)) = Metric.ball s r \ {s} := by
    ext z
    constructor
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ0, hρr⟩, -⟩, rfl⟩
      have hρ0' : (0 : ℝ) < ρ := hρ0
      have habs : ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = ρ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hρ0'.le]
      have hsub : s + (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - s
          = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by ring
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, hsub, habs]
        exact hρr
      · simp only [Set.mem_singleton_iff]
        intro hc
        have h0 : (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = 0 := by
          rw [← hsub, hc, sub_self]
        rw [h0, norm_zero] at habs
        exact absurd habs.symm (ne_of_gt hρ0')
    · rintro ⟨hz1, hz2⟩
      have hzs : z - s ≠ 0 := sub_ne_zero.mpr hz2
      refine ⟨(‖z - s‖, Complex.arg (z - s)), ⟨⟨?_, ?_⟩, Set.mem_univ _⟩, ?_⟩
      · exact norm_pos_iff.mpr hzs
      · rw [Metric.mem_ball, dist_eq_norm] at hz1; exact hz1
      · show s + (‖z - s‖ : ℂ) * Complex.exp ((Complex.arg (z - s) : ℂ) * Complex.I) = z
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
  rwa [himg] at hpc

/-! ### Path connectedness inside a subtype -/

/-- **A path connected set contained in a subtype stays path connected there.** -/
theorem pathConnectedSpace_subtype_setOf {X : Type*} [TopologicalSpace X] {p : X → Prop}
    {W : Set X} (hW : IsPathConnected W) (hWp : ∀ x ∈ W, p x) :
    PathConnectedSpace {a : {x : X // p x} | (a : X) ∈ W} := by
  refine isPathConnected_iff_pathConnectedSpace.mp ?_
  exact hW.preimage_coe (U := {x : X | p x}) fun z hz => hWp z hz

/-- **The complement of a countable set in the plane is path connected.** -/
theorem isPathConnected_compl_countable {S : Set ℂ} (hS : S.Countable) :
    IsPathConnected (Sᶜ : Set ℂ) := by
  have h1 : PathConnectedSpace {z : ℂ // z ∉ S} := pathConnectedSpace_punctured hS
  exact isPathConnected_iff_pathConnectedSpace.mpr h1

/-! ### Composing and identifying induced maps on fundamental groups -/

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem fundamentalGroup_map_comp_apply {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (f : C(A, B)) (g : C(B, C)) {a : A}
    (γ : Path.Homotopic.Quotient a a) :
    FundamentalGroup.map g (f a) (FundamentalGroup.map f a γ)
      = FundamentalGroup.map (g.comp f) a γ := by
  induction γ using Quotient.inductionOn with
  | h q => rfl

/-- **Surjectivity passes to the second factor of a composite.**  If the map induced by `g ∘ f` on
fundamental groups is surjective, so is the map induced by `g`. -/
theorem surjective_fundamentalGroup_map_of_comp {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (f : C(A, B)) (g : C(B, C)) (a : A)
    (h : Function.Surjective (FundamentalGroup.map (g.comp f) a)) :
    Function.Surjective (FundamentalGroup.map g (f a)) := by
  intro α
  obtain ⟨γ, hγ⟩ := h α
  exact ⟨FundamentalGroup.map f a γ, by rw [fundamentalGroup_map_comp_apply f g γ, hγ]⟩

/-- **Surjectivity passes to the second factor of a composite**, stated for a map that is only
propositionally equal to the composite. -/
theorem surjective_fundamentalGroup_map_of_eq_comp {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] (f : C(A, B)) (g : C(B, C)) (k : C(A, C))
    (hk : k = g.comp f) (a : A) (h : Function.Surjective (FundamentalGroup.map k a)) :
    Function.Surjective (FundamentalGroup.map g (f a)) := by
  subst hk
  exact surjective_fundamentalGroup_map_of_comp f g a h

/-- The identity induces the identity on fundamental groups. -/
theorem fundamentalGroup_map_id_apply {A : Type*} [TopologicalSpace A] {a : A}
    (γ : Path.Homotopic.Quotient a a) :
    FundamentalGroup.map (ContinuousMap.id A) a γ = γ := by
  induction γ using Quotient.inductionOn with
  | h q => rfl

/-! ### Surjectivity from a simply connected patch -/

/-- **Seifert–van Kampen with a simply connected patch.**  For an open cover `X = U ∪ V` by path
connected sets with path connected overlap and a basepoint in both, if `V` is simply connected then
`π₁(U, x) → π₁(X, x)` is surjective: every loop can be pushed off `V ∖ U`. -/
theorem surjective_pi1U_of_simplyConnected {X : Type u} [TopologicalSpace X] (U V : Set X)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V)
    [PathConnectedSpace ↥(U ∩ V)] [PathConnectedSpace ↥U] [SimplyConnectedSpace ↥V]
    (hUV : U ∪ V = Set.univ) (hUopen : IsOpen U) (hVopen : IsOpen V) :
    Function.Surjective (VanKampen.pi1U U hxU) := by
  haveI : Subsingleton (FundamentalGroup ↥V ⟨x, hxV⟩) :=
    inferInstanceAs (Subsingleton (Path.Homotopic.Quotient (⟨x, hxV⟩ : ↥V) ⟨x, hxV⟩))
  have hgen := VanKampen.closure_range_pi1_union_of_pathConnected U V hxU hxV hUV hUopen hVopen
  have hsub : Set.range (VanKampen.pi1U U hxU) ∪ Set.range (VanKampen.pi1V V hxV)
      ⊆ ((VanKampen.pi1U U hxU).range : Set (FundamentalGroup X x)) := by
    rintro g (⟨β, rfl⟩ | ⟨β, rfl⟩)
    · exact ⟨β, rfl⟩
    · rw [Subsingleton.elim β 1, map_one]
      exact one_mem _
  have hle := (Subgroup.closure_le _).mpr hsub
  rw [hgen] at hle
  exact MonoidHom.range_eq_top.mp (eq_top_iff.mpr hle)

/-! ### Filling in one puncture -/

/-- The part of `ℂ ∖ T` avoiding one further puncture `s`, viewed as `ℂ ∖ insert s T`. -/
def puncturePatch (T : Set ℂ) (s : ℂ) :
    C(↥{w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T}, {z : ℂ // z ∉ insert s T}) :=
  ⟨fun a => ⟨a.1.1, a.2⟩, (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

/-- **Filling in one puncture is surjective on fundamental groups.**  A small disc around the new
puncture is simply connected and meets the rest of the plane in a path connected punctured disc, so
Seifert–van Kampen in its generation form pushes every loop off the disc. -/
theorem surjective_pi1Punct_insert {T : Set ℂ} (hT : T.Finite) {s : ℂ} (hs : s ∉ T)
    {S : Set ℂ} (hS : S = insert s T) {z₀ : ℂ} (hz₀ : z₀ ∉ S) (h : T ⊆ S) :
    Function.Surjective (pi1Punct h hz₀) := by
  classical
  subst hS
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.ball s r ⊆ Tᶜ :=
    Metric.isOpen_iff.mp hT.isClosed.isOpen_compl s hs
  -- a basepoint on the circle of radius `r / 2` about the new puncture
  obtain ⟨b, hbdef⟩ : ∃ b : ℂ, b = s + ((r / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hbball : b ∈ Metric.ball s r := by
    have h1 : b - s = ((r / 2 : ℝ) : ℂ) := by rw [hbdef]; ring
    rw [Metric.mem_ball, dist_eq_norm, h1, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hbs : b ≠ s := by
    intro hc
    have h1 : ((r / 2 : ℝ) : ℂ) = 0 := by rw [hbdef] at hc; linear_combination hc
    rw [Complex.ofReal_eq_zero] at h1
    linarith
  have hbT : b ∉ T := hball hbball
  have hbS : b ∉ insert s T := by
    rw [Set.mem_insert_iff]
    push_neg
    exact ⟨hbs, hbT⟩
  -- the two pieces of the cover of `ℂ ∖ T`
  have hxU : (⟨b, hbT⟩ : {z : ℂ // z ∉ T})
      ∈ {w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T} := hbS
  have hxV : (⟨b, hbT⟩ : {z : ℂ // z ∉ T})
      ∈ {w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r} := hbball
  have hUopen : IsOpen {w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T} :=
    ((hT.insert s).isClosed.isOpen_compl).preimage continuous_subtype_val
  have hVopen : IsOpen {w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hUV : {w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T} ∪
      {w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r} = Set.univ := by
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases hw : (w : ℂ) = s
    · exact Or.inr (by rw [hw]; exact Metric.mem_ball_self hr)
    · exact Or.inl fun hc => (Set.mem_insert_iff.mp hc).elim hw fun hc' => w.2 hc'
  haveI : PathConnectedSpace ↥{w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T} :=
    pathConnectedSpace_subtype_setOf (W := ((insert s T)ᶜ : Set ℂ))
      (isPathConnected_compl_countable (hT.insert s).countable)
      fun z hz hc => hz (Set.mem_insert_of_mem s hc)
  -- the overlap is a punctured disc
  have hinter : {w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T} ∩
      {w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r}
      = {w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r \ {s}} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_insert_iff, not_or]
    exact ⟨fun hw => ⟨hw.2, hw.1.1⟩, fun hw => ⟨⟨hw.2, w.2⟩, hw.1⟩⟩
  haveI : PathConnectedSpace ↥({w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T} ∩
      {w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r}) := by
    rw [hinter]
    exact pathConnectedSpace_subtype_setOf (W := Metric.ball s r \ {s})
      (isPathConnected_ball_diff_singleton s hr) fun z hz => hball hz.1
  -- the disc is contractible, hence simply connected
  haveI : ContractibleSpace ↥(Metric.ball s r) :=
    (convex_ball s r).contractibleSpace ⟨s, Metric.mem_ball_self hr⟩
  haveI : ContractibleSpace ↥{w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r} :=
    Homeomorph.contractibleSpace
      ((subtypeCommHomeo (fun z : ℂ => z ∉ T) (fun z : ℂ => z ∈ Metric.ball s r)).trans
        (subtypeAllHomeo fun a : ↥(Metric.ball s r) => hball a.2))
  -- Seifert–van Kampen: the punctured piece already carries every loop
  have hsurjU := surjective_pi1U_of_simplyConnected
    {w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T}
    {w : {z : ℂ // z ∉ T} | (w : ℂ) ∈ Metric.ball s r} hxU hxV hUV hUopen hVopen
  have hcomp : VanKampen.inclUX {w : {z : ℂ // z ∉ T} | (w : ℂ) ∉ insert s T}
      = (punctureIncl (Set.subset_insert s T)).comp (puncturePatch T s) := rfl
  have hlocal := surjective_fundamentalGroup_map_of_eq_comp (puncturePatch T s)
    (punctureIncl (Set.subset_insert s T)) _ hcomp ⟨⟨b, hbT⟩, hxU⟩ hsurjU
  -- move the basepoint from `b` to `z₀`
  haveI : PathConnectedSpace {z : ℂ // z ∉ insert s T} :=
    pathConnectedSpace_punctured (hT.insert s).countable
  exact surjective_mapEnd_of_hom
    (FundamentalGroupoid.map (punctureIncl (Set.subset_insert s T)))
    (⟦PathConnectedSpace.somePath (⟨z₀, hz₀⟩ : {z : ℂ // z ∉ insert s T}) ⟨b, hbS⟩⟧)
    hlocal

/-! ### Filling in any finite set of punctures -/

/-- **Filling in punctures one at a time.** -/
theorem surjective_pi1Punct_aux : ∀ (A : Finset ℂ) {T : Set ℂ}, T.Finite →
    ∀ {S : Set ℂ}, S = (A : Set ℂ) ∪ T → ∀ {z₀ : ℂ} (hz₀ : z₀ ∉ S) (h : T ⊆ S),
      Function.Surjective (pi1Punct h hz₀) := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro T _ S hSeq z₀ hz₀ h
    have hST : S = T := by rw [hSeq]; simp
    subst hST
    exact fun α => ⟨α, fundamentalGroup_map_id_apply α⟩
  | insert a A' ha ih =>
    intro T hT S hSeq z₀ hz₀ h
    have hSeq' : S = insert a ((A' : Set ℂ) ∪ T) := by
      rw [hSeq, Finset.coe_insert, Set.insert_union]
    by_cases haT : a ∈ (A' : Set ℂ) ∪ T
    · exact ih hT (by rw [hSeq', Set.insert_eq_self.mpr haT]) hz₀ h
    · have hT'S : (A' : Set ℂ) ∪ T ⊆ S := by
        rw [hSeq']; exact Set.subset_insert a _
      have h1 : Function.Surjective (pi1Punct hT'S hz₀) :=
        surjective_pi1Punct_insert (A'.finite_toSet.union hT) haT hSeq' hz₀ hT'S
      have h2 : Function.Surjective
          (pi1Punct (Set.subset_union_right : T ⊆ (A' : Set ℂ) ∪ T)
            (fun hc => hz₀ (hT'S hc))) :=
        ih hT rfl (fun hc => hz₀ (hT'S hc)) Set.subset_union_right
      intro α
      obtain ⟨β, hβ⟩ := h2 α
      obtain ⟨γ, hγ⟩ := h1 β
      refine ⟨γ, ?_⟩
      rw [← hβ, ← hγ]
      exact (fundamentalGroup_map_comp_apply (punctureIncl hT'S)
        (punctureIncl (Set.subset_union_right : T ⊆ (A' : Set ℂ) ∪ T)) γ).symm

/-- **Filling in punctures is surjective on fundamental groups.**  For finite sets `T ⊆ S` of
punctures the inclusion `ℂ ∖ S ↪ ℂ ∖ T` induces a surjection `π₁(ℂ ∖ S) ↠ π₁(ℂ ∖ T)`: every loop
in the less punctured plane is homotopic to one avoiding the extra punctures. -/
theorem surjective_pi1Punct {S T : Set ℂ} (hS : S.Finite) (h : T ⊆ S) {z₀ : ℂ} (hz₀ : z₀ ∉ S) :
    Function.Surjective (pi1Punct h hz₀) := by
  classical
  refine surjective_pi1Punct_aux hS.toFinset (hS.subset h) ?_ hz₀ h
  rw [hS.coe_toFinset]
  exact (Set.union_eq_self_of_subset_right h).symm

end Rigidity.RET

end
