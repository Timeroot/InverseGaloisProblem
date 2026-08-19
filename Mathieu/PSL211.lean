import Mathieu.ActL211
import Mathieu.CoverL211
import Mathieu.FilterL211
import Mathieu.PSL211Simple

/-!
# `PSL(2, 𝔽₁₁)` embeds into `M₁₁`

We assemble an injective homomorphism `PSL(2, ZMod 11) →* M₁₁`, realising the *exceptional*
`2`-transitive action of `PSL(2,11)` on `11` points (NOT the `12`-point projective line).

The concrete data and `native_decide` certificates live in `ActL211.lean`, `CoverL211.lean`
and `FilterL211.lean`.  Here we:

* mark `reps, inKb, cIdx` irreducible (so the abstract proofs treat them as opaque atoms,
  avoiding `whnf`-blowup through the verified enumeration `EnumL211.KK`);
* prove the transversal makes `g • i := cIdx (g * reps i)` a genuine `MulAction` (`one_smul`,
  `mul_smul`), using only `cover` + `distinctb` and the subgroup structure of `K`;
* show the standard generators `T, S` map into `M₁₁` (`psi11_Tmat = m11a`, `psi11_Smat = wS`),
  hence the image lies in `M₁₁` (`range_le`);
* show the kernel is the centre `{±I}` (`ker_eq_center`);
* quotient by the centre to get `PSL(2,𝔽₁₁) = SL(2,𝔽₁₁) ⧸ center ↪ M₁₁` (`embeds`).
-/

namespace Mathieu

open Matrix Equiv
open scoped MatrixGroups

namespace PSL211

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

attribute [local irreducible] reps inKb cIdx

/-! ### `K`-membership facts (the defs are now treated abstractly) -/

lemma inKb_iff (g : SL(2, ZMod 11)) : inKb g = true ↔ g ∈ K := by
  unfold inKb
  rw [decide_eq_true_iff]
  exact (EnumL211.memK_iff g).symm

lemma inKb_one : inKb 1 = true := by
  rw [inKb_iff]; exact one_mem _

lemma inKb_mul {a b : SL(2, ZMod 11)} (ha : inKb a = true) (hb : inKb b = true) :
    inKb (a * b) = true := by
  rw [inKb_iff] at ha hb ⊢; exact mul_mem ha hb

lemma inKb_inv {a : SL(2, ZMod 11)} (ha : inKb a = true) : inKb a⁻¹ = true := by
  rw [inKb_iff] at ha ⊢; exact inv_mem ha

/-- Abstract rearrangements used below. -/
lemma rearr1 (a b c : SL(2, ZMod 11)) : a⁻¹ * b = (a⁻¹ * c) * (b⁻¹ * c)⁻¹ := by group

lemma rearr2 (a g h r d : SL(2, ZMod 11)) :
    a⁻¹ * (g * h * r) = (a⁻¹ * (g * d)) * (d⁻¹ * (h * r)) := by group

/-- `cIdx` is determined by the coset: if `g ∈ reps i · K` then `cIdx g = i`. -/
lemma cIdx_eq (g : SL(2, ZMod 11)) (i : Fin 11) (h : inKb ((reps i)⁻¹ * g) = true) :
    cIdx g = i := by
  have hm := cIdx_mem g
  have hk : inKb ((reps i)⁻¹ * reps (cIdx g)) = true := by
    rw [rearr1 (reps i) (reps (cIdx g)) g]
    exact inKb_mul h (inKb_inv hm)
  exact (distinctb i (cIdx g) hk).symm

/-! ### The action -/

/-- The `SMul` underlying the exceptional action: `g • i := cIdx (g * reps i)`. -/
instance instSMul : SMul (SL(2, ZMod 11)) (Fin 11) := ⟨fun g i => cIdx (g * reps i)⟩

/-- Definitional unfolding of the action, proved once as a `rfl` lemma so that the abstract
proofs never re-trigger the (expensive) `HSMul`/`SMul` defeq. -/
lemma smul_def (g : SL(2, ZMod 11)) (i : Fin 11) : g • i = cIdx (g * reps i) := rfl

/-- The exceptional action of `SL(2, 𝔽₁₁)` on the `11` cosets `Fin 11`. -/
instance act : MulAction (SL(2, ZMod 11)) (Fin 11) where
  one_smul i := by rw [smul_def]; exact oneCIdx i
  mul_smul g h i := by
    rw [smul_def, smul_def, smul_def]
    set j := cIdx (h * reps i) with hj
    have hα : inKb ((reps j)⁻¹ * (h * reps i)) = true := cIdx_mem (h * reps i)
    refine cIdx_eq (g * h * reps i) (cIdx (g * reps j)) ?_
    have hm : inKb ((reps (cIdx (g * reps j)))⁻¹ * (g * reps j)) = true := cIdx_mem (g * reps j)
    rw [rearr2 (reps (cIdx (g * reps j))) g h (reps i) (reps j)]
    exact inKb_mul hm hα

/-- The action homomorphism `SL(2, 𝔽₁₁) →* Perm (Fin 11)`. -/
def psi11 : SL(2, ZMod 11) →* Equiv.Perm (Fin 11) :=
  MulAction.toPermHom (SL(2, ZMod 11)) (Fin 11)

lemma psi11_apply (g : SL(2, ZMod 11)) (i : Fin 11) : psi11 g i = cIdx (g * reps i) := rfl

/-! ### Generators map into `M₁₁` -/

/-- The image of `T = !![1,0;1,1]` is the `11`-cycle `m11a`. -/
theorem psi11_Tmat : psi11 EnumL211.Tmat = m11a :=
  Equiv.ext (fun i => (psi11_apply _ i).trans (tmatPerm i))

lemma wS_mem : wS ∈ M11 := by
  unfold wS
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem m11b_mem m11a_mem)
    (inv_mem m11b_mem)) (pow_mem m11a_mem 3)) m11b_mem) (inv_mem m11a_mem)

/-- The image of `S = !![1,1;0,1]` is the word `wS`, which lies in `M₁₁`. -/
theorem psi11_Smat : psi11 EnumL211.Smat = wS :=
  Equiv.ext (fun i => (psi11_apply _ i).trans (smatPerm i))

/-- **The image of `psi11` lies in `M₁₁`.** -/
theorem range_le : MonoidHom.range psi11 ≤ M11 := by
  rw [MonoidHom.range_eq_map, ← EnumL211.closure_eq_top, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x hx
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [psi11_Smat]; exact wS_mem
  · rw [psi11_Tmat]; exact m11a_mem

/-! ### Faithfulness modulo the centre -/

lemma psi11_eq_one_iff (g : SL(2, ZMod 11)) :
    psi11 g = 1 ↔ ∀ i, cIdx (g * reps i) = i := by
  rw [Equiv.Perm.ext_iff]
  simp only [psi11_apply, Equiv.Perm.coe_one, id_eq]

/-- `-1` acts trivially, so it lies in the kernel. -/
lemma psi11_neg_one : psi11 (-1 : SL(2, ZMod 11)) = 1 :=
  (psi11_eq_one_iff _).2 negCIdx

/-- **The kernel of the action is exactly the centre of `SL(2, 𝔽₁₁)`.**

Structural (native_decide-free) proof: `center ≤ ker ≤ K ⊊ SL`, and `PSL = SL/center` is
**simple** (`PSL211S.PSL_isSimpleGroup`), so the normal subgroup `ker.map (mk')` of `PSL` is
`⊥` or `⊤`.  If `⊤`, then `ker = SL`, forcing `K = ⊤` — impossible since `|K| = 120 ≠ 1320`.
Hence it is `⊥`, i.e. `ker ≤ center`, and with `center ≤ ker` we get equality. -/
theorem ker_eq_center : psi11.ker = Subgroup.center (SL(2, ZMod 11)) := by
  haveI := PSL211S.PSL_isSimpleGroup
  set Z := Subgroup.center (SL(2, ZMod 11)) with hZ
  -- `center ≤ ker`
  have hZle : Z ≤ psi11.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    rcases (center_eq_pm_one g).mp hg with rfl | rfl
    · exact map_one psi11
    · exact psi11_neg_one
  -- `ker ≤ K`
  have hkerK : psi11.ker ≤ Ksub := by
    obtain ⟨i0, hi0⟩ := cover_exists (1 : SL(2, ZMod 11))
    rw [mul_one] at hi0
    have hri0inv : (reps i0)⁻¹ ∈ Ksub := (inKb_iff_memK _).1 hi0
    have hri0 : reps i0 ∈ Ksub := by simpa using inv_mem hri0inv
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hfix : cIdx (g * reps i0) = i0 := (psi11_eq_one_iff g).1 hg i0
    have hm := cIdx_mem (g * reps i0)
    rw [hfix] at hm
    have hconj : (reps i0)⁻¹ * (g * reps i0) ∈ Ksub := (inKb_iff_memK _).1 hm
    have hg' : g = reps i0 * ((reps i0)⁻¹ * (g * reps i0)) * (reps i0)⁻¹ := by group
    rw [hg']
    exact mul_mem (mul_mem hri0 hconj) (inv_mem hri0)
  -- `K ≠ ⊤`
  have hKne : Ksub ≠ ⊤ := by
    intro h
    have h120 : Nat.card Ksub = 120 := card_Ksub
    rw [h] at h120
    have htop : Nat.card (⊤ : Subgroup (SL(2, ZMod 11))) = 1320 := by
      rw [Subgroup.card_top, Nat.card_eq_fintype_card, EnumL211.slCard]
    rw [htop] at h120; norm_num at h120
  -- quotient by the centre
  set Q := QuotientGroup.mk' Z with hQdef
  have hQker : Q.ker = Z := QuotientGroup.ker_mk' Z
  have hQsurj : Function.Surjective Q := QuotientGroup.mk'_surjective Z
  haveI hkerN : psi11.ker.Normal := MonoidHom.normal_ker psi11
  have hmapN : (psi11.ker.map Q).Normal := hkerN.map Q hQsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (psi11.ker.map Q) hmapN with hbot | htop
  · rw [Subgroup.map_eq_bot_iff, hQker] at hbot
    exact le_antisymm hbot hZle
  · exfalso
    have hcm := Subgroup.comap_map_eq Q psi11.ker
    rw [htop, Subgroup.comap_top, hQker, sup_eq_left.2 hZle] at hcm
    have hk : psi11.ker = ⊤ := hcm.symm
    have hle : (⊤ : Subgroup (SL(2, ZMod 11))) ≤ Ksub := hk ▸ hkerK
    exact hKne (top_le_iff.1 hle)

/-! ### Assembling the embedding -/

/-- The canonical exceptional embedding `PSL(2, 𝔽₁₁) ↪ M₁₁` induced by `psi11`. -/
noncomputable def embedding : PSL(2, ZMod 11) →* M11 := by
  let hmem : ∀ g : SL(2, ZMod 11), psi11 g ∈ M11 := fun g => range_le ⟨g, rfl⟩
  let f0 : SL(2, ZMod 11) →* M11 := psi11.codRestrict M11 hmem
  have hkerf0 : f0.ker = Subgroup.center (SL(2, ZMod 11)) := by
    rw [show f0 = psi11.codRestrict M11 hmem from rfl, MonoidHom.ker_codRestrict, ker_eq_center]
  exact (QuotientGroup.kerLift f0).comp
    (QuotientGroup.quotientMulEquivOfEq hkerf0.symm).toMonoidHom

set_option maxHeartbeats 8000000 in
lemma embedding_injective : Function.Injective embedding := by
  unfold embedding
  dsimp only
  exact (QuotientGroup.kerLift_injective _).comp
    (QuotientGroup.quotientMulEquivOfEq _).injective

/-- **`PSL(2, 𝔽₁₁) ↪ M₁₁`.** -/
theorem embeds : ∃ f : PSL(2, ZMod 11) →* M11, Function.Injective f :=
  ⟨embedding, embedding_injective⟩

end PSL211

end Mathieu
