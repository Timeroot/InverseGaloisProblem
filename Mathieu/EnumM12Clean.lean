import Mathlib
import Mathieu.DefM12
import Mathieu.EnumM11

/-!
# The order of `M₁₂` (`native_decide`-free)

This file proves `Nat.card M₁₂ = 95040` (`M12_card_clean`) using only the Lean **kernel**
(no `native_decide`), replacing the earlier breadth-first enumeration certificate.

The argument is the classical orbit–stabiliser / coset one:

* `M₁₂ = ⟨m12a, m12b, m12c⟩` acts on `Fin 12`; the transversal `Tv j = m12a^j * m12c`
  (and `Tv 11 = 1`) satisfies `Tv j 11 = j`, so `M₁₂` is transitive on the `12` points and
  `|M₁₂| = 12 · |St|`, where `St = M₁₂ ⊓ stab(11)` is the point stabiliser.
* `St = M₁₁copy`, the copy of `M₁₁` fixing `11` (`Subgroup.map (extendDomainHom e12) M₁₁`).
  The inclusion `M₁₁copy ≤ St` is easy (the generators `m11a, m11b` map to `m12a, m12b` which
  fix `11`).  The hard inclusion `St ≤ M₁₁copy` is a **Schreier coset-closure** argument: the
  union of the `12` cosets `Tv j · M₁₁copy` is closed under the generators (checked point-by-point
  by the kernel), where membership of a Schreier element in `M₁₁copy` reduces — via the restriction
  to `Fin 11` — to membership in `M₁₁`, which is decided by the balanced search-tree literal
  `EnumM11.tt` (`EnumM11.keys = φ '' M₁₁`, so `Btree.mem` soundness is enough).
* Hence `|St| = |M₁₁copy| = |M₁₁| = 7920` and `|M₁₂| = 12 · 7920 = 95040`.

Everything is discharged by the kernel; no `native_decide` is used.
-/

namespace Mathieu

open Equiv EnumM11
open scoped MulAction

namespace EnumM12Clean

set_option maxRecDepth 10000

/-- Concrete equivalence `Fin 11 ≃ {x : Fin 12 // x ≠ 11}` (extend by `Fin.castSucc`). -/
def e12 : Fin 11 ≃ {x : Fin 12 // x ≠ 11} where
  toFun i := ⟨i.castSucc, by simp [Fin.castSucc, Fin.ext_iff]; omega⟩
  invFun x := x.1.castPred (by rcases x with ⟨v, hv⟩; simpa using hv)
  left_inv i := by simp
  right_inv x := by ext; simp

/-- `m12b` is a member of `M₁₂` (re-exported so downstream files need not import the old
enumeration file). -/
lemma m12b_mem : m12b ∈ M12 := Subgroup.subset_closure (by right; left; rfl)

/-- The copy of `M₁₁` inside `Perm (Fin 12)` fixing the point `11`. -/
def M11copy : Subgroup (Perm (Fin 12)) := Subgroup.map (Perm.extendDomainHom e12) M11

/-- The point stabiliser of `11` inside `M₁₂`. -/
def St : Subgroup (Perm (Fin 12)) := M12 ⊓ MulAction.stabilizer (Perm (Fin 12)) (11 : Fin 12)

/-! ### The kernel `M₁₁`-membership oracle -/

/-- The search tree holds **exactly** the encodings of `M₁₁` (not merely a superset):
`φ '' M₁₁ ⊆ keys` by `forward_keys`, and both sides have cardinality `7920`. -/
theorem keys_eq_image : (keys : Set ℕ) = φ '' (M11 : Set (Perm (Fin 11))) := by
  have hsub : φ '' (M11 : Set (Perm (Fin 11))) ⊆ (keys : Set ℕ) := by
    rintro _ ⟨p, hp, rfl⟩; exact forward_keys p hp
  have hcardimg : (φ '' (M11 : Set (Perm (Fin 11)))).ncard = 7920 := by
    rw [Set.ncard_image_of_injective _ φ_injective, ← Nat.card_coe_set_eq]; exact M11_card_clean
  have hkc : (keys : Set ℕ).ncard = 7920 := by
    rw [Set.ncard_coe_finset]
    have hle := keys_card_le
    have hge : 7920 ≤ keys.card := by
      have := Set.ncard_le_ncard hsub (keys.finite_toSet)
      rwa [hcardimg, Set.ncard_coe_finset] at this
    omega
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcardimg, hkc]) (keys.finite_toSet)).symm

/-- **`M₁₁`-membership oracle (soundness).**  A `true` tree lookup certifies membership. -/
theorem mem_M11_of_tree (p : Perm (Fin 11)) (h : Btree.mem (φ p) tt = true) : p ∈ M11 := by
  have hk : φ p ∈ keys := List.mem_toFinset.mpr (Btree.mem_toList h)
  have hk2 : φ p ∈ (keys : Set ℕ) := hk
  rw [keys_eq_image] at hk2
  obtain ⟨q, hq, hqp⟩ := hk2
  have : q = p := φ_injective hqp
  rwa [this] at hq

/-! ### Restriction of a permutation fixing `11` -/

lemma pres_of_fix {σ : Perm (Fin 12)} (h11 : σ 11 = 11) :
    ∀ x : Fin 12, σ x ≠ 11 ↔ x ≠ 11 := by
  intro x
  constructor
  · intro hx hxe; subst hxe; exact hx h11
  · intro hx hc; exact hx (σ.injective (hc.trans h11.symm))

/-- The (total) restriction of `σ` to `Fin 11`: genuine when `σ` preserves `(· ≠ 11)`,
otherwise the identity. -/
noncomputable def restT12 (σ : Perm (Fin 12)) : Perm (Fin 11) :=
  if h : (∀ x : Fin 12, σ x ≠ 11 ↔ x ≠ 11) then
    (Equiv.permCongr e12.symm) (σ.subtypePerm h)
  else 1

lemma extendDomainHom_restT12 {σ : Perm (Fin 12)}
    (h : ∀ x : Fin 12, σ x ≠ 11 ↔ x ≠ 11) :
    Perm.extendDomainHom e12 (restT12 σ) = σ := by
  classical
  rw [restT12, dif_pos h]
  apply Equiv.Perm.ext
  intro b
  simp only [Perm.extendDomainHom_apply]
  by_cases hb : b = 11
  · subst hb
    rw [Perm.extendDomain_apply_not_subtype _ _ (by simp)]
    have : σ 11 = 11 := by by_contra hc; exact (h 11).1 hc rfl
    exact this.symm
  · rw [show (((Equiv.permCongr e12.symm) (σ.subtypePerm h)).extendDomain e12) b = _ from
        Perm.extendDomain_apply_subtype _ e12 (show b ≠ 11 from hb)]
    simp only [permCongr_apply, symm_symm]
    rfl

lemma mem_M11copy_of {σ : Perm (Fin 12)} (h : ∀ x : Fin 12, σ x ≠ 11 ↔ x ≠ 11)
    (hr : restT12 σ ∈ M11) : σ ∈ M11copy :=
  ⟨restT12 σ, hr, extendDomainHom_restT12 h⟩

/-! ### The transversal and Schreier elements -/

/-- The coset transversal for `stab(11)`: `Tv j` sends `11` to `j`. -/
def Tv (j : Fin 12) : Perm (Fin 12) := if j = 11 then 1 else m12a ^ (j.val) * m12c

lemma Tv_11 (j : Fin 12) : Tv j 11 = j := by revert j; decide

lemma Tv_eleven_eq : Tv (11 : Fin 12) = 1 := by simp [Tv]

lemma Tv_mem (j : Fin 12) : Tv j ∈ M12 := by
  unfold Tv; split
  · exact one_mem _
  · exact mul_mem (pow_mem m12a_mem _) m12c_mem

/-- The Schreier element for generator `g` and transversal index `j`. -/
def schElt (g : Perm (Fin 12)) (j : Fin 12) : Perm (Fin 12) := (Tv (g j))⁻¹ * g * Tv j

/-- The Schreier check: the element fixes `11` and its restriction lands in `M₁₁` (tree lookup). -/
noncomputable def schOK (g : Perm (Fin 12)) (j : Fin 12) : Prop :=
  (schElt g j) 11 = 11 ∧ Btree.mem (φ (restT12 (schElt g j))) tt = true

noncomputable instance (g : Perm (Fin 12)) (j : Fin 12) : Decidable (schOK g j) := by
  unfold schOK; infer_instance

lemma mem_M11copy_of_schOK {g : Perm (Fin 12)} {j : Fin 12} (h : schOK g j) :
    schElt g j ∈ M11copy :=
  mem_M11copy_of (pres_of_fix h.1) (mem_M11_of_tree _ h.2)

/-! ### The single computational certificate, split per generator -/

section
set_option maxHeartbeats 2000000

lemma schAll_a : ∀ j : Fin 12, schOK m12a j := by decide
lemma schAll_ai : ∀ j : Fin 12, schOK m12a⁻¹ j := by decide
lemma schAll_b : ∀ j : Fin 12, schOK m12b j := by decide
lemma schAll_bi : ∀ j : Fin 12, schOK m12b⁻¹ j := by decide
lemma schAll_c : ∀ j : Fin 12, schOK m12c j := by decide
lemma schAll_ci : ∀ j : Fin 12, schOK m12c⁻¹ j := by decide

end

/-! ### Transversal (coset) closure -/

/-- `x` lies in some coset `Tv j · M₁₁copy`. -/
def inV (x : Perm (Fin 12)) : Prop := ∃ j : Fin 12, (Tv j)⁻¹ * x ∈ M11copy

lemma inV_one : inV 1 := ⟨11, by rw [Tv_eleven_eq]; simp⟩

lemma inV_mul (g : Perm (Fin 12)) (hsch : ∀ j : Fin 12, schElt g j ∈ M11copy)
    {y : Perm (Fin 12)} (hy : inV y) : inV (g * y) := by
  obtain ⟨j, hj⟩ := hy
  refine ⟨g j, ?_⟩
  have e : (Tv (g j))⁻¹ * (g * y) = (schElt g j) * ((Tv j)⁻¹ * y) := by unfold schElt; group
  rw [e]; exact mul_mem (hsch j) hj

lemma inV_of_mem_M12 {x : Perm (Fin 12)} (hx : x ∈ M12) : inV x := by
  refine Subgroup.closure_induction_left (p := fun z _ => inV z) inV_one ?_ ?_ hx
  · intro g hg y _ hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact inV_mul m12a (fun j => mem_M11copy_of_schOK (schAll_a j)) hy
    · exact inV_mul m12b (fun j => mem_M11copy_of_schOK (schAll_b j)) hy
    · exact inV_mul m12c (fun j => mem_M11copy_of_schOK (schAll_c j)) hy
  · intro g hg y _ hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact inV_mul m12a⁻¹ (fun j => mem_M11copy_of_schOK (schAll_ai j)) hy
    · exact inV_mul m12b⁻¹ (fun j => mem_M11copy_of_schOK (schAll_bi j)) hy
    · exact inV_mul m12c⁻¹ (fun j => mem_M11copy_of_schOK (schAll_ci j)) hy

/-! ### `St = M₁₁copy` -/

lemma M11copy_fixes_11 {z : Perm (Fin 12)} (hz : z ∈ M11copy) : z 11 = 11 := by
  obtain ⟨h, _, rfl⟩ := hz
  exact Perm.extendDomain_apply_not_subtype h e12 (by simp)

/-- **The hard direction.** `St ≤ M₁₁copy`. -/
lemma St_le_M11copy : St ≤ M11copy := by
  rintro x ⟨hx12, hxstab⟩
  have hfix : x 11 = 11 := by
    simpa [Equiv.Perm.smul_def] using (MulAction.mem_stabilizer_iff).1 hxstab
  obtain ⟨j, hj⟩ := inV_of_mem_M12 hx12
  have hg11 : ((Tv j)⁻¹ * x) 11 = 11 := M11copy_fixes_11 hj
  rw [Equiv.Perm.mul_apply, hfix] at hg11
  have hTj11 : Tv j 11 = 11 := by
    have h2 : Tv j ((Tv j)⁻¹ 11) = 11 := by simp
    rwa [hg11] at h2
  have hj11 : j = 11 := (Tv_11 j).symm.trans hTj11
  subst hj11
  rw [Tv_eleven_eq] at hj
  simpa using hj

/-- The easy direction. `M₁₁copy ≤ St`. -/
lemma M11copy_le_St : M11copy ≤ St := by
  rw [M11copy, show M11 = Subgroup.closure {m11a, m11b} from rfl, MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · rw [show Perm.extendDomainHom e12 m11a = m12a from by decide]
    exact ⟨m12a_mem, (MulAction.mem_stabilizer_iff).2 (by
      simpa [Equiv.Perm.smul_def] using m12a_apply_eleven)⟩
  · rw [show Perm.extendDomainHom e12 m11b = m12b from by decide]
    exact ⟨m12b_mem, (MulAction.mem_stabilizer_iff).2 (by
      simpa [Equiv.Perm.smul_def] using m12b_apply_eleven)⟩

lemma St_eq : St = M11copy := le_antisymm St_le_M11copy M11copy_le_St

/-! ### The order -/

lemma card_M11copy : Nat.card M11copy = 7920 := by
  have : Nat.card M11copy = Nat.card M11 :=
    (Nat.card_congr (Subgroup.equivMapOfInjective M11 (Perm.extendDomainHom e12)
      (Perm.extendDomainHom_injective e12)).toEquiv).symm
  rw [this, M11_card_clean]

/-- **`|M₁₂| = 95040`** (`native_decide`-free). -/
theorem M12_card_clean : Nat.card M12 = 95040 := by
  haveI : Fintype ↥M12 := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer (↥M12) (11 : Fin 12)) := Fintype.ofFinite _
  haveI : Fintype ↑(MulAction.orbit (↥M12) (11 : Fin 12)) := Fintype.ofFinite _
  have horb : MulAction.orbit (↥M12) (11 : Fin 12) = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro j
    exact ⟨⟨Tv j, Tv_mem j⟩, by
      show (Tv j) • (11 : Fin 12) = j; rw [Equiv.Perm.smul_def]; exact Tv_11 j⟩
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥M12) (11 : Fin 12)
  simp only [← Nat.card_eq_fintype_card] at key
  have hoc : Nat.card ↑(MulAction.orbit (↥M12) (11 : Fin 12)) = 12 := by
    rw [Nat.card_congr (by rw [horb] :
      ↑(MulAction.orbit (↥M12) (11 : Fin 12)) ≃ (Set.univ : Set (Fin 12)))]; simp
  have hstab : (MulAction.stabilizer (↥M12) (11 : Fin 12)) = St.subgroupOf M12 := by
    ext x
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, St, Subgroup.mem_inf]
    constructor
    · intro h; exact ⟨x.2, by simpa [Equiv.Perm.smul_def] using h⟩
    · intro h; simpa [Equiv.Perm.smul_def] using h.2
  have hstabcard : Nat.card ↥(MulAction.stabilizer (↥M12) (11 : Fin 12)) = Nat.card St := by
    rw [Nat.card_congr (by rw [hstab] :
      (MulAction.stabilizer (↥M12) (11 : Fin 12)) ≃ (St.subgroupOf M12))]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : St ≤ M12)).toEquiv
  rw [hoc, hstabcard, St_eq, card_M11copy] at key
  omega

end EnumM12Clean

end Mathieu
