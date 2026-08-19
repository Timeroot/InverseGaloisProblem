import Mathlib
import Mathieu.DefM11
import Mathieu.EnumM11

/-!
# Basic properties of `M₁₁`

The headline facts about `M₁₁`:

* its order is `7920 = 11 · 10 · 9 · 8` (`M11_card`);
* it acts (sharply) 4-transitively on the 11 points (`M11_isMultiplyPretransitive_four`).

Both are now proven.  The order is obtained by a verified enumeration of the generated
subgroup (see `EnumM11.lean`); sharp 4-transitivity then follows from the triviality of the
pointwise stabiliser of four points (`EnumM11.M11_stab4_trivial`) together with the order,
via orbit–stabiliser on the action on `Fin 4 ↪ Fin 11`.
-/

namespace Mathieu

set_option maxRecDepth 100000

open Equiv

/-- The order of `M₁₁` is `7920`.

Proved by a verified breadth-first enumeration of the subgroup `⟨m11a, m11b⟩` in a fast
integer-encoded representation; see `EnumM11.lean`. -/
theorem M11_card : Nat.card M11 = 7920 := EnumM11.M11_card_clean

/-- `m₁₁ₐ` is an 11-cycle. -/
theorem m11a_isCycle : m11a.IsCycle := by
  apply Cycle.isCycle_formPerm
  rw [Cycle.nontrivial_coe_nodup_iff (by decide)]; decide

/-- `m₁₁ₐ` moves every point (it is a full-support cycle). -/
theorem m11a_moves : ∀ x : Fin 11, m11a x ≠ x := by decide

/-- **Base case of `k`-transitivity (PLAN §3.2).**  `M₁₁` acts transitively on the 11
points, because it contains the 11-cycle `m₁₁ₐ` whose support is all of `Fin 11`. -/
theorem M11_isPretransitive : MulAction.IsPretransitive M11 (Fin 11) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, hi⟩ := m11a_isCycle.exists_pow_eq (m11a_moves x) (m11a_moves y)
  exact ⟨⟨m11a ^ i, M11.pow_mem m11a_mem i⟩, by simpa [Submonoid.smul_def] using hi⟩

/-- **`M₁₁` acts (sharply) 4-transitively on the 11 points.**

Proof: the pointwise stabiliser of `0,1,2,3` is trivial (`EnumM11.M11_stab4_trivial`), so the
stabiliser of the base embedding `Fin 4 ↪ Fin 11` is trivial; since `|M₁₁| = 7920` equals
`#(Fin 4 ↪ Fin 11) = 11·10·9·8`, the orbit of the base embedding is everything. -/
theorem M11_isMultiplyPretransitive_four :
    MulAction.IsMultiplyPretransitive M11 (Fin 11) 4 := by
      -- We prove M₁₁ is *sharply* 4-transitive: the action on `Fin 4 ↪ Fin 11` is transitive because it has a point with trivial stabiliser and the group and the embedding type have the same cardinality (7920).
      have h_trans : ∃ e0 : Fin 4 ↪ Fin 11, MulAction.stabilizer (↥M11) e0 = ⊥ := by
        refine' ⟨ _, _ ⟩;
        exact ⟨ fun x => ⟨ x, by fin_cases x <;> trivial ⟩, by decide ⟩;
        ext ⟨ g, hg ⟩ ; simp +decide [ MulAction.mem_stabilizer_iff ] ;
        simp +decide [ Function.Embedding.ext_iff, Fin.forall_fin_succ ];
        exact ⟨ fun h => EnumM11.M11_stab4_trivial g hg h.1 h.2.1 h.2.2.1 h.2.2.2, fun h => h.symm ▸ by decide ⟩;
      -- Since the stabilizer of `e0` is trivial, the orbit of `e0` is all of `Fin 4 ↪ Fin 11`.
      obtain ⟨e0, he0⟩ := h_trans;
      have h_orbit : MulAction.orbit (↥M11) e0 = Set.univ := by
        have h_card : Nat.card (MulAction.orbit (↥M11) e0) = Nat.card (Fin 4 ↪ Fin 11) := by
          have h_orbit_card : Nat.card (MulAction.orbit (↥M11) e0) * Nat.card (MulAction.stabilizer (↥M11) e0) = Nat.card (↥M11) := by
            have := Subgroup.card_mul_index ( MulAction.stabilizer ( ↥M11 ) e0 );
            rw [ mul_comm, ← this, Subgroup.index_eq_card ];
            rw [ Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer ( ↥M11 ) e0 ) ];
          simp_all +decide [ Nat.card_eq_fintype_card ];
          convert Mathieu.M11_card;
        exact Set.eq_of_subset_of_ncard_le ( Set.subset_univ _ ) ( by simpa [ Set.ncard_univ ] using h_card.ge );
      constructor;
      intro x y;
      rw [ Set.eq_univ_iff_forall ] at h_orbit;
      obtain ⟨ g, hg ⟩ := h_orbit x; obtain ⟨ h, hh ⟩ := h_orbit y; use h * g⁻¹; simp_all +decide [ mul_smul ] ;
      simp +decide [ ← hg, ← hh, smul_smul ]

/-- `M₁₁` is nontrivial (sanity check on the definition). -/
theorem M11_neBot : M11 ≠ ⊥ := by
  intro h
  have : m11a ∈ (⊥ : Subgroup (Perm (Fin 11))) := h ▸ m11a_mem
  rw [Subgroup.mem_bot] at this
  exact m11a_ne_one this

end Mathieu