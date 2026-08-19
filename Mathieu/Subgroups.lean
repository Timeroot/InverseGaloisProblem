import Mathlib
import Mathieu.DefM11
import Mathieu.DefM12
import Mathieu.DefM22
import Mathieu.DefM23
import Mathieu.DefM24
import Mathieu.BasicM11
import Mathieu.BasicM12
import Mathieu.EnumM24IsoCore

/-!
# Subgroup relations between the Mathieu groups

The Mathieu groups form a chain in which each is (isomorphic to) a point stabiliser inside
the next:
```
M₁₁ < M₁₂        M₂₁ < M₂₂ < M₂₃ < M₂₄
```
Since the groups live in permutation groups of different types, "`M₁₁` is a subgroup of
`M₁₂`" is made precise as: `M₁₁` is isomorphic to the stabiliser of a point inside `M₁₂`.

This file states those relations.  Proofs are recorded as goals; see `PLAN.md`.
-/

namespace Mathieu

set_option maxRecDepth 100000

open Equiv

/-- The stabiliser of a point `k` inside a permutation subgroup `H`. -/
def ptStab {n : ℕ} (H : Subgroup (Perm (Fin n))) (k : Fin n) : Subgroup (Perm (Fin n)) :=
  H ⊓ MulAction.stabilizer (Perm (Fin n)) k

/-- **Orbit–stabiliser for a transitive permutation subgroup.**  If `H ≤ Perm (Fin n)`
acts transitively on `Fin n`, then `|H| = n · |ptStab H k|` for any point `k`.  This is
the reusable step of the order chain `|M₂₄| = 24·|M₂₃| = 24·23·|M₂₂| = …`. -/
theorem card_eq_of_pretransitive {n : ℕ} (H : Subgroup (Perm (Fin n))) (k : Fin n)
    [MulAction.IsPretransitive H (Fin n)] :
    Nat.card H = n * Nat.card (ptStab H k) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer (↥H) k) := Fintype.ofFinite _
  haveI : Fintype ↑(MulAction.orbit (↥H) k) := Fintype.ofFinite _
  have horb : MulAction.orbit H k = Set.univ := MulAction.orbit_eq_univ H k
  have hstab : (MulAction.stabilizer (↥H) k)
      = (ptStab H k).subgroupOf H := by
    ext x
    simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ptStab]
    rfl
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥H) k
  simp only [← Nat.card_eq_fintype_card] at key
  have horbcard : Nat.card ↑(MulAction.orbit (↥H) k) = n := by
    rw [Nat.card_congr (by rw [horb] : ↑(MulAction.orbit (↥H) k) ≃ (Set.univ : Set (Fin n)))]
    simp
  have hstabcard : Nat.card ↥(MulAction.stabilizer (↥H) k) = Nat.card (ptStab H k) := by
    rw [Nat.card_congr (by rw [hstab] : (MulAction.stabilizer (↥H) k) ≃ _)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left)).toEquiv
  rw [horbcard, hstabcard] at key
  rw [← key]

/-- `M₂₂` is exactly the stabiliser of the point `22` inside `M₂₃` (this is how it is
defined). -/
theorem M22_eq_ptStab : M22 = ptStab M23 (22 : Fin 23) := rfl

/-- Concrete equivalence `Fin 11 ≃ {x : Fin 12 // x ≠ 11}`, extending a point of
`Fin 11` by `Fin.castSucc`.  Used to extend permutations of `Fin 11` to permutations of
`Fin 12` fixing the last point `11`. -/
def e12 : Fin 11 ≃ {x : Fin 12 // x ≠ 11} where
  toFun i := ⟨i.castSucc, by simp [Fin.castSucc, Fin.ext_iff]; omega⟩
  invFun x := x.1.castPred (by rcases x with ⟨v, hv⟩; simpa using hv)
  left_inv i := by simp
  right_inv x := by ext; simp

/-- **`M₁₁ < M₁₂`.** `M₁₁` is isomorphic to the stabiliser of the point `11` inside `M₁₂`.

Proof: the extension homomorphism `Perm.extendDomainHom e12 : Perm (Fin 11) →* Perm (Fin 12)`
(extend a permutation by fixing `11`) sends the generators `m11a, m11b` of `M₁₁` to the
generators `m12a, m12b` of `M₁₂`, hence maps `M₁₁` injectively into `ptStab M12 11`.
Both groups have order `7920` (`M11_card`, and `|M₁₂| / 12 = 7920` by orbit–stabiliser),
so the injective homomorphism is bijective. -/
theorem M11_iso_ptStab_M12 :
    Nonempty (M11 ≃* ptStab M12 (11 : Fin 12)) := by
  classical
  have ha : Perm.extendDomainHom e12 m11a = m12a := by decide
  have hb : Perm.extendDomainHom e12 m11b = m12b := by decide
  have hmap : Subgroup.map (Perm.extendDomainHom e12) M11 ≤ ptStab M12 (11 : Fin 12) := by
    rw [show M11 = Subgroup.closure {m11a, m11b} from rfl, MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [ha]
      exact ⟨m12a_mem, (MulAction.mem_stabilizer_iff).2 (by
        simpa [Equiv.Perm.smul_def] using m12a_apply_eleven)⟩
    · rw [hb]
      exact ⟨EnumM12Clean.m12b_mem, (MulAction.mem_stabilizer_iff).2 (by
        simpa [Equiv.Perm.smul_def] using m12b_apply_eleven)⟩
  let ψ : M11 →* ptStab M12 (11 : Fin 12) :=
    { toFun := fun g => ⟨Perm.extendDomainHom e12 g.1, hmap ⟨g.1, g.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact Subtype.ext (Perm.extendDomainHom_injective e12 (congrArg Subtype.val hab))
  have hcard : Nat.card M11 = Nat.card (ptStab M12 (11 : Fin 12)) := by
    have h2 : Nat.card (ptStab M12 (11 : Fin 12)) = 7920 := by
      haveI := M12_isPretransitive
      have h := card_eq_of_pretransitive M12 (11 : Fin 12)
      rw [M12_card] at h
      omega
    rw [M11_card, h2]
  haveI : Fintype M11 := Fintype.ofFinite _
  haveI : Fintype (ptStab M12 (11 : Fin 12)) := Fintype.ofFinite _
  have hbij : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hψinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  exact ⟨MulEquiv.ofBijective ψ hbij⟩

/-- **`M₂₂ < M₂₃`.** `M₂₂` is contained in `M₂₃` (recorded in `DefM22.lean`). -/
theorem M22_le_M23' : M22 ≤ M23 := M22_le_M23

/-- The Mathieu group `M₂₁`, defined as the stabiliser of the point `21` inside `M₂₂`
(equivalently the three-point stabiliser inside `M₂₄`).  It is isomorphic to `PSL(3,4)`;
see `PSL.lean`. -/
def M21 : Subgroup (Perm (Fin 23)) := ptStab M22 (21 : Fin 23)

/-- **`M₂₁ < M₂₂`.** `M₂₁` is contained in `M₂₂`. -/
theorem M21_le_M22 : M21 ≤ M22 := inf_le_left

end Mathieu
