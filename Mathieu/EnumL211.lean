import Mathlib
import Mathieu.CardSL
import Mathieu.SL211Gen

/-!
# Enumerations in `SL(2, 𝔽₁₁)` for the exceptional action of `PSL(2,11)`

This file provides the data needed for the exceptional `2`-transitive action of `PSL(2,11)`
on `11` points, in the fast integer-encoded style (a `2×2` matrix over `ZMod 11` is encoded by
the base-`11` numeral of its four entries):

* **`closure_eq_top`** — the matrices `S = !![1,1;0,1]` and `T = !![1,0;1,1]` generate
  `SL(2, 𝔽₁₁)`.  This is now a thin wrapper around the **`native_decide`-free** structural proof
  `SL211Gen.closure_eq_top` (Gaussian elimination).
* **`memK_iff`** — a membership test for the order-`120` subgroup `K = ⟨A, B⟩`
  (`A = !![0,1;-1,0]`, `B = !![-1,8;1,2]`), an `SL(2,5) ≅ 2.A₅` of index `11`.  This subgroup
  is the point-stabiliser realising the exceptional `2`-transitive action of `PSL(2,11)` on
  `11` points; see `PSL211.lean`.

## `native_decide`-free enumeration of `K`

The subgroup `K` is small enough (`120` elements) that the Lean **kernel** can reduce its
breadth-first closure `stepK^[10] {idCode}`.  We therefore present `KK` as an explicit literal
list of its `120` codes and bridge it to the closure operator with a single kernel `decide`
(`KK_eq_iterate`); every certificate about `KK` (`stepK_KK`, `KK_card`, `idCode_mem_KK`) is a
kernel `decide`, not `native_decide`.
-/

namespace Mathieu

open Matrix
open scoped MatrixGroups

instance instFact11Prime : Fact (Nat.Prime 11) := ⟨by norm_num⟩

namespace EnumL211

set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

/-! ### Encoding of `2×2` matrices over `ZMod 11` -/

/-- Encode a `2×2` matrix over `ZMod 11` as the base-`11` numeral of its entries. -/
def encM (m : Matrix (Fin 2) (Fin 2) (ZMod 11)) : ℕ :=
  (m 0 0).val + 11 * (m 0 1).val + 11 ^ 2 * (m 1 0).val + 11 ^ 3 * (m 1 1).val

/-- Decode a natural number to a `2×2` matrix over `ZMod 11`. -/
def decM (n : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 11) :=
  !![ ((n % 11 : ℕ) : ZMod 11), ((n / 11 % 11 : ℕ) : ZMod 11) ;
      ((n / 11 ^ 2 % 11 : ℕ) : ZMod 11), ((n / 11 ^ 3 % 11 : ℕ) : ZMod 11) ]

/-- Apply a generator matrix `g` to an encoded matrix: decode, left-multiply, re-encode. -/
def applyM (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) (n : ℕ) : ℕ := encM (g * decM n)

/-- The encoding of the identity matrix. -/
def idCode : ℕ := encM (1 : Matrix (Fin 2) (Fin 2) (ZMod 11))

/-- The encoding of an `SL`-element by its underlying matrix. -/
def φ (p : SL(2, ZMod 11)) : ℕ := encM p.1

lemma decM_encM (m : Matrix (Fin 2) (Fin 2) (ZMod 11)) : decM (encM m) = m := by
  have h00 : (m 0 0).val < 11 := ZMod.val_lt _
  have h01 : (m 0 1).val < 11 := ZMod.val_lt _
  have h10 : (m 1 0).val < 11 := ZMod.val_lt _
  have h11 : (m 1 1).val < 11 := ZMod.val_lt _
  have hri : ∀ a : ZMod 11, ((a.val : ℕ) : ZMod 11) = a := ZMod.natCast_rightInverse
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [decM, encM] <;>
    [ (rw [show ((m 0 0).val + 11 * (m 0 1).val + 11^2*(m 1 0).val + 11^3*(m 1 1).val) % 11 = (m 0 0).val by omega]; exact hri _);
      (rw [show ((m 0 0).val + 11 * (m 0 1).val + 11^2*(m 1 0).val + 11^3*(m 1 1).val) / 11 % 11 = (m 0 1).val by omega]; exact hri _);
      (rw [show ((m 0 0).val + 11 * (m 0 1).val + 11^2*(m 1 0).val + 11^3*(m 1 1).val) / 11^2 % 11 = (m 1 0).val by omega]; exact hri _);
      (rw [show ((m 0 0).val + 11 * (m 0 1).val + 11^2*(m 1 0).val + 11^3*(m 1 1).val) / 11^3 % 11 = (m 1 1).val by omega]; exact hri _) ]

lemma φ_injective : Function.Injective φ := by
  intro p q h
  have h2 : decM (φ p) = decM (φ q) := by rw [h]
  rw [φ, φ, decM_encM, decM_encM] at h2
  exact Subtype.ext h2

lemma applyM_φ (g p : SL(2, ZMod 11)) : applyM g.1 (φ p) = φ (g * p) := by
  unfold applyM φ
  rw [decM_encM]
  rfl

lemma φ_one : φ 1 = idCode := by
  unfold φ idCode
  rfl

/-! ## Part 1 : `S` and `T` generate `SL(2, 𝔽₁₁)` -/

/-- `S = !![1,1;0,1] ∈ SL(2, 𝔽₁₁)`. -/
def Smat : SL(2, ZMod 11) := ⟨!![1,1;0,1], by decide⟩

/-- `T = !![1,0;1,1] ∈ SL(2, 𝔽₁₁)`. -/
def Tmat : SL(2, ZMod 11) := ⟨!![1,0;1,1], by decide⟩

/-- `|SL(2, 𝔽₁₁)| = 1320`, obtained (pen-and-paper) from `|GL(2, 𝔽₁₁)| = 13200` via the order
formula `CardSL.card_GL_eq_card_SL_mul` and `|𝔽₁₁ˣ| = 10`, rather than by enumeration. -/
theorem slCard : Fintype.card SL(2, ZMod 11) = 1320 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hGL : Nat.card (GL (Fin 2) (ZMod 11)) = 13200 := by
    rw [Matrix.card_GL_field]; norm_num [Fin.prod_univ_two, ZMod.card]
  have hmul := CardSL.card_GL_eq_card_SL_mul (𝔽 := ZMod 11) (n := 2)
  rw [hGL, show Fintype.card (ZMod 11) = 11 from by simp [ZMod.card]] at hmul
  rw [← Nat.card_eq_fintype_card]
  omega

/-- **`S` and `T` generate `SL(2, 𝔽₁₁)`.**  A thin wrapper around the `native_decide`-free
structural proof `SL211Gen.closure_eq_top`. -/
theorem closure_eq_top : Subgroup.closure {Smat, Tmat} = ⊤ := by
  have hS : Smat = SL211Gen.Smat := Subtype.ext rfl
  have hT : Tmat = SL211Gen.Tmat := Subtype.ext rfl
  rw [hS, hT]; exact SL211Gen.closure_eq_top

/-! ## Part 2 : the order-`120` subgroup `K = ⟨A, B⟩` -/

/-- `A = !![0,1;-1,0] ∈ SL(2, 𝔽₁₁)` (order 4). -/
def Amat : SL(2, ZMod 11) := ⟨!![0,1;10,0], by decide⟩

/-- `B = !![-1,8;1,2] ∈ SL(2, 𝔽₁₁)` (order 6). -/
def Bmat : SL(2, ZMod 11) := ⟨!![10,8;1,2], by decide⟩

/-- One BFS closure step for `K = ⟨A, B⟩` in encoded space. -/
def stepK (Tset : Finset ℕ) : Finset ℕ :=
  Tset ∪ Tset.image (applyM Amat.1) ∪ Tset.image (applyM Bmat.1)
    ∪ Tset.image (applyM Amat⁻¹.1) ∪ Tset.image (applyM Bmat⁻¹.1)

/-- The subgroup `K = ⟨A, B⟩` in encoded form, as an explicit `120`-element literal.  (This is
`stepK^[10] {idCode}`; see `KK_eq_iterate`.  Presenting it as a literal keeps the membership
test `inKb` cheap for the downstream kernel `decide`s in `ActL211`/`CoverL211`.) -/
def KK : Finset ℕ :=
  {231, 307, 448, 575, 637, 826, 888, 1015, 1156, 1221, 1332, 1549, 1628, 1737, 1865, 1958,
   2144, 2254, 2319, 2533, 2643, 2778, 2881, 2946, 3056, 3232, 3324, 3456, 3562, 3651, 3858,
   3878, 4085, 4137, 4247, 4433, 4539, 4649, 4790, 4873, 4965, 5190, 5321, 5360, 5462, 5592,
   5690, 5871, 5981, 6167, 6265, 6375, 6516, 6607, 6774, 6794, 7002, 7090, 7193, 7318, 7420,
   7597, 7707, 7772, 7874, 7999, 8109, 8332, 8397, 8507, 8684, 8786, 8911, 9014, 9102, 9310,
   9413, 9497, 9588, 9729, 9839, 9937, 10123, 10233, 10293, 10512, 10642, 10688, 10783, 10914,
   11018, 11220, 11314, 11455, 11565, 11660, 11857, 11967, 11995, 12105, 12246, 12453, 12542,
   12648, 12780, 12872, 13048, 13158, 13223, 13320, 13461, 13571, 13785, 13850, 13960, 14135,
   14239, 14367, 14465, 14555}

lemma subset_stepK (Tset : Finset ℕ) : Tset ⊆ stepK Tset := by
  intro x hx; simp only [stepK, Finset.mem_union]; tauto

/-- **The literal `KK` is exactly the breadth-first closure `stepK^[10] {idCode}`** (kernel
`decide`; the closure stabilises by `10` iterations). -/
theorem KK_eq_iterate : KK = stepK^[10] {idCode} := by decide

theorem stepK_KK : stepK KK = KK := by decide

theorem KK_card : KK.card = 120 := by decide

lemma idCode_mem_KK : idCode ∈ KK := by decide

lemma Amat_mem : Amat ∈ Subgroup.closure {Amat, Bmat} :=
  Subgroup.subset_closure (by left; rfl)

lemma Bmat_mem : Bmat ∈ Subgroup.closure {Amat, Bmat} :=
  Subgroup.subset_closure (by right; rfl)

lemma applyM_mem_KK {g : SL(2, ZMod 11)}
    (hg : g = Amat ∨ g = Bmat ∨ g = Amat⁻¹ ∨ g = Bmat⁻¹)
    {c : ℕ} (hc : c ∈ KK) : applyM g.1 c ∈ KK := by
  have hsub : applyM g.1 c ∈ stepK KK := by
    simp only [stepK, Finset.mem_union, Finset.mem_image]
    rcases hg with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c, hc, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨c, hc, rfl⟩))
    · exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
    · exact Or.inr ⟨c, hc, rfl⟩
  rwa [stepK_KK] at hsub

lemma forwardK (p : SL(2, ZMod 11)) (hp : p ∈ Subgroup.closure {Amat, Bmat}) : φ p ∈ KK := by
  refine Subgroup.closure_induction_left (p := fun x _ => φ x ∈ KK) ?_ ?_ ?_ hp
  · show φ (1 : SL(2, ZMod 11)) ∈ KK
    rw [φ_one]; exact idCode_mem_KK
  · intro x hx y _ h
    show φ (x * y) ∈ KK
    rw [← applyM_φ]
    apply applyM_mem_KK _ h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro x hx y _ h
    show φ (x⁻¹ * y) ∈ KK
    rw [← applyM_φ]
    apply applyM_mem_KK _ h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

lemma backwardK_aux :
    ∀ (n : ℕ), ∀ c ∈ stepK^[n] {idCode}, ∃ p ∈ Subgroup.closure {Amat, Bmat}, φ p = c := by
  intro n
  induction n with
  | zero =>
    intro c hc
    rw [Function.iterate_zero, id_eq, Finset.mem_singleton] at hc
    exact ⟨1, one_mem _, by rw [φ_one, hc]⟩
  | succ k ih =>
    intro c hc
    rw [Function.iterate_succ', Function.comp_apply] at hc
    simp only [stepK, Finset.mem_union, Finset.mem_image] at hc
    rcases hc with ((((h | ⟨c', hc', rfl⟩) | ⟨c', hc', rfl⟩) | ⟨c', hc', rfl⟩) | ⟨c', hc', rfl⟩)
    · exact ih c h
    · obtain ⟨p, hp, rfl⟩ := ih c' hc'
      exact ⟨Amat * p, mul_mem Amat_mem hp, (applyM_φ _ _).symm⟩
    · obtain ⟨p, hp, rfl⟩ := ih c' hc'
      exact ⟨Bmat * p, mul_mem Bmat_mem hp, (applyM_φ _ _).symm⟩
    · obtain ⟨p, hp, rfl⟩ := ih c' hc'
      exact ⟨Amat⁻¹ * p, mul_mem (inv_mem Amat_mem) hp, (applyM_φ _ _).symm⟩
    · obtain ⟨p, hp, rfl⟩ := ih c' hc'
      exact ⟨Bmat⁻¹ * p, mul_mem (inv_mem Bmat_mem) hp, (applyM_φ _ _).symm⟩

lemma backwardK (c : ℕ) (hc : c ∈ KK) : ∃ p ∈ Subgroup.closure {Amat, Bmat}, φ p = c :=
  backwardK_aux 10 c (KK_eq_iterate ▸ hc)

/-- **Membership test for `K = ⟨A, B⟩`.** -/
theorem memK_iff (g : SL(2, ZMod 11)) :
    g ∈ Subgroup.closure {Amat, Bmat} ↔ encM g.1 ∈ KK := by
  constructor
  · intro hg; exact forwardK g hg
  · intro hg
    obtain ⟨p, hp, hpc⟩ := backwardK (encM g.1) hg
    have : g = p := φ_injective (by rw [φ]; exact hpc.symm ▸ rfl)
    rw [this]; exact hp

end EnumL211

end Mathieu
