import Mathlib

/-!
# Structural generation of `SL(2, 𝔽₁₁)` by two transvections

This file gives a **`native_decide`-free** proof that the two elementary matrices
`S = !![1,1;0,1]` and `T = !![1,0;1,1]` generate `SL(2, 𝔽₁₁)`.  The proof is the classical
Gaussian-elimination / row-reduction argument (elementary transvections generate `SLₙ` over a
field), so it does not rely on any enumeration.

This is the clean replacement for `EnumL211.closure_eq_top`, whose proof goes through the
`native_decide` BFS certificates `stepST_SS` / `SS_card`.
-/

namespace Mathieu

open Matrix
open scoped MatrixGroups

namespace SL211Gen

/-- `S = !![1,1;0,1] ∈ SL(2, 𝔽₁₁)`. -/
def Smat : SL(2, ZMod 11) := ⟨!![1,1;0,1], by decide⟩

/-- `T = !![1,0;1,1] ∈ SL(2, 𝔽₁₁)`. -/
def Tmat : SL(2, ZMod 11) := ⟨!![1,0;1,1], by decide⟩

/-- The upper transvection `!![1,m;0,1] ∈ SL(2, 𝔽₁₁)`. -/
def upper (m : ZMod 11) : SL(2, ZMod 11) := ⟨!![1,m;0,1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower transvection `!![1,0;m,1] ∈ SL(2, 𝔽₁₁)`. -/
def lower (m : ZMod 11) : SL(2, ZMod 11) := ⟨!![1,0;m,1], by simp [Matrix.det_fin_two_of]⟩

/-
Every upper transvection is a power of `S`, hence lies in the closure.
-/
theorem upper_mem (m : ZMod 11) : upper m ∈ Subgroup.closure {Smat, Tmat} := by
  -- Since $Smat$ is in the closure, any power of $Smat$ is also in the closure.
  have hSmat_pow : ∀ k : ℕ, Smat ^ k ∈ Subgroup.closure {Smat, Tmat} := by
    exact fun k => Subgroup.pow_mem _ ( Subgroup.subset_closure ( Set.mem_insert _ _ ) ) _;
  -- By definition of $Smat$, we know that $Smat^k = !![1, k; 0, 1]$ for any integer $k$.
  have hSmat_pow_eq : ∀ k : ℕ, (Smat ^ k : Matrix.SpecialLinearGroup (Fin 2) (ZMod 11)).val = !![1, (k : ZMod 11); 0, 1] := by
    intro k; induction k <;> simp_all +decide [ pow_succ' ] ;
    rename_i k hk; rw [ show ( Smat : Matrix.SpecialLinearGroup ( Fin 2 ) ( ZMod 11 ) ) = ⟨ !![1, 1; 0, 1], by decide ⟩ from rfl ] ; ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ ] ;
  convert hSmat_pow m.val;
  exact Subtype.ext <| by simpa [ ZMod.natCast_zmod_val ] using hSmat_pow_eq m.val |> Eq.symm;

/-
Every lower transvection is a power of `T`, hence lies in the closure.
-/
theorem lower_mem (m : ZMod 11) : lower m ∈ Subgroup.closure {Smat, Tmat} := by
  -- By definition of $Tmat$, we know that $Tmat^k = !![1, 0; k, 1]$ for any integer $k$.
  have hTmat_pow_eq : ∀ k : ℕ, (Tmat ^ k : Matrix.SpecialLinearGroup (Fin 2) (ZMod 11)).val = !![1, 0; (k : ZMod 11), 1] := by
    intro k; induction k <;> simp_all +decide [ pow_succ' ] ; ring;
    rename_i k hk; rw [ show ( Tmat : Matrix.SpecialLinearGroup ( Fin 2 ) ( ZMod 11 ) ) = ⟨ !![1, 0; 1, 1], by decide ⟩ from rfl ] ; ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ ] ;
  convert Subgroup.pow_mem _ ( Subgroup.subset_closure ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) m.val using 1;
  exact Subtype.ext <| by simpa [ ZMod.natCast_zmod_val ] using hTmat_pow_eq m.val |> Eq.symm;

/-
**`S` and `T` generate `SL(2, 𝔽₁₁)`.**  Proved structurally by row reduction, without any
enumeration / `native_decide`.
-/
set_option maxHeartbeats 2000000 in
theorem closure_eq_top : Subgroup.closure {Smat, Tmat} = ⊤ := by
  ext g;
  -- By definition of $C$, we know that every element of $C$ can be written as a product of $S$ and $T$.
  have h_prod : ∀ g : SL(2, ZMod 11), (g.val 1 0 ≠ 0) → g ∈ Subgroup.closure {Smat, Tmat} := by
    intro g hg_nonzero
    obtain ⟨x, hx⟩ : ∃ x : ZMod 11, g.val 0 0 + x * g.val 1 0 = 1 := by
      have h_inv : ∃ x : ZMod 11, x * g.val 1 0 = 1 := by
        haveI := Fact.mk ( by decide : Nat.Prime 11 ) ; exact ⟨ _, inv_mul_cancel₀ hg_nonzero ⟩ ;
      exact ⟨ h_inv.choose * ( 1 - g.val 0 0 ), by linear_combination' h_inv.choose_spec * ( 1 - g.val 0 0 ) ⟩;
    -- Then $(upper x) * g = !![1, b'; c, d]$ for some $b'$.
    obtain ⟨b', hb'⟩ : ∃ b' : ZMod 11, (upper x * g).val = !![1, b'; g.val 1 0, g.val 1 1] := by
      simp +decide [ ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply ];
      unfold upper; aesop;
    -- Then $(lower (-c)) * ((upper x) * g) = !![1, b'; 0, d - c*b']$, and since determinant is preserved and equals $1$, the $(2,2)$ entry is $1$, so this equals $upper b'$.
    have h_lower : (lower (-g.val 1 0) * (upper x * g)).val = !![1, b'; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ *, Matrix.mul_apply ] ;
      · simp +decide [ lower ];
      · simp +decide [ lower ];
      · simp +decide [ lower ];
      · have := congr_arg Matrix.det hb'; norm_num [ Matrix.det_fin_two ] at this;
        simp +decide [ lower ] ; linear_combination' this.symm;
    -- Hence $(lower (-c)) * (upper x) * g = upper b'$, giving $g = (upper x)⁻¹ * (lower (-c))⁻¹ * (upper b')$, a product of elements of $C$, so $g ∈ C$.
    have h_g : g = (upper x)⁻¹ * (lower (-g.val 1 0))⁻¹ * upper b' := by
      have h_g : lower (-g.val 1 0) * (upper x * g) = upper b' := by
        exact Subtype.ext <| by simpa [ upper ] using h_lower;
      simp +decide [ ← h_g, mul_assoc ];
    exact h_g.symm ▸ Subgroup.mul_mem _ ( Subgroup.mul_mem _ ( Subgroup.inv_mem _ ( upper_mem _ ) ) ( Subgroup.inv_mem _ ( lower_mem _ ) ) ) ( upper_mem _ );
  refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
  by_cases h : (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 0 = 0
  · -- lower-left entry is `0`: multiply by `lower 1` to make it nonzero, then use `h_prod`.
    have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 1
        - (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 0 = 1 := by
      have := g.2; rwa [Matrix.det_fin_two] at this
    have h00 : (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 0 ≠ 0 := by
      intro hc; rw [hc, h] at hdet
      simp only [zero_mul, mul_zero, sub_zero] at hdet
      exact absurd hdet (by decide)
    have hentry : ((lower 1 * g : SL(2, ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 0
        = (g : Matrix (Fin 2) (Fin 2) (ZMod 11)) 0 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      show (lower 1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 0 * _
          + (lower 1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 1 * _ = _
      have e0 : (lower 1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 0 = 1 := by decide
      have e1 : (lower 1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 1 = 1 := by decide
      rw [e0, e1, h]; ring
    have h10 : ((lower 1 * g : SL(2, ZMod 11)) : Matrix (Fin 2) (Fin 2) (ZMod 11)) 1 0 ≠ 0 := by
      rw [hentry]; exact h00
    have hg : g = (lower 1)⁻¹ * (lower 1 * g) := (inv_mul_cancel_left (lower 1) g).symm
    rw [hg]; exact mul_mem (inv_mem (lower_mem 1)) (h_prod _ h10)
  · exact h_prod g h

end SL211Gen

end Mathieu