/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.InfiniteClasses

/-!
# Trivial classes at the infinite places and positivity

A real embedding of a number field is the embedding attached to a real infinite place, and the
completion there is the reals.  A unit whose class at that place is trivial is an even power in the
completion as soon as the exponent is even, so its image under the embedding is a nonzero square
and therefore positive.

Running over the real embeddings turns the condition of being a local power at every infinite
place — the condition the `S`-units of the duality theorem are tested against — into the condition
of being positive at every real embedding, which is what the archimedean half of the product
formula asks of a second argument.

## Main results

* `InverseGalois.CFT.forall_pos_of_forall_infClassHom_eq_one`: **a unit which is a local power of
  an even exponent at every infinite place is positive at every real embedding.**

## Tags

infinite place, real embedding, totally positive, local power, number field
-/

namespace InverseGalois.CFT

open NumberField

section Positive

variable {K : Type} [Field K]

/-- **A unit which is a local power of an even exponent at every infinite place is positive at
every real embedding.**  A real embedding is the embedding of a real infinite place, whose
completion is the reals, and there the unit is a nonzero even power. -/
theorem forall_pos_of_forall_infClassHom_eq_one {n : ℕ} (hn : 2 ∣ n) {u : Kˣ}
    (h : ∀ w : InfinitePlace K, infClassHom w n (u : Kˣ) = 1) (φ : K →+* ℝ) : 0 < φ (u : K) := by
  obtain ⟨m, rfl⟩ := hn
  have hψ : ComplexEmbedding.IsReal ((Complex.ofRealHom : ℝ →+* ℂ).comp φ) :=
    ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))
  set w : InfinitePlace K := InfinitePlace.mk ((Complex.ofRealHom : ℝ →+* ℂ).comp φ) with hwdef
  have hw : w.IsReal := InfinitePlace.isReal_mk_iff.2 hψ
  have hemb : InfinitePlace.embedding_of_isReal hw = φ := by
    ext x
    have hx : ((InfinitePlace.embedding_of_isReal hw x : ℝ) : ℂ) = ((φ x : ℝ) : ℂ) := by
      rw [InfinitePlace.embedding_of_isReal_apply hw x, hwdef,
        InfinitePlace.embedding_mk_eq_of_isReal hψ]
      rfl
    exact_mod_cast hx
  obtain ⟨c, hc⟩ := exists_pow_eq_of_infClassHom_eq_one (h w)
  have hval : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw c ^ (2 * m) = φ (u : K) := by
    rw [← _root_.map_pow, hc]
    rw [show InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (algebraMap K w.Completion (u : K)) = InfinitePlace.embedding_of_isReal hw (u : K) from
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw (u : K), hemb]
  have hnn : 0 ≤ φ (u : K) := by
    rw [← hval, pow_mul]
    exact pow_nonneg (sq_nonneg _) m
  have hne : φ (u : K) ≠ 0 := (map_ne_zero_iff φ φ.injective).2 u.ne_zero
  exact lt_of_le_of_ne hnn (Ne.symm hne)

end Positive

end InverseGalois.CFT
