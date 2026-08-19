import Mathieu.M11SteinerCore

/-!
# `M₁₁` is the full symmetry group of the Witt Steiner system
-/

namespace Mathieu

open Equiv

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

private lemma block_completion_0123 (x : Fin 11)
    (h : ({0, 1, 2, 3, x} : Finset (Fin 11)) ∈ M11Blocks) : x = 9 := by
  revert x
  decide

private lemma block_pair_023 (x y : Fin 11)
    (hx : x ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11)))
    (hy : y ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11))) (hne : x ≠ y)
    (h : ({0, 2, 3, x, y} : Finset (Fin 11)) ∈ M11Blocks) :
    (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4) ∨ (x = 6 ∧ y = 8) ∨
      (x = 8 ∧ y = 6) ∨ (x = 7 ∧ y = 10) ∨ (x = 10 ∧ y = 7) := by
  revert x y
  decide

private lemma block_pair_012 (x y : Fin 11)
    (hx : x ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11)))
    (hy : y ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11))) (hne : x ≠ y)
    (h : ({0, 1, 2, x, y} : Finset (Fin 11)) ∈ M11Blocks) :
    (x = 4 ∧ y = 7) ∨ (x = 7 ∧ y = 4) ∨ (x = 5 ∧ y = 6) ∨
      (x = 6 ∧ y = 5) ∨ (x = 8 ∧ y = 10) ∨ (x = 10 ∧ y = 8) := by
  revert x y
  decide

private lemma block_pair_123 (x y : Fin 11)
    (hx : x ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11)))
    (hy : y ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11))) (hne : x ≠ y)
    (h : ({1, 2, 3, x, y} : Finset (Fin 11)) ∈ M11Blocks) :
    (x = 4 ∧ y = 10) ∨ (x = 10 ∧ y = 4) ∨ (x = 5 ∧ y = 8) ∨
      (x = 8 ∧ y = 5) ∨ (x = 6 ∧ y = 7) ∨ (x = 7 ∧ y = 6) := by
  revert x y
  decide

private lemma block_triple_01 (x y z : Fin 11)
    (hx : x ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11)))
    (hy : y ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11)))
    (hz : z ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : ({0, 1, x, y, z} : Finset (Fin 11)) ∈ M11Blocks) :
    ((x = 4 ∨ x = 5 ∨ x = 10) ∧ (y = 4 ∨ y = 5 ∨ y = 10) ∧
      (z = 4 ∨ z = 5 ∨ z = 10)) ∨
    ((x = 6 ∨ x = 7 ∨ x = 8) ∧ (y = 6 ∨ y = 7 ∨ y = 8) ∧
      (z = 6 ∨ z = 7 ∨ z = 8)) := by
  revert x y z
  decide

private lemma incidence_solution (a b c d f : Fin 11)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (haf' : a ≠ f)
    (hbc' : b ≠ c) (hbd : b ≠ d) (hbf : b ≠ f)
    (hcd : c ≠ d) (hcf : c ≠ f) (hdf : d ≠ f)
    (hde : (d = 4 ∧ f = 5) ∨ (d = 5 ∧ f = 4) ∨ (d = 6 ∧ f = 8) ∨
      (d = 8 ∧ f = 6) ∨ (d = 7 ∧ f = 10) ∨ (d = 10 ∧ f = 7))
    (hbc : (b = 4 ∧ c = 7) ∨ (b = 7 ∧ c = 4) ∨ (b = 5 ∧ c = 6) ∨
      (b = 6 ∧ c = 5) ∨ (b = 8 ∧ c = 10) ∨ (b = 10 ∧ c = 8))
    (haf : (a = 4 ∧ f = 10) ∨ (a = 10 ∧ f = 4) ∨ (a = 5 ∧ f = 8) ∨
      (a = 8 ∧ f = 5) ∨ (a = 6 ∧ f = 7) ∨ (a = 7 ∧ f = 6))
    (habf : ((a = 4 ∨ a = 5 ∨ a = 10) ∧ (b = 4 ∨ b = 5 ∨ b = 10) ∧
        (f = 4 ∨ f = 5 ∨ f = 10)) ∨
      ((a = 6 ∨ a = 7 ∨ a = 8) ∧ (b = 6 ∨ b = 7 ∨ b = 8) ∧
        (f = 6 ∨ f = 7 ∨ f = 8))) :
    a = 4 ∧ b = 5 ∧ c = 6 ∧ d = 7 ∧ f = 10 := by
  rcases hde with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases haf with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
    ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all

/-- Five strategically chosen block incidences rigidify a permutation fixing the base
four points.  The small kernel checks above merely read the relevant rows of the block table;
the synthesis below is an incidence argument and does not enumerate permutations. -/
private lemma fixing_base_of_five_blocks
    (g : Perm (Fin 11))
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3)
    (hB0 : ({0, 1, 2, 3, 9} : Finset (Fin 11)).map g.toEmbedding ∈ M11Blocks)
    (hB1 : ({0, 1, 4, 5, 10} : Finset (Fin 11)).map g.toEmbedding ∈ M11Blocks)
    (hB2 : ({0, 2, 3, 7, 10} : Finset (Fin 11)).map g.toEmbedding ∈ M11Blocks)
    (hB3 : ({0, 1, 2, 5, 6} : Finset (Fin 11)).map g.toEmbedding ∈ M11Blocks)
    (hB4 : ({1, 2, 3, 4, 10} : Finset (Fin 11)).map g.toEmbedding ∈ M11Blocks) : g = 1 := by
  have hinj := g.injective
  have h9 : g 9 = 9 := block_completion_0123 _ (by simpa [h0, h1, h2, h3] using hB0)
  have hout (x : Fin 11) (hx : x ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11))) :
      g x ∉ ({0, 1, 2, 3, 9} : Finset (Fin 11)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    constructor
    · exact fun h => hx.1 (hinj (h.trans h0.symm))
    constructor
    · exact fun h => hx.2.1 (hinj (h.trans h1.symm))
    constructor
    · exact fun h => hx.2.2.1 (hinj (h.trans h2.symm))
    constructor
    · exact fun h => hx.2.2.2.1 (hinj (h.trans h3.symm))
    · exact fun h => hx.2.2.2.2 (hinj (h.trans h9.symm))
  have hp1 := block_pair_023 (g 7) (g 10) (hout 7 (by decide)) (hout 10 (by decide))
    (fun h => (by have := hinj h; contradiction)) (by simpa [h0, h2, h3] using hB2)
  have hp2 := block_pair_012 (g 5) (g 6) (hout 5 (by decide)) (hout 6 (by decide))
    (fun h => (by have := hinj h; contradiction)) (by simpa [h0, h1, h2] using hB3)
  have hp3 := block_pair_123 (g 4) (g 10) (hout 4 (by decide)) (hout 10 (by decide))
    (fun h => (by have := hinj h; contradiction)) (by simpa [h1, h2, h3] using hB4)
  have ht := block_triple_01 (g 4) (g 5) (g 10)
    (hout 4 (by decide)) (hout 5 (by decide)) (hout 10 (by decide))
    (fun h => (by have := hinj h; contradiction)) (fun h => (by have := hinj h; contradiction)) (fun h => (by have := hinj h; contradiction))
    (by simpa [h0, h1] using hB1)
  have hall : g 4 = 4 ∧ g 5 = 5 ∧ g 6 = 6 ∧ g 7 = 7 ∧ g 10 = 10 :=
    incidence_solution (g 4) (g 5) (g 6) (g 7) (g 10)
      (fun h => by have := hinj h; contradiction) (fun h => by have := hinj h; contradiction)
      (fun h => by have := hinj h; contradiction) (fun h => by have := hinj h; contradiction)
      (fun h => by have := hinj h; contradiction) (fun h => by have := hinj h; contradiction)
      (fun h => by have := hinj h; contradiction) (fun h => by have := hinj h; contradiction)
      (fun h => by have := hinj h; contradiction) (fun h => by have := hinj h; contradiction)
      hp1 hp2 hp3 ht
  rcases hall with ⟨h4, h5, h6, h7, h10⟩
  obtain ⟨x, hx⟩ := g.surjective 8
  have h8 : g 8 = 8 := by
    fin_cases x <;> simp_all
  ext x
  fin_cases x <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- A symmetry fixing the four displayed base points is the identity.  Preservation of five
selected blocks reduces rigidity to the preceding finite incidence lemma. -/
lemma M11SteinerAut_fixing_base
    (g : Perm (Fin 11)) (hg : g ∈ M11SteinerAut)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) : g = 1 := by
  apply fixing_base_of_five_blocks g h0 h1 h2 h3
  · exact (hg _).mp (by decide)
  · exact (hg _).mp (by decide)
  · exact (hg _).mp (by decide)
  · exact (hg _).mp (by decide)
  · exact (hg _).mp (by decide)

/-- The full symmetry group of the `(5,4,11)` Steiner system is exactly `M₁₁`. -/
theorem M11_eq_M11SteinerAut : M11 = M11SteinerAut := by
  apply le_antisymm M11_le_M11SteinerAut
  intro g hg
  let e0 : Fin 4 ↪ Fin 11 := Fin.castLEEmb (by omega)
  let eg : Fin 4 ↪ Fin 11 :=
    ⟨fun i => g (e0 i), fun _ _ h => e0.injective (g.injective h)⟩
  obtain ⟨m, hm⟩ := MulAction.isMultiplyPretransitive_iff.mp
    M11_isMultiplyPretransitive_four e0 eg
  have hagree : ∀ i : Fin 4, (m : Perm (Fin 11)) (e0 i) = g (e0 i) := by
    intro i
    have hi := Function.Embedding.ext_iff.mp hm i
    simpa [e0, eg, Subgroup.smul_def, Equiv.Perm.smul_def] using hi
  have hk : (↑m : Perm (Fin 11))⁻¹ * g ∈ M11SteinerAut :=
    M11SteinerAut.mul_mem (M11SteinerAut.inv_mem (M11_le_M11SteinerAut m.property)) hg
  have h0m := hagree (0 : Fin 4)
  have h1m := hagree (1 : Fin 4)
  have h2m := hagree (2 : Fin 4)
  have h3m := hagree (3 : Fin 4)
  change (m : Perm (Fin 11)) 0 = g 0 at h0m
  change (m : Perm (Fin 11)) 1 = g 1 at h1m
  change (m : Perm (Fin 11)) 2 = g 2 at h2m
  change (m : Perm (Fin 11)) 3 = g 3 at h3m
  have hfix : (↑m : Perm (Fin 11))⁻¹ * g = 1 := by
    apply M11SteinerAut_fixing_base _ hk
    all_goals simp only [Equiv.Perm.coe_mul, Equiv.Perm.coe_inv, Function.comp_apply]
    · rw [← h0m]; simp
    · rw [← h1m]; simp
    · rw [← h2m]; simp
    · rw [← h3m]; simp
  have hgm : g = (m : Perm (Fin 11)) := by
    apply_fun (fun k : Perm (Fin 11) => (m : Perm (Fin 11)) * k) at hfix
    simpa using hfix
  rw [hgm]
  exact m.property

end Mathieu
