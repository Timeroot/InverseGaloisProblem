/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Cyclic

/-!
# Finite abelian groups are inverse Galois groups

Every finite abelian group `G` occurs as a Galois group over `ℚ`.

## Strategy

This is the `Fintype`-indexed generalization of the cyclic argument in `Core/Cyclic.lean`
(`ZMod.exists_units_surjection` is the `ι = Unit` case):

1. By the structure theorem (`CommGroup.equiv_prod_multiplicative_zmod_of_finite`),
   `G ≃* ∏ᵢ Multiplicative (ZMod (nᵢ))` for a finite family with `nᵢ ≥ 2`.
2. By Dirichlet (`Nat.exists_prime_gt_modEq_one`) choose **distinct** primes `pᵢ ≡ 1 (mod nᵢ)`.
3. With `m = ∏ᵢ pᵢ`, the CRT (`ZMod.prodEquivPi`) plus `MulEquiv.piUnits` and the cyclicity of
   `(ZMod pᵢ)ˣ` give `(ZMod m)ˣ ≃* ∏ᵢ Multiplicative (ZMod (pᵢ - 1))`.
4. Since `nᵢ ∣ pᵢ - 1`, reduction (`ZMod.castHom_surjective`) gives a surjection onto
   `∏ᵢ Multiplicative (ZMod (nᵢ)) ≃* G`.
5. `(ZMod m)ˣ` is an inverse Galois group (`IsInverseGalois.units_zmod`), and the inverse
   Galois property is closed under surjections (`IsInverseGalois.of_surjective`).

## Main result

* `IsInverseGalois.of_finite_commGroup`: every finite commutative group is an inverse Galois
  group over `ℚ`.
-/

open scoped Classical

noncomputable section

/-- A finite family of **distinct** primes `pᵢ` with `pᵢ ≡ 1 (mod nᵢ)` (so `nᵢ ∣ pᵢ - 1`).
Distinctness is obtained by choosing each prime larger than all previously chosen ones. -/
theorem exists_prime_family {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0) :
    ∃ p : ι → ℕ, (∀ i, (p i).Prime) ∧ (∀ i, n i ∣ p i - 1) ∧ Function.Injective p := by
  classical
  suffices h : ∀ s : Finset ι, ∃ p : ι → ℕ,
      (∀ i ∈ s, (p i).Prime) ∧ (∀ i ∈ s, n i ∣ p i - 1) ∧ Set.InjOn p s by
    obtain ⟨p, h1, h2, h3⟩ := h Finset.univ
    exact ⟨p, fun i ↦ h1 i (Finset.mem_univ i), fun i ↦ h2 i (Finset.mem_univ i),
      fun a b hab ↦ h3 (Finset.mem_univ a) (Finset.mem_univ b) hab⟩
  intro s
  induction s using Finset.induction with
  | empty => refine ⟨fun _ ↦ 2, ?_, ?_, ?_⟩ <;> simp
  | @insert a s ha ih =>
    obtain ⟨p, hp_prime, hp_dvd, hp_inj⟩ := ih
    obtain ⟨q, hq_prime, hq_gt, hq_mod⟩ :=
      Nat.exists_prime_gt_modEq_one (k := n a) (s.sup p) (hn a)
    have hq1 : (1 : ℕ) ≤ q := hq_prime.one_lt.le
    have hlt : ∀ i ∈ s, p i < q := fun i hi ↦ lt_of_le_of_lt (Finset.le_sup hi) hq_gt
    have hne : ∀ {i}, i ∈ s → i ≠ a := fun hi ↦ ne_of_mem_of_not_mem hi ha
    refine ⟨Function.update p a q, ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · rwa [Function.update_self]
      · rw [Function.update_of_ne (hne his)]
        exact hp_prime i his
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · rw [Function.update_self]
        exact (Nat.modEq_iff_dvd' hq1).mp hq_mod.symm
      · rw [Function.update_of_ne (hne his)]
        exact hp_dvd i his
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      -- For `i ∈ s`, `update p a q i = p i ≤ s.sup p < q = update p a q a`, so the new prime
      -- `q` is distinct from every old one.
      rcases hx with rfl | hxs <;> rcases hy with rfl | hys
      · rfl
      · rw [Function.update_self, Function.update_of_ne (hne hys)] at hxy
        exact absurd hxy.symm (Nat.ne_of_lt (hlt y hys))
      · rw [Function.update_self, Function.update_of_ne (hne hxs)] at hxy
        exact absurd hxy (Nat.ne_of_lt (hlt x hxs))
      · rw [Function.update_of_ne (hne hxs), Function.update_of_ne (hne hys)] at hxy
        exact hp_inj (Finset.mem_coe.mpr hxs) (Finset.mem_coe.mpr hys) hxy

/-- **Every finite abelian group is an inverse Galois group over `ℚ`.** -/
theorem IsInverseGalois.of_finite_commGroup (G : Type*) [CommGroup G] [Finite G] :
    IsInverseGalois G := by
  classical
  obtain ⟨ι, hιFin, n, hn1, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have hn0 : ∀ i, n i ≠ 0 := fun i ↦ (zero_lt_one.trans (hn1 i)).ne'
  obtain ⟨p, hp_prime, hp_dvd, hp_inj⟩ := exists_prime_family n hn0
  set m : ℕ := ∏ i, p i with hm
  have hm0 : NeZero m := ⟨hm ▸ Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hp_prime i).ne_zero⟩
  -- Chinese remainder theorem on the units.
  have hcop : Pairwise fun i j ↦ Nat.Coprime (p i) (p j) := fun i j hij ↦
    (Nat.coprime_primes (hp_prime i) (hp_prime j)).mpr (hp_inj.ne hij)
  let eU : (ZMod m)ˣ ≃* ∀ i, (ZMod (p i))ˣ :=
    (Units.mapEquiv (ZMod.prodEquivPi p hcop).toMulEquiv).trans MulEquiv.piUnits
  -- Each `(ZMod pᵢ)ˣ` is cyclic of order `pᵢ - 1`.
  have ecyc : ∀ i, (ZMod (p i))ˣ ≃* Multiplicative (ZMod (p i - 1)) := by
    intro i
    have := Fact.mk (hp_prime i)
    rw [← Nat.totient_prime (hp_prime i), ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact (zmodCyclicMulEquiv inferInstance).symm
  let ePi : (ZMod m)ˣ ≃* ∀ i, Multiplicative (ZMod (p i - 1)) :=
    eU.trans (MulEquiv.piCongrRight ecyc)
  -- Componentwise reduction `ZMod (pᵢ - 1) → ZMod nᵢ` is surjective.
  let f : ∀ i, Multiplicative (ZMod (p i - 1)) →* Multiplicative (ZMod (n i)) := fun i ↦
    (ZMod.castHom (hp_dvd i) (ZMod (n i))).toAddMonoidHom.toMultiplicative
  have hf_surj : ∀ i, Function.Surjective (f i) := fun i ↦ ZMod.castHom_surjective (hp_dvd i)
  let F : (∀ i, Multiplicative (ZMod (p i - 1))) →* ∀ i, Multiplicative (ZMod (n i)) :=
    Pi.monoidHom fun i ↦ (f i).comp (Pi.evalMonoidHom _ i)
  have hF_surj : Function.Surjective F := by
    intro b
    refine ⟨fun i ↦ (hf_surj i (b i)).choose, funext fun i ↦ ?_⟩
    simpa [F, Pi.monoidHom, Pi.evalMonoidHom] using (hf_surj i (b i)).choose_spec
  -- Assemble the surjection `(ZMod m)ˣ ↠ ∏ᵢ Multiplicative (ZMod nᵢ) ≃* G`.
  have hPi : IsInverseGalois (∀ i, Multiplicative (ZMod (n i))) :=
    (IsInverseGalois.units_zmod m).of_surjective (F.comp ePi.toMonoidHom)
      (hF_surj.comp ePi.surjective)
  exact hPi.of_mulEquiv e.symm

end
