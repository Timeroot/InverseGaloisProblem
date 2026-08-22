import Mathlib

/-!
# Scalar semidirect products have no quotient of order `ℓ`

Fix an odd prime `ℓ` and a finite set `S` of primes. The Galois group of
`ℚ(μ_ℓ, p^{1/ℓ} : p ∈ S)` over `ℚ` is a semidirect product `V ⋊ (ℤ/ℓ)ˣ` with
`V = (ℤ/ℓ)^{|S|}` and `(ℤ/ℓ)ˣ` acting on `V` by scalar multiplication. This file records the
group-theoretic fact that such a group admits no quotient of order `ℓ`; equivalently, the
corresponding field has no Galois subextension of degree `ℓ` over `ℚ`. This is the one point in
the Scholz–Reichardt theorem where the hypothesis that `ℓ` is odd is essential.

The mechanism is that scalar multiplication by `2` is an automorphism of `V` precisely because
`2` is invertible mod an odd `ℓ`, and conjugation by an element acting as squaring makes every
`v ∈ V` a commutator, namely `⁅g, v⁆ = v² v⁻¹ = v`.

## Main results

* `le_commutator_of_conj_eq_sq`: if some `g` conjugates every element of a subgroup `V` to its
  square, then `V` is contained in the commutator subgroup.
* `not_surjective_of_le_commutator`: if `V ≤ commutator G` is normal and `ℓ` does not divide
  `Nat.card (G ⧸ V)`, then no homomorphism from `G` onto a commutative group of order `ℓ` is
  surjective.
* `not_exists_normal_quotient_card`: the same hypotheses rule out any normal subgroup with
  quotient of prime order `ℓ`.
* `ScalarSemidirect`: the concrete group `(ℤ/ℓ)^s ⋊ (ℤ/ℓ)ˣ` for the scalar action.
* `scalarSemidirect_not_surjective` and `scalarSemidirect_not_exists_quotient_card`: for an odd
  prime `ℓ` this group has no quotient of order `ℓ`.
-/

namespace InverseGalois.CFT

section Abstract

variable {G : Type*} [Group G]

/-- If an element `g` conjugates every member of a subgroup `V` to its square, then `V` lies in
the commutator subgroup: indeed `⁅g, v⁆ = g v g⁻¹ v⁻¹ = v² v⁻¹ = v` for every `v ∈ V`. -/
theorem le_commutator_of_conj_eq_sq {V : Subgroup G} {g : G}
    (h : ∀ v ∈ V, g * v * g⁻¹ = v ^ 2) : V ≤ commutator G := by
  intro v hv
  have hc : ⁅g, v⁆ = v := by
    rw [commutatorElement_def, h v hv, sq]
    group
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top v)

/-- A group whose commutator subgroup contains a normal subgroup `V` of index prime to `ℓ`
admits no surjection onto a commutative group of order `ℓ`: any such map kills the commutator
subgroup, hence `V`, hence factors through `G ⧸ V`. -/
theorem not_surjective_of_le_commutator {H : Type*} [CommGroup H] {ℓ : ℕ}
    (V : Subgroup G) [V.Normal] (hV : V ≤ commutator G)
    (hℓ : ¬ ℓ ∣ Nat.card (G ⧸ V)) (hH : Nat.card H = ℓ) (f : G →* H) :
    ¬ Function.Surjective f := by
  intro hf
  refine hℓ ?_
  have hker : V ≤ f.ker := hV.trans (Abelianization.commutator_subset_ker f)
  set F : G ⧸ V →* H := QuotientGroup.lift V f fun x hx => MonoidHom.mem_ker.mp (hker hx)
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩
  simpa [hH] using Subgroup.card_dvd_of_surjective F hFs

/-- Under the same hypotheses there is no normal subgroup at all whose quotient has prime
order `ℓ`, since a group of prime order is cyclic and hence commutative. -/
theorem not_exists_normal_quotient_card {ℓ : ℕ} [Fact ℓ.Prime]
    (V : Subgroup G) [V.Normal] (hV : V ≤ commutator G)
    (hℓ : ¬ ℓ ∣ Nat.card (G ⧸ V)) :
    ¬ ∃ N : Subgroup G, ∃ _ : N.Normal, Nat.card (G ⧸ N) = ℓ := by
  rintro ⟨N, hN, hcard⟩
  have : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  letI : CommGroup (G ⧸ N) := IsCyclic.commGroup
  exact not_surjective_of_le_commutator V hV hℓ hcard (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

end Abstract

section Arithmetic

/-- An odd natural number is coprime to `2`. -/
theorem coprime_two_of_odd {ℓ : ℕ} (hodd : Odd ℓ) : Nat.Coprime 2 ℓ :=
  Nat.prime_two.coprime_iff_not_dvd.mpr (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd))

/-- A prime does not divide its own predecessor. -/
theorem not_dvd_sub_one {ℓ : ℕ} (hℓ : ℓ.Prime) : ¬ ℓ ∣ ℓ - 1 := by
  have h := hℓ.two_le
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

end Arithmetic

section Concrete

/-- The elementary abelian group `(ℤ/ℓ)^s`, written multiplicatively so that it can serve as the
kernel of a semidirect product. -/
abbrev ScalarModule (ℓ s : ℕ) := Multiplicative (Fin s → ZMod ℓ)

/-- The action of `(ℤ/ℓ)ˣ` on `(ℤ/ℓ)^s` by scalar multiplication, transported to the
multiplicative type synonym. -/
def scalarAction (ℓ s : ℕ) : (ZMod ℓ)ˣ →* MulAut (ScalarModule ℓ s) :=
  (MulAutMultiplicative (Fin s → ZMod ℓ)).symm.toMonoidHom.comp
    (DistribMulAction.toAddAut (ZMod ℓ)ˣ (Fin s → ZMod ℓ))

/-- The semidirect product `(ℤ/ℓ)^s ⋊ (ℤ/ℓ)ˣ` for the scalar action. -/
abbrev ScalarSemidirect (ℓ s : ℕ) := ScalarModule ℓ s ⋊[scalarAction ℓ s] (ZMod ℓ)ˣ

/-- Unfolding of the scalar action: a unit `u` acts as multiplication by `u`. -/
theorem scalarAction_apply (ℓ s : ℕ) (u : (ZMod ℓ)ˣ) (n : ScalarModule ℓ s) :
    scalarAction ℓ s u n = Multiplicative.ofAdd ((u : ZMod ℓ) • Multiplicative.toAdd n) := rfl

/-- The order of `(ℤ/ℓ)^s ⋊ (ℤ/ℓ)ˣ` for a prime `ℓ`. -/
theorem card_scalarSemidirect (ℓ s : ℕ) [Fact ℓ.Prime] :
    Nat.card (ScalarSemidirect ℓ s) = ℓ ^ s * (ℓ - 1) := by
  have h1 : Nat.card (ScalarModule ℓ s) = ℓ ^ s := by
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have h2 : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, h1, h2]

/-- When `2` is invertible mod `ℓ`, conjugation by the complement element acting as
multiplication by `2` squares every element of the kernel, so the whole kernel of
`(ℤ/ℓ)^s ⋊ (ℤ/ℓ)ˣ` lies in the commutator subgroup. -/
theorem scalarSemidirect_range_inl_le_commutator {ℓ s : ℕ} (hcop : Nat.Coprime 2 ℓ) :
    (SemidirectProduct.inl (φ := scalarAction ℓ s)).range ≤
      commutator (ScalarSemidirect ℓ s) := by
  refine le_commutator_of_conj_eq_sq (g := SemidirectProduct.inr (ZMod.unitOfCoprime 2 hcop)) ?_
  rintro _ ⟨n, rfl⟩
  rw [← map_inv, ← SemidirectProduct.inl_aut, ← map_pow]
  congr 1
  rw [scalarAction_apply]
  simp [ZMod.coe_unitOfCoprime, two_smul, sq]

/-- The same statement for the kernel of the projection to `(ℤ/ℓ)ˣ`, which is the normal
subgroup form used below. -/
theorem scalarSemidirect_ker_rightHom_le_commutator {ℓ s : ℕ} (hcop : Nat.Coprime 2 ℓ) :
    (SemidirectProduct.rightHom (φ := scalarAction ℓ s)).ker ≤
      commutator (ScalarSemidirect ℓ s) := by
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
  exact scalarSemidirect_range_inl_le_commutator hcop

/-- The quotient of `(ℤ/ℓ)^s ⋊ (ℤ/ℓ)ˣ` by its kernel is `(ℤ/ℓ)ˣ`, of order `ℓ - 1`. -/
theorem scalarSemidirect_card_quotient_ker_rightHom (ℓ s : ℕ) [Fact ℓ.Prime] :
    Nat.card (ScalarSemidirect ℓ s ⧸ (SemidirectProduct.rightHom (φ := scalarAction ℓ s)).ker)
      = ℓ - 1 := by
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    SemidirectProduct.rightHom_surjective).toEquiv, Nat.card_eq_fintype_card, ZMod.card_units]

/-- For an odd prime `ℓ`, no homomorphism from `(ℤ/ℓ)^s ⋊ (ℤ/ℓ)ˣ` onto a commutative group of
order `ℓ` is surjective. -/
theorem scalarSemidirect_not_surjective {ℓ s : ℕ} [Fact ℓ.Prime] (hodd : Odd ℓ) {H : Type*}
    [CommGroup H] (hH : Nat.card H = ℓ) (f : ScalarSemidirect ℓ s →* H) :
    ¬ Function.Surjective f :=
  not_surjective_of_le_commutator _
    (scalarSemidirect_ker_rightHom_le_commutator (coprime_two_of_odd hodd))
    (by rw [scalarSemidirect_card_quotient_ker_rightHom]; exact not_dvd_sub_one Fact.out) hH f

/-- For an odd prime `ℓ`, the group `(ℤ/ℓ)^s ⋊ (ℤ/ℓ)ˣ` has no quotient of order `ℓ`. -/
theorem scalarSemidirect_not_exists_quotient_card {ℓ s : ℕ} [Fact ℓ.Prime] (hodd : Odd ℓ) :
    ¬ ∃ N : Subgroup (ScalarSemidirect ℓ s), ∃ _ : N.Normal,
      Nat.card (ScalarSemidirect ℓ s ⧸ N) = ℓ :=
  not_exists_normal_quotient_card _
    (scalarSemidirect_ker_rightHom_le_commutator (coprime_two_of_odd hodd))
    (by rw [scalarSemidirect_card_quotient_ker_rightHom]; exact not_dvd_sub_one Fact.out)

end Concrete

end InverseGalois.CFT
