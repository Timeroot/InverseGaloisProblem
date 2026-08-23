import Mathlib
import InverseGalois.CFT.ScalarSemidirect

/-!
# Radical fields have no Galois subextension of degree `ℓ`

Fix an odd prime `ℓ` and a number field `R`, Galois over `ℚ`, which is generated over `ℚ` by a
primitive `ℓ`-th root of unity `ζ` together with a set `A` of elements whose `ℓ`-th powers are
rational.  The Galois group of such a field has no quotient of order `ℓ`.  Concretely, in Serre's
application `R` is `ℚ(μ_ℓ, p^{1/ℓ} : p ∈ S)` for a finite set of primes `S`, and the statement is
the field-theoretic form of the fact that a scalar semidirect product `V ⋊ (ℤ/ℓ)ˣ` has no quotient
of order `ℓ`.  This is the one point of the Scholz–Reichardt theorem where the hypothesis that `ℓ`
is odd is essential.

The mechanism is entirely explicit.  Every conjugate of an element `α` with `α ^ ℓ ∈ ℚ` is `ζ ^ i α`
for some `i`, so an automorphism `v` fixing `ζ` is described by exponents, and the automorphism `g`
raising `ζ` to its square — which exists because `2` is coprime to the odd prime `ℓ` — doubles
those exponents.  Hence `g v g⁻¹ = v ^ 2` for every `v` fixing `ζ`, which forces the subgroup
fixing `ζ` into the commutator subgroup; its quotient has order dividing `ℓ - 1`.

## Main results

* `exists_pow_mul_of_pow_eq_algebraMap`: an automorphism moves an element with rational `ℓ`-th
  power by a power of `ζ`.
* `conj_eq_sq_of_radical`: conjugating by an automorphism squaring `ζ` squares every automorphism
  fixing `ζ`.
* `ker_autToPow_le_commutator`: the automorphisms fixing `ζ` lie in the commutator subgroup.
* `not_surjective_of_radical`: **no surjection onto a commutative group of order `ℓ`.**
* `not_exists_normal_quotient_card_of_radical`: no normal subgroup of index `ℓ`.
* `finrank_ne_of_radical`: no subextension of `R` is Galois of degree `ℓ` over `ℚ`.
* `inf_eq_bot_of_radical`: inside an ambient number field, such a field meets every Galois field
  of degree `ℓ` in `ℚ` only.
-/

open Module Polynomial

namespace InverseGalois.CFT

section Conjugates

variable {ℓ : ℕ} {R : Type*} [Field R] [Algebra ℚ R] {ζ : R}

/-- An automorphism multiplies an element whose `ℓ`-th power is rational by a power of a
primitive `ℓ`-th root of unity: the ratio of the two elements is itself an `ℓ`-th root of
unity. -/
theorem exists_pow_mul_of_pow_eq_algebraMap [NeZero ℓ] (hζ : IsPrimitiveRoot ζ ℓ) {α : R} {c : ℚ}
    (hα : α ^ ℓ = algebraMap ℚ R c) (σ : R ≃ₐ[ℚ] R) : ∃ i : ℕ, σ α = ζ ^ i * α := by
  rcases eq_or_ne α 0 with rfl | h0
  · exact ⟨0, by simp⟩
  have h1 : σ α ^ ℓ = α ^ ℓ := by rw [← map_pow, hα, AlgEquiv.commutes]
  have h2 : (σ α / α) ^ ℓ = 1 := by rw [div_pow, h1, div_self (pow_ne_zero _ h0)]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h2
  exact ⟨i, by rw [hi, div_mul_cancel₀ _ h0]⟩

end Conjugates

section Radical

variable {ℓ : ℕ} {R : Type*} [Field R] [NumberField R] [IsGalois ℚ R] {ζ : R} {A : Set R}

omit [IsGalois ℚ R] in
/-- **Conjugation by a squaring automorphism squares the automorphisms fixing `ζ`.**  Both sides
are determined by their values on `ζ` and on the radical generators, where the computation is a
bookkeeping of exponents of `ζ`. -/
theorem conj_eq_sq_of_radical [NeZero ℓ] (hζ : IsPrimitiveRoot ζ ℓ)
    (hA : ∀ α ∈ A, ∃ c : ℚ, α ^ ℓ = algebraMap ℚ R c)
    (htop : IntermediateField.adjoin ℚ (insert ζ A) = ⊤) {g v : R ≃ₐ[ℚ] R} (hg : g ζ = ζ ^ 2)
    (hv : v ζ = ζ) : g * v * g⁻¹ = v ^ 2 := by
  have halg : Algebra.adjoin ℚ (insert ζ A) = ⊤ := by
    have h := congrArg IntermediateField.toSubalgebra htop
    rwa [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), IntermediateField.top_toSubalgebra] at h
  have hgpow : ∀ k : ℕ, g (ζ ^ k) = ζ ^ (2 * k) := fun k => by rw [map_pow, hg, ← pow_mul]
  have hvpow : ∀ k : ℕ, v (ζ ^ k) = ζ ^ k := fun k => by rw [map_pow, hv]
  have hgg : ∀ z : R, g (g⁻¹ z) = z := fun z => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have key : ((g * v * g⁻¹ : R ≃ₐ[ℚ] R) : R →ₐ[ℚ] R) = ((v ^ 2 : R ≃ₐ[ℚ] R) : R →ₐ[ℚ] R) := by
    refine AlgHom.ext_of_adjoin_eq_top halg fun y hy => ?_
    obtain ⟨c, hc⟩ : ∃ c : ℚ, y ^ ℓ = algebraMap ℚ R c := by
      rcases hy with rfl | hy
      · exact ⟨1, by rw [hζ.pow_eq_one, map_one]⟩
      · exact hA y hy
    obtain ⟨a, ha⟩ := exists_pow_mul_of_pow_eq_algebraMap hζ hc v
    obtain ⟨b, hb⟩ := exists_pow_mul_of_pow_eq_algebraMap hζ hc g⁻¹
    have hyb : ζ ^ (2 * b) * g y = y := by rw [← hgpow, ← map_mul, ← hb, hgg]
    show (g * v * g⁻¹) y = (v ^ 2) y
    calc (g * v * g⁻¹) y = g (v (g⁻¹ y)) := by rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      _ = g (ζ ^ b * (ζ ^ a * y)) := by rw [hb, map_mul, hvpow, ha]
      _ = ζ ^ (2 * b) * (ζ ^ (2 * a) * g y) := by rw [map_mul, map_mul, hgpow, hgpow]
      _ = ζ ^ (2 * a) * (ζ ^ (2 * b) * g y) := mul_left_comm _ _ _
      _ = ζ ^ (2 * a) * y := by rw [hyb]
      _ = (v ^ 2) y := by
          rw [sq, AlgEquiv.mul_apply, ha, map_mul, hvpow, ha, ← mul_assoc, ← pow_add, two_mul]
  exact AlgEquiv.ext fun x => AlgHom.congr_fun key x

/-- **An automorphism raising `ζ` to its square exists.**  For an odd prime `ℓ` the element `ζ ^ 2`
is again a primitive `ℓ`-th root of unity, so it has the same minimal polynomial over `ℚ`, namely
the `ℓ`-th cyclotomic polynomial, and a normal extension realises every such conjugation. -/
theorem exists_apply_eq_sq [Fact ℓ.Prime] (hodd : Odd ℓ) (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ g : R ≃ₐ[ℚ] R, g ζ = ζ ^ 2 := by
  have hp : ℓ.Prime := Fact.out
  have h2 : IsPrimitiveRoot (ζ ^ 2) ℓ := hζ.pow_of_coprime 2 (coprime_two_of_odd hodd)
  have hmin : minpoly ℚ (ζ ^ 2) = minpoly ℚ ζ := by
    rw [← cyclotomic_eq_minpoly_rat h2 hp.pos, ← cyclotomic_eq_minpoly_rat hζ hp.pos]
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit R).mp hmin
  exact ⟨g, hg⟩

omit [IsGalois ℚ R] in
/-- An automorphism in the kernel of the cyclotomic character fixes `ζ`. -/
theorem apply_eq_of_mem_ker_autToPow [Fact ℓ.Prime] (hζ : IsPrimitiveRoot ζ ℓ) {v : R ≃ₐ[ℚ] R}
    (hv : v ∈ (hζ.autToPow ℚ).ker) : v ζ = ζ := by
  have h := hζ.autToPow_spec ℚ v
  rw [MonoidHom.mem_ker.mp hv, Units.val_one, ZMod.val_one, pow_one] at h
  exact h.symm

omit [IsGalois ℚ R] in
/-- The kernel of the cyclotomic character has index dividing `ℓ - 1`, so `ℓ` does not divide the
order of the quotient by it. -/
theorem not_dvd_card_quotient_ker_autToPow [Fact ℓ.Prime] (hζ : IsPrimitiveRoot ζ ℓ) :
    ¬ ℓ ∣ Nat.card ((R ≃ₐ[ℚ] R) ⧸ (hζ.autToPow ℚ).ker) := by
  intro hdvd
  refine not_dvd_sub_one (Fact.out : ℓ.Prime) (hdvd.trans ?_)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (hζ.autToPow ℚ)).toEquiv]
  have h := Subgroup.card_subgroup_dvd_card (hζ.autToPow ℚ).range
  rwa [Nat.card_eq_fintype_card (α := (ZMod ℓ)ˣ), ZMod.card_units] at h

/-- **The automorphisms fixing `ζ` are commutators.**  Conjugation by an automorphism raising `ζ`
to its square turns every such automorphism `v` into `v ^ 2`, so that `v` itself is the commutator
of the two. -/
theorem ker_autToPow_le_commutator [Fact ℓ.Prime] (hodd : Odd ℓ) (hζ : IsPrimitiveRoot ζ ℓ)
    (hA : ∀ α ∈ A, ∃ c : ℚ, α ^ ℓ = algebraMap ℚ R c)
    (htop : IntermediateField.adjoin ℚ (insert ζ A) = ⊤) :
    (hζ.autToPow ℚ).ker ≤ commutator (R ≃ₐ[ℚ] R) := by
  obtain ⟨g, hg⟩ := exists_apply_eq_sq hodd hζ
  exact le_commutator_of_conj_eq_sq fun v hv =>
    conj_eq_sq_of_radical hζ hA htop hg (apply_eq_of_mem_ker_autToPow hζ hv)

/-- **A field generated by roots of unity and radicals has no quotient of order `ℓ`.**  For an odd
prime `ℓ`, no homomorphism from the Galois group of such a field onto a commutative group of
order `ℓ` is surjective. -/
theorem not_surjective_of_radical [Fact ℓ.Prime] (hodd : Odd ℓ) (hζ : IsPrimitiveRoot ζ ℓ)
    (hA : ∀ α ∈ A, ∃ c : ℚ, α ^ ℓ = algebraMap ℚ R c)
    (htop : IntermediateField.adjoin ℚ (insert ζ A) = ⊤) {H : Type*} [CommGroup H]
    (hH : Nat.card H = ℓ) (f : (R ≃ₐ[ℚ] R) →* H) : ¬ Function.Surjective f :=
  not_surjective_of_le_commutator _ (ker_autToPow_le_commutator hodd hζ hA htop)
    (not_dvd_card_quotient_ker_autToPow hζ) hH f

/-- **The Galois group of a field generated by roots of unity and radicals has no normal subgroup
of index `ℓ`**, for `ℓ` an odd prime. -/
theorem not_exists_normal_quotient_card_of_radical [Fact ℓ.Prime] (hodd : Odd ℓ)
    (hζ : IsPrimitiveRoot ζ ℓ) (hA : ∀ α ∈ A, ∃ c : ℚ, α ^ ℓ = algebraMap ℚ R c)
    (htop : IntermediateField.adjoin ℚ (insert ζ A) = ⊤) :
    ¬ ∃ N : Subgroup (R ≃ₐ[ℚ] R), ∃ _ : N.Normal, Nat.card ((R ≃ₐ[ℚ] R) ⧸ N) = ℓ :=
  not_exists_normal_quotient_card _ (ker_autToPow_le_commutator hodd hζ hA htop)
    (not_dvd_card_quotient_ker_autToPow hζ)

/-- **No subextension is Galois of degree `ℓ`.**  A Galois subextension of degree `ℓ` would have
cyclic Galois group of order `ℓ`, onto which the whole Galois group surjects by restriction. -/
theorem finrank_ne_of_radical [Fact ℓ.Prime] (hodd : Odd ℓ) (hζ : IsPrimitiveRoot ζ ℓ)
    (hA : ∀ α ∈ A, ∃ c : ℚ, α ^ ℓ = algebraMap ℚ R c)
    (htop : IntermediateField.adjoin ℚ (insert ζ A) = ⊤) (E : IntermediateField ℚ R)
    [IsGalois ℚ ↥E] : finrank ℚ ↥E ≠ ℓ := by
  intro hE
  have hcard : Nat.card (↥E ≃ₐ[ℚ] ↥E) = ℓ := by rw [IsGalois.card_aut_eq_finrank ℚ ↥E, hE]
  haveI : IsCyclic (↥E ≃ₐ[ℚ] ↥E) := isCyclic_of_prime_card hcard
  letI : CommGroup (↥E ≃ₐ[ℚ] ↥E) := IsCyclic.commGroup
  exact not_surjective_of_radical hodd hζ hA htop hcard (AlgEquiv.restrictNormalHom ↥E)
    (AlgEquiv.restrictNormalHom_surjective R)

end Radical

section Ambient

variable {ℓ : ℕ} {N : Type*} [Field N] [NumberField N] {ζ : N} {A : Set N}

/-- **A radical field is linearly disjoint from every Galois field of degree `ℓ`.**  Inside an
ambient number field, a subfield generated by a primitive `ℓ`-th root of unity and by elements
with rational `ℓ`-th powers meets a Galois subfield of degree `ℓ` in `ℚ` only, because a Galois
extension of prime degree has no proper intermediate field. -/
theorem inf_eq_bot_of_radical [Fact ℓ.Prime] (hodd : Odd ℓ) (hζ : IsPrimitiveRoot ζ ℓ)
    (hA : ∀ α ∈ A, ∃ c : ℚ, α ^ ℓ = algebraMap ℚ N c) {R : IntermediateField ℚ N} [IsGalois ℚ ↥R]
    (hgen : IntermediateField.adjoin ℚ (insert ζ A) = R) (E : IntermediateField ℚ N)
    [IsGalois ℚ ↥E] (hE : finrank ℚ ↥E = ℓ) : E ⊓ R = ⊥ := by
  have hdvd : finrank ℚ ↥(E ⊓ R) ∣ ℓ := by
    rw [← hE]; exact IntermediateField.finrank_dvd_of_le_right inf_le_left
  rcases (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hl
  · exact IntermediateField.finrank_eq_one_iff.mp h1
  exfalso
  have hER : E ≤ R :=
    inf_eq_left.mp (IntermediateField.eq_of_le_of_finrank_eq inf_le_left (by rw [hl, hE]))
  haveI : NumberField ↥R := ⟨⟩
  have hζR : ζ ∈ R := hgen ▸ IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  have hAR : ∀ α ∈ A, α ∈ R := fun α hα =>
    hgen ▸ IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ hα)
  have himg : (Subtype.val '' (Subtype.val ⁻¹' A : Set ↥R) : Set N) = A :=
    Set.image_preimage_eq_of_subset fun α hα => ⟨⟨α, hAR α hα⟩, rfl⟩
  have hζ' : IsPrimitiveRoot (⟨ζ, hζR⟩ : ↥R) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥R N) hζ (algebraMap ↥R N).injective
  have hA' : ∀ α ∈ (Subtype.val ⁻¹' A : Set ↥R), ∃ c : ℚ, α ^ ℓ = algebraMap ℚ ↥R c := by
    intro α hα
    obtain ⟨c, hc⟩ := hA (α : N) hα
    refine ⟨c, Subtype.ext ?_⟩
    rw [IntermediateField.coe_pow, hc, IsScalarTower.algebraMap_apply ℚ ↥R N]
    rfl
  have htop' : IntermediateField.adjoin ℚ (insert (⟨ζ, hζR⟩ : ↥R) (Subtype.val ⁻¹' A)) = ⊤ := by
    refine IntermediateField.lift_injective R ?_
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_insert_eq, himg]
    exact hgen
  letI : Algebra ↥E ↥R := (IntermediateField.inclusion hER).toAlgebra
  haveI : IsScalarTower ℚ ↥E ↥R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcard : Nat.card (↥E ≃ₐ[ℚ] ↥E) = ℓ := by rw [IsGalois.card_aut_eq_finrank ℚ ↥E, hE]
  haveI : IsCyclic (↥E ≃ₐ[ℚ] ↥E) := isCyclic_of_prime_card hcard
  letI : CommGroup (↥E ≃ₐ[ℚ] ↥E) := IsCyclic.commGroup
  exact not_surjective_of_radical hodd hζ' hA' htop' hcard (AlgEquiv.restrictNormalHom ↥E)
    (AlgEquiv.restrictNormalHom_surjective ↥R)

end Ambient

end InverseGalois.CFT
