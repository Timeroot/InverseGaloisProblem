import Mathlib
import InverseGalois.CFT.Decomposition

/-!
# The tame inertia character

Let `K` be a number field which is Galois over `ℚ`, let `P` be a nonzero prime of `𝓞 K` and let
`π` be a uniformizer at `P`, that is, an element of `P` which does not lie in `P ^ 2`.  Every
element `σ` of the inertia group at `P` satisfies `σ • π ≡ c * π` modulo `P ^ 2` for an element
`c` of `𝓞 K` which is well defined modulo `P`; the resulting map
`Ideal.inertia Gal(K/ℚ) P → (𝓞 K ⧸ P)ˣ` is the tame inertia character.

## Main results

* `InverseGalois.CFT.tameChar`: the tame inertia character, a group homomorphism from the
  inertia group at `P` to the units of the residue field.
* `InverseGalois.CFT.tameChar_eq_of_isUniformizer`: the tame character does not depend on the
  choice of uniformizer.
* `InverseGalois.CFT.tameChar_conj`: the tame character is equivariant for the action of the
  decomposition group on the residue field.
* `InverseGalois.CFT.tameChar_injective`: in the tame case, that is when the residue
  characteristic does not divide the order of the inertia group, the tame character is injective.
* `InverseGalois.CFT.card_inertia_dvd_sub_one_of_liesOver`: if `K / ℚ` is abelian and the prime
  `Q` lies over the rational prime `p`, which does not divide the order of the inertia group at
  `Q`, then that order divides `p - 1`.
-/

open NumberField

open scoped Pointwise

namespace InverseGalois.CFT

variable {K : Type*} [Field K] [NumberField K]

section Uniformizer

/-- An element `π` of `𝓞 K` is a uniformizer at the prime `P` when it lies in `P` but not in
`P ^ 2`, that is, when it has valuation exactly one at `P`. -/
def IsUniformizer (P : Ideal (𝓞 K)) (π : 𝓞 K) : Prop := π ∈ P ∧ π ∉ P ^ 2

variable {P : Ideal (𝓞 K)} [P.IsPrime] {π : 𝓞 K}

omit [NumberField K] in
/-- A prime admitting a uniformizer is nonzero. -/
theorem IsUniformizer.ne_bot (h : IsUniformizer P π) : P ≠ ⊥ := by
  rintro rfl
  obtain ⟨h1, h2⟩ := h
  rw [Ideal.mem_bot] at h1
  exact h2 (h1 ▸ Submodule.zero_mem _)

/-- A prime of `𝓞 K` admitting a uniformizer is maximal. -/
theorem IsUniformizer.isMaximal (h : IsUniformizer P π) : P.IsMaximal :=
  isMaximal_of_ne_bot P h.ne_bot

/-- If `x * π` lies in `P ^ 2` for a uniformizer `π`, then `x` lies in `P`. -/
theorem IsUniformizer.mem_of_mul_mem_sq (h : IsUniformizer P π) {x : 𝓞 K}
    (hx : x * π ∈ P ^ 2) : x ∈ P := by
  by_contra hxP
  obtain ⟨y, i, hi, hyi⟩ := h.isMaximal.exists_inv hxP
  refine h.2 ?_
  have hπeq : π = y * (x * π) + i * π := by
    rw [← mul_assoc, ← add_mul, hyi, one_mul]
  rw [hπeq]
  refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ hx) ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul hi h.1

/-- A uniformizer generates `P` modulo `P ^ 2`. -/
theorem IsUniformizer.span_sup_sq (h : IsUniformizer P π) : Ideal.span {π} ⊔ P ^ 2 = P := by
  have hP := h.ne_bot
  have hprime : Prime P := Ideal.prime_of_isPrime hP inferInstance
  set J : Ideal (𝓞 K) := Ideal.span {π} ⊔ P ^ 2 with hJ
  have hJle : J ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 h.1) (Ideal.pow_le_self two_ne_zero)
  have hdvd : J ∣ P ^ 2 := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨k, hk2, hkJ⟩ := (dvd_prime_pow hprime 2).1 hdvd
  rw [associated_iff_eq] at hkJ
  interval_cases k
  · rw [pow_zero, Ideal.one_eq_top] at hkJ
    exact absurd (top_le_iff.1 (hkJ ▸ hJle)) (Ideal.IsPrime.ne_top ‹_›)
  · rw [pow_one] at hkJ
    exact hkJ
  · exact absurd (hkJ ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)) h.2

/-- Every element of `P` is congruent to a multiple of a uniformizer modulo `P ^ 2`. -/
theorem IsUniformizer.exists_sub_mul_mem_sq (h : IsUniformizer P π) {y : 𝓞 K} (hy : y ∈ P) :
    ∃ c : 𝓞 K, y - c * π ∈ P ^ 2 := by
  rw [← h.span_sup_sq] at hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  exact ⟨c, by simpa using hv⟩

/-- Every nonzero prime of `𝓞 K` admits a uniformizer. -/
theorem exists_isUniformizer (hP : P ≠ ⊥) : ∃ x : 𝓞 K, IsUniformizer P x := by
  obtain ⟨x, hx, hx2⟩ :=
    Ideal.exists_mem_pow_notMem_pow_succ P hP (Ideal.IsPrime.ne_top ‹P.IsPrime›) 1
  refine ⟨x, by rwa [pow_one] at hx, ?_⟩
  simpa using hx2

end Uniformizer

section TameCharacter

variable {P : Ideal (𝓞 K)} [P.IsPrime] {π : 𝓞 K}

omit [P.IsPrime] in
/-- An element of the decomposition group at `P` preserves every power of `P`. -/
theorem smul_mem_pow_of_mem_stabilizer {σ : Gal(K/ℚ)}
    (hσ : σ ∈ MulAction.stabilizer Gal(K/ℚ) P) {n : ℕ} {x : 𝓞 K} (hx : x ∈ P ^ n) :
    σ • x ∈ P ^ n := by
  have hpow : σ • (P ^ n) = P ^ n := by
    rw [smul_pow', MulAction.mem_stabilizer_iff.1 hσ]
  exact hpow ▸ Ideal.smul_mem_pointwise_smul _ _ _ hx

/-- An element of the inertia group at `P` maps a uniformizer to a multiple of it modulo
`P ^ 2`. -/
theorem exists_sub_mul_mem_sq_smul (h : IsUniformizer P π) {σ : Gal(K/ℚ)}
    (hσ : σ ∈ Ideal.inertia Gal(K/ℚ) P) : ∃ c : 𝓞 K, σ • π - c * π ∈ P ^ 2 :=
  h.exists_sub_mul_mem_sq (by simpa using Ideal.add_mem P (hσ π) h.1)

/-- The coefficient by which an element of the inertia group multiplies a uniformizer, modulo
`P ^ 2`. -/
noncomputable def tameCoeff (h : IsUniformizer P π) (σ : Ideal.inertia Gal(K/ℚ) P) : 𝓞 K :=
  (exists_sub_mul_mem_sq_smul h σ.2).choose

/-- The defining property of `InverseGalois.CFT.tameCoeff`. -/
theorem tameCoeff_spec (h : IsUniformizer P π) (σ : Ideal.inertia Gal(K/ℚ) P) :
    (σ : Gal(K/ℚ)) • π - tameCoeff h σ * π ∈ P ^ 2 :=
  (exists_sub_mul_mem_sq_smul h σ.2).choose_spec

/-- The coefficient of `InverseGalois.CFT.tameCoeff` is unique modulo `P`. -/
theorem tameCoeff_unique (h : IsUniformizer P π) (σ : Ideal.inertia Gal(K/ℚ) P) {c : 𝓞 K}
    (hc : (σ : Gal(K/ℚ)) • π - c * π ∈ P ^ 2) :
    Ideal.Quotient.mk P (tameCoeff h σ) = Ideal.Quotient.mk P c := by
  refine Ideal.Quotient.eq.2 (h.mem_of_mul_mem_sq ?_)
  have hsub := Submodule.sub_mem _ hc (tameCoeff_spec h σ)
  have hrw : (σ : Gal(K/ℚ)) • π - c * π - ((σ : Gal(K/ℚ)) • π - tameCoeff h σ * π) =
      (tameCoeff h σ - c) * π := by ring
  exact hrw ▸ hsub

/-- The tame inertia character, before passing to units: the class modulo `P` of the coefficient
by which an element of the inertia group multiplies a uniformizer. -/
noncomputable def tameMonoidHom (h : IsUniformizer P π) :
    Ideal.inertia Gal(K/ℚ) P →* 𝓞 K ⧸ P where
  toFun σ := Ideal.Quotient.mk P (tameCoeff h σ)
  map_one' := by
    rw [tameCoeff_unique h 1 (c := 1) (by simp), map_one]
  map_mul' σ τ := by
    set a := tameCoeff h σ with ha
    set b := tameCoeff h τ with hb
    set q : 𝓞 K := (σ : Gal(K/ℚ)) • π - a * π with hq
    set r : 𝓞 K := (τ : Gal(K/ℚ)) • π - b * π with hr
    have hqmem : q ∈ P ^ 2 := tameCoeff_spec h σ
    have hrmem : r ∈ P ^ 2 := tameCoeff_spec h τ
    have hstab : (σ : Gal(K/ℚ)) ∈ MulAction.stabilizer Gal(K/ℚ) P :=
      Ideal.inertia_le_stabilizer P σ.2
    have h1 : (σ : Gal(K/ℚ)) • ((τ : Gal(K/ℚ)) • π) =
        ((σ : Gal(K/ℚ)) • b) * ((σ : Gal(K/ℚ)) • π) + (σ : Gal(K/ℚ)) • r := by
      rw [← smul_mul', ← smul_add, hr]
      ring_nf
    have h2 : ((σ * τ : Gal(K/ℚ))) • π - a * b * π =
        ((σ : Gal(K/ℚ)) • b - b) * (a * π) + (((σ : Gal(K/ℚ)) • b) * q + (σ : Gal(K/ℚ)) • r) := by
      rw [mul_smul, h1]
      have hσπ : (σ : Gal(K/ℚ)) • π = a * π + q := by rw [hq]; ring
      rw [hσπ]; ring
    have hmem : ((σ * τ : Gal(K/ℚ))) • π - a * b * π ∈ P ^ 2 := by
      rw [h2]
      refine Submodule.add_mem _ ?_ (Submodule.add_mem _ (Ideal.mul_mem_left _ _ hqmem)
        (smul_mem_pow_of_mem_stabilizer hstab hrmem))
      rw [pow_two]
      exact Ideal.mul_mem_mul (σ.2 b) (Ideal.mul_mem_left _ _ h.1)
    show Ideal.Quotient.mk P (tameCoeff h (σ * τ)) = _
    rw [tameCoeff_unique h (σ * τ) (c := a * b) hmem, map_mul]

/-- The tame inertia character attached to a uniformizer `π` at `P`: a group homomorphism from
the inertia group at `P` to the units of the residue field at `P`. -/
noncomputable def tameChar (h : IsUniformizer P π) :
    Ideal.inertia Gal(K/ℚ) P →* (𝓞 K ⧸ P)ˣ :=
  (tameMonoidHom h).toHomUnits

/-- The tame character is computed by any coefficient satisfying the defining congruence. -/
theorem tameChar_eq_mk (h : IsUniformizer P π) (σ : Ideal.inertia Gal(K/ℚ) P) {c : 𝓞 K}
    (hc : (σ : Gal(K/ℚ)) • π - c * π ∈ P ^ 2) :
    ((tameChar h σ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) = Ideal.Quotient.mk P c :=
  (MonoidHom.coe_toHomUnits _ _).trans (tameCoeff_unique h σ hc)

omit [P.IsPrime] in
/-- Translating a uniformizer by an element of the decomposition group gives a uniformizer. -/
theorem IsUniformizer.smul (h : IsUniformizer P π) {σ : Gal(K/ℚ)}
    (hσ : σ ∈ MulAction.stabilizer Gal(K/ℚ) P) : IsUniformizer P (σ • π) := by
  refine ⟨by simpa using smul_mem_pow_of_mem_stabilizer hσ (n := 1) (by simpa using h.1), ?_⟩
  intro hc
  exact h.2 (by simpa using smul_mem_pow_of_mem_stabilizer (inv_mem hσ) (n := 2) hc)

variable {π' : 𝓞 K}

/-- The tame character does not depend on the choice of uniformizer. -/
theorem tameChar_eq_of_isUniformizer (h : IsUniformizer P π) (h' : IsUniformizer P π') :
    tameChar h' = tameChar h := by
  have key : ∀ σ : Ideal.inertia Gal(K/ℚ) P,
      Ideal.Quotient.mk P (tameCoeff h' σ) = Ideal.Quotient.mk P (tameCoeff h σ) := by
    intro σ
    obtain ⟨u, hu⟩ := h.exists_sub_mul_mem_sq h'.1
    set a := tameCoeff h σ with ha
    have hstab : (σ : Gal(K/ℚ)) ∈ MulAction.stabilizer Gal(K/ℚ) P :=
      Ideal.inertia_le_stabilizer P σ.2
    have hW : (σ : Gal(K/ℚ)) • (π' - u * π) =
        (σ : Gal(K/ℚ)) • π' - ((σ : Gal(K/ℚ)) • u) * ((σ : Gal(K/ℚ)) • π) := by
      rw [smul_sub, smul_mul']
    have key : (σ : Gal(K/ℚ)) • π' - a * π' =
        ((σ : Gal(K/ℚ)) • u - u) * (a * π) +
          (((σ : Gal(K/ℚ)) • u) * ((σ : Gal(K/ℚ)) • π - a * π) +
            ((σ : Gal(K/ℚ)) • (π' - u * π) - a * (π' - u * π))) := by
      rw [hW]; ring
    refine tameCoeff_unique h' σ ?_
    rw [key]
    refine Submodule.add_mem _ ?_ (Submodule.add_mem _
      (Ideal.mul_mem_left _ _ (tameCoeff_spec h σ)) (Submodule.sub_mem _
        (smul_mem_pow_of_mem_stabilizer hstab hu) (Ideal.mul_mem_left _ _ hu)))
    rw [pow_two]
    exact Ideal.mul_mem_mul (σ.2 u) (Ideal.mul_mem_left _ _ h.1)
  exact congrArg MonoidHom.toHomUnits (MonoidHom.ext key)

end TameCharacter

section Equivariance

variable {P : Ideal (𝓞 K)} [P.IsPrime] {π : 𝓞 K}

omit [P.IsPrime] in
/-- The inertia group at `P` is normalised by the decomposition group at `P`. -/
theorem conj_mem_inertia {σ : Gal(K/ℚ)} (hσ : σ ∈ MulAction.stabilizer Gal(K/ℚ) P)
    {τ : Gal(K/ℚ)} (hτ : τ ∈ Ideal.inertia Gal(K/ℚ) P) :
    σ * τ * σ⁻¹ ∈ Ideal.inertia Gal(K/ℚ) P := by
  intro x
  have hx : (σ * τ * σ⁻¹) • x - x = σ • ((τ • (σ⁻¹ • x)) - σ⁻¹ • x) := by
    rw [smul_sub, smul_inv_smul, mul_smul, mul_smul]
  rw [hx]
  simpa using smul_mem_pow_of_mem_stabilizer hσ (n := 1) (by simpa using hτ (σ⁻¹ • x))

/-- The tame character is equivariant: conjugating an element of the inertia group by an element
`σ` of the decomposition group applies to the tame character the automorphism of the residue
field induced by `σ`. -/
theorem tameChar_conj (h : IsUniformizer P π) {σ : Gal(K/ℚ)}
    (hσ : σ ∈ MulAction.stabilizer Gal(K/ℚ) P) (τ : Ideal.inertia Gal(K/ℚ) P) :
    ((tameChar h ⟨σ * τ * σ⁻¹, conj_mem_inertia hσ τ.2⟩ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) =
      Ideal.Quotient.stabilizerHom P (P.under ℤ) Gal(K/ℚ) ⟨σ, hσ⟩
        ((tameChar h τ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) := by
  have h₁ : IsUniformizer P (σ⁻¹ • π) := h.smul (inv_mem hσ)
  have hspec : (τ : Gal(K/ℚ)) • (σ⁻¹ • π) - tameCoeff h₁ τ * (σ⁻¹ • π) ∈ P ^ 2 :=
    tameCoeff_spec h₁ τ
  have hτc : ((tameChar h τ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) =
      Ideal.Quotient.mk P (tameCoeff h₁ τ) := by
    rw [tameChar_eq_of_isUniformizer h₁ h]
    exact tameChar_eq_mk h₁ τ hspec
  have hEq : (σ * (τ : Gal(K/ℚ)) * σ⁻¹) • π - (σ • tameCoeff h₁ τ) * π =
      σ • ((τ : Gal(K/ℚ)) • (σ⁻¹ • π) - tameCoeff h₁ τ * (σ⁻¹ • π)) := by
    rw [smul_sub, smul_mul', smul_inv_smul, mul_smul, mul_smul]
  rw [hτc, tameChar_eq_mk h _ (hEq ▸ smul_mem_pow_of_mem_stabilizer hσ hspec)]
  rfl

variable [IsGalois ℚ K] [Finite (𝓞 K ⧸ P)]

/-- Conjugating by an arithmetic Frobenius raises the tame character to the power `#(ℤ ⧸ p)`. -/
theorem tameChar_conj_arithFrobAt (h : IsUniformizer P π) (τ : Ideal.inertia Gal(K/ℚ) P) :
    ((tameChar h ⟨arithFrobAt ℤ Gal(K/ℚ) P * τ * (arithFrobAt ℤ Gal(K/ℚ) P)⁻¹,
        conj_mem_inertia (arithFrobAt_mem_stabilizer P) τ.2⟩ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) =
      ((tameChar h τ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) ^ Nat.card (ℤ ⧸ P.under ℤ) := by
  have h₁ : IsUniformizer P ((arithFrobAt ℤ Gal(K/ℚ) P)⁻¹ • π) :=
    h.smul (inv_mem (arithFrobAt_mem_stabilizer P))
  have hτc : ((tameChar h τ : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) =
      Ideal.Quotient.mk P (tameCoeff h₁ τ) := by
    rw [tameChar_eq_of_isUniformizer h₁ h]
    exact tameChar_eq_mk h₁ τ (tameCoeff_spec h₁ τ)
  rw [tameChar_conj h (arithFrobAt_mem_stabilizer P) τ, hτc]
  exact (IsArithFrobAt.arithFrobAt ℤ Gal(K/ℚ) P).mk_apply (tameCoeff h₁ τ)

end Equivariance

section Injectivity

variable {P : Ideal (𝓞 K)} [P.IsPrime] {π : 𝓞 K}

/-- The sum of the translates of an element under all the powers of a group element `g` is
invariant under `g`. -/
theorem smul_sum_range_orderOf {G M : Type*} [Group G] [AddCommMonoid M] [DistribMulAction G M]
    (g : G) (x : M) :
    g • ∑ i ∈ Finset.range (orderOf g), (g ^ i) • x =
      ∑ i ∈ Finset.range (orderOf g), (g ^ i) • x := by
  rcases Nat.eq_zero_or_pos (orderOf g) with h0 | h0
  · simp [h0]
  · obtain ⟨n, hn⟩ : ∃ n, orderOf g = n + 1 := ⟨orderOf g - 1, by omega⟩
    have hstep : ∀ i : ℕ, g • ((g ^ i) • x) = (g ^ (i + 1)) • x := fun i => by
      rw [← mul_smul, ← pow_succ']
    rw [Finset.smul_sum]
    simp_rw [hstep]
    conv_rhs => rw [hn, Finset.sum_range_succ' (fun i => (g ^ i) • x) n]
    rw [hn, Finset.sum_range_succ (fun i => (g ^ (i + 1)) • x) n, ← hn, pow_orderOf_eq_one]
    simp

/-- An element of the inertia group lies in the kernel of the tame character exactly when it
moves a uniformizer only by an element of `P ^ 2`. -/
theorem tameChar_eq_one_iff (h : IsUniformizer P π) (σ : Ideal.inertia Gal(K/ℚ) P) :
    tameChar h σ = 1 ↔ (σ : Gal(K/ℚ)) • π - π ∈ P ^ 2 := by
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hc := tameChar_eq_mk h σ (tameCoeff_spec h σ)
    rw [h1] at hc
    have hsub : tameCoeff h σ - 1 ∈ P := by
      refine Ideal.Quotient.eq.1 ?_
      rw [← hc, map_one, Units.val_one]
    have heq : (σ : Gal(K/ℚ)) • π - π =
        ((σ : Gal(K/ℚ)) • π - tameCoeff h σ * π) + (tameCoeff h σ - 1) * π := by ring
    rw [heq]
    refine Submodule.add_mem _ (tameCoeff_spec h σ) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hsub h.1
  · have hval := tameChar_eq_mk h σ (c := 1) (by simpa using h1)
    rw [map_one] at hval
    exact Units.val_eq_one.1 hval

variable [IsGalois ℚ K]

attribute [local instance] Ideal.Quotient.field in
/-- An invariant element of a prime `P` lies in the `orderOf σ`-th power of `P`, for `σ` in the
inertia group at `P`: indeed `P` is totally ramified of index `orderOf σ` over the fixed field
of `σ`. -/
theorem mem_pow_orderOf_of_smul_eq (hP : P ≠ ⊥) {σ : Gal(K/ℚ)}
    (hσ : σ ∈ Ideal.inertia Gal(K/ℚ) P) {s : 𝓞 K} (hs : σ • s = s) (hsP : s ∈ P) :
    s ∈ P ^ orderOf σ := by
  haveI := isMaximal_of_ne_bot P hP
  haveI := finite_quotient_of_ne_bot P hP
  let H := Subgroup.zpowers σ
  let F : IntermediateField ℚ K := FixedPoints.intermediateField H
  haveI : IsGaloisGroup H (𝓞 F) (𝓞 K) := IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 K) F K
  have hinv : ∀ g : H, g • s = s := fun g =>
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hs) g.2
  obtain ⟨t, ht⟩ := Algebra.IsInvariant.isInvariant (A := 𝓞 F) (G := H) s hinv
  have hqbot : P.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP
  haveI : (P.under (𝓞 F)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqbot
  haveI : Finite (𝓞 F ⧸ P.under (𝓞 F)) :=
    .of_injective _ (Ideal.algebraMap_quotient_injective (R := 𝓞 F) (A := 𝓞 K) (I := P))
  haveI : Algebra.IsSeparable (𝓞 F ⧸ P.under (𝓞 F)) (𝓞 K ⧸ P) := inferInstance
  have hcard : Nat.card (P.inertia H) = Ideal.ramificationIdxIn (P.under (𝓞 F)) (𝓞 K) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := H) (P.under (𝓞 F)) hqbot P
  have htop : P.inertia H = ⊤ := by
    have hsub : P.inertia H = (Ideal.inertia Gal(K/ℚ) P).subgroupOf H :=
      (AddSubgroup.subgroupOf_inertia P.toAddSubgroup H).symm
    rw [hsub, Subgroup.subgroupOf_eq_top]
    exact Subgroup.zpowers_le.2 hσ
  have he : Ideal.ramificationIdx (algebraMap (𝓞 F) (𝓞 K)) (P.under (𝓞 F)) P = orderOf σ := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P H, ← hcard, htop,
      Subgroup.card_top, Nat.card_zpowers]
  have hmem : s ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 K)) (P.under (𝓞 F)) :=
    ht ▸ Ideal.mem_map_of_mem _ (show t ∈ P.under (𝓞 F) from Ideal.mem_comap.2 (ht ▸ hsP))
  exact he ▸ Ideal.le_pow_ramificationIdx hmem

/-- **Tameness gives injectivity**: if the residue characteristic at `P` does not divide the
order of the inertia group at `P`, then the tame character is injective. -/
theorem tameChar_injective (h : IsUniformizer P π)
    (hp : ¬ ringChar (𝓞 K ⧸ P) ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P)) :
    Function.Injective (tameChar h) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ1
  have hmdvd : orderOf (σ : Gal(K/ℚ)) ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard σ
  have hm1 : orderOf (σ : Gal(K/ℚ)) = 1 := by
    by_contra hne
    have hmpos : 0 < orderOf (σ : Gal(K/ℚ)) := orderOf_pos _
    have hm2 : 2 ≤ orderOf (σ : Gal(K/ℚ)) := by omega
    have hker : ∀ i : ℕ, ((σ : Gal(K/ℚ)) ^ i) • π - π ∈ P ^ 2 := by
      intro i
      have hpow : tameChar h (σ ^ i) = 1 := by rw [map_pow, hσ1, one_pow]
      simpa using (tameChar_eq_one_iff h (σ ^ i)).1 hpow
    obtain ⟨s, hsdef⟩ : ∃ s : 𝓞 K,
        s = ∑ i ∈ Finset.range (orderOf (σ : Gal(K/ℚ))), ((σ : Gal(K/ℚ)) ^ i) • π := ⟨_, rfl⟩
    have hfix : (σ : Gal(K/ℚ)) • s = s := by
      rw [hsdef]; exact smul_sum_range_orderOf _ _
    have hsP : s ∈ P := by
      rw [hsdef]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hmem : ((σ : Gal(K/ℚ)) ^ i) • π - π ∈ P := Ideal.pow_le_self two_ne_zero (hker i)
      simpa using Ideal.add_mem P hmem h.1
    have hs2 : s ∈ P ^ 2 :=
      Ideal.pow_le_pow_right hm2 (mem_pow_orderOf_of_smul_eq h.ne_bot σ.2 hfix hsP)
    have hdiff : s - ((orderOf (σ : Gal(K/ℚ)) : ℕ) : 𝓞 K) * π ∈ P ^ 2 := by
      have hrw : ∑ i ∈ Finset.range (orderOf (σ : Gal(K/ℚ))), (((σ : Gal(K/ℚ)) ^ i) • π - π) =
          s - ((orderOf (σ : Gal(K/ℚ)) : ℕ) : 𝓞 K) * π := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsdef]
      rw [← hrw]
      exact Submodule.sum_mem _ fun i _ => hker i
    have hmul : ((orderOf (σ : Gal(K/ℚ)) : ℕ) : 𝓞 K) * π ∈ P ^ 2 := by
      simpa using Submodule.sub_mem (P ^ 2) hs2 hdiff
    refine hp (dvd_trans (ringChar.dvd ?_) hmdvd)
    rw [← map_natCast (Ideal.Quotient.mk P)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h.mem_of_mul_mem_sq hmul)
  exact Subtype.ext (orderOf_eq_one_iff.1 hm1)

end Injectivity

section Abelian

variable {P : Ideal (𝓞 K)} [P.IsPrime] {π : 𝓞 K} [IsGalois ℚ K]

/-- If the Galois group is commutative, the Frobenius commutes with inertia, so every value of
the tame character is fixed by the Frobenius of the residue field. -/
theorem tameChar_pow_card (h : IsUniformizer P π) (hcomm : ∀ a b : Gal(K/ℚ), a * b = b * a)
    (τ : Ideal.inertia Gal(K/ℚ) P) :
    tameChar h τ ^ Nat.card (ℤ ⧸ P.under ℤ) = tameChar h τ := by
  haveI := finite_quotient_of_ne_bot P h.ne_bot
  have hconj : (⟨arithFrobAt ℤ Gal(K/ℚ) P * (τ : Gal(K/ℚ)) * (arithFrobAt ℤ Gal(K/ℚ) P)⁻¹,
      conj_mem_inertia (arithFrobAt_mem_stabilizer P) τ.2⟩ : Ideal.inertia Gal(K/ℚ) P) = τ :=
    Subtype.ext (show arithFrobAt ℤ Gal(K/ℚ) P * (τ : Gal(K/ℚ)) *
        (arithFrobAt ℤ Gal(K/ℚ) P)⁻¹ = (τ : Gal(K/ℚ)) by
      rw [hcomm (arithFrobAt ℤ Gal(K/ℚ) P) (τ : Gal(K/ℚ)), mul_assoc, mul_inv_cancel, mul_one])
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, ← tameChar_conj_arithFrobAt h τ]
  exact congrArg (fun x => ((tameChar h x : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P)) hconj

/-- **Tame abelian ramification**: if `K / ℚ` is abelian and the residue characteristic at `P`
does not divide the order of the inertia group at `P`, then that order divides `q - 1`, where
`q` is the cardinality of the residue field of the rational prime under `P`. -/
theorem card_inertia_dvd_sub_one (h : IsUniformizer P π)
    (hcomm : ∀ a b : Gal(K/ℚ), a * b = b * a)
    (hp : ¬ ringChar (𝓞 K ⧸ P) ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P)) :
    Nat.card (Ideal.inertia Gal(K/ℚ) P) ∣ Nat.card (ℤ ⧸ P.under ℤ) - 1 := by
  haveI := finite_quotient_under_of_ne_bot P h.ne_bot
  have hinj := tameChar_injective h hp
  haveI : IsCyclic (Ideal.inertia Gal(K/ℚ) P) :=
    isCyclic_of_subgroup_isDomain ((Units.coeHom (𝓞 K ⧸ P)).comp (tameChar h))
      (Units.val_injective.comp hinj)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Ideal.inertia Gal(K/ℚ) P)
  have hq : 1 ≤ Nat.card (ℤ ⧸ P.under ℤ) := Nat.card_pos
  have hgpow : g ^ (Nat.card (ℤ ⧸ P.under ℤ) - 1) = 1 := by
    refine hinj ?_
    rw [map_pow, map_one]
    have hstep : tameChar h g ^ (Nat.card (ℤ ⧸ P.under ℤ) - 1) * tameChar h g =
        tameChar h g ^ Nat.card (ℤ ⧸ P.under ℤ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [tameChar_pow_card h hcomm g] at hstep
    exact mul_eq_right.1 hstep
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_dvd_of_pow_eq_one hgpow

/-- **Tame abelian ramification, in terms of the ramification index**: if `K / ℚ` is abelian and
the residue characteristic at `P` does not divide the ramification index of `P` over `ℤ`, then
that index divides `q - 1`, where `q` is the cardinality of the residue field of the rational
prime under `P`. -/
theorem ramificationIdxIn_dvd_sub_one (h : IsUniformizer P π)
    (hcomm : ∀ a b : Gal(K/ℚ), a * b = b * a)
    (hp : ¬ ringChar (𝓞 K ⧸ P) ∣ Ideal.ramificationIdxIn (P.under ℤ) (𝓞 K)) :
    Ideal.ramificationIdxIn (P.under ℤ) (𝓞 K) ∣ Nat.card (ℤ ⧸ P.under ℤ) - 1 := by
  haveI := isMaximal_of_ne_bot P h.ne_bot
  haveI := finite_quotient_of_ne_bot P h.ne_bot
  haveI := isMaximal_under_of_ne_bot P h.ne_bot
  haveI := isSeparable_residue_of_ne_bot P h.ne_bot
  have hcard : Nat.card (Ideal.inertia Gal(K/ℚ) P) =
      Ideal.ramificationIdxIn (P.under ℤ) (𝓞 K) :=
    Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) (P.under ℤ) (under_ne_bot P h.ne_bot) P
  rw [← hcard] at hp ⊢
  exact card_inertia_dvd_sub_one h hcomm hp

omit [NumberField K] [IsGalois ℚ K] in
/-- The residue field at a prime lying over the rational prime `p` has characteristic `p`. -/
theorem ringChar_quotient_eq (p : ℕ) (hp : p.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] : ringChar (𝓞 K ⧸ Q) = p := by
  have hmem : (p : 𝓞 K) ∈ Q := by
    have hover : (p : ℤ) ∈ Q.under ℤ :=
      Q.over_def (Ideal.span {(p : ℤ)}) ▸ Ideal.mem_span_singleton_self _
    simpa using Ideal.mem_comap.1 hover
  have hzero : ((p : ℕ) : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  rcases hp.eq_one_or_self_of_dvd _ (ringChar.dvd hzero) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

omit [NumberField K] [IsGalois ℚ K] in
/-- The residue field of `ℤ` at a rational prime `p` has `p` elements. -/
theorem natCard_quotient_under (p : ℕ) (Q : Ideal (𝓞 K))
    [Q.LiesOver (Ideal.span {(p : ℤ)})] : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← Q.over_def (Ideal.span {(p : ℤ)}),
    Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- **Tame abelian ramification over `ℚ`**: if `K / ℚ` is abelian, `Q` is a prime of `𝓞 K` over
the rational prime `p` and `p` does not divide the order of the inertia group at `Q`, then that
order divides `p - 1`. -/
theorem card_inertia_dvd_sub_one_of_liesOver [IsMulCommutative Gal(K/ℚ)]
    (p : ℕ) (hp : p.Prime) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (htame : ¬ p ∣ Nat.card (Ideal.inertia Gal(K/ℚ) Q)) :
    Nat.card (Ideal.inertia Gal(K/ℚ) Q) ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_isUniformizer (ne_bot_of_liesOver p Q)
  have hdvd := card_inertia_dvd_sub_one hx (fun a b => mul_comm a b)
    (by rwa [ringChar_quotient_eq p hp Q])
  rwa [natCard_quotient_under p Q] at hdvd

end Abelian

end InverseGalois.CFT
