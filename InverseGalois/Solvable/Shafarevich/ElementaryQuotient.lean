/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.GlobalPowRepresentatives
import InverseGalois.CFT.Profinite.CharacterRoot
import InverseGalois.CFT.Profinite.Symbol
import InverseGalois.Solvable.Shafarevich.LevelLocal

/-!
# A finite elementary quotient out of finitely many power classes

A subgroup of a Galois group has a finite elementary quotient as soon as it carries only finitely
many smooth characters of order dividing the prime, because the product of all of them is then a
homomorphism to a finite group through which every such character factors, and every smooth
homomorphism to a commutative group killed by the prime is separated by such characters.

The finiteness of the characters is bought by Kummer theory.  A smooth character of order dividing
the prime, on a subgroup which fixes the roots of unity of that order, is a one cocycle for the
action on the units, hence a coboundary; a coboundary of a unit whose power is invariant, and the
invariant power determines the character up to a root of unity, which is itself invariant.  So the
characters inject into the power classes of the invariants of the subgroup, and a finite set of
representatives of those classes bounds them.

Finally the bound survives passing to a subgroup of finite index, a character being determined by
its restriction together with its values on one representative of each coset, so the finiteness may
be proved after enlarging the base field to one containing the roots of unity.

## Main results

* `InverseGalois.Shafarevich.exists_monoidHom_apply_ne_one`: **a nontrivial element of a commutative
  group killed by a prime is separated by a character to the cyclic group of that order.**
* `InverseGalois.Shafarevich.finite_smoothTorsionChar`: **finitely many representatives of the power
  classes of the invariants bound the smooth characters killed by the prime.**
* `InverseGalois.Shafarevich.finite_smoothZModChar_of_finite_pow_representatives`: **and hence the
  smooth characters with values in the cyclic group of that order.**
* `InverseGalois.Shafarevich.finite_smoothZModChar_of_le`: **the bound passes from a subgroup of
  finite index to the group.**
* `InverseGalois.Shafarevich.hasFiniteElementaryQuotient_of_finite_smoothZModChar`: **finitely many
  smooth characters give a finite elementary quotient.**
* `InverseGalois.Shafarevich.hasFiniteElementaryQuotient_of_finite`: **a finite subgroup has one
  outright.**

## Tags

Shafarevich's theorem, Kummer theory, Hilbert theorem ninety, smooth character, local field
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT groupCohomology

/-! ### Separating a nontrivial element by a character of exponent a prime -/

section Separate

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A nonzero vector over the field with a prime number of elements is separated by a linear
functional. -/
theorem exists_linearMap_apply_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V] {v : V}
    (hv : v ≠ 0) : ∃ φ : V →ₗ[ZMod ℓ] ZMod ℓ, φ v ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod ℓ) v).1 hc)

/-- A nonzero element of a commutative group killed by a prime is separated by a homomorphism to
the additive group of order that prime. -/
theorem exists_addMonoidHom_apply_ne_zero {V : Type*} [AddCommGroup V] (h : ∀ x : V, ℓ • x = 0)
    {v : V} (hv : v ≠ 0) : ∃ f : V →+ ZMod ℓ, f v ≠ 0 := by
  letI : Module (ZMod ℓ) V := AddCommGroup.zmodModule h
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_ne_zero (ℓ := ℓ) hv
  exact ⟨φ.toAddMonoidHom, hφ⟩

/-- **A nontrivial element of a commutative group killed by a prime is separated by a character to
the cyclic group of that order.**  Such a group is a vector space over the field with that many
elements, and a nonzero vector is separated by a linear functional. -/
theorem exists_monoidHom_apply_ne_one {M : Type*} [CommGroup M] (hM : ∀ y : M, y ^ ℓ = 1)
    {m : M} (hm : m ≠ 1) : ∃ f : M →* Multiplicative (ZMod ℓ), f m ≠ 1 := by
  have hn : ∀ x : Additive M, ℓ • x = 0 := fun x =>
    Additive.toMul.injective (by simpa using hM (Additive.toMul x))
  have h0 : (Additive.ofMul m : Additive M) ≠ 0 := by
    intro h
    exact hm (by simpa using congrArg Additive.toMul h)
  obtain ⟨φ, hφ⟩ := exists_addMonoidHom_apply_ne_zero (ℓ := ℓ) hn h0
  refine ⟨AddMonoidHom.toMultiplicativeRight φ, ?_⟩
  intro h
  exact hφ (by simpa using congrArg Multiplicative.toAdd h)

end Separate

/-! ### Finitely many smooth characters killed by the prime -/

section FiniteChar

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- Reading an automorphism of a subgroup on a unit is reading it on the underlying element. -/
theorem coe_smul_units {A : Subgroup Gal(Ω/k)} (σ : ↥A) (u : Ωˣ) :
    ((σ • u : Ωˣ) : Ω) = (σ : Gal(Ω/k)) (u : Ω) := rfl

/-- **A finite set of representatives for the `ℓ`-th power classes of the invariants bounds the
smooth characters killed by `ℓ`.** -/
theorem finite_smoothTorsionChar {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {A : Subgroup Gal(Ω/k)} (hA : IsClosed (A : Set Gal(Ω/k)))
    (hμ : ∀ ζ : Ωˣ, ζ ^ ℓ = 1 → ∀ σ : ↥A, σ • ζ = ζ)
    {T : Set Ω} (hT : T.Finite)
    (hrep : ∀ x : Ω, x ≠ 0 → (∀ σ : ↥A, (σ : Gal(Ω/k)) x = x) →
      ∃ a ∈ T, ∃ c : Ω, (∀ σ : ↥A, (σ : Gal(Ω/k)) c = c) ∧ x = a * c ^ ℓ) :
    Finite {χ : ↥A →* Ωˣ // IsSmooth₁ (χ : ↥A → Ωˣ) ∧ ∀ σ, χ σ ^ ℓ = 1} := by
  classical
  haveI := hT.to_subtype
  have key : ∀ χ : {χ : ↥A →* Ωˣ // IsSmooth₁ (χ : ↥A → Ωˣ) ∧ ∀ σ, χ σ ^ ℓ = 1},
      ∃ a : Ω, a ∈ T ∧ ∃ γ : Ωˣ, (γ : Ω) ^ ℓ = a ∧ ∀ σ : ↥A, σ • γ / γ = χ.1 σ := by
    rintro ⟨χ, hs, htor⟩
    have hfix : ∀ σ τ : ↥A, σ • χ τ = χ τ := fun σ τ => hμ (χ τ) (htor τ) σ
    have hcoc : IsMulCocycle₁ (χ : ↥A → Ωˣ) := fun σ τ => by
      rw [_root_.map_mul, hfix, mul_comm]
    obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth_subgroup hA hcoc hs
    have hβpow : ∀ σ : ↥A, σ • β ^ ℓ = β ^ ℓ := by
      intro σ
      have h := hβ σ
      rw [div_eq_iff_eq_mul] at h
      rw [smul_pow', h, mul_pow, htor, one_mul]
    have hβinv : ∀ σ : ↥A, (σ : Gal(Ω/k)) ((β : Ω) ^ ℓ) = (β : Ω) ^ ℓ := by
      intro σ
      have h := congrArg (fun u : Ωˣ => (u : Ω)) (hβpow σ)
      simpa [coe_smul_units] using h
    obtain ⟨a, haT, c, hcinv, hac⟩ := hrep ((β : Ω) ^ ℓ) (pow_ne_zero _ β.ne_zero) hβinv
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_pow hℓ, mul_zero] at hac
      exact pow_ne_zero _ β.ne_zero hac
    set cu : Ωˣ := Units.mk0 c hc0 with hcu
    have hcufix : ∀ σ : ↥A, σ • cu = cu := fun σ => Units.ext (by
      simpa [hcu, coe_smul_units] using hcinv σ)
    refine ⟨a, haT, β / cu, ?_, fun σ => ?_⟩
    · have hval : ((β / cu : Ωˣ) : Ω) = (β : Ω) / c := by simp [hcu]
      rw [hval, div_pow, hac, mul_div_assoc, div_self (pow_ne_zero ℓ hc0), mul_one]
    · rw [smul_div', hcufix σ, div_div_div_cancel_right]
      exact hβ σ
  choose aa haaT γ hγpow hγcob using key
  refine Finite.of_injective (fun χ => (⟨aa χ, haaT χ⟩ : ↥T)) ?_
  intro χ₁ χ₂ h
  have ha : aa χ₁ = aa χ₂ := congrArg Subtype.val h
  have hunits : γ χ₁ ^ ℓ = γ χ₂ ^ ℓ := Units.ext (by
    push_cast
    rw [hγpow χ₁, hγpow χ₂, ha])
  have hpow : (γ χ₁ / γ χ₂) ^ ℓ = 1 := by rw [div_pow, hunits, div_self']
  refine Subtype.ext (MonoidHom.ext fun σ => ?_)
  have h3 : σ • (γ χ₁ / γ χ₂) = γ χ₁ / γ χ₂ := hμ _ hpow σ
  rw [smul_div', div_eq_div_iff_div_eq_div] at h3
  rw [← hγcob χ₁ σ, ← hγcob χ₂ σ]
  exact h3

end FiniteChar

/-! ### From the roots of unity to the cyclic group of order the prime -/

section ZModChar

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **A finite set of representatives for the `ℓ`-th power classes of the invariants bounds the
smooth characters with values in the cyclic group of order `ℓ`.** -/
theorem finite_smoothZModChar_of_finite_pow_representatives {ℓ : ℕ} [NeZero ℓ]
    {ξ : Ω} (hξ : IsPrimitiveRoot ξ ℓ)
    {A : Subgroup Gal(Ω/k)} (hA : IsClosed (A : Set Gal(Ω/k)))
    (hμ : ∀ ζ : Ωˣ, ζ ^ ℓ = 1 → ∀ σ : ↥A, σ • ζ = ζ)
    {T : Set Ω} (hT : T.Finite)
    (hrep : ∀ x : Ω, x ≠ 0 → (∀ σ : ↥A, (σ : Gal(Ω/k)) x = x) →
      ∃ a ∈ T, ∃ c : Ω, (∀ σ : ↥A, (σ : Gal(Ω/k)) c = c) ∧ x = a * c ^ ℓ) :
    Finite {χ : ↥A →* Multiplicative (ZMod ℓ) //
      IsSmooth₁ (χ : ↥A → Multiplicative (ZMod ℓ))} := by
  haveI := finite_smoothTorsionChar (NeZero.ne ℓ) hA hμ hT hrep
  refine Finite.of_injective
    (fun χ => (⟨(zmodRootHom hξ).comp χ.1, ?_, fun σ => zmodRootHom_pow_eq_one hξ _⟩ :
      {χ : ↥A →* Ωˣ // IsSmooth₁ (χ : ↥A → Ωˣ) ∧ ∀ σ, χ σ ^ ℓ = 1})) ?_
  · obtain ⟨N, hN, hNa⟩ := χ.2
    exact ⟨N, hN, fun y n hn => by
      show zmodRootHom hξ (χ.1 (y * n)) = zmodRootHom hξ (χ.1 y)
      rw [hNa y n hn]⟩
  · intro χ₁ χ₂ h
    have h' : (zmodRootHom hξ).comp χ₁.1 = (zmodRootHom hξ).comp χ₂.1 := congrArg Subtype.val h
    refine Subtype.ext (MonoidHom.ext fun σ => injective_zmodRootHom hξ ?_)
    exact congrArg (fun f : ↥A →* Ωˣ => f σ) h'

end ZModChar

/-! ### Passing to a subgroup of finite index -/

section Transfer

variable {ℓ : ℕ} [NeZero ℓ] {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- **Finitely many smooth characters on a subgroup of finite index give finitely many on the
group.**  A character is determined by its restriction to the subgroup together with its values on
one representative of each coset. -/
theorem finite_smoothZModChar_of_le {A A' : Subgroup Γ} (hle : A' ≤ A)
    [Finite (↥A ⧸ A'.subgroupOf A)]
    (h : Finite {χ : ↥A' →* Multiplicative (ZMod ℓ) //
      IsSmooth₁ (χ : ↥A' → Multiplicative (ZMod ℓ))}) :
    Finite {χ : ↥A →* Multiplicative (ZMod ℓ) //
      IsSmooth₁ (χ : ↥A → Multiplicative (ZMod ℓ))} := by
  haveI := h
  haveI : Finite (Multiplicative (ZMod ℓ)) := Finite.of_equiv (ZMod ℓ) Multiplicative.ofAdd
  refine Finite.of_injective
    (fun χ => ((⟨χ.1.comp (Subgroup.inclusion hle),
        isSmooth₁_comp_inclusion A' hle χ.2⟩ :
      {χ : ↥A' →* Multiplicative (ZMod ℓ) // IsSmooth₁ (χ : ↥A' → Multiplicative (ZMod ℓ))}),
      fun q : ↥A ⧸ A'.subgroupOf A => χ.1 q.out)) ?_
  rintro ⟨χ₁, h₁⟩ ⟨χ₂, h₂⟩ hEq
  have hres : χ₁.comp (Subgroup.inclusion hle) = χ₂.comp (Subgroup.inclusion hle) :=
    congrArg Subtype.val (congrArg Prod.fst hEq)
  have hout : ∀ q : ↥A ⧸ A'.subgroupOf A, χ₁ q.out = χ₂ q.out :=
    fun q => congrFun (congrArg Prod.snd hEq) q
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  set q : ↥A ⧸ A'.subgroupOf A := QuotientGroup.mk x with hq
  have hqout : (QuotientGroup.mk q.out : ↥A ⧸ A'.subgroupOf A) = q := Quotient.out_eq' q
  have hmem : q.out⁻¹ * x ∈ A'.subgroupOf A := QuotientGroup.eq.1 (by rw [hqout, hq])
  have hval : ∀ χ : ↥A →* Multiplicative (ZMod ℓ), χ x = χ q.out * χ (q.out⁻¹ * x) := by
    intro χ
    rw [← _root_.map_mul]
    congr 1
    group
  have hinc : Subgroup.inclusion hle
      ⟨((q.out⁻¹ * x : ↥A) : Γ), Subgroup.mem_subgroupOf.1 hmem⟩ = q.out⁻¹ * x :=
    Subtype.ext rfl
  have hlast := congrArg (fun f : ↥A' →* Multiplicative (ZMod ℓ) =>
    f ⟨((q.out⁻¹ * x : ↥A) : Γ), Subgroup.mem_subgroupOf.1 hmem⟩) hres
  simp only [MonoidHom.coe_comp, Function.comp_apply, hinc] at hlast
  rw [hval χ₁, hval χ₂, hout q, hlast]

end Transfer

/-! ### The finite elementary quotient -/

section Quotient

variable {ℓ : ℕ} [Fact ℓ.Prime] {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

omit [Fact ℓ.Prime] in
/-- **A finite subgroup has a finite elementary quotient**, namely itself. -/
theorem hasFiniteElementaryQuotient_of_finite (A : Subgroup Γ) [Finite ↥A] :
    HasFiniteElementaryQuotient ℓ A :=
  ⟨↥A, inferInstance, inferInstance, MonoidHom.id _, fun _ _ _ a _ => ⟨a, fun _ => rfl⟩⟩

/-- **A group with only finitely many smooth characters of order dividing a prime has a finite
elementary quotient.** -/
theorem hasFiniteElementaryQuotient_of_finite_smoothZModChar {A : Subgroup Γ}
    (hXfin : Finite {χ : ↥A →* Multiplicative (ZMod ℓ) //
      IsSmooth₁ (χ : ↥A → Multiplicative (ZMod ℓ))}) :
    HasFiniteElementaryQuotient ℓ A := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI := hXfin
  set F : ↥A →* ({χ : ↥A →* Multiplicative (ZMod ℓ) //
      IsSmooth₁ (χ : ↥A → Multiplicative (ZMod ℓ))} → Multiplicative (ZMod ℓ)) :=
    { toFun := fun x χ => χ.1 x
      map_one' := funext fun χ => _root_.map_one _
      map_mul' := fun x y => funext fun χ => _root_.map_mul _ _ _ } with hF
  haveI : Finite (↥A ⧸ F.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange F).symm.toEquiv
  refine ⟨↥A ⧸ F.ker, inferInstance, inferInstance, QuotientGroup.mk' F.ker, ?_⟩
  intro M _ hM a hasm
  have hker : F.ker ≤ a.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    by_contra hax
    obtain ⟨f, hf⟩ := exists_monoidHom_apply_ne_one hM hax
    have hsm : IsSmooth₁ ((f.comp a : ↥A →* Multiplicative (ZMod ℓ)) :
        ↥A → Multiplicative (ZMod ℓ)) := by
      obtain ⟨N, hN, hNa⟩ := hasm
      exact ⟨N, hN, fun y n hn => by
        show f (a (y * n)) = f (a y)
        rw [hNa y n hn]⟩
    have h1 : f (a x) = 1 := congrFun (MonoidHom.mem_ker.1 hx) ⟨f.comp a, hsm⟩
    exact hf h1
  exact ⟨QuotientGroup.lift F.ker a hker, fun x => rfl⟩

end Quotient

end InverseGalois.Shafarevich
