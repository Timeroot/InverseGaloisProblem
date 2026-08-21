import Mathlib
import InverseGalois.CFT.Brauer.Centralizer
import InverseGalois.CFT.Brauer.Division
import InverseGalois.CFT.Brauer.Tower

/-!
# Every Brauer class is split by a finite extension

Let `K` be a field. This file proves that every element of the Brauer group of `K` lies in the
relative Brauer group `Br(F / K)` for some finite extension `F / K` sitting inside a fixed
algebraic closure of `K`.

The argument is the classical one. A Brauer class is represented by a central simple `K`-algebra
`D` whose underlying ring is a domain. Among the `K`-subalgebras of `D` that commute with
themselves there is one of largest dimension; by the double centralizer theorem it is its own
centralizer, and because it is a finite-dimensional commutative domain over `K` it is a field.
A self-centralizing subfield splits the algebra, so `D` becomes a matrix algebra after extending
scalars to it. Finally that subfield, being a finite extension of `K`, embeds into the algebraic
closure of `K`, and transporting the embedding of the subfield into `D` along the resulting
isomorphism realises the splitting field as an intermediate field of `AlgebraicClosure K / K`.

## Main results

* `InverseGalois.CFT.exists_centralizer_eq_self`: a finite-dimensional `K`-algebra has a
  subalgebra that commutes with itself and is maximal with that property.
* `InverseGalois.CFT.exists_centralizer_eq`: a finite-dimensional `K`-algebra has a subalgebra
  equal to its own centralizer.
* `InverseGalois.CFT.isField_of_le_centralizer`: a self-commuting subalgebra of a
  finite-dimensional domain over `K` is a field.
* `InverseGalois.CFT.exists_intermediateField_algEquiv_matrix`: a central simple `K`-algebra
  which is a domain is split by a finite intermediate field of `AlgebraicClosure K / K`.
* `InverseGalois.CFT.exists_intermediateField_mem_relative`: **every Brauer class over `K` is
  split by a finite extension of `K`**.
* `InverseGalois.CFT.iSup_relative_eq_top`: the Brauer group of `K` is the union of the relative
  Brauer groups of the finite intermediate fields of `AlgebraicClosure K / K`.

## Tags

Brauer group, central simple algebra, maximal subfield, splitting field
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

open scoped TensorProduct

open Module

namespace InverseGalois.CFT

variable {K : Type u} [Field K]

/-! ### Maximal self-commuting subalgebras -/

/-- A finite-dimensional `K`-algebra contains a `K`-subalgebra that commutes with itself and is
maximal among the subalgebras with that property: dimensions of self-commuting subalgebras are
bounded by the dimension of the algebra, so one of largest dimension exists. -/
theorem exists_centralizer_eq_self (A : Type u) [Ring A] [Algebra K A]
    [FiniteDimensional K A] :
    ∃ F : Subalgebra K A, F ≤ Subalgebra.centralizer K (F : Set A) ∧
      ∀ F' : Subalgebra K A, F ≤ F' → F' ≤ Subalgebra.centralizer K (F' : Set A) → F' = F := by
  classical
  set S : Set ℕ := {n | ∃ F : Subalgebra K A,
    F ≤ Subalgebra.centralizer K (F : Set A) ∧ finrank K F = n} with hS
  have hbot : (⊥ : Subalgebra K A) ≤ Subalgebra.centralizer K ((⊥ : Subalgebra K A) : Set A) := by
    intro x hx
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    obtain ⟨k, rfl⟩ := Algebra.mem_bot.mp hx
    exact (Algebra.commutes k g).symm
  have hne : S.Nonempty := ⟨_, ⟨⊥, hbot, rfl⟩⟩
  have hbdd : BddAbove S := by
    refine ⟨finrank K A, ?_⟩
    rintro n ⟨F, -, rfl⟩
    exact Submodule.finrank_le (Subalgebra.toSubmodule F)
  obtain ⟨F, hF, hrank⟩ := Nat.sSup_mem hne hbdd
  refine ⟨F, hF, fun F' hle hF' => ?_⟩
  have hmem : finrank K F' ∈ S := ⟨F', hF', rfl⟩
  have hle' : finrank K F' ≤ finrank K F := hrank ▸ le_csSup hbdd hmem
  exact (Subalgebra.eq_of_le_of_finrank_le hle hle').symm

/-- A finite-dimensional `K`-algebra contains a `K`-subalgebra which is its own centralizer,
namely a self-commuting subalgebra of largest dimension. -/
theorem exists_centralizer_eq (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    ∃ F : Subalgebra K A, Subalgebra.centralizer K (F : Set A) = F := by
  obtain ⟨F, hF, hmax⟩ := exists_centralizer_eq_self (K := K) A
  exact ⟨F, Centralizer.centralizer_eq_self_of_maximal F hF hmax⟩

/-! ### Self-commuting subalgebras of a domain are fields -/

/-- A `K`-subalgebra contained in its own centralizer is commutative. -/
theorem mul_comm_of_le_centralizer {A : Type u} [Ring A] [Algebra K A] {F : Subalgebra K A}
    (hF : F ≤ Subalgebra.centralizer K (F : Set A)) (x y : ↥F) : x * y = y * x :=
  Subtype.ext (hF y.2 (x : A) x.2)

/-- A `K`-subalgebra of a finite-dimensional domain over `K` which is contained in its own
centralizer is a field: it is commutative, it has no zero divisors, and multiplication by a
nonzero element is an injective, hence surjective, `K`-linear endomorphism of it. -/
theorem isField_of_le_centralizer {D : Type u} [Ring D] [IsDomain D] [Algebra K D]
    [FiniteDimensional K D] {F : Subalgebra K D}
    (hF : F ≤ Subalgebra.centralizer K (F : Set D)) : IsField ↥F := by
  haveI : FiniteDimensional K ↥F := inferInstance
  refine ⟨exists_pair_ne ↥F, mul_comm_of_le_centralizer hF, fun {a} ha => ?_⟩
  have ha' : (a : D) ≠ 0 := fun h0 => ha (Subtype.ext h0)
  have hinj : Function.Injective (LinearMap.mulLeft K a) := by
    intro b c h
    have h' : (a : D) * (b : D) = (a : D) * (c : D) := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ ha' h')
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  exact ⟨b, hb⟩

/-! ### Splitting by a finite intermediate field of the algebraic closure -/

/-- A finite-dimensional central simple `K`-algebra whose underlying ring is a domain is split by
a finite extension of `K` inside `AlgebraicClosure K`: a maximal self-commuting subalgebra is a
self-centralizing subfield, it embeds into `AlgebraicClosure K`, and extending scalars to its
image turns the algebra into a matrix algebra. -/
theorem exists_intermediateField_algEquiv_matrix (D : Type u) [Ring D] [IsDomain D] [Algebra K D]
    [Algebra.IsCentral K D] [IsSimpleRing D] [FiniteDimensional K D] :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty ((E ⊗[K] D) ≃ₐ[E] Matrix (Fin n) (Fin n) E) := by
  classical
  obtain ⟨F, hF, hmax⟩ := exists_centralizer_eq_self (K := K) D
  have hcent : Subalgebra.centralizer K (F : Set D) = F :=
    Centralizer.centralizer_eq_self_of_maximal F hF hmax
  letI : Field ↥F := (isField_of_le_centralizer hF).toField
  haveI : FiniteDimensional K ↥F := inferInstance
  haveI : Algebra.IsAlgebraic K ↥F := Algebra.IsAlgebraic.of_finite K ↥F
  let φ : ↥F →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let e : ↥F ≃ₐ[K] ↥φ.fieldRange := AlgEquiv.ofInjectiveField φ
  refine ⟨φ.fieldRange, Module.Finite.equiv e.toLinearEquiv, ?_⟩
  set g : ↥φ.fieldRange →ₐ[K] D := (Subalgebra.val F).comp e.symm.toAlgHom with hg
  have hrange : g.range = F := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨z, rfl⟩
      exact (e.symm z).2
    · intro y hy
      exact ⟨e ⟨y, hy⟩, by simp [hg]⟩
  have hfr : Subalgebra.centralizer K (g.range : Set D) = g.range := by
    rw [hrange]; exact hcent
  obtain ⟨n, ⟨eqv⟩⟩ := Centralizer.exists_algEquiv_matrix_of_centralizer_eq_range g hfr
  refine ⟨n, ?_, ⟨eqv⟩⟩
  rintro rfl
  have h1 : finrank ↥φ.fieldRange (↥φ.fieldRange ⊗[K] D) = finrank K D :=
    Module.finrank_baseChange
  have h2 : finrank ↥φ.fieldRange (↥φ.fieldRange ⊗[K] D) = 0 := by
    rw [eqv.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  have h3 : 0 < finrank K D := Module.finrank_pos_iff.2 inferInstance
  omega

/-- **Every Brauer class over a field is split by a finite extension.** A class is represented by
a central simple algebra which is a domain, and such an algebra is split by a finite intermediate
field of `AlgebraicClosure K / K`. -/
theorem exists_intermediateField_mem_relative (x : BrauerGroup K) :
    ∃ F : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K F ∧ x ∈ BrauerGroup.relative K (F : Type u) := by
  obtain ⟨B, hBdom, rfl⟩ := BrauerGroup.exists_isDomain_mk_eq x
  haveI := hBdom
  obtain ⟨E, hE, n, hn, ⟨eqv⟩⟩ := exists_intermediateField_algEquiv_matrix (K := K) (B : Type u)
  exact ⟨E, hE, BrauerGroup.mk_mem_relative_of_algEquiv_matrix _ hn eqv⟩

/-- The Brauer group of `K` is exhausted by the relative Brauer groups of the finite intermediate
fields of `AlgebraicClosure K / K`. -/
theorem iSup_relative_eq_top :
    ⨆ F : {F : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K ↥F},
      BrauerGroup.relative K ↥(F : IntermediateField K (AlgebraicClosure K)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨F, hF, hx⟩ := exists_intermediateField_mem_relative x
  exact le_iSup
    (fun F : {F : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K ↥F} =>
      BrauerGroup.relative K ↥(F : IntermediateField K (AlgebraicClosure K))) ⟨F, hF⟩ hx

end InverseGalois.CFT
