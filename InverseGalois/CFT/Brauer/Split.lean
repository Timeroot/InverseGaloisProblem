import Mathlib
import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.Division
import InverseGalois.CFT.Brauer.SkolemNoether

/-!
# Recognising the trivial class of the Brauer group

Let `K` be a field. A finite-dimensional central simple `K`-algebra `A` has trivial class in
`BrauerGroup K` as soon as it is a matrix algebra over `K`; this file proves the converse, so
that the split classes are exactly the classes of matrix algebras.

The class of `A` is trivial precisely when `Mₙ(A) ≃ₐ[K] Mₘ(K)` for some `n, m ≠ 0`. Writing `A`
as `Mᵣ(D)` for a division algebra `D` by the Wedderburn–Artin theorem, this reads
`M_{nr}(D) ≃ₐ[K] Mₘ(K)`, and the task is to see that `D` is the base field, that is, that the
Wedderburn division algebra is uniquely determined.

The uniqueness is obtained by counting dimensions of modules. Over a matrix ring `M_N(D)` the
space of column vectors `Dᴺ` is a simple module, so by the theory of isotypic modules over a
simple Artinian ring every `M_N(D)`-module has `K`-dimension a multiple of
`N · dim_K D`. Transporting the tautological `Mₘ(K)`-module `Kᵐ` along the given isomorphism
makes it an `M_N(D)`-module of `K`-dimension `m`, whence `N · dim_K D` divides `m`; comparing
with `N² · dim_K D = m²`, which is the dimension of the two isomorphic matrix algebras, forces
`dim_K D = 1`.

## Main results

* `Matrix.isSimpleModule_pi`: the column vectors `ι → D` form a simple module over `Mᵢ(D)` for a
  division ring `D`.
* `Matrix.finrank_eq_one_of_algEquiv_matrix`: uniqueness in the Wedderburn–Artin theorem, in the
  split case: if a matrix algebra over a finite-dimensional division algebra `D` is isomorphic to
  a matrix algebra over the base field, then `D` is the base field.
* `BrauerGroup.exists_algEquiv_matrix_of_mk_eq_one`, `BrauerGroup.mk_eq_one_iff_algEquiv_matrix`:
  a central simple algebra is trivial in the Brauer group if and only if it is a matrix algebra
  over the base field.
* `BrauerGroup.mem_relative_iff_algEquiv_matrix`: a class lies in the relative Brauer group
  `Br(L / K)` if and only if the base-changed algebra is a matrix algebra over `L`.

## Tags

Brauer group, central simple algebra, splitting field, Wedderburn
-/

universe u v

open scoped TensorProduct

open Module

attribute [instance] Brauer.CSA_Setoid

/-! ### The column module of a matrix ring over a division ring -/

/-- The column vectors `ι → D` form a simple module over the ring `Mᵢ(D)` of square matrices
over a division ring `D`: a single nonzero coordinate of a nonzero vector can be spread over an
arbitrary target vector by one matrix. -/
theorem Matrix.isSimpleModule_pi (D : Type v) [DivisionRing D] (ι : Type*) [Fintype ι]
    [DecidableEq ι] [Nonempty ι] : IsSimpleModule (Matrix ι ι D) (ι → D) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun v hv w => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  refine ⟨Matrix.of fun i k => if k = j then w i * (v j)⁻¹ else 0, ?_⟩
  ext i
  simp only [LinearMap.toSpanSingleton_apply, Matrix.smul_eq_mulVec, Matrix.mulVec,
    Matrix.of_apply, dotProduct, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_assoc, inv_mul_cancel₀ hj, mul_one]

/-! ### Uniqueness of the Wedderburn division algebra in the split case -/

/-- **Uniqueness in the Wedderburn–Artin theorem**, in the split case: if a matrix algebra over a
finite-dimensional division algebra `D` over a field `K` is isomorphic, as a `K`-algebra, to a
matrix algebra over `K`, then `D` has dimension one over `K`. -/
theorem Matrix.finrank_eq_one_of_algEquiv_matrix {K : Type u} [Field K] {D : Type v}
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D] {N m : ℕ} (hN : N ≠ 0)
    (f : Matrix (Fin N) (Fin N) D ≃ₐ[K] Matrix (Fin m) (Fin m) K) : finrank K D = 1 := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)
  haveI : IsArtinianRing (Matrix (Fin N) (Fin N) D) :=
    IsArtinianRing.of_finite K (Matrix (Fin N) (Fin N) D)
  haveI : IsSimpleModule (Matrix (Fin N) (Fin N) D) (Fin N → D) :=
    Matrix.isSimpleModule_pi D (Fin N)
  letI : Module (Matrix (Fin N) (Fin N) D) (Fin m → K) :=
    Module.compHom (Fin m → K) f.toAlgHom.toRingHom
  have hsmul : ∀ (b : Matrix (Fin N) (Fin N) D) (w : Fin m → K), b • w = f b • w :=
    fun _ _ => rfl
  haveI : IsScalarTower K (Matrix (Fin N) (Fin N) D) (Fin m → K) :=
    IsScalarTower.of_algebraMap_smul fun c w => by
      rw [hsmul, f.commutes, algebraMap_smul]
  haveI : Module.Finite (Matrix (Fin N) (Fin N) D) (Fin m → K) :=
    Module.Finite.of_restrictScalars_finite K _ _
  obtain ⟨k, ⟨eW⟩⟩ := (SkolemNoether.isIsotypicOfType_of_isSimpleModule
    (Matrix (Fin N) (Fin N) D) (Fin m → K) (Fin N → D)).linearEquiv_fun
  have hPdim : finrank K (Fin N → D) = N * finrank K D := by
    rw [finrank_pi_fintype K (M := fun _ : Fin N => D)]
    simp
  have h1 : m = k * (N * finrank K D) :=
    calc m = finrank K (Fin m → K) := by simp
      _ = finrank K (Fin k → (Fin N → D)) := (eW.restrictScalars K).finrank_eq
      _ = k * (N * finrank K D) := by
          rw [finrank_pi_fintype K (M := fun _ : Fin k => (Fin N → D))]
          simp [hPdim]
  have h2 : N * N * finrank K D = m * m := by
    have hf := f.toLinearEquiv.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_matrix] at hf
    simpa using hf
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hbase : 0 < N * N * finrank K D :=
    Nat.mul_pos (Nat.mul_pos hNpos hNpos) Module.finrank_pos
  have key : N * N * finrank K D * (k * k * finrank K D) = N * N * finrank K D * 1 := by
    rw [mul_one]
    calc N * N * finrank K D * (k * k * finrank K D)
        = (k * (N * finrank K D)) * (k * (N * finrank K D)) := by ring
      _ = m * m := by rw [← h1]
      _ = N * N * finrank K D := h2.symm
  exact Nat.dvd_one.mp ⟨k * k, by rw [← Nat.eq_of_mul_eq_mul_left hbase key]; ring⟩

/-! ### Split classes are the classes of matrix algebras -/

/-- A finite-dimensional central simple algebra whose class in the Brauer group is trivial is a
matrix algebra over the base field. -/
theorem BrauerGroup.exists_algEquiv_matrix_of_mk_eq_one {K : Type u} [Field K] (A : CSA.{u, u} K)
    (h : (⟦A⟧ : BrauerGroup K) = 1) :
    ∃ n : ℕ, n ≠ 0 ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := (BrauerGroup.mk_eq_one_iff A).mp h
  obtain ⟨r, hr, D, hD, hDalg, hDcen, hDfin, ⟨eA⟩⟩ := A.exists_divisionRing
  have hrne : r ≠ 0 := hr.out
  have hd1 : finrank K D = 1 := by
    refine Matrix.finrank_eq_one_of_algEquiv_matrix (N := n * r) (m := m)
      (Nat.mul_ne_zero hn hrne) ?_
    exact ((Matrix.reindexAlgEquiv K D finProdFinEquiv).symm.trans
      ((Matrix.compAlgEquiv (Fin n) (Fin r) D K).symm.trans eA.mapMatrix.symm)).trans e
  have hbij : Function.Bijective (algebraMap K D) := by
    refine ⟨(algebraMap K D).injective, ?_⟩
    have hfr : finrank K K = finrank K D := by rw [Module.finrank_self, hd1]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := Algebra.linearMap K D)).mp (algebraMap K D).injective
  exact ⟨r, hrne,
    ⟨eA.trans (AlgEquiv.mapMatrix (AlgEquiv.ofBijective (Algebra.ofId K D) hbij).symm)⟩⟩

/-- A finite-dimensional central simple algebra is trivial in the Brauer group exactly when it is
a matrix algebra over the base field. -/
theorem BrauerGroup.mk_eq_one_iff_algEquiv_matrix {K : Type u} [Field K] (A : CSA.{u, u} K) :
    (⟦A⟧ : BrauerGroup K) = 1 ↔
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) :=
  ⟨BrauerGroup.exists_algEquiv_matrix_of_mk_eq_one A,
    fun ⟨_, hn, ⟨e⟩⟩ => BrauerGroup.mk_eq_one_of_algEquiv_matrix hn e⟩

/-- A class lies in the relative Brauer group `Br(L / K)` exactly when the base-changed algebra
is a matrix algebra over `L`. -/
theorem BrauerGroup.mem_relative_iff_algEquiv_matrix {K L : Type u} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, u} K) :
    (⟦A⟧ : BrauerGroup K) ∈ BrauerGroup.relative K L ↔
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  rw [BrauerGroup.relative, MonoidHom.mem_ker, BrauerGroup.baseChangeHom_mk]
  exact BrauerGroup.mk_eq_one_iff_algEquiv_matrix (A.baseChange L)
