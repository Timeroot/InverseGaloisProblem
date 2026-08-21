import Mathlib
import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.BaseChange

/-!
# Division representatives, and Brauer groups that vanish

Every finite-dimensional central simple algebra `A` over a field `K` is, by the Wedderburn–Artin
theorem, a matrix algebra `Mₙ(D)` over a division algebra `D`; the division algebra is again
central over `K` and finite-dimensional, because the centre of a matrix algebra is the centre of
its coefficient ring. Consequently `D` represents the class of `A` in the Brauer group of `K`.

Two classical vanishing statements follow. Over an algebraically closed field the only
finite-dimensional central division algebra is the field itself, since every element generates a
finite field extension. Over a finite field, Wedderburn's little theorem makes every finite
division ring commutative, and centrality again forces it to be the base field. In both cases
every central simple algebra is a matrix algebra and the Brauer group is trivial.

## Main definitions

* `Algebra.IsCentral.algEquivOfComm`: the identification of a commutative central algebra with
  its base field.

## Main results

* `Algebra.IsCentral.of_matrix`: centrality of a matrix algebra descends to the coefficients.
* `Algebra.IsCentral.bijective_algebraMap_of_comm`: a commutative central algebra is the base
  field.
* `CSA.exists_divisionRing`: the Wedderburn division algebra of a central simple algebra.
* `CSA.exists_isDomain_brauerEquivalent`, `BrauerGroup.exists_isDomain_mk_eq`: every Brauer class
  is represented by a division algebra.
* `BrauerGroup.mk_eq_one_of_isAlgClosed`, `BrauerGroup.subsingleton_of_isAlgClosed`: the Brauer
  group of an algebraically closed field is trivial.
* `CSA.exists_algEquiv_matrix_of_finite`, `BrauerGroup.mk_eq_one_of_finite`,
  `BrauerGroup.subsingleton_of_finite`: the Brauer group of a finite field is trivial.
* `CSA.exists_algEquiv_matrix_baseChange_of_isAlgClosed`,
  `BrauerGroup.relative_eq_top_of_subsingleton`, `BrauerGroup.relative_eq_top_of_isAlgClosed`: an
  algebraically closed extension splits every class.
* `CSA.exists_sq_finrank`: the dimension of a central simple algebra is a perfect square.

## Tags

Brauer group, central simple algebra, division algebra, Wedderburn
-/

universe u v

open scoped TensorProduct

attribute [instance] Brauer.CSA_Setoid

variable {K : Type u} [Field K]

/-! ### Centrality of the coefficients of a central matrix algebra -/

/-- If a nonempty matrix algebra over `D` is central over `K`, then so is `D`: the centre of
`Mₙ(D)` consists of the scalar matrices with entries in the centre of `D`. -/
theorem Algebra.IsCentral.of_matrix (F : Type*) [CommSemiring F] (D : Type*) [Semiring D]
    [Algebra F D] (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Algebra.IsCentral F (Matrix ι ι D)] : Algebra.IsCentral F D where
  out x hx := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hset : Matrix.scalar ι x ∈ Subalgebra.center F (Matrix ι ι D) := by
      have : Matrix.scalar ι x ∈ Set.center (Matrix ι ι D) := by
        rw [Matrix.center_eq_scalar_image]
        exact ⟨x, Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp hx), rfl⟩
      exact Subalgebra.mem_center_iff.mpr fun b => (Semigroup.mem_center_iff.mp this b)
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hset)
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    have := congrFun (congrFun hc i) i
    simpa [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply] using this

/-- A commutative central algebra over a field is the field itself: the structure map is
bijective. -/
theorem Algebra.IsCentral.bijective_algebraMap_of_comm (F : Type*) [Field F] (D : Type*)
    [CommRing D] [Nontrivial D] [Algebra F D] [Algebra.IsCentral F D] :
    Function.Bijective (algebraMap F D) := by
  refine ⟨(algebraMap F D).injective, fun x => ?_⟩
  have hx : x ∈ Subalgebra.center F D := by rw [Subalgebra.center_eq_top]; trivial
  exact Algebra.mem_bot.mp (Algebra.IsCentral.out hx)

/-- A commutative central algebra over a field is the field itself. -/
noncomputable def Algebra.IsCentral.algEquivOfComm (F : Type*) [Field F] (D : Type*)
    [CommRing D] [Nontrivial D] [Algebra F D] [Algebra.IsCentral F D] : F ≃ₐ[F] D :=
  AlgEquiv.ofBijective (Algebra.ofId F D)
    (Algebra.IsCentral.bijective_algebraMap_of_comm F D)

/-! ### The Wedderburn division algebra of a central simple algebra -/

/-- **Wedderburn–Artin** for central simple algebras: a finite-dimensional central simple
`K`-algebra `A` is a matrix algebra over a finite-dimensional central division `K`-algebra `D`. -/
theorem CSA.exists_divisionRing (A : CSA.{u, v} K) :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type v) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
      Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) := by
  have : IsArtinianRing (A : Type v) := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, hD, hDalg, hDfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K (A : Type v)
  refine ⟨n, hn, D, hD, hDalg, ?_, hDfin, ⟨e⟩⟩
  have hcen : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv K (A : Type v) _ e
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn.out⟩⟩
  exact Algebra.IsCentral.of_matrix K D (Fin n)

/-- Every finite-dimensional central simple algebra is Brauer equivalent to a central simple
algebra which is a division algebra, namely to its Wedderburn division algebra. -/
theorem CSA.exists_isDomain_brauerEquivalent (A : CSA.{u, v} K) :
    ∃ B : CSA.{u, v} K, IsDomain (B : Type v) ∧ IsBrauerEquivalent A B := by
  obtain ⟨n, hn, D, hD, hDalg, hDcen, hDfin, ⟨e⟩⟩ := A.exists_divisionRing
  refine ⟨⟨AlgCat.of K D⟩, inferInstanceAs (IsDomain D), ?_⟩
  exact IsBrauerEquivalent.of_algEquiv_matrix (B := ⟨AlgCat.of K D⟩) hn.out e

/-- Every element of the Brauer group of `K` is the class of a central simple algebra which is a
division algebra. -/
theorem BrauerGroup.exists_isDomain_mk_eq (x : BrauerGroup.{u, u} K) :
    ∃ B : CSA.{u, u} K, IsDomain (B : Type u) ∧ x = ⟦B⟧ := by
  induction x using Quotient.ind with
  | _ A =>
    obtain ⟨B, hB, hAB⟩ := A.exists_isDomain_brauerEquivalent
    exact ⟨B, hB, Quotient.sound hAB⟩

/-! ### Algebraically closed fields -/

/-- Over an algebraically closed field every finite-dimensional central simple algebra is trivial
in the Brauer group. -/
theorem BrauerGroup.mk_eq_one_of_isAlgClosed [IsAlgClosed K] (A : CSA.{u, u} K) :
    (⟦A⟧ : BrauerGroup K) = 1 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K (A : Type u)
  exact mk_eq_one_of_algEquiv_matrix hn.out e

/-- The Brauer group of an algebraically closed field is trivial. -/
theorem BrauerGroup.subsingleton_of_isAlgClosed (K : Type u) [Field K] [IsAlgClosed K] :
    Subsingleton (BrauerGroup.{u, u} K) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with
  | _ A =>
    induction y using Quotient.ind with
    | _ B => rw [mk_eq_one_of_isAlgClosed A, mk_eq_one_of_isAlgClosed B]

/-! ### Finite fields -/

/-- Over a finite field every finite-dimensional central division algebra is the field itself:
this is **Wedderburn's little theorem** together with centrality. -/
theorem CSA.exists_algEquiv_matrix_of_finite [Finite K] (A : CSA.{u, u} K) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, hn, D, hD, hDalg, hDcen, hDfin, ⟨e⟩⟩ := A.exists_divisionRing
  have : Finite D := Module.finite_of_finite K (M := D)
  let _ : Field D := littleWedderburn D
  refine ⟨n, hn, ⟨e.trans (AlgEquiv.mapMatrix (Algebra.IsCentral.algEquivOfComm K D).symm)⟩⟩

/-- Over a finite field every finite-dimensional central simple algebra is trivial in the Brauer
group. -/
theorem BrauerGroup.mk_eq_one_of_finite [Finite K] (A : CSA.{u, u} K) :
    (⟦A⟧ : BrauerGroup K) = 1 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := A.exists_algEquiv_matrix_of_finite
  exact mk_eq_one_of_algEquiv_matrix hn.out e

/-- The Brauer group of a finite field is trivial. -/
theorem BrauerGroup.subsingleton_of_finite (K : Type u) [Field K] [Finite K] :
    Subsingleton (BrauerGroup.{u, u} K) := by
  refine ⟨fun x y => ?_⟩
  induction x using Quotient.ind with
  | _ A =>
    induction y using Quotient.ind with
    | _ B => rw [mk_eq_one_of_finite A, mk_eq_one_of_finite B]

/-! ### Splitting by an algebraically closed extension -/

/-- An algebraically closed extension splits every finite-dimensional central simple algebra:
the base-changed algebra is a matrix algebra. -/
theorem CSA.exists_algEquiv_matrix_baseChange_of_isAlgClosed (L : Type*) [Field L] [Algebra K L]
    [IsAlgClosed L] (A : CSA.{u, v} K) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty ((L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) :=
  IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed L (L ⊗[K] A)

/-- If the Brauer group of `L` is trivial, then `L` splits every class over `K`. -/
theorem BrauerGroup.relative_eq_top_of_subsingleton (L : Type u) [Field L] [Algebra K L]
    (h : Subsingleton (BrauerGroup.{u, u} L)) : BrauerGroup.relative K L = ⊤ :=
  eq_top_iff.mpr fun x _ =>
    show x ∈ (baseChangeHom L).ker from MonoidHom.mem_ker.mpr (h.elim _ _)

/-- Every class of the Brauer group of `K` is split by an algebraically closed extension `L`, so
the relative Brauer group `Br(L / K)` is everything. -/
theorem BrauerGroup.relative_eq_top_of_isAlgClosed (L : Type u) [Field L] [Algebra K L]
    [IsAlgClosed L] : BrauerGroup.relative K L = ⊤ := by
  rw [eq_top_iff]
  refine fun x _ => ?_
  induction x using Quotient.ind with
  | _ A =>
    obtain ⟨n, hn, ⟨e⟩⟩ := A.exists_algEquiv_matrix_baseChange_of_isAlgClosed L
    exact mk_mem_relative_of_algEquiv_matrix L hn.out e

/-- The dimension of a finite-dimensional central simple algebra is a perfect square: after base
change to an algebraic closure it becomes a matrix algebra. -/
theorem CSA.exists_sq_finrank (A : CSA.{u, v} K) : ∃ n : ℕ, Module.finrank K A = n ^ 2 := by
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    A.exists_algEquiv_matrix_baseChange_of_isAlgClosed (AlgebraicClosure K)
  refine ⟨n, ?_⟩
  have h1 : Module.finrank (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A) =
      Module.finrank K A := Module.finrank_baseChange
  have h2 : Module.finrank (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A) = n ^ 2 := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Module.finrank_self]
    simp [sq]
  rw [← h1, h2]
