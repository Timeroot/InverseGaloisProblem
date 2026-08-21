import Mathlib
import InverseGalois.CFT.Brauer.H2Brauer
import InverseGalois.CFT.GroupCohomology.CyclicSurjective

/-!
# The Brauer group of a cyclic extension

For a finite cyclic Galois extension `L / K` with generator `σ₀` of `Gal(L/K)`, the cyclic algebra
construction `a ↦ (L / K, σ₀, a)` is a homomorphism from the units of `K` to the Brauer group of
`K`: the defining cocycles multiply pointwise, and Brauer classes of crossed products multiply.
Its kernel is exactly the group of norms from `L`, so it induces an injection of `Kˣ / N(Lˣ)` into
the relative Brauer group `Br(L / K)`.

Moreover every cocycle of a cyclic group is cohomologous to one of the explicit cyclic cocycles,
so every crossed product of a cyclic extension already is a cyclic algebra up to Brauer
equivalence.

## Main results

* `InverseGalois.CFT.cyclicBrauerHom`: the homomorphism `Kˣ →* Br(K)` given by the cyclic algebra
  construction, with `InverseGalois.CFT.cyclicBrauerHom_apply` computing it.
* `InverseGalois.CFT.cyclicBrauerHom_mem_relative`: its image lies in `Br(L / K)`.
* `InverseGalois.CFT.mem_ker_cyclicBrauerHom_iff`: its kernel is the group of norms from `L`.
* `InverseGalois.CFT.cyclicBrauerHom_eq_iff`: two cyclic algebras have the same Brauer class
  exactly when their units differ by a norm.
* `InverseGalois.CFT.exists_mk_csa_eq_cyclicBrauerHom`: every crossed product of a cyclic
  extension is a cyclic algebra in the Brauer group.
-/

universe u

open Module

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-! ### Multiplicativity of the cyclic cocycle -/

section Cocycle

variable {G M : Type*} [Group G] [CommGroup M]

/-- The cyclic cocycle is multiplicative in its coefficient. -/
theorem cyclicCocycle_mul (g : G) (a b : M) (p : G × G) :
    cyclicCocycle g a p * cyclicCocycle g b p = cyclicCocycle g (a * b) p := by
  simp only [cyclicCocycle]
  split <;> simp

/-- The cyclic cocycle of the identity coefficient is the trivial cocycle. -/
theorem cyclicCocycle_one (g : G) : cyclicCocycle g (1 : M) = fun _ => 1 := by
  funext p
  simp only [cyclicCocycle]
  split <;> rfl

end Cocycle

variable {σ₀ : Gal(L/K)}

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The cyclic unit cocycle is multiplicative in its coefficient. -/
theorem cyclicUnitCocycle_mul (σ₀ : Gal(L/K)) (a b : Kˣ) :
    (fun p => cyclicUnitCocycle σ₀ a p * cyclicUnitCocycle σ₀ b p) =
      cyclicUnitCocycle σ₀ (a * b) := by
  funext p
  rw [cyclicUnitCocycle, cyclicUnitCocycle, cyclicUnitCocycle, cyclicCocycle_mul, map_mul]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The cyclic unit cocycle of the identity is the trivial cocycle. -/
theorem cyclicUnitCocycle_one (σ₀ : Gal(L/K)) :
    cyclicUnitCocycle σ₀ (1 : Kˣ) = fun _ : Gal(L/K) × Gal(L/K) => (1 : Lˣ) := by
  rw [cyclicUnitCocycle, map_one, cyclicCocycle_one]

/-! ### The homomorphism out of the units of the base field -/

variable (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)

/-- **The cyclic algebra homomorphism.**  For a cyclic Galois extension with generator `σ₀`, the
Brauer class of the cyclic algebra `(L / K, σ₀, a)` is multiplicative in `a`. -/
noncomputable def cyclicBrauerHom : Kˣ →* BrauerGroup K where
  toFun a := ⟦CrossedProduct.csa (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)⟧
  map_one' := by
    refine Eq.trans ?_ (CrossedProduct.mk_csa_one (K := K) (L := L))
    exact CrossedProduct.mk_csa_congr _ _ (cyclicUnitCocycle_one σ₀)
  map_mul' a b := by
    refine Eq.trans ?_ (CrossedProduct.mk_csa_mul (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)
      (isMulCocycle₂_cyclicUnitCocycle hσ₀ b))
    exact CrossedProduct.mk_csa_congr _ _ (cyclicUnitCocycle_mul σ₀ a b).symm

/-- The cyclic algebra homomorphism is computed by the crossed product of the cyclic cocycle. -/
theorem cyclicBrauerHom_apply (a : Kˣ) :
    cyclicBrauerHom hσ₀ a = ⟦CrossedProduct.csa (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)⟧ :=
  rfl

/-- The image of the cyclic algebra homomorphism lies in the relative Brauer group. -/
theorem cyclicBrauerHom_mem_relative (a : Kˣ) :
    cyclicBrauerHom hσ₀ a ∈ BrauerGroup.relative K L :=
  mk_cyclicAlgebra_mem_relative hσ₀ a

/-- **The kernel of the cyclic algebra homomorphism is the group of norms.** -/
theorem mem_ker_cyclicBrauerHom_iff (a : Kˣ) :
    a ∈ (cyclicBrauerHom hσ₀).ker ↔ ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K) := by
  rw [MonoidHom.mem_ker, cyclicBrauerHom_apply]
  exact mk_cyclicAlgebra_eq_one_iff hσ₀ a

/-- Two cyclic algebras have the same Brauer class exactly when their units differ by a norm. -/
theorem cyclicBrauerHom_eq_iff (a b : Kˣ) :
    cyclicBrauerHom hσ₀ a = cyclicBrauerHom hσ₀ b ↔
      ∃ c : Lˣ, Algebra.norm K (c : L) = ((a * b⁻¹ : Kˣ) : K) := by
  rw [← mem_ker_cyclicBrauerHom_iff hσ₀, MonoidHom.mem_ker, map_mul, map_inv,
    mul_inv_eq_one]

/-! ### Every crossed product of a cyclic extension is a cyclic algebra -/

/-- **Normal form.**  Over a cyclic extension every crossed product has the Brauer class of a
cyclic algebra. -/
theorem exists_mk_csa_eq_cyclicBrauerHom {f : Gal(L/K) × Gal(L/K) → Lˣ}
    (hf : IsMulCocycle₂ f) :
    ∃ a : Kˣ, (⟦CrossedProduct.csa hf⟧ : BrauerGroup K) = cyclicBrauerHom hσ₀ a := by
  obtain ⟨a, ha⟩ := exists_isMulCoboundary₂_div_cyclicUnitCocycle hσ₀ hf
  exact ⟨a, (CrossedProduct.mk_csa_eq_mk_csa_iff hf
    (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)).mpr ha⟩

end InverseGalois.CFT
