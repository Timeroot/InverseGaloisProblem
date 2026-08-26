import Mathlib
import InverseGalois.CFT.Brauer.Tower

/-!
# Splitting a relative Brauer group along a tower

For a tower `K ⊆ L ⊆ M`, base change to `L` carries a class of `Br(K)` split by `M` to a class of
`Br(L)` split by `M`, and it kills exactly the classes already split by `L`.  The resulting exact
sequence

`1 → Br(L / K) → Br(M / K) → Br(M / L)`

is the inflation-restriction sequence of the Brauer group, and in this language its exactness is
nothing but the transitivity of base change: a class dies in `Br(L)` precisely when it lies in the
kernel of `Br(K) → Br(L)`.  The consequence used downstream is the multiplicativity bound
`|Br(M / K)| ≤ |Br(L / K)| · |Br(M / L)|`, which turns an induction on the degree of `M / K` into a
counting argument over the steps of a tower.

## Main results

* `BrauerGroup.towerHom`: base change `Br(M / K) → Br(M / L)` along the bottom step of a tower.
* `BrauerGroup.ker_towerHom`: its kernel is `Br(L / K)`.
* `BrauerGroup.card_relative_le_mul`: **`|Br(M / K)| ≤ |Br(L / K)| · |Br(M / L)|`.**
* `BrauerGroup.finite_relative_of_tower`: a relative Brauer group is finite as soon as those of the
  two steps of a tower are.

## Tags

Brauer group, relative Brauer group, tower, inflation, restriction, base change
-/

universe u

namespace BrauerGroup

variable (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

/-- **Base change along the bottom step of a tower preserves being split by the top field**: if `M`
splits a class of `Br(K)`, it splits its image in `Br(L)`. -/
theorem baseChangeHom_mem_relative {x : BrauerGroup.{u, u} K} (hx : x ∈ relative K M) :
    baseChangeHom L x ∈ relative L M := by
  rw [relative, MonoidHom.mem_ker] at hx ⊢
  rw [show baseChangeHom M (baseChangeHom L x) = baseChangeHom M x from
    DFunLike.congr_fun (baseChangeHom_comp K L M) x]
  exact hx

/-- **Restriction to the intermediate field of a tower**, as a homomorphism `Br(M / K) → Br(M / L)`
of relative Brauer groups. -/
noncomputable def towerHom : ↥(relative K M) →* ↥(relative L M) :=
  MonoidHom.codRestrict ((baseChangeHom L).comp (relative K M).subtype) (relative L M)
    fun x => baseChangeHom_mem_relative K L M x.2

@[simp]
theorem coe_towerHom_apply (x : ↥(relative K M)) :
    (towerHom K L M x : BrauerGroup.{u, u} L) = baseChangeHom L (x : BrauerGroup.{u, u} K) :=
  rfl

/-- **A class split by the top field of a tower dies in the intermediate field exactly when it is
already split there**: the inflation-restriction sequence of Brauer groups is exact. -/
theorem ker_towerHom : (towerHom K L M).ker = (relative K L).subgroupOf (relative K M) := by
  ext x
  constructor
  · intro hx
    have hx' : baseChangeHom L (x : BrauerGroup.{u, u} K) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact hx'
  · intro hx
    exact MonoidHom.mem_ker.mpr (Subtype.ext (Subgroup.mem_subgroupOf.mp hx))

/-- **The relative Brauer group of a tower is bounded by the product of those of its two steps.**
Combined with a description of the bottom step, this is what turns an induction on the degree into
a bound on the order of a relative Brauer group. -/
theorem card_relative_le_mul [Finite ↥(relative L M)] :
    Nat.card ↥(relative K M) ≤ Nat.card ↥(relative K L) * Nat.card ↥(relative L M) := by
  have hker : Nat.card ↥((towerHom K L M).ker) = Nat.card ↥(relative K L) := by
    rw [ker_towerHom]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (relative_le_relative K L M)).toEquiv
  calc Nat.card ↥(relative K M)
      = Nat.card ↥((towerHom K L M).ker) * ((towerHom K L M).ker).index :=
        (Subgroup.card_mul_index _).symm
    _ = Nat.card ↥(relative K L) * Nat.card ↥((towerHom K L M).range) := by
        rw [hker, Subgroup.index_ker]
    _ ≤ Nat.card ↥(relative K L) * Nat.card ↥(relative L M) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

/-- The kernel of restriction along the bottom step of a tower is finite as soon as the relative
Brauer group of that step is. -/
theorem finite_ker_towerHom [Finite ↥(relative K L)] : Finite ↥((towerHom K L M).ker) := by
  rw [ker_towerHom]
  exact Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe (relative_le_relative K L M)).symm.toEquiv

/-- **A relative Brauer group is finite as soon as those of the two steps of a tower are.** -/
theorem finite_relative_of_tower [Finite ↥(relative K L)] [Finite ↥(relative L M)] :
    Finite ↥(relative K M) := by
  haveI := finite_ker_towerHom K L M
  have hne : Nat.card ↥(relative K M) ≠ 0 := by
    rw [← Subgroup.card_mul_index ((towerHom K L M).ker)]
    refine Nat.mul_ne_zero Nat.card_pos.ne' ?_
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  exact (Nat.card_ne_zero.mp hne).2

/-- The bound of `BrauerGroup.card_relative_le_mul` for an intermediate field of a fixed
extension. -/
theorem card_relative_le_mul_intermediateField {K M : Type u} [Field K] [Field M] [Algebra K M]
    (L : IntermediateField K M) [Finite ↥(relative ↥L M)] :
    Nat.card ↥(relative K M) ≤ Nat.card ↥(relative K ↥L) * Nat.card ↥(relative ↥L M) :=
  card_relative_le_mul K ↥L M

/-- The finiteness of `BrauerGroup.finite_relative_of_tower` for an intermediate field of a fixed
extension. -/
theorem finite_relative_of_intermediateField {K M : Type u} [Field K] [Field M] [Algebra K M]
    (L : IntermediateField K M) [Finite ↥(relative K ↥L)] [Finite ↥(relative ↥L M)] :
    Finite ↥(relative K M) :=
  finite_relative_of_tower K ↥L M

end BrauerGroup
