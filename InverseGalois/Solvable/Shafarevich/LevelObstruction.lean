/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.EmbeddingClass
import InverseGalois.CFT.Profinite.EmbeddingConj
import InverseGalois.CFT.Profinite.TransgressionClass
import InverseGalois.Solvable.Shafarevich.LayerSection
import InverseGalois.Solvable.Shafarevich.LevelSolution

/-!
# What a solution at one level buys for the step to the next

A solution at one level of the filtration carries two pieces of data beyond being a surjection: it
projects onto the fixed base realization, and it is trivial on a prescribed family of subgroups
wherever the base realization is.  Together those two say that the projection onto the operator
group is injective on each member of the family and has a prescribed image there, which is exactly
the input the shrinking count consumes: a subgroup on which the projection is injective is carried
isomorphically onto a subgroup downstairs settled by the base realization alone, so the count may
be run before the solution at the level is chosen, and the number of letters it asks for does not
depend on which solution is produced.

Running the count therefore turns a solution at one level, for every number of letters, into a
single solution at that level whose lifting obstruction to the next level dies on every member of
the family: the class of the extension one layer gives already dies on the images of those
subgroups, and an obstruction which is inflated from a class already trivial upstairs is trivial.

The family the count consumes is finite, while the family against which local triviality is
measured is the whole of the decomposition subgroups, and the difference matters: a class trivial at
finitely many places need not be trivial.  Along the members the finite family does not name the
step is asked outright to be locally solvable, which the structure of the local groups there
supplies.  The obstruction of the step is then an everywhere locally trivial class, and what is left
of the step is to make such classes vanish.

Granting that there is no such class the lift exists, and the step is reduced to its two remaining
clauses, that the lift is again onto and again trivial along the family.  The statements are proved
here, the first over an arbitrary abstract group, since nothing about a Galois group is used until
the obstruction itself is formed.

## Main definitions

* `InverseGalois.Shafarevich.conjFamily` — the conjugates of the members of a finite family of
  subgroups.
* `InverseGalois.Shafarevich.IsShrinkStable` — a property of solutions which a shrinking does not
  destroy.
* `InverseGalois.Shafarevich.HasLocalLift` — the step is solvable along every member of the wider
  family which the finite one does not name, for every solution carrying the prescribed property.
* `InverseGalois.Shafarevich.HasSolutionRepair` — a lift which is already onto, already over the
  base realization and already trivial along the finite family can be corrected into a solution
  carrying the prescribed property.

## Main results

* `InverseGalois.Shafarevich.exists_operatorHom_forall_exists_subgroup_resH2_extensionClass_eq_one`
  — **a homomorphism over the operator group which is trivial on a family of subgroups wherever the
  operator map is meets, after one shrinking, a subgroup over which the extension of the layer
  splits.**
* `InverseGalois.Shafarevich.exists_levelSolution_liftObstructionClass_mem_sha2` — **solutions at
  one level for every number of letters give a single solution whose obstruction to the next level
  is everywhere locally trivial.**
* `InverseGalois.Shafarevich.exists_lift_of_levelSolution` — **and hence, once no class is
  everywhere locally trivial, a solution at one level lifts to the next.**

## Tags

Shafarevich's theorem, embedding problem, obstruction, p-central series, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

attribute [local instance] genericQuotAction

/-! ### The conjugates of a finite family -/

/-- **The conjugates of the members of a finite family of subgroups.**

A family of subgroups chosen once and for all is necessarily finite, and over a number field a
place of the base field carries not one decomposition subgroup of the absolute Galois group but a
whole conjugacy class of them, one for each prime of the big field above it, of which there are
infinitely many.  The family can therefore name only one member of each class, and everything
arranged at the named member has to be transported to the others by conjugation. -/
def conjFamily {Γ : Type*} [Group Γ] {t : ℕ} (D : Fin t → Subgroup Γ) : Set (Subgroup Γ) :=
  {A | ∃ (ν : Fin t) (σ : Γ), A = (D ν).map (MulAut.conj σ).toMonoidHom}

/-- **A member of the family is one of its own conjugates.** -/
theorem self_mem_conjFamily {Γ : Type*} [Group Γ] {t : ℕ} (D : Fin t → Subgroup Γ) (ν : Fin t) :
    D ν ∈ conjFamily D := by
  refine ⟨ν, 1, ?_⟩
  have h1 : (MulAut.conj (1 : Γ)).toMonoidHom = MonoidHom.id Γ := by
    ext x
    show (1 : Γ) * x * 1⁻¹ = x
    group
  rw [h1, Subgroup.map_id]

/-- **Triviality along a family wherever a homomorphism is trivial extends to the conjugates of the
family.**  Conjugating an element of a conjugate back into the family changes the value of both
homomorphisms by conjugation, which neither creates nor destroys triviality. -/
theorem eq_one_of_mem_conjFamily {Γ V W : Type*} [Group Γ] [Group V] [Group W] (φ : Γ →* V)
    (Φ : Γ →* W) {t : ℕ} {D : Fin t → Subgroup Γ}
    (h : ∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1) :
    ∀ A ∈ conjFamily D, ∀ x ∈ A, φ x = 1 → Φ x = 1 := by
  rintro _ ⟨ν, σ, rfl⟩ x hx hx1
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  show Φ (σ * y * σ⁻¹) = 1
  have hy1 : φ y = 1 := by
    have := hx1
    rw [show (MulAut.conj σ).toMonoidHom y = σ * y * σ⁻¹ from rfl, _root_.map_mul,
      _root_.map_mul, _root_.map_inv] at this
    simpa using this
  rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, h (D ν) ⟨ν, rfl⟩ y hy hy1]
  simp

/-! ### Splitting over the image of a completely decomposed subgroup -/

/-- **A homomorphism over the operator group which is trivial on a family of subgroups wherever the
operator map is meets, after one shrinking, a subgroup over which the extension given by one layer
splits.**

The family of subgroups downstairs is the image of the given one under the operator map, and it is
settled before the count is run; the subgroups upstairs are produced afterwards by whatever
homomorphism over the operator map one happens to have.  Being trivial on a member of the family
wherever the operator map is says precisely that the projection is injective there, so the member
is carried isomorphically onto its image downstairs. -/
theorem exists_operatorHom_forall_exists_subgroup_resH2_extensionClass_eq_one (ℓ : ℕ)
    [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U]
    (n : ℕ) (S : Type) [Group S] [Finite S] (hS : IsPGroup ℓ S) (j : ℕ) {Γ : Type*} [Group Γ]
    (φ : Γ →* U) {t : ℕ} (D : Fin t → Subgroup Γ)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section) :
    ∃ m : ℕ, ∀ Φ : Γ →* GenericQuot ℓ U m S j,
      (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) →
      (∀ (ν : Fin t), ∀ x ∈ D ν, φ x = 1 → Φ x = 1) →
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ A ∈ conjFamily D, ∃ H : Subgroup (GenericQuot ℓ U n S j),
          (∀ d : ↥A, ((layerSemidirectMap ℓ hα j).comp Φ) (d : Γ) ∈ H) ∧
            resH2 H (extensionClass (layerExtension ℓ (genericAut U n S) j)
              (smul_eq_conjActHom_genericLayer ℓ U n S j) σn) = 1 := by
  obtain ⟨m, hm⟩ := exists_operatorHom_forall_resH2_extensionClass_subgroup_eq_one ℓ U n S hS j t
    (fun ν => (D ν).map φ) σn
  refine ⟨m, fun Φ hright hloc => ?_⟩
  have hcomp : (SemidirectProduct.rightHom : GenericQuot ℓ U m S j →* U).comp Φ = φ :=
    MonoidHom.ext hright
  have hinj : ∀ (ν : Fin t), ∀ x ∈ (D ν).map Φ,
      SemidirectProduct.rightHom x = (1 : U) → x = 1 := by
    intro ν x hx hx1
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    exact hloc ν d hd ((hright d).symm.trans hx1)
  have hmap : ∀ ν : Fin t, ((D ν).map Φ).map
      (SemidirectProduct.rightHom : GenericQuot ℓ U m S j →* U) = (D ν).map φ := by
    intro ν
    rw [Subgroup.map_map, hcomp]
  obtain ⟨α, hα, hαsurj, hkill⟩ := hm (fun ν => (D ν).map Φ) hinj hmap
  refine ⟨α, hα, hαsurj, ?_⟩
  rintro _ ⟨ν, σ, rfl⟩
  set Ψ := (layerSemidirectMap ℓ hα j).comp Φ
  refine ⟨(((D ν).map Φ).map (layerSemidirectMap ℓ hα j)).map
      (MulAut.conj (Ψ σ)).toMonoidHom, fun d => ?_,
    resH2_extensionClass_map_conj_eq_one (layerExtension ℓ (genericAut U n S) j)
      (smul_eq_conjActHom_genericLayer ℓ U n S j) σn _ (Ψ σ) (hkill ν)⟩
  obtain ⟨y, hy, hyd⟩ := Subgroup.mem_map.1 d.2
  have hcoe : (d : Γ) = σ * y * σ⁻¹ := hyd.symm
  have hmemH : Ψ y ∈ ((D ν).map Φ).map (layerSemidirectMap ℓ hα j) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hy)
  refine Subgroup.mem_map.2 ⟨Ψ y, hmemH, ?_⟩
  show Ψ σ * Ψ y * (Ψ σ)⁻¹ = Ψ (d : Γ)
  rw [hcoe, _root_.map_mul, _root_.map_mul, _root_.map_inv]

/-! ### The obstruction of the step is everywhere locally trivial -/

/-- **A property of solutions which a shrinking does not destroy.**

Every statement of the ladder produces its solution by pushing an earlier one down along a
shrinking, so a property that is to be carried up the ladder has to survive that push.  In the
arithmetic the property is a prescription on the ramification of the field the solution cuts out,
and a shrinking only makes that field smaller, so nothing is lost. -/
def IsShrinkStable (ℓ : ℕ) (U : Type) [Group U] (S : Type) [Group S] {k Ω : Type*} [Field k]
    [Field Ω] [Algebra k Ω] (P : LevelProperty ℓ U S k Ω) : Prop :=
  ∀ (m n j : ℕ) {α : Generic U m S →* Generic U n S} (hα : IsOperatorHom α)
    (Ψ : Gal(Ω/k) →* GenericQuot ℓ U m S j),
    P m j Ψ → P n j ((layerSemidirectMap ℓ hα j).comp Ψ)

/-- **The step is solvable along every member of the wider family which the finite one does not
name.**

Local triviality of the obstruction is measured against the whole family of decomposition
subgroups, which is far larger than the finite family the shrinking count consumes; along the
conjugates of the finite family the extension itself is made to split, and along the rest the step
is asked outright to have a local solution.  Conjugates have to be counted as named, since a place
of the base field carries a whole conjugacy class of decomposition subgroups and a finite family
can name only one member of it, while what the shrinking arranges at the named member holds at all
of them.  In the arithmetic the members not named are the places at which the field cut out
is unramified, where the local group is procyclic and any element of the group above generates a
lift, and the places at which it is ramified but the base field splits completely, where a root of a
uniformizer produces one.

That second case is why the condition is asked only of the solutions carrying the prescribed
property: a place at which the field cut out ramifies without the base field splitting completely
there has no reason to admit a local solution at all, the local group having a bounded supply of
roots of unity.  Within that restriction the condition is asked of every solution at the level which
is smooth, over the base realization and trivial along the finite family, since which solution the
count produces is settled only after the count has been run. -/
def HasLocalLift (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type)
    [Group S] [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))
    (T : Set (Subgroup Gal(Ω/k))) (P : LevelProperty ℓ U S k Ω) : Prop :=
  ∀ Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j, IsSmoothHom Φ →
    (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) →
    (∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1) → P n j Φ →
    ∀ A ∈ T, A ∉ conjFamily D →
      ∃ g : ↥A →* GenericQuot ℓ U n S (j + 1),
        IsSmooth₁ (g : ↥A → GenericQuot ℓ U n S (j + 1)) ∧
          ∀ x : ↥A, (layerExtension ℓ (genericAut U n S) j).rightHom (g x) = Φ x

/-- **A lift which is already onto, already over the base realization and already trivial along the
finite family can be corrected into a solution carrying the prescribed property.**

Every clause of a solution at the next level is supplied by such a lift except the prescribed
property itself, and the property is not inherited: making the lift trivial along the family is
arranged by a shrinking, and the field the shrunken lift cuts out ramifies at places the field below
did not.  The correction is a twist by a global class of the first cohomology whose components at
those places are prescribed, which disturbs neither the surjectivity nor the projection nor the
triviality along the family, and which restores the property. -/
def HasSolutionRepair (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type)
    [Group S] [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) {t : ℕ} (D : Fin t → Subgroup Gal(Ω/k))
    (P : LevelProperty ℓ U S k Ω) : Prop :=
  ∀ (Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j) (f : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1)),
    IsSmoothHom Φ → (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) → P n j Φ →
    Function.Surjective f → IsSmoothHom f →
    (∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (f x) = Φ x) →
    (∀ ν : Fin t, ∀ x ∈ D ν, φ x = 1 → f x = 1) →
    LevelSolution ℓ U S φ (Set.range D) P n (j + 1)

/-- **Solutions at one level of the filtration for every number of letters give a single solution
whose obstruction to the next level is everywhere locally trivial.**

The count which makes the class of the extension die on the prescribed family asks for some number
of letters; a solution is available at that number, and the count then produces a surjection onto
the group with fewer letters over which the class does die.  The obstruction of the step is
inflated from that class, so it dies on the finite family too.

The family against which local triviality is measured may be much larger than the finite one the
count consumes, and for the arithmetic it has to be: local triviality at finitely many places is a
far weaker statement than local triviality everywhere.  Along the extra members the step is asked
outright to be locally solvable, which is what the structure of the local groups there provides.
The whole of what is left of the step is then to make an everywhere locally trivial class
vanish. -/
theorem exists_levelSolution_liftObstructionClass_mem_sha2 (ℓ : ℕ) [Fact ℓ.Prime] (U : Type)
    [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S]
    [Finite S] (hS : IsPGroup ℓ S) (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)] {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (T : Set (Subgroup Gal(Ω/k)))
    (P : LevelProperty ℓ U S k Ω) (hstab : IsShrinkStable ℓ U S P)
    (hvan : HasLocalLift ℓ U n S j φ D T P)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) P m j) :
    ∃ Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j, Function.Surjective Φ ∧ IsSmoothHom Φ ∧
      (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) ∧
      (∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1) ∧ P n j Φ ∧
      ∀ (hact : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
            x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom (Φ x) v)
          (hker : IsOpenNormal Φ.ker),
        liftObstructionClass (layerExtension ℓ (genericAut U n S) j) Φ hact hker σn
          ∈ sha2 ↥(layerSub ℓ (Generic U n S) j) T := by
  obtain ⟨m, hm⟩ :=
    exists_operatorHom_forall_exists_subgroup_resH2_extensionClass_eq_one ℓ U n S hS j φ D σn
  obtain ⟨Φ₀, hsurj, hsm, hright, hloc, hP⟩ := h m
  obtain ⟨α, hα, hαsurj, hres⟩ := hm Φ₀ hright fun ν => hloc (D ν) ⟨ν, rfl⟩
  set Φ := (layerSemidirectMap ℓ hα j).comp Φ₀ with hΦdef
  have hΦsm : IsSmoothHom Φ :=
    isSmoothHom_comp hsm (isSmoothHom_of_continuous continuous_of_discreteTopology)
  have hΦright : ∀ x, SemidirectProduct.rightHom (Φ x) = φ x := fun x => hright x
  have hΦloc : ∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1 := by
    rintro _ ⟨ν, rfl⟩ x hx hx1
    show layerSemidirectMap ℓ hα j (Φ₀ x) = 1
    rw [hloc (D ν) ⟨ν, rfl⟩ x hx hx1, _root_.map_one]
  have hΦP : P n j Φ := hstab m n j hα Φ₀ hP
  refine ⟨Φ, (layerSemidirectMap_surjective ℓ hα j hαsurj).comp hsurj, hΦsm, hΦright, hΦloc, hΦP,
    fun hact hker => mem_sha2.2 fun A hA => ?_⟩
  by_cases hAD : A ∈ conjFamily D
  · exact mem_sha2.1 (liftObstructionClass_mem_sha2_of_extensionClass
      (layerExtension ℓ (genericAut U n S) j) Φ
      (smul_eq_conjActHom_genericLayer ℓ U n S j) hact hker σn hres) A hAD
  · exact (resH2_liftObstructionClass_eq_one_iff (layerExtension ℓ (genericAut U n S) j) Φ
      hact hker σn A).2 (hvan Φ hΦsm hΦright hΦloc hΦP A hA hAD)

/-! ### The lift itself, once there is no locally trivial class -/

/-- **Once no class of the second cohomology is everywhere locally trivial, a solution at one level
of the filtration lifts to the next.**

The lift is a homomorphism to the group one layer up over the solution at the level, and nothing
more: whether it is onto, and whether it is again trivial along the family, is left open, those
being the two things the arithmetic still has to arrange. -/
theorem exists_lift_of_levelSolution (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U]
    [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S]
    (hS : IsPGroup ℓ S) (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)]
    (hactφ : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)), x • v = φ x • v) {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (T : Set (Subgroup Gal(Ω/k)))
    (P : LevelProperty ℓ U S k Ω) (hstab : IsShrinkStable ℓ U S P)
    (hvan : HasLocalLift ℓ U n S j φ D T P)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section)
    (hbot : sha2 ↥(layerSub ℓ (Generic U n S) j) T = ⊥)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) P m j) :
    ∃ (Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j) (f : Gal(Ω/k) →* GenericQuot ℓ U n S (j + 1)),
      Function.Surjective Φ ∧ IsSmoothHom Φ ∧ (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) ∧
        (∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1) ∧ P n j Φ ∧ IsSmoothHom f ∧
          ∀ x, (layerExtension ℓ (genericAut U n S) j).rightHom (f x) = Φ x := by
  obtain ⟨Φ, hsurj, hsm, hright, hloc, hΦP, hsha⟩ :=
    exists_levelSolution_liftObstructionClass_mem_sha2 ℓ U n S hS j φ D T P hstab hvan σn h
  have hact : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
      x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom (Φ x) v := by
    intro x v
    rw [hactφ x v, ← hright x]
    exact (genericQuotAction_smul ℓ U n n S j (Φ x) v).symm.trans
      (smul_eq_conjActHom_genericLayer ℓ U n S j (Φ x) v)
  have hker : IsOpenNormal Φ.ker := isOpenNormal_ker_of_isSmoothHom hsm
  obtain ⟨f, hfsm, hf⟩ :=
    (liftObstructionClass_eq_one_iff (layerExtension ℓ (genericAut U n S) j) Φ hact hker σn).1
      ((Subgroup.eq_bot_iff_forall _).1 hbot _ (hsha hact hker))
  exact ⟨Φ, f, hsurj, hsm, hright, hloc, hΦP, isSmoothHom_of_isSmooth₁ hfsm, hf⟩

end InverseGalois.Shafarevich
