import Mathlib
import Mathieu.Primitivity
import Mathieu.Perfect
import Mathieu.M11SimpleClean

/-!
# Simplicity of `M₁₁`

`M₁₁` is a simple group.  The headline theorem `M11_isSimpleGroup` is proved by the
**`native_decide`-free** route assembled in `M11SimpleClean.lean`: `M₁₁` has a maximal,
core-free, simple subgroup `H ≅ PSL(2, 𝔽₁₁)` of index `12` (with `11 ∣ |H|`), and the abstract
criterion `isSimpleGroup_of_coatom_index_twelve` (`CosetSimple.lean`) turns this into
simplicity of `M₁₁`.  Every input is discharged with only the standard axioms
(`propext, Classical.choice, Quot.sound`); in particular `|M₁₁| = 7920` is obtained by the
kernel (`EnumM11.M11_card_clean`) rather than by `native_decide`.

(An earlier alternative, `native_decide`-based proof by the classical **class equation** on the
verified integer encoding of `M₁₁` — formerly in `EnumM11Simple.lean` / `EnumM11Classes.lean` —
has been removed, since the structural route above is `native_decide`-free.)

## Historical note

An earlier session reduced `M11_isSimpleGroup` to an *Iwasawa structure for the action of
`M₁₁` on its `11` points*, i.e. a term of type `IwasawaStructure (↥M11) (Fin 11)`.  **No such
term exists** (the natural action is primitive, so the point stabiliser `M₁₀` is maximal and
almost simple, leaving no nontrivial abelian normal subgroup to serve as the Iwasawa data), so
that decomposition could never be completed.  Both routes above sidestep the Iwasawa machinery
on the `11`-point action entirely (the clean route instead uses an Iwasawa structure for
`PSL(2, 𝔽₁₁)` on the projective line `ℙ¹(𝔽₁₁)`).
-/

namespace Mathieu

open MulAction

/-- **`M₁₁` is a simple group.**  Proved `native_decide`-free via the index-`12` maximal
core-free simple subgroup `H ≅ PSL(2, 𝔽₁₁)`; see `M11SimpleClean.lean`. -/
theorem M11_isSimpleGroup : IsSimpleGroup M11 := M11Clean.M11_isSimpleGroup_clean

end Mathieu
