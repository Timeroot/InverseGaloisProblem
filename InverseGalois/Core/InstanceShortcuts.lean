/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Shortcut instances

Two constructions used throughout this development — the field of rational functions and the
integral closure of a ring in an algebra over it — carry algebraic structure that the generic
search finds only after a long detour.  A field of rational functions is a localization, so the
search for its own scalar action unfolds it all the way down to the polynomial ring; an integral
closure is a subalgebra cut out by a membership predicate, so the search for the induced structure
first tries the graded-piece instances, whose heads unify with almost anything.  Either detour
wanders through the graded-monoid and normed hierarchies before coming back with the obvious
answer.

The instances below name those obvious answers directly.  Each is `inferInstance`, hence
definitionally the very term the long search produces, so nothing about the resulting algebraic
structure changes — only how quickly it is found.  The ones guarding against the graded-piece
detour are given a high priority, since otherwise they are reached only after it.

## Main declarations

* `RatFunc.smulSelf` — the self-action of a field of rational functions.
* `RatFunc.algebraSelf` — the self-algebra structure of a field of rational functions.
* `integralClosure.smulShortcut` — the base action on an integral closure.
* `integralClosure.moduleShortcut` — the base module structure on an integral closure.
* `integralClosure.algebraShortcut` — the base algebra structure on an integral closure.
-/

noncomputable section

namespace RatFunc

variable (K : Type*) [CommRing K] [IsDomain K]

/-- The self-action of a field of rational functions, named to short-circuit the generic
localization search. -/
noncomputable instance smulSelf : SMul (RatFunc K) (RatFunc K) := inferInstance

/-- The self-algebra structure of a field of rational functions, named to short-circuit the
generic localization search. -/
noncomputable instance algebraSelf : Algebra (RatFunc K) (RatFunc K) := inferInstance

end RatFunc

namespace integralClosure

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The base action on an integral closure, named to short-circuit the graded-piece search. -/
instance (priority := high) smulShortcut : SMul R ↥(integralClosure R A) := inferInstance

/-- The base module structure on an integral closure, named to short-circuit the graded-piece
search. -/
instance (priority := high) moduleShortcut : Module R ↥(integralClosure R A) := inferInstance

/-- The base algebra structure on an integral closure, named to short-circuit the graded-piece
search. -/
instance (priority := high) algebraShortcut : Algebra R ↥(integralClosure R A) := inferInstance

end integralClosure
