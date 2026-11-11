import LeanWang.CoRE

/-!
# Computability terminology in the main statements

We use Mathlib's `Computable`, `ComputablePred`, `REPred`, and `ManyOneReducible`,
and the co-r.e. definitions from `LeanWang.CoRE`. All refer to the declared
`Primcodable` encodings of the finite input data, not to arbitrary encodings.

* `Computable f`: a total recursive map on the encoded inputs.
* `ComputablePred p`: a total algorithm decides `p` (both yes and no answers).
* `REPred p`: a partial recursive algorithm halts exactly on inputs satisfying `p`.
* `CoREPred p`: `REPred (fun a => ¬ p a)`; noninstances can be enumerated.
* `CoREHard p`: every co-r.e. predicate computably many-one reduces to `p`.

The following checked expansions make the quantifiers explicit. The foundational
notions of recursive functions and encodings remain those of Mathlib.
-/

namespace Tiling.MainResults

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- A many-one reduction is a single total computable map preserving both answers. -/
theorem manyOneReducible_definition (p : α → Prop) (q : β → Prop) :
    ManyOneReducible p q ↔ ∃ f : α → β, Computable f ∧ ∀ a, p a ↔ q (f a) := Iff.rfl

/-- Co-r.e. membership is recursive enumerability of the complement. -/
theorem coREPred_definition (p : α → Prop) :
    LeanWang.CoREPred p ↔ REPred (fun a => ¬ p a) := Iff.rfl

/-- Hardness quantifies over all co-r.e. predicates on effectively encoded types. -/
theorem coREHard_definition (q : β → Prop) :
    LeanWang.CoREHard q ↔
      ∀ {γ : Type} [Primcodable γ] (p : γ → Prop),
        LeanWang.CoREPred p → ManyOneReducible p q := Iff.rfl

end Tiling.MainResults
