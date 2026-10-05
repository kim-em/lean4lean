import Lean4Lean.Theory.Typing.AnchoredProfiles
import Lean4Lean.Theory.Typing.Lemmas

/-! The data eligibility needed at family type supports. This predicate
recurses through padding only; it imposes no policy on hidden function inputs.
Record bounds refer to the actual environment, so no registry completeness
assumption is needed to rule out a field-free family. -/
namespace Lean4Lean.AnchoredProfiles
open VExpr VEnv

/-- A constructor tag distinguishes only families without structure eta;
a record observes a concrete, bounded field with a nonempty value demand. -/
def ValueDataEligible (env : VEnv) : {n : Nat} → Atom n → Prop
  | _ + 1, .ctor data => ∀ info, env.projections data.family.name info → info.nindices ≠ 0
  | _ + 1, .record data => ∃ info, env.projections data.family.name info ∧
      ∃ entry ∈ data.fields, entry.1 < info.numFields ∧ Profile.Nonempty entry.2.input
  | _ + 1, .pad atom => ValueDataEligible env atom
  | _, _ => True

end Lean4Lean.AnchoredProfiles
