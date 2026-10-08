import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.PatShape
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Inductive.CaseRegistration
import Batteries.Tactic.OpenPrivate

/-! Coverage: every computation rule of a well-formed environment, and every
generic case equation of a registered eliminator schema, has the pattern shape.

The origin of an installed rule is recomputed here by induction on the
declaration history (`VEnv.WF'.defeq_origin`) rather than taken from
`WF'.nativeRegistry`, whose module transitively imports `ChurchRosser` and
`HeadInversion`. -/

namespace Lean4Lean
open InductiveSignature

/-- The restoration table of a finite compilation specializes exactly the
common parameters. -/
theorem InductiveSignature.CompilationData.restoration_nparams {s : InductiveSignature}
    {g : Instance s} (H : CompilationData env source expanded s g auxiliaries block) :
    ∀ head ∈ (compilationRestoration source auxiliaries).heads,
      head.nparams = s.params.length := by
  intro head hhead
  obtain ⟨a, _, hhead⟩ := List.mem_flatMap.mp hhead
  have hn := H.model.nparams.trans H.nparams
  change head ∈ _ :: _ at hhead
  rcases List.mem_cons.mp hhead with rfl | hhead
  · exact hn.symm
  · obtain ⟨ctor, _, rfl⟩ := List.mem_map.mp hhead
    exact hn.symm

/-- A restored native recursor equation is never a bare constant. -/
theorem InductiveSignature.CompilationData.equation_not_const {s : InductiveSignature}
    {g : Instance s} (H : CompilationData env source expanded s g auxiliaries block)
    (index : Fin s.constructors.size) {df : VDefEq}
    (he : (compilationRestoration source auxiliaries).equation (g.equation index) = some df) :
    ∀ n ls, df.lhs ≠ .const n ls :=
  (g.equation_patShape_strong index .native
    (fun h hh => Nat.le_of_eq (H.restoration_nparams h hh))
    (fun _ _ heq h hh => by
      cases heq
      exact H.heads_not_recursors _ h hh) he).2

end Lean4Lean
