import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramTrace
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstOrigin

/-! Every enclosing retained demand supplies a genuine constant occurrence
in its own original source. Universe changes and skipped binders preserve
that occurrence; no lookup is transported between different source worlds. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private listLevelsTrans from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandHead
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedConstantPath (name : Name) (levels : List VLevel) : VExpr → Type where
  | here : RetainedConstantPath name levels (.const name levels)
  | function (child : RetainedConstantPath name levels f) : RetainedConstantPath name levels (.app f a)
  | domain (child : RetainedConstantPath name levels A) : RetainedConstantPath name levels (.forallE A B)
  | body (child : RetainedConstantPath name levels B) : RetainedConstantPath name levels (.forallE A B)

/-- If reverse execution reaches the original two-variable application
without crossing a charge, its retained constant is already at the literal
caller universe instance. No fresh equality call is needed. -/
theorem RetainedConstantPath.twoVariableLevels
    (path : RetainedConstantPath name sourceLevels
      (.app (.app (.const name levels) (.bvar firstIndex)) (.bvar secondIndex))) :
    sourceLevels = levels := by
  cases path with
  | function first =>
    cases first with
    | function head => cases head; rfl

noncomputable def RetainedConstantPath.lift
    (path : RetainedConstantPath name levels expression) (ρ : Lift) :
    RetainedConstantPath name levels (expression.lift' ρ) := by
  induction path generalizing ρ with
  | here => exact .here
  | function child ih => exact .function (ih ρ)
  | domain child ih => exact .domain (ih ρ)
  | body child ih => exact .body (ih ρ.cons)

theorem RetainedConstantPath.levelsLeft
    (path : RetainedConstantPath name levels expression)
    (equal : EqUpToLevels U other expression) :
    ∃ originalLevels, Nonempty (RetainedConstantPath name originalLevels other) ∧
      List.Forall₂ (· ≈ ·) originalLevels levels := by
  induction path generalizing other with
  | here =>
    cases equal with
    | const _ _ same => exact ⟨_, ⟨.here⟩, same⟩
  | function child ih =>
    cases equal with
    | app function argument =>
      obtain ⟨levels, ⟨next⟩, same⟩ := ih function
      exact ⟨levels, ⟨.function next⟩, same⟩
  | domain child ih =>
    cases equal with
    | forallE domain body =>
      obtain ⟨levels, ⟨next⟩, same⟩ := ih domain
      exact ⟨levels, ⟨.domain next⟩, same⟩
  | body child ih =>
    cases equal with
    | forallE domain body =>
      obtain ⟨levels, ⟨next⟩, same⟩ := ih body
      exact ⟨levels, ⟨.body next⟩, same⟩

theorem RetainedApplicationDemand.constantPath
    {name : Name} {levels : List VLevel}
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (goalPath : RetainedConstantPath name levels goalFunction) :
    ∃ originalLevels, Nonempty (RetainedConstantPath name originalLevels expression) ∧
      List.Forall₂ (· ≈ ·) originalLevels levels := by
  induction demand with
  | application => exact ⟨levels, ⟨.function goalPath⟩, Lean4Lean.List.Forall₂.rfl fun _ _ => rfl⟩
  | output _ _ ih => exact ih
  | domain _ _ ih =>
    obtain ⟨levels, ⟨path⟩, same⟩ := ih
    exact ⟨levels, ⟨.domain path⟩, same⟩
  | body _ _ _ _ _ ih =>
    obtain ⟨levels, ⟨path⟩, same⟩ := ih
    exact ⟨levels, ⟨.body path⟩, same⟩
  | levels equal _ ih =>
    obtain ⟨levels, ⟨path⟩, same⟩ := ih
    obtain ⟨previous, next, previousEq⟩ := path.levelsLeft equal
    exact ⟨previous, next, listLevelsTrans previousEq same⟩
  | rename ρ _ ih =>
    obtain ⟨levels, ⟨path⟩, same⟩ := ih
    exact ⟨levels, ⟨path.lift ρ⟩, same⟩

/-- Original Pi/application prefixes expose real original subterms, including
through conversions. This is syntactic descent and uses no inversion bank. -/
theorem RetainedConstantPath.original
    (path : RetainedConstantPath name levels expression)
    (node : EndpointState sourceEnv U source expression assigned) :
    ∃ constantSource constantAssigned,
      Nonempty (EndpointState sourceEnv U constantSource (.const name levels) constantAssigned) := by
  induction path generalizing source assigned with
  | here => exact ⟨source, assigned, ⟨node⟩⟩
  | function child ih =>
    obtain ⟨type, head, route, normal⟩ := prefixHead node
    cases head with
    | ref reference => exact (reference.primitive_atomic normal).elim
    | convert plan term => exact normal.elim
    | app hu hv domain body function argument result => exact ih function
  | domain child ih =>
    obtain ⟨type, head, route, normal⟩ := prefixHead node
    cases head with
    | ref reference => exact (reference.primitive_atomic normal).elim
    | convert plan term => exact normal.elim
    | pi hu hv domain body => exact ih domain
  | body child ih =>
    obtain ⟨type, head, route, normal⟩ := prefixHead node
    cases head with
    | ref reference => exact (reference.primitive_atomic normal).elim
    | convert plan term => exact normal.elim
    | pi hu hv domain body => exact ih body

theorem RetainedProgramState.constantSite
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (goalPath : RetainedConstantPath name levels goalFunction) :
    ∃ originalLevels assigned,
      Nonempty (ClosedPrimitiveConstant state.sourceEnv U name originalLevels assigned) ∧
      List.Forall₂ (· ≈ ·) originalLevels levels := by
  obtain ⟨originalLevels, ⟨path⟩, same⟩ := state.demand.constantPath goalPath
  obtain ⟨source, assigned, ⟨node⟩⟩ := path.original state.node
  let primitive := constantPrefix node
  exact ⟨originalLevels, primitive.type,
    EndpointRef.closedPrimitiveConstant primitive.reference rfl primitive.primitive, same⟩

/-- The requested universe instance is reified in this SAME source using
the source's own closed constant. Its well-formed levels come from the caller
constant, not from a transported source lookup. -/
theorem RetainedProgramState.constantSiteAtGoalLevels
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (goalPath : RetainedConstantPath name levels goalFunction)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    ∃ assigned, Nonempty (EndpointRef state.sourceEnv U [] (.const name levels) assigned) := by
  obtain ⟨sourceLevels, assigned, ⟨constant⟩, same⟩ := state.constantSite goalPath
  have equal : EqUpToLevels U (.const name sourceLevels) (.const name levels) :=
    .const constant.levelsWF levelsWF same
  have comparison := (EndpointState.ref constant.site).sound.defeq.eqUpToLevels
    state.controls.ordered (by trivial) equal
  obtain ⟨original⟩ := Derivation.reify (comparison.strong state.controls.ordered (by trivial))
  exact ⟨_, ⟨.right original⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
