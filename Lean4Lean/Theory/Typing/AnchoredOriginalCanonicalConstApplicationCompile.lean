import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstSiteProducer
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiVariableBody

/-! Compile the actual native row body `c #0`. The function query is closed
at its real canonical primitive, while only the variable leaves selected by
the row's binder pack are demanded from the caller argument. The resulting
finite application query interprets as code; it is not a full term-F result
with a dependent assigned-type certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
variable {σ : Subst}

/-- The native application's variable child determines an actual finite
argument program. Only its used leaves are retained; no whole-key demand is
added to the caller's footprint. -/
theorem variableApplicationDemand
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {node : EndpointState sourceEnv U (D :: source) (.bvar 0) A}
    (query : RichObs sourceEnv env U registry target node (Locals.push locals)
      (σ.cons anchor) (rawInput : Profile n) argumentFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput keyInput)
    (pack : BinderPack n packed (functionFootprint ++ argumentFootprint) outside)
    (covered : List.Subset packed.atoms outerInput.atoms)
    (closed : available.AtomClosed) (resources : outside.Available available) :
    Nonempty (VariableBodyDemand env U registry target outerInput keyInput) := by
  let localNeeds := (functionFootprint ++ argumentFootprint).localNeeds
  have supplied := pack.available_atomized_localNeeds resources
  obtain ⟨required, ⟨variableQuery⟩, requiredAvailable⟩ := query.variableQuery
    (Valuation.push_atomized_closed closed localNeeds)
    (fun index need member => supplied index need (List.mem_append_right _ member))
  have leaves : ∀ index need, (index, need) ∈ required → index = 0 ∧
      need ∈ localNeeds ++ localNeeds.flatMap Need.singletons := by
    intro index need member
    have indexEq := variableQuery.variableTrace.indices member
    subst index
    exact ⟨rfl, requiredAvailable 0 need member⟩
  have bounded : ∀ index need, (index, need) ∈ required → need.rank ≤ n := by
    intro index need member
    exact (pack.atomized_localNeeds need (leaves index need member).2).1
  have included : List.Subset (required.atGrade n).atoms outerInput.atoms := by
    intro atom member
    obtain ⟨⟨index, need⟩, selected, belongs⟩ := List.mem_flatMap.mp member
    exact covered ((pack.atomized_localNeeds need (leaves index need selected).2).2 atom belongs)
  let trace := variableQuery.variableTrace
  let N := max n trace.height
  have hn : n ≤ N := Nat.le_max_left _ _
  have ht : trace.height ≤ N := Nat.le_max_right _ _
  refine ⟨⟨required.atGrade n, included, N, hn, ?_⟩⟩
  rw [← Footprint.atGrade_raise hn bounded]
  exact (trace.normalize henv hscoped formed N ht).comp
    (GeneralNormalProfileAdapter.raise henv hscoped formed hn adapter)

/-- Finite compiled row syntax, with the exact constant packet and the
computed variable program. The anchor admission is already present in the
actual native application query. -/
structure CanonicalConstApplicationProgram (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (strata : EquationStratification env)
    (name : Name) (levels : List VLevel) (anchor : VExpr)
    (outerInput : Profile n) (key : Key n) (output : Atom n) (relevant : Bool) where
  functionQuery : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output)
  demand : VariableBodyDemand env U registry target outerInput key.input
  admitted : Admitted env U registry target key anchor anchor
  sorted : (Profile.singleton output).HasType (.sort relevant)

/-- This constructor consumes exactly the child queries, argument adapter,
and binder pack occurring in a native rich Pi row whose body is `c #0`.
Closing the constant uses its own retained constDF child, never a caller R. -/
theorem compileNativeConstApplication
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {function : EndpointState owner.selected.origin.source U (D :: source)
      (.const name levels) (.forallE A B)}
    {argument : EndpointState owner.selected.origin.source U (D :: source) (.bvar 0) A}
    (functionQuery : RichObs owner.selected.origin.source env U registry target function
      (Locals.push locals) (σ.cons anchor) (Profile.fn (key : Key n) output) functionFootprint)
    (argumentQuery : RichObs owner.selected.origin.source env U registry target argument
      (Locals.push locals) (σ.cons anchor) rawInput argumentFootprint)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key anchor anchor)
    (sorted : (Profile.singleton output).HasType (.sort relevant))
    (pack : BinderPack n packed (functionFootprint ++ argumentFootprint) outside)
    (covered : List.Subset packed.atoms outerInput.atoms)
    (closed : available.AtomClosed) (resources : outside.Available available) :
    ∃ program : CanonicalConstApplicationProgram env U registry target strata name levels anchor
        outerInput key output relevant,
      program.functionQuery.ownerName = ownerName ∧ HEq program.functionQuery.owner owner ∧
      ∀ control, program.functionQuery.chargeDepth control =
        headDepth owner.selected.ordinal
          (fun k => functionQuery.stratifiedDepth (strata.headOrdinal registry) k) control := by
  obtain ⟨packet, nameEq, ownerEq, depthEq⟩ := canonicalConstSiteOfQuery owner functionQuery
  obtain ⟨demand⟩ := variableApplicationDemand henv hscoped formed argumentQuery arguments
    pack covered closed resources
  exact ⟨⟨packet, demand, admitted, sorted⟩, nameEq, ownerEq, depthEq⟩

namespace CanonicalConstApplicationProgram

/-- Replay a compiled native row at the actual caller argument. The raw
source-display equality identifies the initial argument with the retained
row anchor; subsequent paired interpretation computes the right admission. -/
noncomputable def atArgument
    (program : CanonicalConstApplicationProgram env U registry target strata name levels anchor
      outerInput key output relevant)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {function : EndpointRef callerEnv U callerSource (.const name levels) (.forallE callerA callerB)}
    {argument : EndpointState callerEnv U callerSource expression callerA}
    (query : RichGradedResult callerEnv env U registry target argument callerLocals callerσ callerAvailable
      program.demand.input)
    (sourceDisplay : expression.subst callerσ = anchor) :
    CanonicalConstApplicationAt callerEnv env U registry target strata function argument callerLocals
      callerσ callerAvailable key output relevant where
  functionQuery := program.functionQuery
  argumentQuery := program.demand.program.replay henv hscoped formed query
  admitted := by simpa only [sourceDisplay] using program.admitted
  sorted := program.sorted

/-- Same returned witness and same external argument charge. The canonical
mask does not enclose the caller-owned argument observation. -/
theorem atArgument_depth
    (program : CanonicalConstApplicationProgram env U registry target strata name levels anchor
      outerInput key output relevant)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {function : EndpointRef callerEnv U callerSource (.const name levels) (.forallE callerA callerB)}
    {argument : EndpointState callerEnv U callerSource expression callerA}
    (query : RichGradedResult callerEnv env U registry target argument callerLocals callerσ callerAvailable
      program.demand.input)
    (sourceDisplay : expression.subst callerσ = anchor) (control : Nat) :
    (program.atArgument (function := function) henv hscoped formed query sourceDisplay).depth control =
      max (program.functionQuery.chargeDepth control)
        (query.observation.stratifiedDepth (strata.headOrdinal registry) control) := by
  change max _ ((program.demand.program.replay henv hscoped formed query).observation.headDepth _) = _
  rw [program.demand.program.replay_headDepth]
  rfl

end CanonicalConstApplicationProgram
end Lean4Lean.AnchoredSource.Adapted
