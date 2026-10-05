import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
import Lean4Lean.Theory.Typing.AnchoredFamilyLiteralArguments
import Lean4Lean.Theory.Typing.AnchoredRecordRequestRetag
import Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
import Lean4Lean.Theory.Typing.AnchoredAtomActionInterpretation

/-! Return a retained projection demand through the actual caller variable
programs. The major F is a proper original child. Its record witness supplies
the complete request admission, including the frozen raw domain and anchor;
finite output actions change only the input/support grades. This does not
assert a new syntactic certificate at the caller's projected field type. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private projectionMajor_cost_lt from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private recordControlled from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- Descend every component of the actual record field admission. Its
anchor and domain are literal lifts of the retained request. -/
theorem Related.retainedRecordAdmission
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (related : Related env U registry target left right assigned
      (Profile.singleton (n := n+1) (.record record)) support)
    (member : (index, request) ∈ record.fields) :
    RankedData.RequestAdmission env U (relations env U registry n) target request
      (.proj record.family.name index left) (.proj record.family.name index right) := by
  obtain ⟨witness⟩ := related.recordRelation henv hscoped formed target .refl (.refl formed)
  have rename : record.rename .refl = record := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  exact (witness.fields.map_member member).mixedBack henv hscoped witness.insertion

/-- Normalize the actual finite output path at its own bounded common
rank. The resulting admission keeps the same domain and anchor, including
when a code action changes the support or the requested grade goes down. -/
theorem RankedData.RequestAdmission.retainedOutput
    {request : DataRequest (Profile n)} {atom : Atom n} {output : Atom m}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) target request left right)
    (selected : atom ∈ request.input.atoms)
    (path : GeneralOutputPath env U registry target atom output) :
    Admitted env U registry target
      (show Key m from ⟨request.domain, request.anchor, Profile.singleton output⟩) left right := by
  let key : Key m := ⟨request.domain, request.anchor, Profile.singleton output⟩
  have source := Admitted.raiseFamily henv path.bounds.1 ((admitted.singleton selected).toAdmission)
  obtain ⟨anchor, pair, oldSupport, typed, supported, code, first, second⟩ := source
  let action := path.normalize path.height (Nat.le_refl _)
  have highTyped : (Profile.singleton (raiseAtom path.height path.bounds.1 atom)).HasType oldSupport := by
    simpa only [raiseKey, raiseProfile_singleton] using typed
  have highFirst : Related env U registry target request.anchor left request.domain
      (Profile.singleton (raiseAtom path.height path.bounds.1 atom)) oldSupport := by
    simpa only [Related, raiseKey, raiseProfile_singleton] using first
  have highSecond : Related env U registry target left right request.domain
      (Profile.singleton (raiseAtom path.height path.bounds.1 atom)) oldSupport := by
    simpa only [Related, raiseKey, raiseProfile_singleton] using second
  have next : Admitted env U registry target (raiseKey path.height path.bounds.2 key) left right := by
    refine ⟨anchor, pair, action.support.apply oldSupport, ?_,
      action.support.preservesSort supported, action.support.codeMap henv hscoped code, ?_, ?_⟩
    · simpa only [key, raiseKey, raiseProfile_singleton] using action.typed highTyped
    · simpa only [Related, key, raiseKey, raiseProfile_singleton] using
        action.termMap henv hscoped formed highTyped highFirst
    · simpa only [Related, key, raiseKey, raiseProfile_singleton] using
        action.termMap henv hscoped formed highTyped highSecond
  exact next.lowerFamily henv path.bounds.2 formed

/-- Execute the actual caller major with a reconstructed record query.
The only call is strictly below the caller's own projection original. -/
theorem ProjectionHead.recordMajorValueWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation callerEnv U callerSource}
    {node : EndpointState callerEnv U callerSource (.proj name fieldIndex major) assigned}
    (head : ProjectionHead node)
    (provenance : EndpointProvenance context node)
    (controls : OriginalWorldControls strata callerEnv)
    (frame : OriginalRichFrame callerEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ callerSource)
    {record : RecordData (Profile n)}
    (query : RichGradedResult callerEnv env U registry target (.ref (.right head.major))
      locals σ available (Profile.singleton (n := n+1) (.record record)))
    (ready : ControlledStoredQuery controls frontier (.observation query.observation))
    (henv : env.Ordered)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured])) :
    ∃ value : RichComputationalValue callerEnv env U registry target (.ref (.right head.major))
        locals σ τ available (Profile.singleton (n := n+1) (.record record)),
      Nonempty (ControlledStoredQuery controls frontier (.certificate value.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation value.rightQuery.observation)) := by
  obtain ⟨footprint, observation, resources, ⟨observed⟩⟩ := recordControlled henv query ready
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.ref (.right head.major)) captured)
      (originalCallWorld controls .fundamental node captured) :=
    original_child (richSchedule_strict (projectionMajor_cost_lt head controls.ordered _) _ _) _ _ _ _ captured.worlds
  have fund : ∀ inherited : List (World strata.rules.length),
      CallBelow strata.rules.length
        (inherited ++ [originalCallWorld controls .fundamental (.ref (.right head.major)) captured])
        (inherited ++ [originalCallWorld controls .fundamental node captured]) := by
    intro inherited
    induction inherited with
    | nil => exact split_call (by intro world member; cases List.mem_singleton.mp member; exact lower)
    | cons world rest ih => exact ih.cons world
  let majorProvenance : EndpointProvenance context (.ref (.right head.major)) := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .projMajor (head.route.locate provenance.location)
    context_eq := by
      change context = (head.route.locate provenance.location).contextDerivation provenance.initial
      rw [PrefixRoute.locate_contextDerivation]
      exact provenance.context_eq }
  exact (bank _ (fund frontier)).computational (.ref (.right head.major)) majorProvenance controls
    frame captured captured frontier (Nat.le_refl _) (Covered.refl _) rfl
    (singletonSponsoredBelow paid lower) data closed formed substitutions observation resources observed

/-- Consume a literal physical terminal and its actual traced caller scope.
The result is a caller query at the original major plus a complete admission
for the requested output atom at the caller's prior projection. No projected
field certificate or comparison answer is an input. -/
theorem RetainedNativeProjectionOrigin.returnVariableDemandWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : RetainedNativeProjectionOrigin root env registry target source sourceLocals sourceσ
      name fieldIndex (.bvar sourceIndex))
    (scope : CallerVariableProgramScope env U registry target
      (fun i need => need ∈ callerAvailable i) sourceAvailable)
    (resources : (origin.majorFootprint ++ origin.fieldFootprint).Available sourceAvailable)
    (sourceClosed : sourceAvailable.AtomClosed)
    (mapped : scope.index sourceIndex = some callerIndex)
    {context : ContextDerivation callerEnv U callerSource}
    {callerAssigned : VExpr}
    {callerNode : EndpointState callerEnv U callerSource (.proj name fieldIndex (.bvar callerIndex)) callerAssigned}
    (callerHead : ProjectionHead callerNode)
    (provenance : EndpointProvenance context callerNode)
    (controls : OriginalWorldControls strata callerEnv)
    (frame : OriginalRichFrame callerEnv env U registry target context callerLocals callerσ callerτ callerAvailable)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : callerAvailable.AtomClosed)
    (substitutions : Ctx.SubstEq env U target callerσ callerτ callerSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental callerNode captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental callerNode captured]))
    {m : Nat} {output : Atom m}
    (path : GeneralOutputPath env U registry target origin.output output) :
    ∃ query : RichGradedResult callerEnv env U registry target (.ref (.right callerHead.major))
        callerLocals callerσ callerAvailable (Profile.singleton (n := origin.rank+1) (.record origin.record)),
    ∃ queryReady : ControlledStoredQuery controls frontier (.observation query.observation),
    ∃ value : RichComputationalValue callerEnv env U registry target (.ref (.right callerHead.major))
        callerLocals callerσ callerτ callerAvailable (Profile.singleton (n := origin.rank+1) (.record origin.record)),
      Nonempty (ControlledStoredQuery controls frontier (.certificate value.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation value.rightQuery.observation)) ∧
      RankedData.RequestAdmission env U (relations env U registry origin.rank) target origin.request
        (.proj name fieldIndex (callerσ callerIndex)) (.proj name fieldIndex (callerτ callerIndex)) ∧
      Admitted env U registry target
        (show Key m from ⟨origin.request.domain, origin.request.anchor, Profile.singleton output⟩)
        (.proj name fieldIndex (callerσ callerIndex)) (.proj name fieldIndex (callerτ callerIndex)) := by
  obtain ⟨query, ⟨queryReady⟩⟩ := origin.rebuildVariableMajorWorld scope resources sourceClosed mapped
    henv hscoped formed controls.ordered frame (.ref (.right callerHead.major)) controls frontier
  obtain ⟨value, certificateReady, valueReady⟩ := ProjectionHead.recordMajorValueWorld callerHead provenance controls
    frame captured frontier data closed formed substitutions query queryReady henv paid bank
  have admitted : RankedData.RequestAdmission env U (relations env U registry origin.rank) target origin.request
      (.proj name fieldIndex (callerσ callerIndex)) (.proj name fieldIndex (callerτ callerIndex)) := by
    simpa only [subst_bvar, origin.nameEq] using
      Related.retainedRecordAdmission henv hscoped formed value.related origin.member
  exact ⟨query, queryReady, value, certificateReady, valueReady, admitted,
    RankedData.RequestAdmission.retainedOutput henv hscoped formed admitted origin.selected path⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
