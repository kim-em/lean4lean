import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionInterpretation

/-! Full paired projection F at arbitrary original source frames. All child
costs and original-prefix calls use the same computed generic environment;
no closed declaration header or synthetic header location is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichFrame.projectionComputationalStep
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node)
    (location : Located root (projectionNatural head))
    (lineage : location.contextDerivation initialContext = context)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major))
      locals σ (Profile.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (resources : (majorFootprint ++ fieldFootprint).Available available)
    (majorF : OriginalComputationalInductionAt env registry ordered initialContext
      (.projMajor location)
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (fieldF : OriginalCodeInductionAt env registry ordered initialContext (.projField location)
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost) :
    Nonempty (RichComputationalValue sourceEnv env U registry target (projectionNatural head)
      locals σ τ available request.input) := by
  subst context
  have majorResources := fun i need hm => resources i need (List.mem_append_left _ hm)
  have fieldResources := fun i need hm => resources i need (List.mem_append_right _ hm)
  have majorBound : (Closure.close ((EndpointState.ref (.right head.major)).dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by
    apply original_child_same_environment
    apply Origin.rule_child
    simp [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin]
  have fieldBound : (Closure.close (head.field.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by
    apply original_child_same_environment
    apply Origin.rule_child
    simp
  obtain ⟨majorAnswer⟩ := majorF target locals σ τ available frame majorBound closed formed substitutions
    majorQuery majorResources
  obtain ⟨fieldAnswer⟩ := fieldF target locals σ τ available frame fieldBound closed formed substitutions
    fieldCode fieldResources
  exact RichComputationalValue.projected head henv hscoped sourceBelow formed substitutions nameEq member
    fieldCode fieldResources typed alignment majorAnswer fieldAnswer


theorem OriginalRichFrame.projectionPrefixComputationalInterpret
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (reference : EndpointRef sourceEnv U source (.proj name index value) assigned)
    (head : ProjectionHead (.ref reference))
    (route : DirectPrefixRoute sourceEnv U source (.proj name index value) (.ref reference)
      (projectionNatural head))
    (prefixCalls : route.RestoreCalls env registry target ordered
      (frame.dependencyEnvironment ordered) locals σ available)
    (majorF : OriginalComputationalInductionAt env registry ordered context
      (.projMajor (head.route.locate .here))
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (fieldF : OriginalCodeInductionAt env registry ordered context (.projField (head.route.locate .here))
      (Closure.close ((projectionNatural head).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    {profile : Profile n}
    (query : RichObs sourceEnv env U registry target (.ref reference) locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue sourceEnv env U registry target (.ref reference)
      locals σ τ available profile) := by
  have each : ∀ atom ∈ profile.atoms,
      Nonempty (RichComputationalValue sourceEnv env U registry target (.ref reference)
        locals σ τ available (.singleton atom)) := by
    intro atom member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := query.projectionOrigin member
    obtain ⟨⟨majorQuery⟩, ⟨fieldCode⟩, ⟨alignment⟩⟩ := origin.originalQueriesAt head rooted
    obtain ⟨answer⟩ := frame.projectionComputationalStep context head (head.route.locate .here)
      (by rw [PrefixRoute.locate_contextDerivation]; rfl) henv hscoped sourceBelow ordered
      closed formed substitutions origin.nameEq origin.member majorQuery fieldCode origin.typed alignment
      (fun i need present => resources i need (included present)) majorF fieldF
    obtain ⟨selected⟩ := (answer.singletonOfMem origin.atomMember).outputPath henv hscoped formed path
    exact route.restoreOriginalComputational henv ordered frame prefixCalls selected
  suffices collect : ∀ atoms : List (Atom n),
      (∀ atom ∈ atoms, Nonempty (RichComputationalValue sourceEnv env U registry target (.ref reference)
        locals σ τ available (.singleton atom))) →
      Nonempty (RichComputationalValue sourceEnv env U registry target (.ref reference)
        locals σ τ available (.mk atoms)) from collect profile.atoms each
  intro atoms
  induction atoms with
  | nil => intro _; exact ⟨.empty⟩
  | cons atom rest ih =>
    intro each
    obtain ⟨head⟩ := each atom List.mem_cons_self
    obtain ⟨tail⟩ := ih (fun next member => each next (List.mem_cons_of_mem _ member))
    exact ⟨head.union henv hscoped formed tail⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
