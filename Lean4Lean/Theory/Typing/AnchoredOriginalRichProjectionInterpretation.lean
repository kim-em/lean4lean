import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalPrefix

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Determinism of the original exposure route identifies the actual
field and major occurrences, rather than comparing their raw assigned types. -/
theorem RichProjectionOrigin.originalQueriesAt
    {assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node)
    (origin : RichProjectionOrigin sourceEnv env U registry target source locals σ name index value)
    (rooted : origin.RootedAt node) :
    Nonempty (RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ
      (Profile.singleton (n := origin.rank + 1) (.record origin.record)) origin.majorFootprint) ∧
    Nonempty (RichCert sourceEnv env U registry target head.field locals σ true origin.support origin.fieldFootprint) ∧
    Nonempty (DomainChain env U registry target origin.request.input origin.request.domain (head.fieldType.subst σ)) := by
  obtain ⟨route⟩ := rooted
  have equal := route.structural_unique (by trivial) head.route (by trivial)
  cases origin with
  | mk assigned' node' sourceHead rank record request nameEq member support majorFootprint fieldFootprint
      majorQuery fieldCode typed alignment atom atomMember =>
    cases sourceHead with
    | mk info' registered' levels' levelsWF' levelCount' parameters' parameterCount' indices' indexCount'
        sourceMajor' fieldType' selected' fieldLevel' fieldWF' field' major' closed' relevance' route' =>
      cases head with
      | mk info registered levels levelsWF levelCount parameters parameterCount indices indexCount
          sourceMajor fieldType selected fieldLevel fieldWF field major closed relevance route =>
        simp only [projectionNatural] at equal
        obtain ⟨_, _, _, infoEq, levelsEq, parametersEq, _, sourceMajorEq, fieldTypeEq,
          _, fieldLevelEq, _, indicesEq, fieldEq, majorEq⟩ :=
          EndpointState.proj.hinj rfl rfl rfl rfl equal.1 equal.2
        cases infoEq
        cases levelsEq
        cases parametersEq
        cases sourceMajorEq
        cases fieldTypeEq
        cases fieldLevelEq
        cases indicesEq
        have sameField := eq_of_heq fieldEq
        have sameMajor := eq_of_heq majorEq
        cases sameField
        cases sameMajor
        exact ⟨⟨majorQuery⟩, ⟨fieldCode⟩, ⟨alignment⟩⟩

noncomputable def RichComputationalValue.singletonOfMem
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available (profile : Profile n))
    (member : atom ∈ profile.atoms) :
    RichComputationalValue sourceEnv env U registry target node locals σ τ available (.singleton atom) :=
  { answer with
    typed := answer.typed.singleton_of_mem member
    related := answer.related.singleton_of_mem member
    rightQuery := answer.rightQuery.restrict (fun a h => by cases List.mem_singleton.mp h; exact member) }

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

/-- Complete paired projection F for all incoming rich query wrappers.
Every leaf is first aligned to the one actual structural projection, then
the finite original conversion route restores its assigned-type channel. -/
theorem HeaderBinderFrame.projectionPrefixComputationalInterpret
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (reference : EndpointRef headerEnv U headerSource (.proj name index value) assigned)
    (head : ProjectionHead (.ref reference))
    (route : DirectPrefixRoute headerEnv U headerSource (.proj name index value) (.ref reference)
      (projectionNatural head))
    (prefixCalls : route.RestoreCalls env registry target hf
      (frame.dependencyEnvironment hf sf initial) locals σ available)
    (majorF : HeaderComputationalInductionAt header field major env registry hf sf initial context
      (.ref (.right head.major))
      (Closure.close ((projectionNatural head).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost)
    (fieldF : HeaderCodeInductionAt header field major env registry hf sf initial context head.field
      (Closure.close ((projectionNatural head).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost)
    {profile : Profile n}
    (query : RichObs headerEnv env U registry target (.ref reference) locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue headerEnv env U registry target (.ref reference)
      locals σ τ available profile) := by
  have each : ∀ atom ∈ profile.atoms,
      Nonempty (RichComputationalValue headerEnv env U registry target (.ref reference)
        locals σ τ available (.singleton atom)) := by
    intro atom member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := query.projectionOrigin member
    obtain ⟨⟨majorQuery⟩, ⟨fieldCode⟩, ⟨alignment⟩⟩ := origin.originalQueriesAt head rooted
    obtain ⟨answer⟩ := frame.projectionComputationalStep head henv hscoped headerBelow hf sf initial
      closed formed substitutions origin.nameEq origin.member majorQuery fieldCode origin.typed alignment
      (fun i need present => resources i need (included present)) majorF fieldF
    obtain ⟨selected⟩ := (answer.singletonOfMem origin.atomMember).outputPath henv hscoped formed path
    exact route.restoreComputational henv hf sf initial frame prefixCalls selected
  suffices collect : ∀ atoms : List (Atom n),
      (∀ atom ∈ atoms, Nonempty (RichComputationalValue headerEnv env U registry target (.ref reference)
        locals σ τ available (.singleton atom))) →
      Nonempty (RichComputationalValue headerEnv env U registry target (.ref reference)
        locals σ τ available (.mk atoms)) from collect profile.atoms each
  intro atoms
  induction atoms with
  | nil => intro _; exact ⟨.empty⟩
  | cons atom rest ih =>
    intro each
    obtain ⟨head⟩ := each atom List.mem_cons_self
    obtain ⟨tail⟩ := ih (fun next member => each next (List.mem_cons_of_mem _ member))
    exact ⟨head.union henv hscoped formed tail⟩

/-- The direct original route is constructed from the reference's actual
exposure; no synthetic Pi-domain conversion eligibility is assumed. -/
theorem projectionDirect
    (reference : EndpointRef sourceEnv U source (.proj name index value) assigned)
    (head : ProjectionHead (.ref reference)) :
    Nonempty (DirectPrefixRoute sourceEnv U source (.proj name index value) (.ref reference)
      (projectionNatural head)) :=
  head.route.direct (fun _ _ equal => by cases equal) trivial

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
