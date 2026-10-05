import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionParameters
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedLowerCallBank

/-! The installed family result-sort equality is a separate original root.
It is not inferred from uniqueness of the literal family's assigned type. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

private theorem typedPrefixContext
    {env : VEnv} {U : Nat} {source domains : List VExpr}
    {expression assigned result : VExpr}
    (ordered : env.Ordered) (formed : OnCtx source (env.IsType U))
    (typed : env.HasType U source expression assigned)
    (parsed : expression.takeForalls count = some (domains, result)) :
    OnCtx (domains.reverse ++ source) (env.IsType U) ∧
      ∃ resultType, env.HasType U (domains.reverse ++ source) result resultType := by
  induction count generalizing source expression assigned domains with
  | zero =>
    change some ([], expression) = some (domains, result) at parsed
    cases Option.some.inj parsed
    exact ⟨formed, _, typed⟩
  | succ count ih =>
    cases expression <;> simp only [takeForalls] at parsed <;> try contradiction
    case forallE A B =>
      simp only [bind, Option.bind_eq_some_iff] at parsed
      obtain ⟨⟨ds, rest⟩, tail, equal⟩ := parsed
      cases equal
      obtain ⟨domain, level, body⟩ := typed.forallE_inv ordered
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (source := A :: source) ⟨formed, domain⟩ body tail

private theorem contextInstance
    {env : VEnv} {sourceU U : Nat} {source : List VExpr} {levels : List VLevel}
    (context : env.CtxStrong sourceU source)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    env.CtxStrong U (source.map (VExpr.instL levels)) := by
  induction source with
  | nil => trivial
  | cons A source ih =>
    obtain ⟨tail, level, domain⟩ := context
    exact ⟨ih tail, level.inst levels, domain.instL levelsWF⟩

/-- This context is obtained from the actual normalization endpoint by
finite Π inversion, including all original family and index domains. -/
theorem ProjectionParameterShape.resultContext
    {origin : ProjectionParameterOrigin env name info}
    (shape : ProjectionParameterShape origin) :
    OnCtx (shape.indices.reverse ++ shape.familyParams.reverse)
      (origin.base.IsType origin.declaration.uvars) := by
  obtain ⟨familyContext, assigned, familyTyped⟩ := typedPrefixContext origin.baseOrdered
    (by trivial) shape.normalization.hasType.2 shape.familyTake
  simp only [List.append_nil] at familyContext familyTyped
  exact (typedPrefixContext origin.baseOrdered familyContext familyTyped shape.indicesTake).1

structure ProjectionResultSortInstance
    {origin : ProjectionParameterOrigin env name info}
    (shape : ProjectionParameterShape origin) (U : Nat) (levels : List VLevel) where
  context : ContextDerivation origin.base U
    ((shape.indices.reverse ++ shape.familyParams.reverse).map (VExpr.instL levels))
  original : Derivation origin.base U
    ((shape.indices.reverse ++ shape.familyParams.reverse).map (VExpr.instL levels))
    (shape.result.instL levels) (.sort (info.resultLevel.inst levels))
    (.sort (.succ (info.resultLevel.inst levels)))

noncomputable def ProjectionParameterShape.resultSortInstance
    {origin : ProjectionParameterOrigin env name info}
    (shape : ProjectionParameterShape origin)
    (levelsWF : ∀ level ∈ levels, level.WF U) : ProjectionResultSortInstance shape U levels := by
  have context := CtxStrong.strong origin.baseOrdered shape.resultContext
  let originalContext := Classical.choice (ContextDerivation.reify (contextInstance context levelsWF))
  let original := Classical.choice (Derivation.reify
    ((shape.resultSort.strong origin.baseOrdered shape.resultContext).instL levelsWF))
  exact ⟨originalContext, original⟩

def ProjectionResultSortInstance.root
    {origin : ProjectionParameterOrigin env name info}
    {shape : ProjectionParameterShape origin}
    (retained : ProjectionResultSortInstance shape U levels) : ParameterEqualityRoot origin.base U :=
  ⟨_, retained.context, _, _, _, retained.original⟩

/-- Its declaration stage is strictly earlier than the registered projection,
independently of the instantiated equality's proof size. -/
theorem ProjectionResultSortInstance.stage_lt
    {origin : ProjectionParameterOrigin env name info}
    {shape : ProjectionParameterShape origin}
    (_instance : ProjectionResultSortInstance shape U levels) (ordered : env.Ordered) :
    origin.baseOrdered.constantCount < ordered.constantCount := origin.base_count_lt ordered

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The actual fourth installation root is callable by the staged equality
IH under its own hereditary source-stage frame, without any proof-size bound. -/
theorem ProjectionResultSortInstance.equalityAtBaseStage
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {name : Name} {info : VProjectionInfo}
    {origin : ProjectionParameterOrigin sourceEnv name info}
    {shape : ProjectionParameterShape origin} {levels : List VLevel}
    (retained : ProjectionResultSortInstance shape U levels)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (sourceStage : SourceAtStage stage sourceEnv)
    (forward : Bool) {target : List VExpr} {locals : List Nat}
    {σ : Subst} {available : Valuation}
    (frame : OriginalRichFrame origin.base env U registry target retained.context
      locals σ σ available)
    (ambient : frame.Ambient)
    (sources : frame.AllSources (SourceAtStage origin.baseOrdered.constantCount))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ
      ((shape.indices.reverse ++ shape.familyParams.reverse).map (VExpr.instL levels)))
    {n : Nat} {profile : Profile n} {footprint : Footprint}
    (query : RichObs origin.base env U registry target
      (.ref (originalTypeRouteSide retained.original forward)) locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (OriginalDirectionalEqualityResult retained.original forward env registry target
      locals σ σ available profile) := by
  exact bank.equality origin.baseOrdered.constantCount origin.baseOrdered
    (origin.baseBelow.trans below) retained.context retained.original forward
    target locals σ available frame ambient sources
    (.left _ _ (Nat.lt_of_lt_of_le (origin.base_count_lt ordered) (sourceStage ordered)))
    closed formed substitutions query resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
