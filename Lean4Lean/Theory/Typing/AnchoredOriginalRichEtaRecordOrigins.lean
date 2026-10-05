import Lean4Lean.Theory.Typing.AnchoredOriginalStagedProjectionOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordOrigins

/-! The original structure-eta premise supplies each primitive field guard.
Its raw equality transports the guarded projection to the literal expanded
constructor; the retained field alignment fixes the exact frozen domain. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalFactorCut
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Guard production uses only the strictly smaller original assigned-type
comparison already charged by `etaProjectionOriginStaged`. Transport to the
expanded constructor uses the raw original eta derivation, including when
the requested input is empty. -/
theorem etaConstructorProjectionOriginStaged
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {info : VProjectionInfo}
    {parameters : List VExpr} {levels : List VLevel} {expression : VExpr}
    (registered : sourceEnv.projections name info)
    (parameterCount : parameters.length = info.nparams) (noIndices : info.nindices = 0)
    (major : Derivation sourceEnv U source expression expression
      (mkApps (.const name levels) parameters))
    (constructor : Derivation sourceEnv U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => VExpr.proj name j expression))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => VExpr.proj name j expression))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (ambient : frame.Ambient) (sources : frame.AllSources (SourceAtStage stage))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (bank : StagedOriginalLowerCallBank env U registry stage
      (richSchedule .fundamental (Closure.close
        ((Derivation.structEta registered parameterCount noIndices major constructor).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost))
    {input : Profile n} {domain : VExpr}
    (alignment : DomainChain env U registry target input domain
      ((etaProjectionArgument constructor index bound).type.subst σ)) :
    Nonempty (RankedData.ProjectionOrigin env U target info name index
      (mkApps (.const info.ctorName levels)
        ((parameters ++ (List.range info.numFields).map fun j => VExpr.proj name j expression).map
          (fun value : VExpr => value.subst σ)))
      ((mkApps (.const name levels) parameters).subst σ) domain) := by
  obtain ⟨origin⟩ := etaProjectionOriginStaged registered parameterCount noIndices major constructor
    index bound henv ordered below context frame ambient sources closed formed substitutions bank
  have pair := ((Derivation.structEta registered parameterCount noIndices major constructor).forget.defeq.mono
    below).substDF henv substitutions.wf formed substitutions
  let moved := origin.replaceMajor pair.symm
  have final : RankedData.ProjectionOrigin env U target info name index
      ((mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map fun j => VExpr.proj name j expression)).subst σ)
      ((mkApps (.const name levels) parameters).subst σ) domain :=
    { moved with fieldPath := moved.fieldPath.trans alignment.path.symm }
  exact ⟨by simpa only [subst_mkApps, subst_const] using final⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
