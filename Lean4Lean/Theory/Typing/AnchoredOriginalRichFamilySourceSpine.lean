import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyConstantOrigin

/-! Parse a family application into its actual retained constant leaf and
original application occurrences. The finite trace has no header transfer
or family-answer premise; the later consumption phase uses only liveness
of the actual argument observations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedRichFamilySpine
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (name : Name) (levels : List VLevel) :
    VExpr → {n : Nat} → Atom n → Footprint → Type where
  | constant (seed : RetainedRichFamilySeed root env registry target name levels)
      (path : GeneralOutputPath env U registry target seed.atom atom) :
      RetainedRichFamilySpine root env registry target locals σ name levels (.const name levels) atom footprint
  | app (origin : RichAppOrigin root env registry target source locals σ f a)
      (function : RetainedRichFamilySpine root env registry target locals σ name levels
        f (n := origin.rank+1) (.fn origin.key origin.output) origin.functionFootprint)
      (path : GeneralOutputPath env U registry target origin.output atom)
      (included : List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint) :
      RetainedRichFamilySpine root env registry target locals σ name levels (.app f a) atom footprint

/-- No query selection or output adapter changes the retained native seed. -/
noncomputable def RetainedRichFamilySpine.seed
    (spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint) :
    RetainedRichFamilySeed root env registry target name levels := by
  cases spine with
  | constant seed _ => exact seed
  | app _ function _ _ => exact function.seed

/-- The only semantic data needed to turn the parsed spine into its consumed
header frame are the finite actual argument queries' liveness. These are
ordinary proper argument F conclusions, not family answers. -/
def RetainedRichFamilySpine.ArgumentsLive
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint) : Prop := by
  cases spine with
  | constant => exact True
  | app origin function _ _ => exact function.ArgumentsLive ∧ Profile.Live env U registry target origin.rawInput

/-- Recover all applications from the actual original query. General code
and output wrappers are already part of each retained origin's path. -/
theorem RichObs.familySourceSpine
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    Nonempty (RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint) := by
  match expression with
  | .const found foundLevels =>
    simp only [getAppFnArgs_const] at head
    cases head
    obtain ⟨seed, ⟨path⟩⟩ := query.familyConstantOrigin henv hscoped formed ordered below
      notDefinition notNative location member ends
    exact ⟨.constant seed path⟩
  | .app f a =>
    obtain ⟨origin, ⟨path⟩, included⟩ := query.applicationOrigin location member
    have outputEnds : FamilyEndDemand origin.output := ends.outputBack henv hscoped formed path
    obtain ⟨function⟩ := origin.function.familySourceSpine henv hscoped formed ordered below
      notDefinition notNative (.appFunction origin.location)
      (by simpa only [getAppFnArgs_app] using head)
      (List.mem_singleton_self _) outputEnds
    exact ⟨.app origin function path included⟩
  | .bvar _ | .sort _ | .lam _ _ | .forallE _ _ | .proj _ _ _ | .elim _ _ _ =>
    simp [getAppFnArgs, getAppFnArgs.go] at head
termination_by sizeOf expression

/-- Consume the parsed applications while retaining the exact constant
packet and the original source query backing every terminal capture. -/
theorem RetainedRichFamilySpine.consume
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint)
    (resources : footprint.Available available) (live : spine.ArgumentsLive) :
    ∃ result : RetainedRichFamilyConsumption root env registry target locals σ available
      name levels expression.getAppFnArgs.2 atom, result.seed = spine.seed := by
  induction spine with
  | constant seed path =>
    exact ⟨seed.initial.outputPath henv hscoped formed path, rfl⟩
  | app origin function path included ih =>
    have all : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
      fun i need member => resources i need (included member)
    obtain ⟨prior, same⟩ := ih
      (fun i need member => all i need (List.mem_append_left _ member)) live.1
    obtain ⟨next, seedEq⟩ := prior.appOrigin henv hscoped below formed origin all live.2 path
    exact ⟨{ seed := next.seed, cursor := by simpa only [getAppFnArgs_app] using next.cursor },
      seedEq.trans same⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
