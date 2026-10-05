import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationFuture
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderPairedApplication

/-! Paired replay of the complete finite application query ledger. The
right source certificate and admission are reconstructed from actual header
slots, including freshly admitted binders. Original query paths are retained. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem RichAppOrigin.headerReplayPaired
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef currentEnv U current fieldExpression fieldType}
    {major : EndpointRef currentEnv U current majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {A B : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (origin : RichAppOrigin root env registry target source ownerLocals σ f a)
    (path : GeneralOutputPath env U registry target origin.output atom)
    (sorted : (Profile.singleton atom).HasType (.sort relevant))
    (tail : HeaderBinderFrame header field major env registry target context locals left right available)
    (substitutions : Ctx.SubstEq env U target left right headerSource)
    (node : EndpointState headerEnv U headerSource (.app (.bvar functionIndex) (.bvar argumentIndex)) assigned)
    (functionNeed : origin.functionNeed ∈ available functionIndex)
    (functionLookup : Lookup headerSource functionIndex (.forallE A B))
    (argumentLookup : Lookup headerSource argumentIndex A)
    (argumentNeed : origin.argumentNeed ∈ available argumentIndex)
    (functionEq : f.subst σ = left functionIndex)
    (argumentEq : a.subst σ = left argumentIndex) :
    ∃ required, Nonempty (RichCert headerEnv env U registry target node locals right
      relevant (.singleton atom) required) ∧ required.Available available ∧
      TypeRelated env U registry target ((VExpr.app f a).subst σ)
        ((VExpr.app (.bvar functionIndex) (.bvar argumentIndex)).subst right) (.singleton atom) := by
  obtain ⟨flag, inputSorted, ⟨action⟩⟩ := GeneralOutputPath.codeAtOutput henv path sorted
  have admitted : Admitted env U registry target origin.key (left argumentIndex) (left argumentIndex) :=
    argumentEq ▸ origin.admitted
  obtain ⟨inputFootprint, ⟨input⟩, inputResources, related⟩ :=
    tail.pairedCapturedApplication henv hscoped formed substitutions node
      origin.key origin.output inputSorted functionNeed functionLookup origin.rawInput
      origin.arguments argumentNeed argumentLookup admitted
  obtain ⟨required, ⟨certificate⟩, resources⟩ := input.codeAction action inputResources
  exact ⟨required, ⟨certificate⟩, resources, by
    simpa only [subst, functionEq, argumentEq] using action.codeMap henv hscoped related⟩

private theorem typeSubset {small large support : Profile n}
    (subset : ∀ atom ∈ small.atoms, atom ∈ large.atoms)
    (typed : large.HasType support) : small.HasType support := by
  cases n with
  | zero => exact fun atom member => typed atom (subset atom member)
  | succ n => exact ⟨fun atom member => typed.1 atom (subset atom member), typed.2.1,
      fun atom member => typed.2.2 atom (subset atom member)⟩

/-- The whole original profile is rebuilt from its finite extracted seeds.
All source output certificates are produced here; only the computed capture
footprint must already be available in the actual header tail. -/
theorem RichApplicationSeeds.headerReplayPaired
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef currentEnv U current fieldExpression fieldType}
    {major : EndpointRef currentEnv U current majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {A B : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (seeds : RichApplicationSeeds root env registry target source ownerLocals σ f a footprint atoms)
    (sorted : (Profile.mk atoms).HasType (.sort relevant))
    (tail : HeaderBinderFrame header field major env registry target context locals left right available)
    (substitutions : Ctx.SubstEq env U target left right headerSource)
    (node : EndpointState headerEnv U headerSource (.app (.bvar functionIndex) (.bvar argumentIndex)) assigned)
    (resources : (seeds.required functionIndex argumentIndex).Available available)
    (functionLookup : Lookup headerSource functionIndex (.forallE A B))
    (argumentLookup : Lookup headerSource argumentIndex A)
    (functionEq : f.subst σ = left functionIndex)
    (argumentEq : a.subst σ = left argumentIndex) :
    ∃ required, Nonempty (RichCert headerEnv env U registry target node locals right
      relevant (.mk atoms) required) ∧ required.Available available ∧
      TypeRelated env U registry target ((VExpr.app f a).subst σ)
        ((VExpr.app (.bvar functionIndex) (.bvar argumentIndex)).subst right) (.mk atoms) := by
  induction seeds with
  | nil =>
    exact ⟨[], ⟨.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant)))⟩,
      (by intro _ _ member; cases member), by
        apply TypeRelated.of_singletons
        intro atom member; cases member⟩
  | cons origin path included rest ih =>
    obtain ⟨headFootprint, ⟨headCode⟩, headResources, headRelated⟩ := origin.headerReplayPaired henv hscoped formed
      path (sorted.singleton_of_mem (List.mem_cons_self)) tail substitutions node
      (resources _ _ (by simp [required])) functionLookup argumentLookup
      (resources _ _ (by simp [required])) functionEq argumentEq
    obtain ⟨tailFootprint, ⟨tailCode⟩, tailResources, tailRelated⟩ := ih
      (typeSubset (fun _ h => List.mem_cons_of_mem _ h) sorted)
      (fun index need member => resources index need (List.mem_append_right _ member))
    refine ⟨headFootprint ++ tailFootprint, ⟨.union headCode tailCode⟩, ?_, ?_⟩
    · intro index need member
      exact (List.mem_append.mp member).elim (headResources index need) (tailResources index need)
    · apply TypeRelated.of_singletons
      intro atom member
      rcases List.mem_cons.mp member with equal | member
      · cases equal; exact headRelated
      · exact tailRelated.singleton member


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
