import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyBinder
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyCaptures

/-! Full native family-plan interpretation. Every binder keeps its actual
original rich frame; terminal captures use that frame's concrete lookups.
No legacy source-domain theorem or semantic callback is required. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail InductiveSignature
open private eta_spine from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

private theorem prefixRealizedEqual
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (signature : ConstantTelescope declaredType)
    (constant : env.HasType U [] (.const name levels) declaredType)
    {count : Nat} (bound : count ≤ signature.domains.length)
    (arguments : Ctx.SubstEq env U target σ τ (signature.domains.take count).reverse) :
    env.IsDefEq U target (mkApps (.const name levels) (realizedCaptures count σ))
      (mkApps (.const name levels) (realizedCaptures count τ))
      ((wrapForalls (signature.domains.drop count) signature.result).subst σ) := by
  have declared : env.HasType U [] (.const name levels)
      (wrapForalls (signature.domains.take count)
        (wrapForalls (signature.domains.drop count) signature.result)) := by
    rw [← wrapForalls_append, List.take_append_drop, ← signature.type_eq]
    exact constant
  obtain ⟨context, opened⟩ := HasType.native_open henv (by trivial) declared
  have taken : (signature.domains.take count).length = count := by
    simp only [List.length_take, Nat.min_eq_left bound]
  simp only [List.append_nil, eta_spine, liftN, taken] at context opened
  have raw := opened.substDF henv context formed arguments
  simpa only [subst_mkApps, subst_const, realizedCaptures, constantCaptureVariables, vars, Nat.zero_add] using raw

theorem RichFamilyPlan.supported
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldAssigned}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {signature : ConstantTelescope declaredType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (constant : env.HasType U [] (.const name levels) declaredType)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    {target arguments headerSource} {context : ContextDerivation headerEnv U headerSource}
    {σ τ : Subst} {demand support : Profile n} {footprint available}
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments demand footprint)
    (formed : OnCtx target (env.IsType U)) (bound : arguments.length ≤ signature.domains.length)
    (sourceEq : headerSource = (signature.domains.take arguments.length).reverse)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context (List.range arguments.length) σ τ available)
    (resources : footprint.Available available) (typed : demand.HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) support) :
    Related env U registry target (mkApps (.const name levels) (realizedCaptures arguments.length σ))
      (mkApps (.const name levels) (realizedCaptures arguments.length τ))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) demand support := by
  match n, demand, footprint, plan with
  | _ + 1, _, _, .terminal saturated resultSort relevance captures =>
    have fields := captures.interpretRichFrame henv hscoped formed frame substitutions resources
    have raw := prefixRealizedEqual henv formed signature constant bound (sourceEq ▸ substitutions)
    rw [saturated, List.drop_length, resultSort] at raw code ⊢
    simp only [wrapForalls] at raw code ⊢
    exact Related.family henv hscoped typed code
      (RankedData.literalFamilyCode henv hscoped notDefinition notNative notQuotient raw relevance (by simpa only [realizedCaptures, saturated] using fields))
  | _ + 1, _, _, .binder origin original location lineage domainCode guard body pack covered =>
    apply RichFamilyPlanSupported.binder henv hscoped headerBelow
      (fun child formed bound sourceEq closed substitutions frame resources typed code =>
        child.supported henv hscoped headerBelow constant notDefinition notNative notQuotient
          formed bound sourceEq closed substitutions frame resources typed code)
      origin original location lineage domainCode guard body pack covered formed sourceEq closed
      substitutions frame resources typed code
  | _, _, _, .view child change =>
    have inverse := change.inverse henv
    have before := child.supported henv hscoped headerBelow constant notDefinition notNative notQuotient
      formed bound sourceEq closed substitutions frame resources
      (inverse.mapType_typed typed) (inverse.codeMap henv hscoped code)
    exact (change.termMap henv hscoped formed before).retag henv typed code
  | _ + 1, _, _, .pad child =>
    have before := child.supported henv hscoped headerBelow constant notDefinition notNative notQuotient
      formed bound sourceEq closed substitutions frame resources typed.pad_inv (code.down henv)
    exact (before.pad henv).retag henv typed code
termination_by (n, sizeOf plan)
decreasing_by all_goals simp_wf; omega

/-- At the closed source header, the computed captured applications are
literally the bare constant. Only the actual header code is supplied. -/
theorem RichFamilyPlan.bareSupported
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (constant : env.HasType U [] (.const name levels) declaredType)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (typeClosed : declaredType.Closed) (formed : OnCtx target (env.IsType U))
    (plan : RichFamilyPlan env U registry target header name levels signature .nil σ [] demand [])
    (typed : demand.HasType support)
    (code : TypeRelated env U registry target declaredType declaredType support) :
    Related env U registry target (.const name levels) (.const name levels) declaredType demand support := by
  have residual : (wrapForalls (signature.domains.drop 0) signature.result).subst σ = declaredType := by
    rw [List.drop_zero, ← signature.type_eq]
    exact typeClosed.subst_eq .zero
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  have result := plan.supported (field := header) (major := header) henv hscoped headerBelow
    constant notDefinition notNative notQuotient formed (Nat.zero_le _) rfl emptyClosed
    (τ := σ) .nil (.captured .nil) (by intro _ _ member; cases member) typed
    (by simpa only [List.length_nil, residual] using code)
  simpa only [realizedCaptures, constantCaptureVariables, List.length_nil, List.range_zero,
    List.reverse_nil, List.map_nil, mkApps, List.foldl_nil, residual] using result

/-- The native family leaf calls precisely the stored earlier header, with
the actual closed source query. Its declaration decrease is supplied by the
real installation origin, independently of that query's size or rank. -/
theorem RichFamilyPlan.fromOriginalHeader
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceOrdered : sourceEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelCount : levels.length = info.uvars)
    (typeClosed : info.type.Closed) (formed : OnCtx target (env.IsType U))
    (certificate : RichCert origin.source env U registry target
      (.ref (origin.familyHeader levelsWF).reference) [] typeRealization true support [])
    (typed : demand.HasType support)
    (plan : RichFamilyPlan env U registry target (origin.familyHeader levelsWF).reference
      name levels signature .nil planRealization [] demand [])
    (headerF : origin.ordered.constantCount < sourceOrdered.constantCount →
      RichCert origin.source env U registry target (.ref (origin.familyHeader levelsWF).reference)
        [] typeRealization true support [] →
      Nonempty (RichCodeTransferResult env U registry target
        (.ref (origin.familyHeader levelsWF).reference) (.ref (origin.familyHeader levelsWF).reference)
        [] typeRealization typeRealization (fun _ => []) true support)) :
    Related env U registry target (.const name levels) (.const name levels)
      (info.type.instL levels) demand support := by
  obtain ⟨answer⟩ := headerF (origin.count_lt sourceOrdered) certificate
  have code : TypeRelated env U registry target (info.type.instL levels) (info.type.instL levels) support := by
    simpa only [typeClosed.instL.subst_eq (σ := typeRealization) .zero] using answer.related
  exact plan.bareSupported henv hscoped (origin.sourceBelow.trans sourceBelow)
    (.const lookup levelsWF levelCount) notDefinition notNative notQuotient typeClosed.instL formed typed code

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
