import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze
import Lean4Lean.Theory.Typing.AnchoredOriginalRichNativeDepthFuture

/-! Resource freezing and request adaptation preserve the unfolding depth of
the actual returned observation. These equalities hold for every control on
the same witness; they do not select a new reply for each declaration budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

@[simp] theorem RichGradedResult.nativeDepth_availableMono (current : Name → Bool)
    {next : Valuation}
    (query : RichGradedResult sourceEnv env U registry target node locals σ available requested)
    (included : ∀ index need, need ∈ available index → need ∈ next index) :
    (query.availableMono included).observation.nativeDepth current =
      query.observation.nativeDepth current := rfl

@[simp] theorem RichGradedResult.nativeDepth_adaptRequest (current : Name → Bool)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (query : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile k))
    (bound : n ≤ k)
    (adapter : GeneralNormalProfileAdapter env U registry target input (raiseProfile k bound (next : Profile n))) :
    (query.adaptRequest henv hscoped formed bound adapter).observation.nativeDepth current =
      query.observation.nativeDepth current := rfl

/-- The locals and realization casts used when freezing a reply change no
retained source query. The available table is proof-only for this operation. -/
@[simp] theorem RichGradedResult.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {ls ms : List Nat} {available next : Valuation}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (resources : available = next)
    (equal : RichGradedResult sourceEnv env U registry target node ls σ available p =
      RichGradedResult sourceEnv env U registry target node ms τ next q)
    (query : RichGradedResult sourceEnv env U registry target node ls σ available p) :
    (equal.mp query).observation.nativeDepth current = query.observation.nativeDepth current := by
  cases locals
  cases realization
  cases profile
  cases resources
  cases equal
  rfl

@[simp] theorem RichGradedResult.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {ls ms : List Nat} {available next : Valuation}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (resources : available = next)
    (equal : RichGradedResult sourceEnv env U registry target node ms τ next q =
      RichGradedResult sourceEnv env U registry target node ls σ available p)
    (query : RichGradedResult sourceEnv env U registry target node ls σ available p) :
    (equal.mpr query).observation.nativeDepth current = query.observation.nativeDepth current := by
  cases locals
  cases realization
  cases profile
  cases resources
  cases equal
  rfl

@[simp] theorem BoundedGeneratedQueryReply.nativeDepth_mapQuery (current : Name → Bool)
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity)
    (query : RichGradedResult display.sourceEnv env U registry target display.node reply.answer.reply.locals
      (display.raw.comp commonLeft) reply.answer.reply.available next) :
    (reply.mapQuery query).answer.reply.query.observation.nativeDepth current =
      query.observation.nativeDepth current := rfl

/-- Freezing uses precisely the selected observation, including its native
definition children, under the fixed base's resource table. -/
@[simp] theorem CappedGeneratedQueryReply.nativeDepth_freezeBase (current : Name → Bool)
    {base : OriginalCaptureBase env U registry target}
    {node : EndpointState base.sourceEnv U base.source expression assigned}
    {provenance : EndpointProvenance base.context node}
    (reply : CappedGeneratedQueryReply base base.initialCaps
      (OriginalNestedDisplay.identity base node provenance) base.left base.right requested) :
    reply.freezeBase.observation.nativeDepth current =
      reply.reply.query.observation.nativeDepth current := by
  unfold CappedGeneratedQueryReply.freezeBase
  rw [RichGradedResult.nativeDepth_mp current reply.reply.locals_eq rfl rfl rfl]
  rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
