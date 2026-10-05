import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetBetaRow
import Lean4Lean.Theory.Typing.AnchoredSortableDepthLambdaTrace
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBetaApplication

/-! Every function-query wrapper selects a real bounded lambda row. The
same caller controls survive output actions and grade restoration. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
private def lowerRaised {p : Profile n} (h : n ≤ N)
    (result : HereditaryBudgeted.Result budgets env U registry Γ locals σ τ available l r A
      (raiseProfile N h p)) :
    HereditaryBudgeted.Result budgets env U registry Γ locals σ τ available l r A p :=
  { result with
    bound := Nat.le_trans h result.bound
    adapter := by simpa only [raiseProfile_trans] using result.adapter
    typed := by simpa only [raiseProfile_trans] using result.typed
    related := by simpa only [raiseProfile_trans] using result.related }

private theorem unnormalizeAdmission
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {key : Key n} (admitted : Admitted env U registry Γ (AdapterNormal.key key) x y) :
    Admitted env U registry Γ key x y := by
  have view := (AdapterNormal.profileView (U := U) (registry := registry)
    (Γ := Γ) henv key.input).inverse henv
  exact view.admissionMapWith (key := AdapterNormal.key key) hΓ
    (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
    (fun hΓ {_ _} v {_ _ _ _} ht h => v.termMap henv hscoped hΓ ht h) admitted

theorem SortableObs.betaAppBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    {functionFootprint argumentFootprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (originalArgument : HereditaryBudgeted.StateFundamentalAt budgets env registry context argumentRef)
    (originalBody : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (originalCodomain : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : HereditaryBudgeted.StateFundamentalAt budgets env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (function : SortableObs env U registry target locals σ (.lam A body)
      (Profile.fn key output) functionFootprint)
    (argumentObservation : SortableObs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (functionBound : HereditaryBudgeted.Within budgets function.nativeDepth)
    (argumentBound : HereditaryBudgeted.Within budgets argumentObservation.nativeDepth)
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨origin, ⟨path⟩, footprint, originDepth⟩ := function.lambda_factorFunction_allDepth (.fn key output) rfl True.intro
  let M := path.height
  have ho : origin.rank ≤ M := Nat.le_trans (Nat.le_succ _) path.bounds.1
  have hn : n ≤ M := Nat.le_trans (Nat.le_succ _) path.bounds.2
  let oldKey := raiseKey M ho origin.key
  let newKey := raiseKey M hn key
  let oldOut := raiseAtom M ho origin.output
  let newOut := raiseAtom M hn output
  have actions : AtomAction env U registry target (n := M + 1)
      (.fn oldKey oldOut) (.fn newKey newOut) :=
    .comp (.view ((functionGradeView ho origin.key origin.output).inverse henv))
      (.comp (path.normalize (M + 1) (Nat.le_succ _)) (.view (functionGradeView hn key output)))
  obtain ⟨sk, so, eq, ⟨keys⟩, ⟨outputAction⟩⟩ := actions.normal_fn_inv henv hscoped hTarget rfl
  obtain ⟨rfl, rfl⟩ := AtomData.fn.inj eq
  have oldGuard := origin.node.guard.raise henv ho
  have normalAdmission := keys.pull henv hscoped hTarget
    (AdapterNormal.normalizeAdmission henv hscoped hTarget oldGuard.anchor)
    (AdapterNormal.normalizeAdmission henv hscoped hTarget (Admitted.raise henv hn admitted))
  have oldAdmission := unnormalizeAdmission henv hscoped hTarget normalAdmission
  have raisedArgs := GeneralNormalProfileAdapter.raise henv hscoped hTarget hn argumentAdapter
  have arguments : GeneralNormalProfileAdapter env U registry target
      (raiseProfile M hn rawInput) oldKey.input :=
    GeneralProfileAdapter.comp raisedArgs keys.arguments.toGeneral
  let bodyObs : SortableObs env U registry target (Locals.push locals) (σ.cons oldKey.anchor) body
      (.singleton oldOut) origin.node.bodyFootprint :=
    cast (congrArg (fun p : Profile M => SortableObs env U registry target (Locals.push locals)
      (σ.cons oldKey.anchor) body p origin.node.bodyFootprint)
      (raiseProfile_singleton ho origin.output)) (origin.node.bodyObservation.raise ho)
  have bodyDepth (current : Name → Bool) : bodyObs.nativeDepth current = origin.node.bodyObservation.nativeDepth current :=
    (SortableObs.nativeDepth_cast current (raiseProfile_singleton ho origin.output) _ _).trans
      (origin.node.bodyObservation.nativeDepth_raise current ho)
  have domainAvailable : origin.node.domainFootprint.Available available :=
    fun i need hm => functionAvailable i need (footprint (List.mem_append_left _ hm))
  have outsideAvailable : origin.node.outside.Available available :=
    fun i need hm => functionAvailable i need (footprint (List.mem_append_right _ hm))
  obtain ⟨result⟩ := SortableObs.betaRowBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument
    originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
    closed hTarget substitutions fits frameBound (origin.node.domain.raise ho) oldGuard bodyObs
    (origin.node.pack.raise ho) (raiseProfile_subset ho origin.node.covered)
    (argumentObservation.raise hn) arguments oldAdmission
    (by intro current fuel member; simpa only [SortableCert.nativeDepth_raise] using
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (originDepth current) (functionBound current fuel member)))
    (by intro current fuel member; change bodyObs.nativeDepth current ≤ fuel; rw [bodyDepth current]; exact
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (originDepth current) (functionBound current fuel member)))
    (by intro current fuel member; simpa only [SortableObs.nativeDepth_raise] using argumentBound current fuel member)
    domainAvailable outsideAvailable argumentAvailable
  have finish : AtomAction env U registry target oldOut newOut :=
    .comp (.view (AdapterNormal.view henv oldOut))
      (.comp outputAction (.view ((AdapterNormal.view henv newOut).inverse henv)))
  obtain ⟨result⟩ := result.action henv hscoped hTarget closed finish
  have result : HereditaryBudgeted.Result budgets env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument)
      (raiseProfile M hn (.singleton output)) := by
    simpa only [raiseProfile_singleton] using result
  exact ⟨lowerRaised hn result⟩

end Lean4Lean.AnchoredSource.Adapted
