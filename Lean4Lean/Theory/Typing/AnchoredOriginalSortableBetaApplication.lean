import Lean4Lean.Theory.Typing.AnchoredAtomActionFunction
import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBetaRow
import Lean4Lean.Theory.Typing.AnchoredSortableLambdaTrace

/-! Contract an actual hereditary beta observation after selecting its
retained source lambda node through finite actions and grade changes. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private def lowerRaised {p : Profile n} (h : n ≤ N)
    (result : SortableComputationalTransferResult env U registry Γ locals σ τ available l r A
      (raiseProfile N h p)) :
    SortableComputationalTransferResult env U registry Γ locals σ τ available l r A p :=
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

theorem SortableObs.betaAppOriginal
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
    (originalDomain : EndpointHereditaryFundamental env registry context domainRef)
    (originalArgument : StateHereditaryFundamental env registry context argumentRef)
    (originalBody : StateHereditaryFundamental env registry (.cons context domainRef) bodyRef)
    (originalCodomain : StateHereditaryFundamental env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : StateHereditaryFundamental env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (function : SortableObs env U registry target locals σ (.lam A body)
      (Profile.fn key output) functionFootprint)
    (argumentObservation : SortableObs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨origin, ⟨path⟩, footprint⟩ := function.lambda_factorFunction (.fn key output) rfl True.intro
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
  have bodyObs := origin.node.bodyObservation.raise ho
  rw [raiseProfile_singleton] at bodyObs
  have domainAvailable : origin.node.domainFootprint.Available available :=
    fun i need hm => functionAvailable i need (footprint (List.mem_append_left _ hm))
  have outsideAvailable : origin.node.outside.Available available :=
    fun i need hm => functionAvailable i need (footprint (List.mem_append_right _ hm))
  obtain ⟨result⟩ := SortableObs.betaRowOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument
    originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
    closed hTarget substitutions fits (origin.node.domain.raise ho) oldGuard bodyObs
    (origin.node.pack.raise ho) (raiseProfile_subset ho origin.node.covered)
    (argumentObservation.raise hn) arguments oldAdmission domainAvailable outsideAvailable argumentAvailable
  have finish : AtomAction env U registry target oldOut newOut :=
    .comp (.view (AdapterNormal.view henv oldOut))
      (.comp outputAction (.view ((AdapterNormal.view henv newOut).inverse henv)))
  obtain ⟨result⟩ := result.action henv hscoped hTarget closed finish
  have result : SortableComputationalTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument)
      (raiseProfile M hn (.singleton output)) := by
    simpa only [raiseProfile_singleton] using result
  exact ⟨lowerRaised hn result⟩

end Lean4Lean.AnchoredSource.Adapted
