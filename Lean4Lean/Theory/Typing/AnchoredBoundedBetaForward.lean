import Lean4Lean.Theory.Typing.AnchoredBoundedBeta
import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaTrace
import Lean4Lean.Theory.Typing.AnchoredFunctionViewOutput
import Lean4Lean.Theory.Typing.AnchoredBoundedConversion

/-! Forward beta for every finite observation of the redex. Function views
are replayed through their actual lambda origin and reversible output path. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

private def lowerRaised {p : Profile n} (h : n ≤ N)
    (result : Result current fuel env U registry Γ locals σ τ available l r A
      (raiseProfile N h p)) :
    Result current fuel env U registry Γ locals σ τ available l r A p :=
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

theorem Obs.beta_app
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    {functionFootprint argumentFootprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalArgument : Joint current fuel env U registry source argument argument A)
    (originalBody : Joint current fuel env U registry (A :: source) body body B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : Joint current fuel env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    (function : Obs env U registry target locals σ (.lam A body)
      (Profile.fn key output) functionFootprint)
    (functionBound : function.nativeDepth current ≤ fuel)
    (argumentObservation : Obs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentBound : argumentObservation.nativeDepth current ≤ fuel)
    (argumentAdapter : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨origin, ⟨path⟩, footprint, domainBound, bodyBound⟩ := function.lambda_factor_bounded functionBound (.fn key output) rfl
  let M := path.height
  have ho : origin.rank ≤ M := Nat.le_trans (Nat.le_succ _) path.bounds.1
  have hn : n ≤ M := Nat.le_trans (Nat.le_succ _) path.bounds.2
  let oldKey := raiseKey M ho origin.key
  let newKey := raiseKey M hn key
  let oldOut := raiseAtom M ho origin.output
  let newOut := raiseAtom M hn output
  have views : AtomView env U registry target (n := M + 1)
      (.fn oldKey oldOut) (.fn newKey newOut) :=
    .trans ((functionGradeView ho origin.key origin.output).inverse henv)
      (.trans (path.normalize (M + 1) (Nat.le_succ _)) (functionGradeView hn key output))
  have change := views.toAdapter henv hscoped hTarget
  change AtomAdapter (n := M + 1) env U registry target
    (.fn (AdapterNormal.key oldKey) (AdapterNormal.atom oldOut))
    (.fn (AdapterNormal.key newKey) (AdapterNormal.atom newOut)) at change
  obtain ⟨sk, so, eq, ⟨keys⟩, _⟩ := change.fn_inv
  obtain ⟨rfl, rfl⟩ := AtomData.fn.inj eq
  have oldGuard := origin.node.guard.raise henv ho
  have normalAdmission := keys.pull henv hscoped hTarget
    (AdapterNormal.normalizeAdmission henv hscoped hTarget oldGuard.anchor)
    (AdapterNormal.normalizeAdmission henv hscoped hTarget (Admitted.raise henv hn admitted))
  have oldAdmission := unnormalizeAdmission henv hscoped hTarget normalAdmission
  have raisedArgs := NormalProfileAdapter.raise henv hscoped hTarget hn argumentAdapter
  have arguments : NormalProfileAdapter env U registry target
      (raiseProfile M hn rawInput) oldKey.input :=
    ProfileAdapter.comp raisedArgs keys.arguments
  let bodyObs := origin.node.bodyObservation.raise ho
  have raisedBodyBound : bodyObs.nativeDepth current ≤ fuel := by
    simpa only [bodyObs, Obs.nativeDepth_raise] using bodyBound
  clear_value bodyObs
  generalize originalEq : raiseProfile M ho (.singleton origin.output) = raisedDemand at bodyObs raisedBodyBound
  have eq : raisedDemand = .singleton oldOut := by rw [← originalEq, raiseProfile_singleton]
  clear originalEq
  subst raisedDemand
  have domainAvailable : origin.node.domainFootprint.Available available :=
    fun i need hm => functionAvailable i need (footprint ▸ List.mem_append_left _ hm)
  have outsideAvailable : origin.node.outside.Available available :=
    fun i need hm => functionAvailable i need (footprint ▸ List.mem_append_right _ hm)
  obtain ⟨result⟩ := Obs.beta_row henv hscoped originalDomain originalArgument
    originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
    closed hTarget substitutions fits (origin.node.domain.raise ho)
    (by simpa only [CodeCert.nativeDepth_raise] using domainBound) oldGuard bodyObs raisedBodyBound
    (origin.node.pack.raise ho) (raiseProfile_subset ho origin.node.covered)
    (argumentObservation.raise hn) (by simpa only [Obs.nativeDepth_raise] using argumentBound) arguments oldAdmission domainAvailable outsideAvailable argumentAvailable
  obtain ⟨outputView⟩ := views.normal_fn_output henv hscoped hTarget rfl rfl
  have finish : AtomView env U registry target oldOut newOut :=
    .trans (AdapterNormal.view henv oldOut)
      (.trans outputView ((AdapterNormal.view henv newOut).inverse henv))
  have result := Result.view henv hscoped hTarget finish result
  have result : Result current fuel env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument)
      (raiseProfile M hn (.singleton output)) := by
    simpa only [raiseProfile_singleton] using result
  exact ⟨lowerRaised hn result⟩

theorem Obs.beta_diagonal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalArgument : Joint current fuel env U registry source argument argument A)
    (originalBody : Joint current fuel env U registry (A :: source) body body B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : Joint current fuel env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    (observation : Obs env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (bounded : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app function argumentObservation arguments admitted =>
    simp only [Obs.nativeDepth] at bounded
    exact Obs.beta_app henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits function (Nat.max_le.mp bounded).1 argumentObservation (Nat.max_le.mp bounded).2 arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [Obs.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits left (Nat.max_le.mp bounded).1 (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits right (Nat.max_le.mp bounded).2 (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    simp only [Obs.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits source bounded resources
    exact ⟨Result.view henv hscoped hTarget change a⟩
  | .pad source =>
    simp only [Obs.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [Obs.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits source bounded resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [Obs.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨Result.view henv hscoped hTarget (AtomView.commutePadFn key output) padded⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem Transfer.beta_forward
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalArgument : Joint current fuel env U registry source argument argument A)
    (originalBody : Joint current fuel env U registry (A :: source) body body B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : Joint current fuel env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    : Transfer current fuel env U registry target locals σ τ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) := by
  apply Transfer.trans henv hscoped hTarget
  · intro n demand footprint observation bounded resources
    exact Obs.beta_diagonal henv hscoped originalDomain originalArgument
      originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
      closed hTarget substitutions.left fits.left observation bounded resources
  · exact (originalInstantiated target locals σ τ available closed hTarget substitutions fits).1

end Lean4Lean.AnchoredSource.Adapted.Staged
