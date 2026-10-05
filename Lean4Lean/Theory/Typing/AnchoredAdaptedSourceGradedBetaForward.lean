import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedBeta
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaTrace
import Lean4Lean.Theory.Typing.AnchoredFunctionViewOutput
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty

/-! Forward beta for every finite observation of the redex. Function views
are replayed through their actual lambda origin and reversible output path. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private def lowerRaised {p : Profile n} (h : n ≤ N)
    (result : GradedTransferResult env U registry Γ locals σ τ available l r A
      (raiseProfile N h p)) :
    GradedTransferResult env U registry Γ locals σ τ available l r A p :=
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

theorem Obs.graded_beta_app
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    {functionFootprint argumentFootprint : Footprint}
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalArgument : GradedJoint env U registry source argument argument A)
    (originalBody : GradedJoint env U registry (A :: source) body body B)
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : GradedJoint env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (function : Obs env U registry target locals σ (.lam A body)
      (Profile.fn key output) functionFootprint)
    (argumentObservation : Obs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentAdapter : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨origin, ⟨path⟩, footprint⟩ := function.lambda_factor (.fn key output) rfl
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
  have bodyObs := origin.node.bodyObservation.raise ho
  rw [raiseProfile_singleton] at bodyObs
  have domainAvailable : origin.node.domainFootprint.Available available :=
    fun i need hm => functionAvailable i need (footprint ▸ List.mem_append_left _ hm)
  have outsideAvailable : origin.node.outside.Available available :=
    fun i need hm => functionAvailable i need (footprint ▸ List.mem_append_right _ hm)
  obtain ⟨result⟩ := Obs.graded_beta_row henv hscoped originalDomain originalArgument
    originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
    closed hTarget substitutions fits (origin.node.domain.raise ho) oldGuard bodyObs
    (origin.node.pack.raise ho) (raiseProfile_subset ho origin.node.covered)
    (argumentObservation.raise hn) arguments oldAdmission domainAvailable outsideAvailable argumentAvailable
  obtain ⟨outputView⟩ := views.normal_fn_output henv hscoped hTarget rfl rfl
  have finish : AtomView env U registry target oldOut newOut :=
    .trans (AdapterNormal.view henv oldOut)
      (.trans outputView ((AdapterNormal.view henv newOut).inverse henv))
  have result := result.view henv hscoped hTarget finish
  have result : GradedTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument)
      (raiseProfile M hn (.singleton output)) := by
    simpa only [raiseProfile_singleton] using result
  exact ⟨lowerRaised hn result⟩

theorem Obs.graded_beta_diagonal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalArgument : GradedJoint env U registry source argument argument A)
    (originalBody : GradedJoint env U registry (A :: source) body body B)
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : GradedJoint env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (observation : Obs env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app function argumentObservation arguments admitted =>
    exact Obs.graded_beta_app henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits function argumentObservation arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := left.graded_beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := right.graded_beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := source.graded_beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := source.graded_beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := source.graded_beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := source.graded_beta_diagonal henv hscoped originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem GradedTransfer.beta_forward
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalArgument : GradedJoint env U registry source argument argument A)
    (originalBody : GradedJoint env U registry (A :: source) body body B)
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : GradedJoint env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    : GradedTransfer env U registry target locals σ τ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) := by
  apply GradedTransfer.trans henv hscoped hTarget
  · intro n demand footprint observation resources
    exact observation.graded_beta_diagonal henv hscoped originalDomain originalArgument
      originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
      closed hTarget substitutions.left fits.left resources
  · exact (originalInstantiated target locals σ τ available closed hTarget substitutions fits).1

end Lean4Lean.AnchoredSource.Adapted
