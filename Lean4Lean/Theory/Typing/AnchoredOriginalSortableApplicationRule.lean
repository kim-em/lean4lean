import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplicationTransfer
import Lean4Lean.Theory.Typing.AnchoredOriginalTailApplication

/-! Complete hereditary application F traverses every old and rich query
wrapper, then assembles the five original appDF children at exact source tails. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

mutual
theorem Obs.appHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : SortableComputationalTransfer env U registry target locals σ τ available a b A)
    (resultChild : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : Obs env U registry target locals σ (.app f a) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app fn arg arguments admitted =>
    exact SortableObs.appTransferOriginal henv hscoped hle context originalDomain originalBody
      domainIH bodyIH functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits
      (.legacy fn) (.legacy arg) arguments.toGeneral admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.appHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : SortableComputationalTransfer env U registry target locals σ τ available a b A)
    (resultChild : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : SortableObs env U registry target locals σ (.app f a) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) demand) := by
  match observation with
  | .legacy source =>
    exact Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
  | .code relevant certificate =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits certificate resources
    exact ⟨answer.computational henv⟩
  | .app fn arg arguments admitted =>
    exact SortableObs.appTransferOriginal henv hscoped hle context originalDomain originalBody
      domainIH bodyIH functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits
      fn arg arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    obtain ⟨a⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    obtain ⟨a⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.appHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : SortableComputationalTransfer env U registry target locals σ τ available a b A)
    (resultChild : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (certificate : CodeCert env U registry target locals σ (.app f a) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) true demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .map view source =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.appHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : SortableComputationalTransfer env U registry target locals σ τ available a b A)
    (resultChild : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (certificate : SortableCert env U registry target locals σ (.app f a) relevant demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    obtain ⟨answer⟩ := CodeCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.retag formed⟩
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .observe observation formed =>
    obtain ⟨answer⟩ := SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .support action source =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.supportAction henv hscoped action⟩
  | .map view source =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
  | .sortPad source =>
    obtain ⟨answer⟩ := SortableCert.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits source resources
    exact answer.sortPad henv
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end


/-- Hereditary transfer of an actual source application. -/
theorem SortableComputationalTransfer.appOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : SortableComputationalTransfer env U registry target locals σ τ available a b A)
    (resultChild : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available) :
    SortableComputationalTransfer env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) :=
  SortableObs.appHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH
    functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits

/-- The five original appDF children are queried at their exact retained
tails; the reverse result conversion is the original result equality. The
strict schedules are `OriginalTail.appDF_schedule` for this same derivation. -/
theorem OriginalTail.DerivationHereditaryFundamental.appDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (function : Derivation sourceEnv U source f g (.forallE A B))
    (argument : Derivation sourceEnv U source a b A)
    (result : Derivation sourceEnv U source (B.inst a) (B.inst b) (.sort bodyLevel))
    (domainIH : DerivationHereditaryFundamental env registry context domain)
    (bodyIH : DerivationHereditaryFundamental env registry (.cons context (.left domain)) body)
    (functionIH : DerivationHereditaryFundamental env registry context function)
    (argumentIH : DerivationHereditaryFundamental env registry context argument)
    (resultIH : DerivationHereditaryFundamental env registry context result) :
    DerivationHereditaryFundamental env registry context (.appDF domainWF bodyWF domain body function argument result) := by
  have domainF : StateSortableFundamental env registry context (.ref (.left domain)) := by
    intro target locals σ τ available closed hTarget substitutions fits
    exact SortableComputationalTransfer.sortable henv hscoped closed hTarget
      (domainIH target locals σ τ available closed hTarget substitutions fits).1
  have bodyF : StateSortableFundamental env registry (.cons context (.left domain)) (.ref (.left body)) := by
    intro target locals σ τ available closed hTarget substitutions fits
    exact SortableComputationalTransfer.sortable henv hscoped closed hTarget
      (bodyIH target locals σ τ available closed hTarget substitutions fits).1
  intro target locals σ τ available closed hTarget substitutions fits
  have functionAnswer := functionIH target locals σ τ available closed hTarget substitutions fits
  have argumentAnswer := argumentIH target locals σ τ available closed hTarget substitutions fits
  have resultAnswer := resultIH target locals σ σ available closed hTarget substitutions.left fits.left
  have resultJoint : HereditaryTailJoint env registry context (B.inst a) (B.inst b) (.sort bodyLevel) := resultIH
  have resultLeft : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel) :=
    (resultJoint.left henv hscoped target locals σ σ available closed hTarget substitutions.left fits.left).1
  have resultRight : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst b) (B.inst b) (.sort bodyLevel) :=
    (resultJoint.symm.left henv hscoped target locals σ σ available closed hTarget substitutions.left fits.left).1
  have forward : SortableComputationalTransfer env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) :=
    SortableComputationalTransfer.appOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      domainF bodyF functionAnswer.1 argumentAnswer.1 resultLeft
      (argument.forget.defeq.mono hle) closed hTarget substitutions fits
  have backwardNatural : SortableComputationalTransfer env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst b) :=
    SortableComputationalTransfer.appOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      domainF bodyF functionAnswer.2 argumentAnswer.2 resultRight
      (argument.forget.defeq.mono hle).symm closed hTarget substitutions fits
  have backward : SortableComputationalTransfer env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst a) :=
    SortableComputationalTransfer.convertAnswer henv hscoped closed hTarget resultAnswer.2 backwardNatural
  exact ⟨forward, backward⟩

end Lean4Lean.AnchoredSource.Adapted
