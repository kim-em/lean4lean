import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBetaApplication
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults

/-! Complete hereditary forward beta transfer. Every wrapper preserves the
actual assigned-type certificate; the only replay is the instantiated-term
child already stored in the original beta rule. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
mutual
theorem Obs.betaHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
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
    (observation : Obs env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app function argumentObservation arguments admitted =>
    exact SortableObs.betaAppOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits (.legacy function) (.legacy argumentObservation) arguments.toGeneral admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.betaHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
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
    (observation : SortableObs env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) demand) := by
  match observation with
  | .legacy source =>
    exact Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
  | .code relevant certificate =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits certificate resources
    exact ⟨answer.computational henv⟩
  | .app function argumentObservation arguments admitted =>
    exact SortableObs.betaAppOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits function argumentObservation arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    obtain ⟨a⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    obtain ⟨a⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.betaHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
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
    (certificate : CodeCert env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) true demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .map view source =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.betaHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
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
    (certificate : SortableCert env U registry target locals σ (.app (.lam A body) argument) relevant
      demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    obtain ⟨answer⟩ := CodeCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.retag formed⟩
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .observe observation formed =>
    obtain ⟨answer⟩ := SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .support action source =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.supportAction henv hscoped action⟩
  | .map view source =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
  | .sortPad source =>
    obtain ⟨answer⟩ := SortableCert.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits source resources
    exact answer.sortPad henv
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

theorem SortableComputationalTransfer.betaForwardOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
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
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    : SortableComputationalTransfer env U registry target locals σ τ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) := by
  apply SortableComputationalTransfer.trans henv hscoped hTarget
  · intro n demand footprint observation resources
    exact SortableObs.betaHereditary henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument
      originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
      closed hTarget substitutions.left fits.left observation resources
  · exact (originalInstantiated target locals σ τ available closed hTarget substitutions fits)


end Lean4Lean.AnchoredSource.Adapted
