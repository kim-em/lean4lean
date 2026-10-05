import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableEtaContraction
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredSortableTransferConversion

/-! The complete original lambda equality for hereditary observations. The
mutual traversal covers both legacy and rich computational/certificate
wrappers; reverse typing is transported through the actual Pi equality. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
mutual
theorem Obs.etaContractHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : Obs env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    exact SortableObs.etaLamOriginal henv hscoped hle (.ofCode domain domain.formed) guard (.legacy body) pack covered
      context originalDomain originalBody domainIH bodyIH functionChild formedA formedB functionTyped
      closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.etaContractHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : SortableObs env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) demand) := by
  match observation with
  | .legacy source =>
    exact Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
  | .code relevant certificate =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits certificate resources
    exact ⟨answer.computational henv⟩
  | .lam domain guard body pack covered =>
    exact SortableObs.etaLamOriginal henv hscoped hle domain guard body pack covered
      context originalDomain originalBody domainIH bodyIH functionChild formedA formedB functionTyped
      closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    obtain ⟨a⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    obtain ⟨a⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.etaContractHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (certificate : CodeCert env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) true demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .map view source =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.etaContractHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (certificate : SortableCert env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) relevant demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    obtain ⟨answer⟩ := CodeCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.retag formed⟩
  | .seed observation formed =>
    obtain ⟨answer⟩ := Obs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .observe observation formed =>
    obtain ⟨answer⟩ := SortableObs.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.unpad henv⟩
  | .support action source =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.supportAction henv hscoped action⟩
  | .map view source =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
  | .sortPad source =>
    obtain ⟨answer⟩ := SortableCert.etaContractHereditary henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits source resources
    exact answer.sortPad henv
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted
