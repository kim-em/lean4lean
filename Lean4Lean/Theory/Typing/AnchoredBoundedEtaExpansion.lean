import Lean4Lean.Theory.Typing.AnchoredBoundedEtaExpansionRow
import Lean4Lean.Theory.Typing.AnchoredEtaSubstitution

namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim (fun h => first.singleton h) (fun h => second.singleton h)

def EtaExpansionResult.empty :
    EtaExpansionResult current fuel env U registry target locals σ τ available A B f (Profile.empty (n := n)) where
  rawDemand := .empty
  footprint := []
  observation := .empty
  resultAvailable := fun _ _ h => nomatch h
  adapter := .nil _
  support := .empty
  typeFootprint := []
  certificate := .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value)
  typeAvailable := fun _ _ h => nomatch h
  typed := Profile.HasType.empty Profile.WF.empty
  rawTyped := Profile.HasType.empty Profile.WF.empty
  code := by cases n <;> exact fun Δ ρ insertion atom hm => nomatch hm
  related := by cases n <;> exact fun _ h => nomatch h
  rawRelated := by cases n <;> exact fun _ h => nomatch h
  observationBound := by simp only [Obs.nativeDepth]; omega
  certificateBound := by simp only [CodeCert.nativeDepth, Obs.nativeDepth]; omega

noncomputable def EtaExpansionResult.union
    (henv : env.Ordered)
    (a : EtaExpansionResult current fuel env U registry target locals σ τ available A B f (p : Profile n))
    (b : EtaExpansionResult current fuel env U registry target locals σ τ available A B f (q : Profile n)) :
    EtaExpansionResult current fuel env U registry target locals σ τ available A B f (p.union q) := by
  have wf := a.typed.wf_type.union b.typed.wf_type
  have aTyped := a.typed.enlarge (Profile.le_union_left _ _) wf
  have bt := b.typed.enlarge (Profile.le_union_right _ _) wf
  have ar := a.rawTyped.enlarge (Profile.le_union_left _ _) wf
  have br := b.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have code := code_union a.code b.code
  exact {
    rawDemand := a.rawDemand.union b.rawDemand
    footprint := a.footprint ++ b.footprint
    observation := .union a.observation b.observation
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.resultAvailable i need) (b.resultAvailable i need)
    adapter := NormalProfileAdapter.union a.adapter b.adapter
    support := a.support.union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    certificate := .union a.certificate b.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.typeAvailable i need) (b.typeAvailable i need)
    typed := aTyped.union bt
    rawTyped := ar.union br
    code := code
    related := (Related.retag henv aTyped code a.related).union (Related.retag henv bt code b.related)
    rawRelated := (Related.retag henv ar code a.rawRelated).union (Related.retag henv br code b.rawRelated)
    observationBound := by simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨a.observationBound, b.observationBound⟩
    certificateBound := by simpa only [CodeCert.nativeDepth] using Nat.max_le.mpr ⟨a.certificateBound, b.certificateBound⟩ }

theorem Obs.expand_eta_profile
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {profile support : Profile n} {footprint typeFootprint : Footprint}
    (observation : Obs env U registry target locals τ f profile footprint)
    (observationBound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available)
    (certificate : CodeCert env U registry target locals σ (.forallE A B) support typeFootprint)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (typeAvailable : typeFootprint.Available available)
    (typed : profile.HasType support)
    (code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) support)
    (related : Related env U registry target (f.subst τ) (f.subst τ)
      ((VExpr.forallE A B).subst σ) profile support)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    Nonempty (EtaExpansionResult current fuel env U registry target locals σ τ available A B f profile) := by
  have rawEta := IsDefEq.eta_subst_right henv hTarget substitutions formedA formedB functionTyped
  have go : ∀ selected : Profile n, List.Subset selected profile →
      Nonempty (EtaExpansionResult current fuel env U registry target locals σ τ available A B f selected) := by
    intro selected included
    induction selected with
    | nil => exact ⟨.empty⟩
    | cons atom rest ih =>
      have member := included List.mem_cons_self
      obtain ⟨selected, selectedBound⟩ := observation.atom_bounded (current := current) member
      have localResources := selected.atomizes.available_closed resources closed
      obtain ⟨head⟩ := Obs.expand_eta_atom henv hscoped selected.observation (Nat.le_trans selectedBound observationBound) localResources certificate
        certificateBound typeAvailable (typed.singleton_of_mem member) code
        (related.singleton_of_mem member) rawEta originalDomain originalCodomain
        formedA formedB closed hTarget substitutions fits
      obtain ⟨tail⟩ := ih (fun _ h => included (List.mem_cons_of_mem _ h))
      exact ⟨head.union henv tail⟩
  exact go profile (fun _ h => h)

theorem Result.etaExpand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {profile : Profile n}
    (result : Result current fuel env U registry target locals σ τ available f f (.forallE A B) profile)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      f (.lam A (.app f.lift (.bvar 0))) (.forallE A B) profile) := by
  obtain ⟨expanded⟩ := Obs.expand_eta_profile henv hscoped result.observation result.observationBound
    result.resultAvailable result.certificate result.certificateBound result.typeAvailable result.rawTyped result.typeCode
    result.rawRelated originalDomain originalCodomain formedA formedB functionTyped
    closed hTarget substitutions fits
  have requested := result.adapter.termMap henv hscoped hTarget result.typed result.typeCode expanded.related
  have cross := Related.trans henv hscoped result.related requested
  have code := code_union result.typeCode expanded.code
  have wf := result.typed.wf_type.union expanded.rawTyped.wf_type
  have typed := result.typed.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := expanded.rawTyped.enlarge (Profile.le_union_right _ _) wf
  exact ⟨{
    rank := result.rank
    bound := result.bound
    rawDemand := expanded.rawDemand
    resultFootprint := expanded.footprint
    observation := expanded.observation
    adapter := expanded.adapter.comp result.adapter
    resultAvailable := expanded.resultAvailable
    support := result.support.union expanded.support
    typeFootprint := result.typeFootprint ++ expanded.typeFootprint
    certificate := .union result.certificate expanded.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (result.typeAvailable i need) (expanded.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code cross
    rawRelated := Related.retag henv rawTyped code expanded.rawRelated
    observationBound := expanded.observationBound
    certificateBound := by simpa only [CodeCert.nativeDepth] using Nat.max_le.mpr ⟨result.certificateBound, expanded.certificateBound⟩ }⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
