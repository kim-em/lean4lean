import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePi
import Lean4Lean.Theory.Typing.AnchoredSortableSortResult

/-! The actual original Pi rule for the complete hereditary observer syntax.
Native formation flags, code wrappers, and all computational closures are
interpreted through the same fixed original domain/body calls. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def PiRows.toSortable
    (rows : PiRows env U registry target locals σ A B ambient entries footprint) :
    SortableRows env U registry target locals σ A B true ambient entries footprint :=
  match rows with
  | .nil => .nil
  | .cons guard body normal covered tail =>
    .cons guard (.ofCode body body.formed) normal covered tail.toSortable

mutual
theorem Obs.piHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : Obs env U registry target locals σ (.forallE A B) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel)) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .pi domain guard body =>
    exact SortableCert.piTransferOriginal henv hscoped context domainRef originalDomain originalBody domains bodies rightBody
      closed hTarget substitutions fits (.ofCode domain domain.formed) guard body.toSortable
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.piHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (observation : SortableObs env U registry target locals σ (.forallE A B) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel)) demand) := by
  match observation with
  | .legacy source =>
    exact Obs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
  | .code requestedFlag certificate =>
    obtain ⟨actualFlag, flag⟩ : ∃ actualFlag, Relevant (.imax domainLevel bodyLevel) actualFlag := by
      by_cases h : VLevel.imax domainLevel bodyLevel ≈ .zero
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits flag certificate resources
    have sourceA : OnCtx (A :: source) (env.IsType U) := ⟨substitutions.wf, _, domains.hasType.1⟩
    exact ⟨result.computational henv
      ⟨domains.sort_r henv substitutions.wf,
        bodies.sort_r henv sourceA⟩ flag⟩
  | .union left right =>
    obtain ⟨a⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    obtain ⟨a⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    obtain ⟨a⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.piHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (flag : Relevant (.imax domainLevel bodyLevel) actualFlag)
    (certificate : CodeCert env U registry target locals σ (.forallE A B) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableSortResult env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') true actualFlag demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨result⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits observation resources
    exact result.atSort henv hscoped closed hTarget formed flag
  | .union left right =>
    obtain ⟨hl⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨{
      footprint := hl.footprint ++ hr.footprint, certificate := .union hl.certificate hr.certificate
      available := fun i need hm => (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
      related := ?_, sorted := hl.sorted.union hr.sorted }⟩
    apply TypeRelated.of_singletons
    intro atom hm
    exact (List.mem_append.mp hm).elim
      (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .pad result.certificate,
      available := result.available, related := result.related.pad henv, sorted := result.sorted.pad_sort }⟩
  | .familyPad source =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .familyPad result.certificate,
      available := result.available, related := result.related.familyPad henv, sorted := result.sorted.familyPad }⟩
  | .unpad source =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .unpad result.certificate,
      available := result.available, related := (TypeRelated.pad_iff henv).mp result.related, sorted := by simpa only [Profile.down_sort] using result.sorted.pad_inv }⟩
  | .down source =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .down result.certificate,
      available := result.available, related := result.related.down henv, sorted := by simpa only [Profile.down_sort] using result.sorted.down }⟩
  | .map view source =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .map view result.certificate,
      available := result.available, related := view.codeMap henv hscoped result.related, sorted := view.mapType_sort result.sorted }⟩
  | .select source member =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .select result.certificate member,
      available := result.available, related := result.related.singleton member, sorted := result.sorted.singleton_of_mem member }⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .focusMinimal result.certificate minimal bound,
      available := result.available, related := result.related.focusMinimal henv minimal bound, sorted := result.sorted.restrict bound minimal.formation.wf_value }⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableCert.piHereditary
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryTailJoint env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryTailJoint env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (flag : Relevant (.imax domainLevel bodyLevel) actualFlag)
    (certificate : SortableCert env U registry target locals σ (.forallE A B) requestedFlag demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableSortResult env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') requestedFlag actualFlag demand) := by
  match certificate with
  | .ofCode source requested =>
    obtain ⟨result⟩ := CodeCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .observe (.code true result.certificate) requested,
      available := result.available, related := result.related, sorted := result.sorted }⟩
  | .pi domain guard rowBodies =>
    obtain ⟨result⟩ := SortableCert.piTransferOriginal henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits domain guard rowBodies
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact result.atSort henv hscoped closed hTarget (SortableCert.pi domain guard rowBodies).formed flag
  | .observe observation formed =>
    obtain ⟨result⟩ := SortableObs.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits observation resources
    exact result.atSort henv hscoped closed hTarget formed flag
  | .seed observation formed =>
    obtain ⟨result⟩ := Obs.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits observation resources
    exact result.atSort henv hscoped closed hTarget formed flag
  | .union left right =>
    obtain ⟨hl⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨{
      footprint := hl.footprint ++ hr.footprint, certificate := .union hl.certificate hr.certificate
      available := fun i need hm => (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
      related := ?_, sorted := hl.sorted.union hr.sorted }⟩
    apply TypeRelated.of_singletons
    intro atom hm
    exact (List.mem_append.mp hm).elim
      (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .pad result.certificate,
      available := result.available, related := result.related.pad henv, sorted := result.sorted.pad_sort }⟩
  | .sortPad source =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .sortPad result.certificate,
      available := result.available, related := result.related.sortPad, sorted := result.sorted.sortPad }⟩
  | .familyPad source =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .familyPad result.certificate,
      available := result.available, related := result.related.familyPad henv, sorted := result.sorted.familyPad }⟩
  | .unpad source =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .unpad result.certificate,
      available := result.available, related := (TypeRelated.pad_iff henv).mp result.related, sorted := by simpa only [Profile.down_sort] using result.sorted.pad_inv }⟩
  | .down source =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .down result.certificate,
      available := result.available, related := result.related.down henv, sorted := by simpa only [Profile.down_sort] using result.sorted.down }⟩
  | .support action source =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .support action result.certificate,
      available := result.available, related := action.codeMap henv hscoped result.related, sorted := action.preservesSort result.sorted }⟩
  | .map view source =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .map view result.certificate,
      available := result.available, related := view.codeMap henv hscoped result.related, sorted := view.mapType_sort result.sorted }⟩
  | .select source member =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .select result.certificate member,
      available := result.available, related := result.related.singleton member, sorted := result.sorted.singleton_of_mem member }⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨result⟩ := SortableCert.piHereditary henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits flag source resources
    exact ⟨{
      footprint := result.footprint, certificate := .focusMinimal result.certificate minimal bound,
      available := result.available, related := result.related.focusMinimal henv minimal bound, sorted := result.sorted.restrict bound minimal.formation.wf_value }⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

end

/-- The actual original Pi equality, with each body interpreted in its
own retained original domain context. -/
theorem OriginalTail.DerivationHereditaryFundamental.forallEDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source : List VExpr} {A A' B B' : VExpr} {u v : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort u))
    (body : Derivation sourceEnv U (A :: source) B B' (.sort v))
    (body' : Derivation sourceEnv U (A' :: source) B B' (.sort v))
    (domainIH : DerivationHereditaryFundamental env registry context domain)
    (bodyIH : DerivationHereditaryFundamental env registry (.cons context (.left domain)) body)
    (bodyIH' : DerivationHereditaryFundamental env registry (.cons context (.right domain)) body') :
    DerivationHereditaryFundamental env registry context (.forallEDF hu hv domain body body') := by
  intro target locals σ τ available closed hTarget substitutions fits
  have domains := domain.forget.defeq.mono below
  have bodies := body.forget.defeq.mono below
  have bodies' := body'.forget.defeq.mono below
  have domainJoint : HereditaryTailJoint env registry context A A' (.sort u) := domainIH
  have bodyJoint : HereditaryTailJoint env registry (.cons context (.left domain)) B B' (.sort v) := bodyIH
  have bodyJoint' : HereditaryTailJoint env registry (.cons context (.right domain)) B B' (.sort v) := bodyIH'
  have forward : SortableComputationalTransfer env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax u v)) :=
    SortableObs.piHereditary henv hscoped context (.left domain) domainJoint bodyJoint
      domains bodies bodies'.hasType.2 closed hTarget substitutions fits
  have backward : SortableComputationalTransfer env U registry target locals σ τ available
      (.forallE A' B') (.forallE A B) (.sort (.imax u v)) :=
    SortableObs.piHereditary henv hscoped context (.right domain) domainJoint.symm bodyJoint'.symm
      domains.symm bodies'.symm bodies.hasType.1 closed hTarget substitutions fits
  exact ⟨forward, backward⟩

end Lean4Lean.AnchoredSource.Adapted
