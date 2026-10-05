import Lean4Lean.Theory.Typing.AnchoredBoundedEtaCertificate
import Lean4Lean.Theory.Typing.AnchoredBoundedEtaFactor
import Lean4Lean.Theory.Typing.AnchoredEtaExpansion

/-! Graded eta contraction retains the original function child's actual raw
observation and composes only finite endpoint adapters. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

private theorem code_union
    (left : TypeRelated env U registry Γ A B p)
    (right : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim (fun h => left.singleton h) (fun h => right.singleton h)

private theorem eta_subst (A f : VExpr) (σ : Subst) :
    (VExpr.lam A (.app f.lift (.bvar 0))).subst σ =
      .lam (A.subst σ) (.app (f.subst σ).lift (.bvar 0)) := by
  show VExpr.lam (A.subst σ) (.app (f.lift.subst σ.lift) ((VExpr.bvar 0).subst σ.lift)) = _
  rw [lift_subst_lift]
  rfl

theorem EtaFactor.complete
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint outside : Footprint}
    (factor : EtaFactor env U registry target locals σ f key output outside)
    (functionResult : Result current fuel env U registry target locals σ τ available
      f f (.forallE A B) (Profile.fn factor.key factor.rawOutput))
    {resultSupport : Profile factor.rank}
    (row : PiRowCertificate current fuel env U registry target locals σ available A B factor.key resultSupport)
    (outputTyped : (Profile.singleton factor.rawOutput).HasType resultSupport)
    (domain : CodeCert env U registry target locals σ A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (domainAvailable : domainFootprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) (Profile.fn key output)) := by
  have functionRelated := functionResult.toGradedTransferResult.requestedRelated henv hTarget
  obtain ⟨adapt⟩ := factor.adapter henv hscoped hTarget guard functionRelated
  obtain ⟨support, footprint, ⟨certificate, certificateBound⟩, resources, typed, code⟩ :=
    EtaFactor.certificate henv hscoped factor row outputTyped domain guard domainBound originalDomain originalCodomain
      formedA formedB closed hTarget substitutions.left fits.left domainAvailable
  have raw := functionTyped.substDF henv substitutions.wf hTarget substitutions
  have expanded := Related.etaExpand henv raw functionRelated
  have requested := adapt.termMap henv hscoped hTarget typed code expanded
  let highCertificate := certificate.raise functionResult.bound
  have highCode := TypeRelated.raise henv functionResult.bound code
  have highTyped := Profile.HasType.raise functionResult.bound typed
  have highRelated := Related.raise henv functionResult.bound requested
  have allCode := code_union highCode functionResult.typeCode
  have wf := highTyped.wf_type.union functionResult.rawTyped.wf_type
  have requestedTyped := highTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := functionResult.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have adapter := functionResult.adapter.comp
    (NormalProfileAdapter.raise henv hscoped hTarget functionResult.bound adapt)
  refine ⟨{
    rank := functionResult.rank
    bound := Nat.le_trans (Nat.succ_le_succ factor.bound) functionResult.bound
    rawDemand := functionResult.rawDemand
    resultFootprint := functionResult.resultFootprint
    observation := functionResult.observation
    adapter := by simpa only [raiseProfile_trans] using adapter
    resultAvailable := functionResult.resultAvailable
    support := _
    typeFootprint := _
    certificate := .union highCertificate functionResult.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (resources i need) (functionResult.typeAvailable i need)
    typed := by simpa only [raiseProfile_trans] using requestedTyped
    rawTyped := rawTyped
    typeCode := allCode
    related := ?_
    rawRelated := Related.retag henv rawTyped allCode functionResult.rawRelated
    observationBound := functionResult.observationBound
    certificateBound := by simpa only [highCertificate, CodeCert.nativeDepth, CodeCert.nativeDepth_raise] using
      (Nat.max_le.mpr ⟨certificateBound, functionResult.certificateBound⟩) }⟩
  simpa only [eta_subst, raiseProfile_trans] using
    Related.retag henv requestedTyped allCode highRelated


theorem Obs.eta_lam_transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : CodeCert env U registry target locals σ A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (body : Obs env U registry target (Locals.push locals) (σ.cons key.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalFunction : Joint current fuel env U registry source f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) (Profile.fn key output)) := by
  obtain ⟨factor, factorBound⟩ := body.eta_factorBounded henv hscoped hTarget bodyBound pack covered
  obtain ⟨returned⟩ := (originalFunction target locals σ τ available closed hTarget
    substitutions fits).1 factor.function factorBound outsideAvailable
  obtain ⟨resultSupport, ⟨row⟩, outputTyped⟩ := CodeCert.piRow
    henv hscoped hTarget closed formedA formedB substitutions.left fits.left
    originalDomain originalCodomain returned.toGradedTransferResult.requestedCertificate
    (by simpa only [GradedTransferResult.requestedCertificate, CodeCert.nativeDepth_lower] using returned.certificateBound)
    returned.typeAvailable returned.toGradedTransferResult.requestedTyped
  exact EtaFactor.complete henv hscoped factor returned row outputTyped domain guard domainBound
    originalDomain originalCodomain formedA formedB functionTyped closed hTarget
    substitutions fits domainAvailable

/-- Full forward eta transfer for the replacement source grammar, including
all enclosing demand views, finite conjunctions, and grade changes. -/
theorem Obs.eta_contract
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {demand : Profile n} {footprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalFunction : Joint current fuel env U registry source f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (observation : Obs env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (observationBound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using observationBound)
    exact Obs.eta_lam_transfer henv hscoped domain guard body bounds.2 pack covered bounds.1
      originalDomain originalCodomain originalFunction formedA formedB functionTyped
      closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using observationBound)
    obtain ⟨hl⟩ := Obs.eta_contract henv hscoped originalDomain originalCodomain originalFunction
      formedA formedB functionTyped closed hTarget substitutions fits left bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := Obs.eta_contract henv hscoped originalDomain originalCodomain originalFunction
      formedA formedB functionTyped closed hTarget substitutions fits right bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨hl.union henv hscoped hTarget hr⟩
  | .view source change =>
    obtain ⟨result⟩ := Obs.eta_contract henv hscoped originalDomain originalCodomain originalFunction
      formedA formedB functionTyped closed hTarget substitutions fits source
      (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨result.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨result⟩ := Obs.eta_contract henv hscoped originalDomain originalCodomain originalFunction
      formedA formedB functionTyped closed hTarget substitutions fits source
      (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨result.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨result⟩ := Obs.eta_contract henv hscoped originalDomain originalCodomain originalFunction
      formedA formedB functionTyped closed hTarget substitutions fits source
      (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨result.unpad⟩
  | .rowShift source =>
    obtain ⟨result⟩ := Obs.eta_contract henv hscoped originalDomain originalCodomain originalFunction
      formedA formedB functionTyped closed hTarget substitutions fits source
      (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨(result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation

end Lean4Lean.AnchoredSource.Adapted.Staged
