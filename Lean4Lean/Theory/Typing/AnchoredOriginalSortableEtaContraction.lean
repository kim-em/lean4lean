import Lean4Lean.Theory.Typing.AnchoredOriginalSortableEtaCertificate
import Lean4Lean.Theory.Typing.AnchoredSortablePiShape

/-! The eta contraction consumes the actual original function child and
rebuilds its requested Pi support from the original formation children. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

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

theorem SortableEtaFactor.completeOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint outside : Footprint}
    (factor : SortableEtaFactor env U registry target locals σ f key output outside)
    (functionResult : SortableComputationalTransferResult env U registry target locals σ τ available
      f f (.forallE A B) (Profile.fn factor.key factor.rawOutput))
    {resultSupport : Profile factor.rank}
    (row : SortablePiRowCertificate env U registry target locals σ available true A B factor.key resultSupport)
    (outputTyped : (Profile.singleton factor.rawOutput).HasType resultSupport)
    (domain : SortableCert env U registry target locals σ A true domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (domainAvailable : domainFootprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) (Profile.fn key output)) := by
  have functionRelated := functionResult.requestedRelated henv hTarget
  obtain ⟨adapt⟩ := factor.adapter henv hscoped hTarget guard functionRelated
  obtain ⟨support, footprint, ⟨certificate⟩, resources, typed, code⟩ :=
    factor.certificateOriginal henv hscoped hle row outputTyped domain guard context originalDomain originalBody domainIH bodyIH
      formedA formedB closed hTarget substitutions.left fits.left domainAvailable
  have raw := functionTyped.substDF henv substitutions.wf hTarget substitutions
  have expanded := Related.etaExpand henv raw functionRelated
  have requested := adapt.termMap henv hscoped hTarget typed code expanded
  have highCertificate := certificate.raise functionResult.bound
  have highCode := TypeRelated.raise henv functionResult.bound code
  have highTyped := Profile.HasType.raise functionResult.bound typed
  have highRelated := Related.raise henv functionResult.bound requested
  have allCode := code_union highCode functionResult.typeCode
  have wf := highTyped.wf_type.union functionResult.rawTyped.wf_type
  have requestedTyped := highTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := functionResult.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have adapter := functionResult.adapter.comp
    (GeneralNormalProfileAdapter.raise henv hscoped hTarget functionResult.bound adapt)
  refine ⟨{
    rank := functionResult.rank
    bound := Nat.le_trans (Nat.succ_le_succ factor.bound) functionResult.bound
    raw := functionResult.raw
    footprint := functionResult.footprint
    observation := functionResult.observation
    adapter := by simpa only [raiseProfile_trans] using adapter
    resources := functionResult.resources
    support := _
    typeFootprint := _
    typeCertificate := .union highCertificate functionResult.typeCertificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (resources i need) (functionResult.typeAvailable i need)
    typed := by simpa only [raiseProfile_trans] using requestedTyped
    rawTyped := rawTyped
    typeCode := allCode
    related := ?_
    rawRelated := Related.retag henv rawTyped allCode functionResult.rawRelated
    live := functionResult.live }⟩
  simpa only [eta_subst, raiseProfile_trans] using
    Related.retag henv requestedTyped allCode highRelated


theorem SortableObs.etaLamOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : SortableCert env U registry target locals σ A true domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (body : SortableObs env U registry target (Locals.push locals) (σ.cons key.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) (Profile.fn key output)) := by
  obtain ⟨factor⟩ := body.eta_factor henv hscoped hTarget pack covered
  obtain ⟨returned⟩ := functionChild factor.function (fun i need hm => outsideAvailable i need (factor.included hm))
  obtain ⟨resultSupport, ⟨row⟩, outputTyped⟩ := returned.requestedCertificate.piRowOriginal
    henv hscoped hle hTarget closed context originalDomain originalBody substitutions.left fits.left.forward
    domainIH bodyIH returned.typeAvailable returned.requestedTyped
  exact factor.completeOriginal henv hscoped hle returned row outputTyped domain guard
    context originalDomain originalBody domainIH bodyIH formedA formedB functionTyped closed hTarget
    substitutions fits domainAvailable


end Lean4Lean.AnchoredSource.Adapted
