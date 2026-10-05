import Lean4Lean.Theory.Typing.AnchoredSortableEtaAdapter
import Lean4Lean.Theory.Typing.AnchoredSortableInputReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePiDiagonal

/-! Eta rebuilds its actual source Pi certificate by replaying retained input
leaves and executing the finite output action on its original codomain row. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem SortableEtaFactor.certificateOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint outside : Footprint}
    (factor : SortableEtaFactor env U registry target locals σ f key output outside)
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
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (domainAvailable : domainFootprint.Available available) :
    ∃ support footprint,
      Nonempty (SortableCert env U registry target locals σ (.forallE A B) true support footprint) ∧
      footprint.Available available ∧
      (raiseProfile (factor.rank + 1) (Nat.succ_le_succ factor.bound)
        (Profile.fn key output)).HasType support ∧
      TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
        ((VExpr.forallE A B).subst σ) support := by
  obtain ⟨anchored⟩ := row.reanchorOriginal henv hle hTarget closed context originalDomain originalBody
    substitutions fits.forward domainIH bodyIH factor.admitted
  have scope := formedB.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  have externalLive := fits.forward.leavesLive henv hscoped hTarget anchored.outsideAvailable
    (anchored.pack.scoped (anchored.body.scoped scope))
  have highDomain := domain.raise factor.bound
  have highGuard := guard.raise henv factor.bound
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := highGuard.anchor
  have newLive := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨bodyFootprint, external, packed, ⟨body⟩, pack, covered, resources⟩ :=
    anchored.body.replayInput henv hscoped hTarget factor.arguments newLive
      anchored.pack anchored.covered anchored.outsideAvailable externalLive closed
  have changedBody := SortableCert.support factor.resultAction.support body
  have certificate := highDomain.piLiteral
    (SortableRows.cons highGuard changedBody pack covered SortableRows.nil)
  have typed : (Profile.fn (raiseKey factor.rank factor.bound key)
      (raiseAtom factor.rank factor.bound output)).HasType
      (Profile.pi (A.subst σ) (B.subst σ.lift)
        (raiseProfile factor.rank factor.bound domainSupport)
        [(raiseKey factor.rank factor.bound key, factor.resultAction.support.apply resultSupport)]) :=
    Profile.HasType.fn certificate.formed.wf_value (List.mem_singleton_self _)
      (factor.resultAction.typed outputTyped)
  have code := SortableCert.piDiagonalOriginal henv hscoped hle context
    originalDomain originalBody domainIH bodyIH closed hTarget substitutions fits
    highDomain PiGuard.literal (.cons highGuard changedBody pack covered .nil)
    domainAvailable (fun i need member => resources i need (by simpa using member))
  let view := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) factor.bound key output).inverse henv
  refine ⟨_, _, ⟨SortableCert.map view certificate⟩, ?_, ?_, view.codeMap henv hscoped code⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (domainAvailable i need)
      (fun h => resources i need (by simpa using h))
  · simpa only [Profile.fn, raiseProfile_singleton] using view.mapType_typed typed

end Lean4Lean.AnchoredSource.Adapted
