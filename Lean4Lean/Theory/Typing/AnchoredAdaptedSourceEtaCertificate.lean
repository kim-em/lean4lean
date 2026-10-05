import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaAdapter
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceInputReplay
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiCode

/-! Eta's requested source Pi cover is rebuilt from the original extracted
row, with directional replay of its actual codomain leaves. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem EtaFactor.certificate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint outside : Footprint}
    (factor : EtaFactor env U registry target locals σ f key output outside)
    {resultSupport : Profile factor.rank}
    (row : PiRowCertificate env U registry target locals σ available A B factor.key resultSupport)
    (outputTyped : (Profile.singleton factor.rawOutput).HasType resultSupport)
    (domain : CodeCert env U registry target locals σ A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (domainAvailable : domainFootprint.Available available) :
    ∃ support footprint,
      Nonempty (CodeCert env U registry target locals σ (.forallE A B) support footprint) ∧
      footprint.Available available ∧
      (raiseProfile (factor.rank + 1) (Nat.succ_le_succ factor.bound)
        (Profile.fn key output)).HasType support ∧
      TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
        ((VExpr.forallE A B).subst σ) support := by
  obtain ⟨anchored⟩ := row.reanchor henv hscoped hTarget closed formedA substitutions fits
    originalDomain originalCodomain factor.admitted
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
  have changedBody := CodeCert.map factor.resultView body
  have certificate := highDomain.piLiteral
    (PiRows.cons highGuard changedBody pack covered PiRows.nil)
  have typed : (Profile.fn (raiseKey factor.rank factor.bound key)
      (raiseAtom factor.rank factor.bound output)).HasType
      (Profile.pi (A.subst σ) (B.subst σ.lift)
        (raiseProfile factor.rank factor.bound domainSupport)
        [(raiseKey factor.rank factor.bound key, factor.resultView.mapType resultSupport)]) :=
    Profile.HasType.fn certificate.formed.wf_value (List.mem_singleton_self _)
      (factor.resultView.mapType_typed outputTyped)
  have code := highDomain.piTypeCode henv hscoped highGuard changedBody pack covered
    originalDomain originalCodomain formedA formedB closed hTarget substitutions fits
    domainAvailable resources
  let view := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) factor.bound key output).inverse henv
  refine ⟨_, _, ⟨CodeCert.map view certificate⟩, ?_, ?_, view.codeMap henv hscoped code⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (domainAvailable i need)
      (fun h => resources i need (by simpa using h))
  · simpa only [Profile.fn, raiseProfile_singleton] using view.mapType_typed typed

end Lean4Lean.AnchoredSource.Adapted
