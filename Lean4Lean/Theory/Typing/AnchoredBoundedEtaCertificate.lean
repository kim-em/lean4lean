import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaAdapter
import Lean4Lean.Theory.Typing.AnchoredBoundedPiCode

/-! Eta's requested source Pi cover is rebuilt from the original extracted
row, with directional replay of its actual codomain leaves. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem EtaFactor.certificate
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint outside : Footprint}
    (factor : EtaFactor env U registry target locals σ f key output outside)
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
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    (domainAvailable : domainFootprint.Available available) :
    ∃ support footprint,
      (∃ certificate : CodeCert env U registry target locals σ (.forallE A B) support footprint,
        certificate.nativeDepth current ≤ fuel) ∧
      footprint.Available available ∧
      (raiseProfile (factor.rank + 1) (Nat.succ_le_succ factor.bound)
        (Profile.fn key output)).HasType support ∧
      TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
        ((VExpr.forallE A B).subst σ) support := by
  obtain ⟨anchored⟩ := row.reanchor henv hscoped hTarget closed formedA substitutions fits
    originalDomain originalCodomain factor.admitted
  have scope := formedB.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  have externalLive := fits.forward.forget.leavesLive henv hscoped hTarget anchored.outsideAvailable
    (anchored.pack.scoped (anchored.body.scoped scope))
  let highDomain := domain.raise factor.bound
  have highGuard := guard.raise henv factor.bound
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := highGuard.anchor
  have newLive := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨bodyFootprint, external, packed, ⟨body, bodyBound⟩, pack, covered, resources⟩ :=
    anchored.body.replayInputBounded henv hscoped hTarget anchored.bodyBound factor.arguments newLive
      anchored.pack anchored.covered anchored.outsideAvailable externalLive closed
  let changedBody := CodeCert.map factor.resultView body
  let certificate := highDomain.piLiteral
    (PiRows.cons highGuard changedBody pack covered PiRows.nil)
  have typed : (Profile.fn (raiseKey factor.rank factor.bound key)
      (raiseAtom factor.rank factor.bound output)).HasType
      (Profile.pi (A.subst σ) (B.subst σ.lift)
        (raiseProfile factor.rank factor.bound domainSupport)
        [(raiseKey factor.rank factor.bound key, factor.resultView.mapType resultSupport)]) :=
    Profile.HasType.fn certificate.formed.wf_value (List.mem_singleton_self _)
      (factor.resultView.mapType_typed outputTyped)
  have code := CodeCert.piTypeCode henv hscoped highDomain highGuard changedBody pack covered
    (by simpa only [highDomain, CodeCert.nativeDepth_raise] using domainBound)
    (by simpa only [changedBody, CodeCert.nativeDepth] using bodyBound) originalDomain originalCodomain formedA formedB closed hTarget substitutions fits
    domainAvailable resources
  let view := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) factor.bound key output).inverse henv
  refine ⟨_, _, ⟨CodeCert.map view certificate, ?_⟩, ?_, ?_, view.codeMap henv hscoped code⟩
  · simpa only [certificate, CodeCert.piLiteral, CodeCert.pi, CodeCert.nativeDepth,
      Obs.nativeDepth, PiRows.nativeDepth, changedBody, highDomain, CodeCert.nativeDepth_raise,
      Nat.max_zero] using Nat.max_le.mpr ⟨domainBound, bodyBound⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (domainAvailable i need)
      (fun h => resources i need (by simpa using h))
  · simpa only [Profile.fn, raiseProfile_singleton] using view.mapType_typed typed

end Lean4Lean.AnchoredSource.Adapted.Staged
