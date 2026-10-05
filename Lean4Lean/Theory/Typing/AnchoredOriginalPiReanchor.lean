import Lean4Lean.Theory.Typing.AnchoredOriginalTailFundamental
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalPairedApplication

/-! Pi-row replay using only the fixed original domain and body endpoints.
The contexts sent to the fundamental induction are constructed from the
actual source tails, including both directions at the new anchor. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

theorem PiRowCertificate.reanchorOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B anchor : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (row : PiRowCertificate env U registry target locals σ available A B (key : Key n) result)
    (admitted : Admitted env U registry target key anchor anchor) :
    Nonempty (PiRowCertificate env U registry target locals σ available A B
      (reanchorKey key anchor) result) := by
  let frame := TailPairedFits.diagonal context tail
  have domainChild : GradedTransfer env U registry target locals σ σ available
      A A (.sort domainLevel) :=
    (domainIH target locals σ σ available closed hTarget substitutions frame).1
  obtain ⟨domainCode⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    domainChild row.domainAvailable
  have atA : Admitted env U registry target ⟨A.subst σ, key.anchor, key.input⟩ anchor anchor :=
    row.alignment.admission henv admitted
  obtain ⟨raw, _, _, _, _, _, first, _⟩ := atA
  have arguments := Related.retag henv row.inputTyped domainCode.related first
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n :=
    fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => row.covered atom
      ((row.pack.atomized_localNeeds need member).2 atom present)
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons anchor) (A :: source) :=
    .cons substitutions (originalDomain.sound.defeq.mono hle) raw
  let bodyFrame := frame.pushCertificates originalDomain row.domain row.domain
    row.domainAvailable row.domainAvailable row.inputTyped row.inputTyped arguments
    (arguments.symm henv) needs bounded covered
  have bodyChild : GradedTransfer env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons anchor) (Valuation.push needs available) B B (.sort bodyLevel) :=
    (bodyIH target (Locals.push locals) (σ.cons key.anchor) (σ.cons anchor)
    (Valuation.push needs available) (Valuation.push_atomized_closed closed _)
    hTarget paired bodyFrame).1
  obtain ⟨changed⟩ := row.body.transfer_graded henv hscoped hTarget
    (Valuation.push_atomized_closed closed _) bodyChild
    (row.pack.available_atomized_localNeeds row.outsideAvailable)
  obtain ⟨packed, outside, pack, coverage, resources⟩ :=
    Footprint.pack_available changed.available bounded covered
  exact ⟨{ row with
    anchor := admitted.reset_anchor
    bodyFootprint := changed.footprint
    body := changed.certificate
    packed := packed
    outside := outside
    pack := pack
    covered := coverage
    outsideAvailable := resources }⟩

theorem CodeCert.piOriginsOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available) :
    PiProfileOrigins env U registry target locals σ available A B profile :=
  certificate.piOriginsWith henv hscoped hTarget closed
    (originalDomain.sound.defeq.mono hle) (originalBody.sound.defeq.mono hle)
    substitutions (PairedFits.diagonal (tail.toFits henv hTarget))
    (fun row admitted => row.reanchorOriginal henv hscoped hle hTarget closed
      context originalDomain originalBody substitutions tail domainIH bodyIH admitted) resources

theorem OriginalFactorCut.rowInstantiateOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B argument : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (row : PiRowCertificate env U registry target locals σ available A B key result)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (argumentResult : GradedResult env U registry target locals σ available argument key.input) :
    Nonempty (CertificateResult env U registry target locals σ available (B.inst argument) result) := by
  obtain ⟨anchored⟩ := row.reanchorOriginal henv hscoped hle hTarget closed
    context originalDomain originalBody substitutions tail domainIH bodyIH admitted
  have formedDomain := originalDomain.sound.defeq.mono hle
  have formedBody := originalBody.sound.defeq.mono hle
  have bodyScope := formedBody.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedDomain⟩)
  have outsideLive := (tail.toFits henv hTarget).leavesLive henv hscoped hTarget
    anchored.outsideAvailable (anchored.pack.scoped (anchored.body.scoped bodyScope))
  exact anchored.body.instantiate henv hscoped hTarget closed argumentResult
    anchored.pack anchored.covered anchored.outsideAvailable outsideLive

end Lean4Lean.AnchoredSource.Adapted
