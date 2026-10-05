import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalCodeSite

/-! Concrete closed code-site producers retain the certificate's actual
formation occurrence. Definition return, canonical subterm assigned types,
and the native recursor signature all share the same charged representation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

variable {name : Name} {canonicalExpression : VExpr} {level : VLevel}
  {realization : Subst} {footprint : Footprint}

noncomputable def CanonicalCodeSitePacket.ofCertificate
    (owner : CanonicalCodeOwner env registry strata name)
    (node : EndpointState owner.selected.origin.source U [] canonicalExpression (.sort level))
    (expressionEq : EqUpToLevels U canonicalExpression expression)
    (certificate : RichCert owner.selected.origin.source env U registry target node
      [] realization relevant profile footprint)
    (resources : footprint.Available (fun _ => [])) :
    CanonicalCodeSitePacket env U registry target strata expression relevant profile where
  name := name
  owner := owner
  canonicalExpression := canonicalExpression
  level := level
  node := node
  canonicalClosed := VExpr.WF.closedN (Γ := []) owner.selected.origin.ordered
    ⟨.sort level, node.sound.defeq⟩ (by trivial)
  expressionEq := expressionEq
  realization := realization
  footprint := footprint
  certificate := certificate
  resources := resources

/-- A returned value's assigned certificate remains at its computed actual
typeFormation. No independently reconstructed header proof is substituted. -/
noncomputable def CanonicalCodeSitePacket.ofSupportedValue
    (owner : CanonicalCodeOwner env registry strata name)
    (node : EndpointState owner.selected.origin.source U [] term assigned)
    (expressionEq : EqUpToLevels U assigned expression)
    (answer : RichSupportedValue owner.selected.origin.source env U registry target
      node [] realization realization (fun _ => []) profile) :
    CanonicalCodeSitePacket env U registry target strata expression true answer.support :=
  .ofCertificate owner node.typeFormation.node expressionEq answer.certificate answer.resources

theorem CanonicalCodeSitePacket.ofSupportedValue_chargeDepth
    (owner : CanonicalCodeOwner env registry strata name)
    (node : EndpointState owner.selected.origin.source U [] term assigned)
    (expressionEq : EqUpToLevels U assigned expression)
    (answer : RichSupportedValue owner.selected.origin.source env U registry target
      node [] realization realization (fun _ => []) profile) :
    (CanonicalCodeSitePacket.ofSupportedValue owner node expressionEq answer).chargeDepth =
      headDepth owner.selected.ordinal
        (fun control => answer.certificate.stratifiedDepth (strata.headOrdinal registry) control) := rfl

/-- Existing definition type packets embed without changing the canonical
node, source certificate, or named mask. -/
noncomputable def CanonicalDeltaTypePacket.codeSite
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) :
    CanonicalCodeSitePacket env U registry target strata expression relevant profile :=
  .ofCertificate (CanonicalCodeOwner.ofDefinition strata packet.lookup packet.registered.2)
    packet.codeNode (by
      simpa only [packet.expressionEq, VDefVal.toDefEq] using
        EqUpToLevels.instL_expr packet.value.type packet.seedWF packet.levelsWF packet.equivalent)
    packet.certificate packet.resources

@[simp] theorem CanonicalDeltaTypePacket.codeSite_chargeDepth
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) :
    packet.codeSite.chargeDepth = packet.chargeDepth := rfl

namespace CanonicalNativeOpening
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels displayedLevels : List VLevel}

/-- Fix the native header's actual canonical original proof once, before
query interpretation. It is selected from the canonical source's constWF. -/
noncomputable def signatureOriginal
    (opening : CanonicalNativeOpening env registry strata name)
    (signature : NativeConstantSignature opening.data levels)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    Derivation opening.selected.origin.source U [] (signature.type.instL levels)
      (signature.type.instL levels) (.sort (opening.signatureFormation signature levelsWF).choose) :=
  Classical.choice (Derivation.reify (opening.signatureFormation signature levelsWF).choose_spec)

/-- Native signature code uses the native rule's mask, while its child is
the actual recursor header formation rather than the singleton rule's type. -/
noncomputable def signatureCodeSite
    (opening : CanonicalNativeOpening env registry strata name)
    (signature : NativeConstantSignature opening.data levels)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (displayedWF : ∀ level ∈ displayedLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels displayedLevels)
    (certificate : RichCert opening.selected.origin.source env U registry target
      (.ref (.left (opening.signatureOriginal signature levelsWF)))
      [] realization relevant profile footprint)
    (resources : footprint.Available (fun _ => [])) :
    CanonicalCodeSitePacket env U registry target strata
      (signature.type.instL displayedLevels) relevant profile :=
  .ofCertificate (CanonicalCodeOwner.ofNative opening)
    (.ref (.left (opening.signatureOriginal signature levelsWF)))
    (EqUpToLevels.instL_expr signature.type levelsWF displayedWF equivalent) certificate resources

theorem signatureCodeSite_chargeDepth
    (opening : CanonicalNativeOpening env registry strata name)
    (signature : NativeConstantSignature opening.data levels)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (displayedWF : ∀ level ∈ displayedLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels displayedLevels)
    (certificate : RichCert opening.selected.origin.source env U registry target
      (.ref (.left (opening.signatureOriginal signature levelsWF)))
      [] realization relevant profile footprint)
    (resources : footprint.Available (fun _ => [])) :
    (opening.signatureCodeSite signature levelsWF displayedWF equivalent certificate resources).chargeDepth =
      headDepth opening.selected.ordinal
        (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control) := rfl

end CanonicalNativeOpening

theorem CanonicalCodeSiteAt.interpret
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (query : CanonicalCodeSiteAt sourceEnv env U registry target strata node locals σ relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel query.packet.chargeDepth)
    (lower : query.packet.CodeBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (τ : Subst) :
    ∃ output : CanonicalCodeSiteAt sourceEnv env U registry target strata node locals τ relevant profile,
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile ∧
      WithinAbove cutoff fuel output.packet.chargeDepth := by
  obtain ⟨output, _, _, related, bounded⟩ :=
    query.packet.interpret henv hscoped formed cutoff cutoffBound fuel constants callerSchedule bounded lower σ τ
  exact ⟨⟨output⟩, related, bounded⟩

end Lean4Lean.AnchoredSource.Adapted
