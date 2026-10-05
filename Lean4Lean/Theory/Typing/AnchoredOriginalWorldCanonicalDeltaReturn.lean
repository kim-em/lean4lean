import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaStep
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyEndpoints

/-! Canonical delta uses one actual selected RHS original. Its assigned return
retains the SAME certificate produced by that RHS call, at the RHS's computed
type formation. That formation's dependency cost is bounded by the RHS cost;
the returned recipe root therefore reuses the actual RHS opening sponsor.
This construction does not relocate declaration-history delta children. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalEndpointFactor EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace CanonicalDeltaPacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel}
  {profile : Profile n}

/-- The selected equation and its source are definitionally the packet's
original ones, including when another declaration history also exists. -/
noncomputable def codeOwner
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    CanonicalCodeOwner env registry strata name :=
  .ofDefinition strata packet.lookup packet.registered.2

/-- The child controls are computed from the incoming packet, rather than
chosen independently for its body and assigned formation. -/
noncomputable def bodyControls
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    OriginalWorldControls strata packet.selected.origin.source where
  ordered := packet.selected.origin.ordered
  cutoff := packet.selected.ordinal - 1
  cutoffBound := Nat.le_trans (Nat.sub_le _ _) packet.selected.ordinal_le
  sourceCutoff := packet.selected.sourceCutoff
  fuel := packet.stratifiedChildren

noncomputable def bodyProvenance
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    EndpointProvenance .nil packet.bodyNode :=
  EndpointProvenance.ofLocation .here .nil

noncomputable def typeProvenance
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    EndpointProvenance .nil packet.bodyNode.typeFormation.node :=
  EndpointProvenance.ofLocation (.assignedFormation .here) .nil

noncomputable def bodySite
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    WorldQuerySite (registry := registry) (target := target) strata
      packet.bodyNode [] packet.bodyRealization :=
  .empty packet.bodyControls packet.bodyProvenance packet.bodyRealization

noncomputable def typeSite
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    WorldQuerySite (registry := registry) (target := target) strata
      packet.bodyNode.typeFormation.node [] packet.bodyRealization :=
  .empty packet.bodyControls packet.typeProvenance packet.bodyRealization

/-- The input is an actual shared query at the caller's actual original. -/
noncomputable def observation
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) :
    RichObs sourceEnv env U registry target caller locals σ profile [] :=
  .canonicalDelta (strata := strata) packet.lookup packet.nameEq packet.registered
    packet.seedWF packet.seedLength packet.levelsWF packet.equivalent
    packet.bodyClosed packet.typeClosed packet.certificate packet.typed packet.body

noncomputable def observationProvenance
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (certificate : WorldCertProvenance strata packet.certificate)
    (body : WorldObsProvenance strata packet.body) :
    WorldObsProvenance strata (packet.observation caller locals σ) :=
  .canonicalDelta packet.lookup packet.nameEq packet.registered packet.seedWF
    packet.seedLength packet.levelsWF packet.equivalent packet.bodyClosed packet.typeClosed
    packet.certificate packet.typed certificate body packet.bodyControls
    packet.typeProvenance packet.bodyProvenance

theorem observation_stratifiedDepth
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) :
    (fun control => (packet.observation caller locals σ).stratifiedDepth
      (strata.headOrdinal registry) control) = packet.stratifiedDepth := by
  funext control
  simp only [observation, RichObs.stratifiedDepth, RichObs.headDepth,
    stratifiedHeadPolicy, stratifiedDepth, stratifiedChildren, headDepth]
  rw [packet.codeOwner.headOrdinal_eq]
  rfl

/-- The actual canonical input annotation already retains this body site.
No independently supplied body reserve is needed by the return producer. -/
theorem observation_body_sponsored
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (certificate : WorldCertProvenance strata packet.certificate)
    (body : WorldObsProvenance strata packet.body)
    (paid : Sponsored frontier
      (packet.observationProvenance caller locals σ certificate body).worlds) :
    Sponsored frontier packet.bodySite.worlds := by
  intro child member
  apply paid child
  change child ∈ ((_ ++ packet.bodySite.worlds) ++ certificate.worlds) ++ body.worlds
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member))

section Return
variable (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
  (answer : RichSupportedValue packet.selected.origin.source env U registry target
    packet.bodyNode [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
  {assignedLevels : List VLevel}
  (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
  (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
  (caller : EndpointState sourceEnv U source (packet.value.type.instL assignedLevels) (.sort level))
  (locals : List Nat) (σ : Subst)

/-- A shared charged certificate containing precisely `answer.certificate`.
No call on a reconstructed canonical type proof is performed. -/
noncomputable def returnCertificate :
    RichCert sourceEnv env U registry target caller locals σ true answer.support [] :=
  .recipe (.root source locals σ packet.codeOwner packet.bodyNode.typeFormation.node
    packet.typeClosed.instL
    (EqUpToLevels.instL_expr packet.value.type packet.seedWF assignedWF seedAssigned)
    packet.bodyRealization answer.certificate answer.resources)

noncomputable def returnProvenance
    (annotation : WorldCertProvenance strata answer.certificate) :
    WorldCertProvenance strata
      (packet.returnCertificate answer assignedWF seedAssigned caller locals σ) :=
  .recipe (.root source locals σ packet.codeOwner packet.bodyNode.typeFormation.node
    packet.typeClosed.instL
    (EqUpToLevels.instL_expr packet.value.type packet.seedWF assignedWF seedAssigned)
    packet.bodyRealization answer.certificate answer.resources annotation
    packet.bodyControls packet.typeProvenance)

theorem returnProvenance_worlds
    (annotation : WorldCertProvenance strata answer.certificate) :
    (packet.returnProvenance answer assignedWF seedAssigned caller locals σ annotation).worlds =
      packet.typeSite.worlds ++ annotation.worlds := rfl

include assignedWF seedAssigned caller locals in
theorem returnCertificate_related (henv : env.Ordered) (τ : Subst) :
    TypeRelated env U registry target
      ((packet.value.type.instL assignedLevels).subst σ)
      ((packet.value.type.instL assignedLevels).subst τ) answer.support :=
  packet.returnType_related henv answer assignedWF seedAssigned caller locals σ τ

theorem returnCertificate_stratifiedDepth :
    (fun control =>
      (packet.returnCertificate answer assignedWF seedAssigned caller locals σ).stratifiedDepth
        (strata.headOrdinal registry) control) =
      headDepth packet.selected.ordinal (fun control =>
        answer.certificate.stratifiedDepth (strata.headOrdinal registry) control) := by
  funext control
  simp only [returnCertificate, RichCert.stratifiedDepth, RichCert.headDepth,
    RichCodeRecipe.headDepth, stratifiedHeadPolicy, headDepth]
  rw [packet.codeOwner.headOrdinal_eq]
  rfl

theorem returnCertificate_within
    (bounded : WithinAbove cutoff fuel packet.stratifiedDepth)
    (child : WithinAbove packet.bodyControls.cutoff packet.bodyControls.fuel
      (fun control => answer.certificate.stratifiedDepth (strata.headOrdinal registry) control)) :
    WithinAbove cutoff fuel (fun control =>
      (packet.returnCertificate answer assignedWF seedAssigned caller locals σ).stratifiedDepth
        (strata.headOrdinal registry) control) := by
  rw [returnCertificate_stratifiedDepth]
  exact rebuild packet.selected.ordinal_pos bounded child

end Return

/-- The newly exposed assigned-formation opening does not require another
reserve. At equal dependency cost the two empty-frame worlds are identical;
otherwise the actual original schedule strictly decreases. -/
theorem typeSite_covered
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    Covered (@EquationControlMeasure.Less strata.rules.length)
      packet.typeSite.worlds packet.bodySite.worlds := by
  have cost := packet.bodyNode.typeFormation_dependency_cost_le packet.bodyControls.ordered []
  change Covered _
    [EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key strata.rules.length packet.bodyControls.cutoff packet.bodyControls.fuel
        packet.bodyControls.ordered.constantCount (richSchedule .fundamental
          (Closure.close (packet.bodyNode.typeFormation.node.dependencyOrigin packet.bodyControls.ordered) []).cost)) []]
    [EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key strata.rules.length packet.bodyControls.cutoff packet.bodyControls.fuel
        packet.bodyControls.ordered.constantCount (richSchedule .fundamental
          (Closure.close (packet.bodyNode.dependencyOrigin packet.bodyControls.ordered) []).cost)) []]
  intro child member
  cases List.mem_singleton.mp member
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rcases Nat.eq_or_lt_of_le cost with equal | smaller
  · left
    rw [equal]
  · right
    exact original_child (richSchedule_strict smaller .fundamental .fundamental) _ _ _ _ _

theorem returnProvenance_sponsored
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichSupportedValue packet.selected.origin.source env U registry target
      packet.bodyNode [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (packet.value.type.instL assignedLevels) (.sort level))
    (locals : List Nat) (σ : Subst)
    (annotation : WorldCertProvenance strata answer.certificate)
    (bodyPaid : Sponsored frontier packet.bodySite.worlds)
    (childPaid : Sponsored frontier annotation.worlds) :
    Sponsored frontier
      (packet.returnProvenance answer assignedWF seedAssigned caller locals σ annotation).worlds := by
  rw [returnProvenance_worlds]
  apply Sponsored.merge _ childPaid
  intro child member
  obtain ⟨body, belongs, equal | smaller⟩ := packet.typeSite_covered child member
  · subst child
    exact bodyPaid body belongs
  · obtain ⟨sponsor, present, lower⟩ := bodyPaid body belongs
    exact ⟨sponsor, present,
      EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans smaller lower⟩

/-- The shared canonical input and actual lower-F answer produce the shared
assigned certificate with one joint annotation, semantics and caller bounds.
The answer is not replaced by a separately selected certificate. -/
theorem returnShared
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichSupportedValue packet.selected.origin.source env U registry target
      packet.bodyNode [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (.const name levels)
      (packet.value.type.instL assignedLevels))
    (locals : List Nat) (σ τ : Subst) (henv : env.Ordered)
    (inputType : WorldCertProvenance strata packet.certificate)
    (inputBody : WorldObsProvenance strata packet.body)
    (inputPaid : Sponsored frontier
      (packet.observationProvenance caller locals σ inputType inputBody).worlds)
    (inputBound : WithinAbove cutoff fuel (fun control =>
      (packet.observation caller locals σ).stratifiedDepth (strata.headOrdinal registry) control))
    (answerAnnotation : WorldCertProvenance strata answer.certificate)
    (answerPaid : Sponsored frontier answerAnnotation.worlds)
    (answerBound : WithinAbove packet.bodyControls.cutoff packet.bodyControls.fuel
      (fun control => answer.certificate.stratifiedDepth (strata.headOrdinal registry) control)) :
    let returned := packet.returnCertificate answer assignedWF seedAssigned
      caller.typeFormation.node locals σ
    ∃ annotation : WorldCertProvenance strata returned,
      annotation.worlds = packet.typeSite.worlds ++ answerAnnotation.worlds ∧
      Sponsored frontier annotation.worlds ∧
      WithinAbove cutoff fuel (fun control =>
        returned.stratifiedDepth (strata.headOrdinal registry) control) ∧
      TypeRelated env U registry target
        ((packet.value.type.instL assignedLevels).subst σ)
        ((packet.value.type.instL assignedLevels).subst τ) answer.support := by
  refine ⟨packet.returnProvenance answer assignedWF seedAssigned
    caller.typeFormation.node locals σ answerAnnotation, rfl, ?_, ?_, ?_⟩
  · exact packet.returnProvenance_sponsored answer assignedWF seedAssigned
      caller.typeFormation.node locals σ answerAnnotation
      (packet.observation_body_sponsored caller locals σ inputType inputBody inputPaid) answerPaid
  · apply packet.returnCertificate_within answer assignedWF seedAssigned
      caller.typeFormation.node locals σ _ answerBound
    rwa [packet.observation_stratifiedDepth] at inputBound
  · exact packet.returnCertificate_related answer assignedWF seedAssigned
      caller.typeFormation.node locals σ henv τ

end CanonicalDeltaPacket
end Lean4Lean.AnchoredSource.Adapted
