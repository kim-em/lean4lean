import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpinePreparation
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRichComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFuture
import Lean4Lean.Theory.Typing.AnchoredLevels

/-! The input packet and primitive semantics of the shared rigid constant
observation. Its exact prepared demand, earlier-header certificate, and
independently equivalent universe packets are preserved by installation,
primitive equality interpretation, and future transport. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- `frozenLevels` belongs to the unchanged finite demand; `levels` belongs
to the current displayed constant; `seed` belongs to the retained original
header. The initializer may set the first two equal, but equality replay must
not require that equality. No telescope or semantic code answer is stored. -/
structure RichRigidConstantInput (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (name : Name)
    (frozenLevels levels : List VLevel) (plan : RigidFamilySpine n)
    (support : Profile n) where
  info : VConstant
  origin : ConstantHeaderOrigin sourceEnv name info
  lookup : env.constants name = some info
  inert : CanonicalDataHead.HeadInert registry name
  seed : List VLevel
  seedWF : ∀ level ∈ seed, level.WF U
  seedLength : seed.length = info.uvars
  frozenWF : ∀ level ∈ frozenLevels, level.WF U
  levelsWF : ∀ level ∈ levels, level.WF U
  seedFrozen : List.Forall₂ (· ≈ ·) seed frozenLevels
  frozenLevelsEq : List.Forall₂ (· ≈ ·) frozenLevels levels
  typeClosed : info.type.Closed
  realization : Subst
  certificate : RichCert origin.source env U registry target
    (.ref (origin.familyHeader seedWF).reference) [] realization true support []
  ready : plan.Ready env U registry target
  typed : (Profile.singleton (plan.atom name frozenLevels [])).HasType support

namespace RichRigidConstantInput

/-- Install the checked payload in the shared query grammar at an actual
constant endpoint in the same source environment. -/
def observation
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) :
    RichObs sourceEnv env U registry target node locals σ
      (.singleton (plan.atom name frozenLevels [])) [] :=
  .rigidFamily input.origin input.lookup input.inert input.seedWF input.seedLength
    input.frozenWF input.levelsWF input.seedFrozen input.frozenLevelsEq input.typeClosed
    plan input.certificate input.ready input.typed

/-- Equality changes only the displayed packet. The actual header query,
frozen argument program, full support, and code demand are retained verbatim. -/
def redisplay
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (frozenRight : List.Forall₂ (· ≈ ·) frozenLevels rightLevels) :
    RichRigidConstantInput sourceEnv env U registry target name frozenLevels rightLevels plan support :=
  { input with levelsWF := rightWF, frozenLevelsEq := frozenRight }

/-- Future transport moves exactly the stored code and finite key guards.
It does not execute a query or change the declaration/header universe seed. -/
noncomputable def future
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (henv : env.Ordered) (route : FutureInsertion env U target nextTarget ρ) :
    RichRigidConstantInput sourceEnv env U registry nextTarget name frozenLevels levels
      (plan.rename ρ) (support.rename ρ) where
  info := input.info
  origin := input.origin
  lookup := input.lookup
  inert := input.inert
  seed := input.seed
  seedWF := input.seedWF
  seedLength := input.seedLength
  frozenWF := input.frozenWF
  levelsWF := input.levelsWF
  seedFrozen := input.seedFrozen
  frozenLevelsEq := input.frozenLevelsEq
  typeClosed := input.typeClosed
  realization := input.realization.lift_r ρ
  certificate := by
    simpa only [Footprint.rename, List.map_nil] using input.certificate.future henv route
  ready := plan.ready_transport input.ready (Admitted.future henv route)
  typed := by
    have renamed := (Profile.rename_hasType_iff (ρ := ρ)).mpr input.typed
    simpa only [Profile.rename_singleton, ← RigidFamilySpine.atom_rename,
      List.map_nil] using renamed

/-- This is the primitive semantic step after the actual lower F call on the
retained header. The answer is indexed by that exact original header and full
support. The result keeps the frozen demand even when either runtime constant
uses a different, equivalent universe packet. -/
theorem fromHeaderAnswer
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (answer : RichCodeTransferResult env U registry target
      (.ref (input.origin.familyHeader input.seedWF).reference)
      (.ref (input.origin.familyHeader input.seedWF).reference)
      [] input.realization outputRealization (fun _ => []) true support)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (frozenRight : List.Forall₂ (· ≈ ·) frozenLevels rightLevels) :
    TypeRelated env U registry target (input.info.type.instL input.seed)
        (input.info.type.instL input.seed) support ∧
      Related env U registry target (.const name levels) (.const name rightLevels)
        (input.info.type.instL input.seed)
        (.singleton (plan.atom name frozenLevels [])) support := by
  have code : TypeRelated env U registry target (input.info.type.instL input.seed)
      (input.info.type.instL input.seed) support := by
    simpa only [input.typeClosed.instL.subst_eq (σ := input.realization) .zero,
      input.typeClosed.instL.subst_eq (σ := outputRealization) .zero] using answer.related
  have seedFrozen : env.IsDefEq U target (.const name input.seed)
      (.const name frozenLevels) (input.info.type.instL input.seed) :=
    .constDF input.lookup input.seedWF input.frozenWF input.seedLength input.seedFrozen
  have raw : env.IsDefEq U target (.const name frozenLevels)
      (.const name frozenLevels) (input.info.type.instL input.seed) :=
    seedFrozen.symm.trans seedFrozen
  have frozen := plan.supported henv hscoped input.ready formed input.inert
    (past := []) (values := []) .nil raw input.typed code
  exact ⟨code, frozen.levels henv
    (.const input.frozenWF input.levelsWF input.frozenLevelsEq)
    (.const input.frozenWF rightWF frozenRight)⟩

/-- A primitive constDF may itself assign another equivalent header packet.
Its support is transported from the same lower answer, without retagging the
prepared demand or asking for an independent assigned-code semantic answer. -/
theorem fromHeaderAnswerAt
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (answer : RichCodeTransferResult env U registry target
      (.ref (input.origin.familyHeader input.seedWF).reference)
      (.ref (input.origin.familyHeader input.seedWF).reference)
      [] input.realization outputRealization (fun _ => []) true support)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (frozenRight : List.Forall₂ (· ≈ ·) frozenLevels rightLevels)
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) input.seed assignedLevels) :
    TypeRelated env U registry target (input.info.type.instL assignedLevels)
        (input.info.type.instL assignedLevels) support ∧
      Related env U registry target (.const name levels) (.const name rightLevels)
        (input.info.type.instL assignedLevels)
        (.singleton (plan.atom name frozenLevels [])) support := by
  obtain ⟨code, related⟩ := input.fromHeaderAnswer henv hscoped formed answer rightWF frozenRight
  have same : List.Forall₂ (· ≈ ·) input.seed input.seed :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ => rfl)
  have original := EqUpToLevels.instL_expr input.info.type input.seedWF input.seedWF same
  have changed := EqUpToLevels.instL_expr input.info.type input.seedWF assignedWF seedAssigned
  exact ⟨code.levels henv changed changed,
    related.convert henv input.typed (code.levels henv original changed)⟩

end RichRigidConstantInput
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
