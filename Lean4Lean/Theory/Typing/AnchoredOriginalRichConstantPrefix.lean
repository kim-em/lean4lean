import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalPrefix

/-! Peel assigned code along an actual constant/application prefix. Each
conversion uses its original equality backwards; formation reindex calls
retain the two exact occurrences of the same source expression. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalTail
set_option backward.isDefEq.respectTransparency false

def PeelCalls
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : DirectPrefixRoute sourceEnv U source expression first last)
    (locals : List Nat) (σ : Subst) (available : Valuation) : Prop :=
  match route with
  | .done _ => True
  | .expose reference rest =>
    FormationRestoreCall env U registry target ordered captured (reference.dependencyOrigin ordered)
      reference.typeFormation.node reference.expose.typeFormation.node locals σ available ∧
    PeelCalls env registry target ordered captured rest locals σ available
  | .forward wf original term rest =>
    EqualityRestoreCall env U registry target ordered captured
      ((EndpointState.convert (.forward wf original) term).dependencyOrigin ordered)
      original false locals σ available ∧
    FormationRestoreCall env U registry target ordered captured
      ((EndpointState.convert (.forward wf original) term).dependencyOrigin ordered)
      (.ref (.left original)) term.typeFormation.node locals σ available ∧
    PeelCalls env registry target ordered captured rest locals σ available
  | .backward wf original term rest =>
    EqualityRestoreCall env U registry target ordered captured
      ((EndpointState.convert (.backward wf original) term).dependencyOrigin ordered)
      original true locals σ available ∧
    FormationRestoreCall env U registry target ordered captured
      ((EndpointState.convert (.backward wf original) term).dependencyOrigin ordered)
      (.ref (.right original)) term.typeFormation.node locals σ available ∧
    PeelCalls env registry target ordered captured rest locals σ available

private theorem conversion_pair
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (original : Derivation sourceEnv U source A B (.sort level))
    (term : EndpointState sourceEnv U source expression assigned) :
    (Closure.close (original.dependencyOrigin ordered) captured).cost +
      (Closure.close (term.typeFormation.node.dependencyOrigin ordered) captured).cost <
    (Closure.close (.rule [term.dependencyOrigin ordered, original.dependencyOrigin ordered]) captured).cost := by
  have pair := original_two_children (term.dependencyOrigin ordered) (original.dependencyOrigin ordered) [] captured
  have bound := term.typeFormation_dependency_cost_le ordered captured
  omega

/-- The terminal producer is the fixed actual primitive header bridge. The
route worker adds no source-synthesis premise, and composes all intermediate
semantic relations with the exact reconstructed destination certificate. -/
theorem peelCode
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : DirectPrefixRoute sourceEnv U source expression first last)
    (calls : route.PeelCalls env registry target ordered captured locals σ available)
    {destination : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel)}
    (finish : RichCodeTransfer env U registry target last.typeFormation.node destination
      locals rightLocals σ τ available rightAvailable) :
    RichCodeTransfer env U registry target first.typeFormation.node destination
      locals rightLocals σ τ available rightAvailable := by
  intro relevant n profile footprint certificate resources
  induction route generalizing relevant n profile footprint with
  | done node => exact finish certificate resources
  | expose reference rest ih =>
    rcases reference.exposure_formation_cost_reserve ordered captured with same | smaller
    · change RichCert sourceEnv env U registry target reference.typeFormation.node locals σ relevant profile footprint at certificate
      rw [← same] at certificate
      obtain ⟨result⟩ := ih calls.2 finish certificate resources
      exact ⟨{ result with related := result.related }⟩
    · have schedule := richSchedule_strict smaller RichPhase.expressionReindex RichPhase.fundamental
      have reverseSchedule : richSchedule .expressionReindex
          ((Closure.close (reference.typeFormation.node.dependencyOrigin ordered) captured).cost +
           (Closure.close (reference.expose.typeFormation.node.dependencyOrigin ordered) captured).cost) <
          richSchedule .fundamental (Closure.close (reference.dependencyOrigin ordered) captured).cost := by
        simpa only [Nat.add_comm] using schedule
      obtain ⟨changed⟩ := calls.1 reverseSchedule certificate resources
      obtain ⟨result⟩ := ih calls.2 finish changed.certificate changed.resources
      exact ⟨{ result with related := changed.related.trans henv result.related }⟩
  | forward wf original term rest ih =>
    have child := richSchedule_strict
      (original_child_same_environment
        (show (original.dependencyOrigin ordered).weight <
          (Origin.rule [term.dependencyOrigin ordered, original.dependencyOrigin ordered]).weight from
          Origin.rule_child (by simp)) captured)
      RichPhase.fundamental RichPhase.fundamental
    obtain ⟨changed⟩ := calls.1 child certificate resources
    obtain ⟨body⟩ := calls.2.1 (richSchedule_strict (conversion_pair ordered captured original term) _ _)
      changed.certificate changed.resources
    obtain ⟨result⟩ := ih calls.2.2 finish body.certificate body.resources
    exact ⟨{ result with related := changed.related.trans henv (body.related.trans henv result.related) }⟩
  | backward wf original term rest ih =>
    have child := richSchedule_strict
      (original_child_same_environment
        (show (original.dependencyOrigin ordered).weight <
          (Origin.rule [term.dependencyOrigin ordered, original.dependencyOrigin ordered]).weight from
          Origin.rule_child (by simp)) captured)
      RichPhase.fundamental RichPhase.fundamental
    obtain ⟨changed⟩ := calls.1 child certificate resources
    obtain ⟨body⟩ := calls.2.1 (richSchedule_strict (conversion_pair ordered captured original term) _ _)
      changed.certificate changed.resources
    obtain ⟨result⟩ := ih calls.2.2 finish body.certificate body.resources
    exact ⟨{ result with related := changed.related.trans henv (body.related.trans henv result.related) }⟩

/-- A complete actual prefix terminating in the retained left constant
primitive. Its terminal R child is the computed earlier original header,
not a caller-selected destination or a semantic declaration interpretation. -/
theorem replayConstantLeftPrefix
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (lookup : sourceEnv.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (otherWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation sourceEnv U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (captured : List Closure)
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (route : DirectPrefixRoute sourceEnv U source (.const name levels) first
      (.ref (.left (.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient))))
    (calls : route.PeelCalls env registry target ordered captured locals σ available)
    (headerR : richSchedule .expressionReindex
      ((Closure.close (ambient.dependencyOrigin ordered) captured).cost +
       (Closure.close ((selectOriginalHeader ordered lookup levelsWF).original.dependencyOrigin
         (selectOriginalHeader ordered lookup levelsWF).ordered) []).cost) <
      richSchedule .fundamental
        (Closure.close ((Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
          captured).cost →
      RichCodeTransfer env U registry target (.ref (.left ambient))
        (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
        locals [] σ headerRealization available (fun _ => [])) :
    RichCodeTransfer env U registry target first.typeFormation.node
      (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
      locals [] σ headerRealization available (fun _ => []) := by
  apply route.peelCode henv ordered captured calls
  intro relevant n profile footprint certificate resources
  exact replayConstantHeader ordered lookup levelsWF otherWF count equivalent levelWF closed ambient
    captured certificate resources headerR

/-- The right endpoint retains the primitive's original seed header. The
universe display may differ; the actual source header is not relabelled. -/
theorem replayConstantRightPrefix
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (lookup : sourceEnv.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (otherWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation sourceEnv U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (captured : List Closure)
    {first : EndpointState sourceEnv U source (.const name otherLevels) assigned}
    (route : DirectPrefixRoute sourceEnv U source (.const name otherLevels) first
      (.ref (.right (.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient))))
    (calls : route.PeelCalls env registry target ordered captured locals σ available)
    (headerR : richSchedule .expressionReindex
      ((Closure.close (ambient.dependencyOrigin ordered) captured).cost +
       (Closure.close ((selectOriginalHeader ordered lookup levelsWF).original.dependencyOrigin
         (selectOriginalHeader ordered lookup levelsWF).ordered) []).cost) <
      richSchedule .fundamental
        (Closure.close ((Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
          captured).cost →
      RichCodeTransfer env U registry target (.ref (.left ambient))
        (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
        locals [] σ headerRealization available (fun _ => [])) :
    RichCodeTransfer env U registry target first.typeFormation.node
      (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
      locals [] σ headerRealization available (fun _ => []) := by
  apply route.peelCode henv ordered captured calls
  intro relevant n profile footprint certificate resources
  exact replayConstantHeader ordered lookup levelsWF otherWF count equivalent levelWF closed ambient
    captured certificate resources headerR

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure

theorem ConstantPrefix.directRef
    {reference : EndpointRef sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix (.ref reference)) :
    Nonempty (DirectPrefixRoute sourceEnv U source (.const name levels) (.ref reference) (.ref packet.reference)) :=
  packet.route.direct (fun _ _ equal => by cases equal) trivial

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
