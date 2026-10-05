import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantInput
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantObservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineForward
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidEqualityInitialization
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidReadback
import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpineLive

/-! Complete conditional rigid-application adequacy. The actual original
sort typing seeds the backwards construction, its genuine earlier constant
header supplies the new shared query, and forwards reconstruction returns to
the same equality original. Only the global world banks remain semantic inputs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

/-- Turn the exact primitive seed into its shared rigid observation and
execute the finite forward trace. The opening world is paid by the actual
earlier declaration; the stored certificate retains all of its own worlds. -/
theorem WorldRigidBackwardTrace.observationOfWorldBanks
    {registry : CanonicalHead.Registry} {target source : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned} {location : Located root node}
    {prepared : RigidFamilySpine.Prepared env U registry target name levels (profile : Profile n)}
    {input : WorldAssignedQuery (registry := registry) (target := target)
      (context := location.contextDerivation initial) P controls baseline frontier node σ τ true profile}
    (trace : WorldRigidBackwardTrace (source := source) (P := P) initial controls baseline frontier
      σ τ name levels node location prepared input)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (inert : CanonicalDataHead.HeadInert registry name)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata P budget) :
    ∃ past : List RigidFamilyArgument,
    ∃ query : RichGradedResult sourceEnv env U registry target node input.locals σ input.available
        (.singleton (prepared.plan.atom name levels past)),
      Nonempty (ControlledStoredQuery controls frontier (.observation query.observation)) := by
  let seed := trace.primitiveSeed
  obtain ⟨packet, ⟨certificateReady⟩⟩ := seed.constantInputOfWorldBanks
    trace.primitiveSeed_relevant henv hscoped formed inert sourceClosed banks
  have headerPaid : Sponsored frontier
      [originalCallWorld (controls.atHeader packet.origin) .fundamental
        (.ref (packet.origin.familyHeader packet.seedWF).reference) .nil] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, smaller⟩ := seed.funded _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (originalClosedHeader_below controls packet.origin
        (.ref (packet.origin.familyHeader packet.seedWF).reference) (.ref seed.reference)
        baseline .fundamental .assignedComparison) smaller⟩
  let leaf : RichGradedResult sourceEnv env U registry target (.ref seed.reference)
      seed.input.locals σ seed.input.available (.singleton (seed.prepared.plan.atom name levels [])) := {
    rank := seed.rank, bound := Nat.le_refl _, raw := .singleton (seed.prepared.plan.atom name levels []),
    footprint := [], observation := packet.observation (.ref seed.reference) seed.input.locals σ,
    adapter := by
      simp only [raiseProfile_self]
      exact .refl _
    resources := by
      intro index need member
      cases member
    live := seed.prepared.live [] }
  have leafReady : ControlledStoredQuery controls frontier (.observation leaf.observation) :=
    packet.observationControlled controls (.ref seed.reference) seed.input.locals σ certificateReady headerPaid
  exact trace.forward henv hscoped formed leaf leafReady

/-- The exact public rigid-head injectivity conclusion. Registry inertness
is the syntactic fact furnished by `WF.canonicalRegistry`, not an inversion
or semantic interpretation hypothesis. No literal telescope is assumed. -/
theorem rawRigidInversionOfWorldBanks
    (strata : EquationStratification env) (henv : env.WF) (hscoped : registry.Scoped)
    (rigidHeads : ∀ name, env.Rigid name → CanonicalDataHead.HeadInert registry name)
    (formed : OnCtx Γ (env.IsType U)) (rigid : env.Rigid name)
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (equal : env.IsDefEqU U Γ (mkApps (.const name levels) arguments)
      (mkApps (.const name rightLevels) rightArguments))
    (typed : env.HasType U Γ (mkApps (.const name levels) arguments) (.sort level)) :
    List.Forall₂ (· ≈ ·) levels rightLevels ∧
      List.Forall₂ (env.IsDefEqU U Γ) arguments rightArguments := by
  obtain ⟨assigned, raw⟩ := equal
  obtain ⟨original⟩ := Derivation.reify (raw.strong henv formed)
  obtain ⟨typing⟩ := Derivation.reify (typed.strong henv formed)
  obtain ⟨context⟩ := ContextDerivation.reify (CtxStrong.strong henv formed)
  obtain ⟨locals, frame, baseline, flag, _relevant, input, ⟨trace⟩⟩ :=
    Derivation.rigidSpineOfWorldBanks strata henv hscoped formed context (.left typing) original unary replay
  obtain ⟨past, query, ⟨queryReady⟩⟩ := trace.observationOfWorldBanks henv hscoped formed
    (rigidHeads name rigid) (fun _ _ => trivial) replay
  exact input.rigidReadback original (worldAdequacyControls strata henv) baseline _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) past query queryReady henv hscoped formed unary

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
