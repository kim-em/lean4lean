import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixMinimum
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaFrameOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqDelayedSupply
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqConsumedArgument
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFrameProgress
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaBodyCut

/-! # Eq exposure reaches a non-level root inside a minimum eta body

Minimize over all finite stages, read every outer singleton directly, and
bypass administrative and proof-argument eta cases. The retained native eta
must itself contain a non-level cut on its original constant-headed body.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
open private singleton_spine_readout
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaBodyCut
variable [Params]

/-- The original lower equation holds, or an original-prefix eta of arity at
most four contains a non-level body-spine cut. The whole path has minimum
primitive count among all finite stages; every prefix and suffix is retained.
The outer and body decompositions have exact costs, and the body path is
globally minimal with smaller count (via `CountedEtaBodySpineCut.smaller_minimum`).
The body and its application continuation are jointly minimal with variable
body endpoint; identity and constant expansion are excluded at the selected
inner root, with its typing and the actual argument's context substitution retained.
Both singleton forms read the original lower equation. The remaining inner
root is native function eta. Its exact selected source now retains an
`EqHeadCompletion`, constructed from the original component history, recovered
eta domain and body component history (`CountedEtaBodySpineCut.complete_root`).
This is derived ancestry at that root, not an added hypothesis. Completing the
next fresh body requires a remaining target argument; a completed five-slot
prefix needs separate handling for its fresh proof major. The smaller typed
minimum now retains this exact alternative: its source has a completion, or
its pre-eta prefix has exactly five arguments and retains that completion,
and its fresh argument is proved to be the literal proof marker
(`nested_eta_completed_frames`). Its actual inner recovery and domain-sort
witnesses are also retained. The same smaller source now uniformly carries
`EqTargetPrefixCompletion`: its first at most five arguments retain iterated
completion even when the fresh sixth proof argument has no target inhabitant.
This invariant survives further native eta opening at every arity, actual
component computation, computed used annotations and component-body eta
consumption beyond the target vector. `EqSpineConsumptionHistory.target_prefix_completion`
composes the component, eta and consumption cases for every finite recorded
spine history. `EqTargetPrefixCompletion.eta_execution` derives retained and
consumed branches from actual counted execution with arbitrary pending
arguments; retained completion uses the changed displayed annotation.
`consumed_eta_minimum` retains a strictly smaller completed post-beta minimum,
and `eta_typed_minimum` preserves the bounded prefix while descending through
another native eta at any arity. Identity expansion at any tracked root of
a minimum is now excluded through arbitrary mixed frames by
`pi_inert_frames_minimum_no_identity`: deleting the wrapper simulates the
current path and all enclosing frames without increasing their primitive
count, while its insertion costs one. The corresponding constant case is
excluded by `pi_inert_frames_minimum_no_constant`, using actual source typing
to recover the lower payload before unused-binder certificate descent. Its
competitor keeps the same continuation predicate through every mixed frame.
Thus both administrative expansion cases are excluded at tracked roots of
typed minima. `TargetPrefixEqSpineCut.eq_or_smaller` now combines both
exclusions with direct positive singleton readout and structure/core exclusion:
every completed non-level cut reads the original equation or yields a strictly
smaller completed minimum. The cut now retains completion of the whole
supplied spine as well as its selected prefix. `CountedEtaFrameOrigin` retains
the exact lambda, annotation, body and argument-vector paths in both branches.
`eta_origin_minimum` uses that supply to return through an actually consumed
component-only body to its completed post-beta source with the parent
continuation. The other branches retain the smaller fresh-body minimum;
`pi_inert_native_retained_eta_frame_origin` now reconstructs an origin at a
later substitution/application after a retained component body, allowing any
remaining typed continuation and either retained or consumed outcome. Its
positive earlier insertion supplies strict decrease without immediate carrier
exposure. An arbitrary intervening retained prefix
is now represented by `PiInertNextApplicationAtHole`: it records a tracked
application/binder hole and interpreted substitution into its precise binder
context, with the original continuation predicate preserved on every competitor. Ordinary eta
origin survives at that location. `SpineBinderHole.focus_path` reifies the
whole subsequent computation as a typed continuation at the inner term;
every competitor maps back to the original path at the same count.
`EqTargetPrefixComponentMinimum.focus_next` consequently gives a typed
minimum at the substituted Eq spine with the remaining budget. Target
agreement at that substituted spine is still open, as is a well-founded
progress argument for arbitrary moves whose preceding component path costs
zero. At an actual primitive inserting a lambda,
`pi_inert_lambda_hole_body_minimum` instead charges that insertion and gives
a strictly smaller fresh-body minimum beneath any application/binder hole.
`EqTargetPrefixCompletion.hole_cut_eq_or_smaller` classifies a completed
non-level root at such a location: positive singleton guards read the target;
administrative, core and structure cases are excluded; native eta gives that
strictly smaller completed body. The spine-cut classifier now uses this
general result and retains its existing consumed-body return shortcut.
Completion must still be established at the actual selected root.
`EqPrefixSpecializationAt.eta_delayed_compute_inst` now preserves the chosen
binder image across an agreeing outer frame, computed annotation, later body
components and actual argument consumption. Its retained and consumption
frames are derived from the original shared supply and actual computations;
no new image-compatibility premise is added. The result gives post-beta
specialization and exact erased arguments.
`eta_delayed_compute_spine_inst` also restores the independently computed
remaining source arguments, preserving their original target agreement and
the assigned type of the whole supplied application. Its output retains the
full actual supply for later consumption. The outer frame must already carry
target agreement; deriving and linking those witnesses throughout every
actual global history, including unused insertions, remains open.
`minimum_frontier` iterates this decrease
by strong induction and reaches a component-only current path with completion
at both endpoints. The conclusion retains this actual
`EqTargetPrefixComponentMinimum` within the smaller budget, including its
next application at such an exact substituted hole and its
original typed continuation and unrestricted competitor minimum. The actual
application maps now retain their construction in `PiInertEndpointMap`: each
is identity or consumes exactly one binder. Focusing beneath a retained prefix
records the literal finite binder lift of that same map. Consequently
`focus_next` derives `SingleEndpointSubstitution` at the selected inner spine,
without a new assumption on the global path. Agreement is therefore needed
for identity or one actual consumption beneath retained binders, rather than
an unrestricted endpoint substitution. The consumed argument's agreement
with the chosen target image is still to be derived from its linked ancestry.
The focused map now retains `PiInertEndpointContext`, recording every
annotation computation above the actual identity or consumed-binder map.
Its identity case derives `PiInertContextHistory` from those annotations. `AnnotationContextCompute.descend_insertion`
replays those changes through unused insertions at arbitrary depths, and
`EqTargetPrefixCompletion.context_history` preserves completion through the
whole finite history. `focus_next_completed_or_consumed` therefore gives
completion at the actual next substituted spine or leaves one binder
consumption. Identity moves no longer require an agreement hypothesis; their
possible equal cost still needs a progress argument. Consumption of an
unused ambient binder is now handled by `PiInertEndpointContext.unused_ancestry`:
the recorded annotations descend through that exact insertion, leaving a
lower context history. `UnusedTargetPrefixCompletion.consume` cancels the
lifted bounded prefix independently of the argument; later source arguments
may still use the binder. The remaining branch of
`focus_next_completed_or_consumed` explicitly lacks a completion below the
consumed binder at its derived depth. Target agreement for that remaining
argument is still open in general. `ContextSubstitution.realize_one` now
recovers an actual argument at the original displayed type by normalizing
older-variable identity erasures. `EqSpecializationFrame.inst_iff` identifies
the exact remaining image equality. In a chosen semantic source realization,
`ProofEndpointContext.frame` derives it automatically for proof-valued
consumption and lifts that agreement through every recorded retained annotation.
`endpoint_context_frame_or_unwitnessed_domain` therefore returns the complete
transported specialization or the actual consumed base binder without a Prop
domain witness. This requires a target assignment for the chosen source context;
arbitrary unused insertions in the global completion do not provide one.
`ProofEndpointContext.retraction` removes that assignment requirement for
head-loss readout: after replaying the retained annotations, reverse renaming
fixes every retained source variable. `EqTargetPrefixRetraction.read_loss`
therefore reads a nonstructural head loss through arbitrary unused insertions.
The actual frontier's `focus_next_retracted_or_unwitnessed_domain` now carries
that witness or identifies its consumed base binder without a Prop-domain
witness. This is not ordinary completion in the consumed context.
`EqTargetPrefixRetraction` now survives actual component computations, eta
opening and supplied eta consumption. Its counted execution and positive
singleton readout support `minimum_frontier`, which removes every non-level
cut by strict descent. `eq_or_retracted_frontier_or_consumed` follows the
ordinary frontier through its actual next scope move and applies that descent:
it yields target equality, a later retraction component frontier, or the
particular consumed base binder without a Prop-domain witness. Propagation
through the later frontier's next scope map and equal-cost progress remain open.
The reverse map now permits any exact context renaming: variable renaming
reflects wrapped constant heads, including identity wrappers, so readout needs
no single-insertion restriction. `EqTargetPrefixRetraction.pullback` composes
these maps. `consume_proof_binder` and `EqRepeatedProofHistory.retraction`
preserve the witness through arbitrarily many further topmost proof-binder
consumptions, interleaved with component and eta histories. The actual base
endpoint classifier retains only its consumed domain without a Prop witness.
The general-renaming witness alone does not record how to replay changed
retained annotations above later consumption. `ContextEmbedding` now retains
the actual insertion, binder extension and composition structure. Its annotation
transport replays every source change in the embedded target while preserving
the map. `EqTargetPrefixEmbedding.proof_endpoint` consequently preserves the
same constructed witness through any further proof endpoint, at arbitrary
retained depth and with its recorded annotation computations. Component and
eta histories and the strict minimum descent retain that construction.
The strict descent now uses the full supplied vector at selected eta roots.
`consumed_eta_spine_minimum` returns to the parent scope after a component-only
body, preserving the exact full arity and original continuation. Thus selecting
an underfilled prefix no longer loses arguments already present in its supply.
`retained_eta_spine_minimum` advances a component-only retained body to its
actual endpoint under the final annotation, with cost equal to the remaining
outer continuation and one actual retained frame. Completion transports along
the recorded annotation history. A non-level body cut still uses the strictly
smaller fresh-body minimum. These alternatives are integrated into
`EmbeddedTargetPrefixEqSpineCut.eq_or_smaller`; unrelated later scope moves
still require their own agreement and progress argument.
`embedding_scope_frontier` starts from ordinary completion and reaches the
actual next scope move: it preserves the embedding invariant or records the
consumed base domain without a Prop witness. Repeated proof-valued scope moves
therefore need no new agreement assumption. Non-proof argument agreement and
termination through equal-cost scope moves remain open.
`PiInertFrameMinimum.idle_refocus` now proves a concrete obstruction to a naive
frame measure: empty identity refocusing preserves source, context and cost
while adding a frame. Empty-hole `focus_minimum` therefore retains the original
path directly. `PiInertRunFrames.next_application` removes selected frames
before any refocusing. For a direct application whose target prefix is full,
`direct_application_progress` keeps the actual whole suffix and its embedding:
the primitive cost decreases, or at equal cost the selected tail has one fewer
frame. This does not yet cover underfilled prefixes or restoration of retained
lambda wrappers; those cases still need their actual supply history or a
progress-preserving execution decomposition.
Component-only
transitions through enclosing wrappers still need target agreement from their
actual histories; coverage of arbitrary wrapped-body histories remains open. `read_full_eta_loss_in_minimum` reads a head-losing root
in the full-prefix body component history through any iterated insertions.
In the proof-major case, a head-losing primitive
reached through its body component history either reads the original equation
or is native structure eta (`EqHeadCompletion.read_proof_major_loss`). This
uses descent through the fresh proof binder, not an assumed lower proof;
the structure alternative is excluded when the actual prefix and sort-ending
minimum are retained (`read_proof_major_loss_in_minimum`). The returned smaller
source now explicitly lacks every rigid-tail assignment: those assignments
survive arbitrary mixed typed continuations and contradict the original
output's sort typing. Preserving argument ancestry through arbitrary later
wrapper histories remains open. The conclusion also retains a positive, strictly smaller
`PiInertTypedContinuationMinimum` under both eta binders, derived by
`CountedEtaBodySpineCut.nested_eta_typed_frames` from the selected inner eta.
It records actual typing at every application source in its continuation;
`pi_inert_eta_typed_continuation_frames` preserves that execution through
further consumed or retained eta cuts. `PiInertTypedContinuationMinimum.advance`
follows its actual execution through any finite retained-lambda prefix to the
next application unless its current endpoint already exposes a carrier. The
next application inherits full minimality and the prefix preserves joint
competitors (`PiInertNextApplication.joint_minimum`). Its count is positive:
`eq_positive` excludes zero-cost Eq exposure through arbitrary mixed frames.
The conclusion additionally selects an `IteratedAmbientSingletonFailure`
within that smaller budget. Its exact hole follows function positions, retained
lambda bodies and identity payloads. The selected root excludes native
structure recovery at every finite stage: its hypothetical rigid assignment
would propagate through the tracked hole and back along the typed prefix,
contradicting the sort-ending execution. Forgetting these restrictions recovers
`EqHeadCompletionFailure` and then `TypedWrappedHeadLoss`. The root also excludes
level conversion, constant expansion, identity expansion and native function
eta, even across arbitrary mixed continuation frames. Canonical typing forces
the sixth Eq argument to erase to proof; registered iota patterns require a
visible constructor there. `typed_eq_no_core_root` therefore excludes ordinary
core reduction at the selected root without any ancestry or arity premise.
The root must be one of the two singleton forms, whose code generation then
derives its arity bound of five (`typed_nonstructural_eq_head_loss_singleton`). The selected loss can occur later
than the original nested eta. `EqHeadCompletion.read_loss` derives both short
arity and semantic readout from one completing realization, allowing ambient
unused binders. `IteratedAmbientEqCompletion.read_loss` extends this readout
to every finite sequence of additional unused insertions, including blocks
at different depths. Each primitive descends at its original stage before
semantic readout. Thus this branch explicitly lacks any such iterated
completion at the selected root. Deriving completion ancestry through the actual history
remains open; the root's typing alone does not supply it. `CountedEtaBodySpineCut.nested_eta_cut`
supplies a smaller body/continuation minimum in both the consumed and retained
lambda cases. `CountedEtaBodySpineCut.nested_eta_frames` retains concrete typed
application and annotated lambda frames ending at this same original output.
For a retained component-only body, `pi_inert_native_retained_eta_later_body_cut`
extracts a smaller body/suffix minimum from the actual later path to an exposed
output. If the short function remains constant-headed, that body has a typed
non-level root. `CountedLaterEtaBodyCut.eq_guarded` classifies the later short
Eq root as singleton or native eta while retaining the same cut.
`CountedLaterEtaBodyCut.read_singleton` reads both singleton guards through a
retained source-to-target Eq specialization, leaving the same native eta cut.
Its `read_singleton_of_origin` variant obtains the later Pi assignment from
the retained typed eta origin, without requiring renewed native recovery.
Supplying that specialization throughout arbitrary mixed frames and eliminating
the remaining eta recursively remain open. `EqPrefixSpecializationAt.compute_inst` transports a retained
specialization through the two endpoint histories when the actual argument's
agreement with the chosen target binder image has been established.
`EqPrefixSpecializationAt.eta_compute_inst` derives that agreement when the
prefix and its next actual argument share the retained target completion.
`EqPrefixSpecializationAt.eta_compute_spine_inst` also retains the independently
computed remaining source arguments, the whole spine's assigned type and exact
erasure. `compute_annotation` preserves the chosen specialization across a
computed retained annotation. `CountedLaterEtaBodyCut.eq_or_eta_of_completion`
then derives short-prefix inputs from that whole completion and reads its
singleton cases. `EqSpecializationFrame` records actual endpoint substitution
and semantic agreement of the target assignments. Its witnesses compose, lift
under retained binders and arise from context conversion or computed argument
supply (`eta_supply_frame`). `eq_or_eta_after_frame` reads the later cut after
such a composed frame. Deriving agreeing frames throughout the actual arbitrary
mixed continuation remains open at the component-only frontier. The completed
non-level cuts are handled by the strict minimum descent above. -/
theorem pi_inert_eq_exposure_eq_or_global_eta_spine_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (Eargs : args = (([α,a,M,m,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof])
    (HT : ControlTyping (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out) (HE : CarrierExposure out) :
    env.IsDefEq univs Γ a b α ∨
    (∃ stage cost ls pre pending A B u k cp ct,
      ScopedComputeCount (PiInertStage D stage) cost (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out ∧
      (∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out → cost ≤ j) ∧
      cp+1+ct = cost ∧ List.Forall₂ (· ≈ ·) [v,w] ls ∧ pre.length ≤ 4 ∧
      List.Forall₂ (ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ')) args (pre ++ pending) ∧
      ScopedComputeCount (PiInertStage D stage) cp (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args)
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
      TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) ∧
      k < stage ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) (.forallE A B) ∧
      DomainSort (proofEraseCtx Γ') A u ∧
      ScopedComputeCount (PiInertStage D stage) ct (proofEraseCtx Γ')
        (ProofShape.mkApps (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1)
          (etaArgument u))) pending) out ∧
      CountedEtaBodySpineCut D stage (proofEraseCtx Γ') ``Eq.rec ls pre A u pending out ct
        (fun rootStage Ξ source target => EqEtaRemainingRoot D rootStage Ξ source target ∧
          EqHeadCompletion Γ v w [α,a,M,m,b] Ξ source) ∧
      ∃ innerA innerU bodyLs bodyPre smaller, 0 < smaller ∧ smaller < cost ∧
        PiInertTypedContinuationMinimum D (proofEraseCtx Γ') out (innerA :: A :: proofEraseCtx Γ')
          (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) smaller ∧
        IteratedAmbientSingletonFailure D Γ v w [α,a,M,m,b] smaller ∧
        (EqHeadCompletion Γ v w [α,a,M,m,b] (innerA :: A :: proofEraseCtx Γ')
            (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) ∨
          bodyPre.length = 5 ∧ etaArgument innerU = .proof ∧
            EqHeadCompletion Γ v w [α,a,M,m,b] (A :: proofEraseCtx Γ')
            (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre)) ∧
        EqTargetPrefixCompletion Γ v w [α,a,M,m,b] (innerA :: A :: proofEraseCtx Γ')
          (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) ∧
        EqTargetPrefixComponentMinimum D Γ v w [α,a,M,m,b] (proofEraseCtx Γ') out smaller ∧
        ∃ innerStage innerB,
          ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: proofEraseCtx Γ')
            (ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre) (.forallE innerA innerB) ∧
          DomainSort (A :: proofEraseCtx Γ') innerA innerU ∧
          ∀ c, env.Rigid c → ¬ RigidTailTyping (innerA :: A :: proofEraseCtx Γ')
            (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) c) := by
  classical
  have HCout := HT.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) R
  obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have Eargs' : args = [(proofErase Γ α).liftN count offset,
      (proofErase Γ a).liftN count offset, (proofErase Γ M).liftN count offset,
      (proofErase Γ m).liftN count offset, (proofErase Γ b).liftN count offset, .proof] := by
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using Eargs
  obtain ⟨initialCost, RC₀⟩ := R.count
  obtain ⟨stage, cost, RC, hminAll⟩ := RC₀.minimal_across_stages
  have hmin := hminAll stage
  rcases RC.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls, args', EO, _, _⟩ | ⟨ls, pre, pending, target, cp, ct, hcost, HL, HA, RP, H, HN, RT⟩
  · exact ((carrier_exposure_ne_eqRec heq HE) (by rw [EO, constHead_mkApps]; rfl)).elim
  · have hcostExact : cp+1+ct = cost := by
      have RT' := ((ScopedComputeCount.base H).mkApps ScopedArgumentsCount.refl).trans RT
      rw [← ProofShape.mkApps_append] at RT'
      have HM := hmin (cp+1+ct) (by
        simpa only [Nat.add_zero, ← Nat.add_assoc] using RP.trans RT')
      omega
    have HA6 := Eargs' ▸ HA
    have hd : ErasedScopedPrimitiveCertificateDescent
        (ErasedStaticStructureEtaExpansionStage D stage) (ErasedStaticStructureEtaExpansionStage D stage) :=
      erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage
    by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D stage)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target
    · have HG := HQ.spine_component_guard (HA6.imp (fun _ _ R => R.mono pi_inert_stage_embed))
      have HGl := proofErase_computed_joint_carrier_certificate_descend hd hΓ hΓ' W ha hb HG
      exact .inl (proofErase_computed_joint_carrier_reflect hd.descent hΓ ha hb HGl)
    · have HC : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) pre) target := by
        rintro (HC | HC)
        · exact pi_inert_eq_prefix_no_core_root hreg hoff hRec HA6 HC
        · exact HN HC
      have hp : ErasedScopedPrimitiveDescent (PiInertStage D stage) :=
        ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs stage)
      have HTsrc : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
        obtain ⟨Γ₀, e₀, hΓ₀, EΓ₀, ht₀, Ee₀⟩ := HT
        exact ⟨Γ₀, e₀, _, hΓ₀, EΓ₀, ht₀, Ee₀⟩
      have HS := HT.compute hp RP.forget
      rw [ProofShape.mkApps_append] at HS
      have HTpre := RP.forget.spine_cut_source_typed hp HTsrc
      have hbypass : ∀ {Recovery},
          (ConstantExpansion (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∨
           NativeIdentityExpansion Recovery (proofEraseCtx Γ')
             (ProofShape.mkApps (.const ``Eq.rec ls) pre) target) → False := by
        intro Recovery HX
        obtain ⟨j, hj, RB⟩ := pi_inert_expansion_prefix_count_bypass heq hs HTpre HX RT HE
        have HM := hmin _ (RP.trans (by simpa only [ProofShape.mkApps_append] using RB))
        omega
      rcases static_other_spine_root H.1 HC HQ
          (fun H => HS.no_masked_structure_spine hd.descent H) with HC | ⟨k, hk, HG | HI | Heta⟩
      · exact (hbypass (Recovery := ErasedStaticStructureEtaExpansionStage D stage) (.inl HC)).elim
      · exact .inl (singleton_spine_readout heq hs hΓ hΓ' W ht hn Eargs HL HA HG)
      · exact (hbypass (.inr HI)).elim
      · have HTwhole : TypedSource (proofEraseCtx Γ')
            (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) pending) := by
          obtain ⟨Γ₀, e₀, hΓ₀, EΓ₀, ht₀, Ee₀⟩ := HS
          exact ⟨Γ₀, e₀, _, hΓ₀, EΓ₀, ht₀, Ee₀⟩
        have hnotProof : ∀ rest, pending ≠ .proof :: rest := by
          intro rest EP
          obtain ⟨j, hj, RB⟩ := pi_inert_proof_eta_spine_count_eliminate heq hs
            (erased_static_structure_eta_expansion_stage_descent heq hs k)
            (EP ▸ HTwhole) Heta (EP ▸ RT) HE
          have HM := hmin _ (RP.trans (by simpa only [EP, ProofShape.mkApps_append] using RB))
          omega
        cases Heta with
        | intro RN SD =>
          rename_i outerA outerB outerU
          have HB := globally_minimal_pi_inert_eta_body_spine_cut heq hs
            (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole RN SD
            (by simpa only [ProofShape.mkApps_append] using RP) H RT hcost hminAll HE
          have hpending : 0 < pending.length := by
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, RX, _⟩ := HB
            cases RX with | cons => simp
          have hlength := HA.length_eq
          rw [Eargs'] at hlength
          simp only [List.length_cons, List.length_nil, List.length_append] at hlength
          have hshort : pre.length ≤ 4 := by
            by_contra hlong
            have hfive : pre.length = 5 := by omega
            have Hdrop : (pre ++ pending).drop 5 = pending := by
              rw [← hfive, List.drop_left]
            have HD : List.Forall₂ (ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ'))
                [.proof] pending := by
              simpa only [List.drop_succ_cons, List.drop_zero, Hdrop] using
                Lean4Lean.List.forall₂_drop HA6 5
            cases HD with | cons HP HD =>
              cases HD
              exact hnotProof [] (by rw [HP.pi_inert_proof_fixed])
          have HP := eq_head_completion_of_probe_components heq hs hΓ hΓ' W ht hn HL
            (by simpa only [Eargs] using HA) (by omega) HTpre
          have HPfresh := HP.eta
            (erased_static_structure_eta_expansion_stage_descent heq hs k) hΓ ht
            (by simpa only [List.length_cons, List.length_nil] using (show pre.length < 5 by omega)) RN SD
          rcases CountedEtaBodySpineCut.read_singleton heq hs hΓ hΓ' W ht hn HL
              (by simpa only [Eargs] using HA) hshort HTpre RN SD
              (HB.eq_guarded heq hs hreg hoff hRec hshort) with Hlower | HB'
          · exact .inl Hlower
          · have HBcompleted := HB'.complete_root heq hs hΓ HPfresh
            obtain ⟨innerA, innerU, bodyLs, bodyPre, smaller, hsmall, HM, HPnested, innerStage, innerB, RNinner, SDinner⟩ :=
              HBcompleted.nested_eta_completed_frames heq hs
                (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole RN SD H hΓ ht
                (cp := cp) (cost := cost) (by omega)
            have HPuniform : EqTargetPrefixCompletion Γ v w [α,a,M,m,b]
                (innerA :: outerA :: proofEraseCtx Γ')
                (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) := by
              rcases HPnested with HPbody | ⟨_, _, HPpre⟩
              · exact .of_completion (.base HPbody)
              · exact (EqTargetPrefixCompletion.of_completion (.base HPpre)).eta
                  heq hs hΓ ht RNinner SDinner
            have Hhead : RetainedConstHead ``Eq.rec
                (.app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU)) := by
              apply RetainedConstHead.app
              simpa only [ProofShape.liftN_mkApps, ProofShape.liftN] using
                (RetainedConstHead.const (ls := bodyLs)).mkApps (bodyPre.map (·.liftN 1))
            rcases (HM.tracked_head_loss heq hs Hhead.wrapped HE HCout).eq_or_completion_failure
                heq hs hreg hoff hRec hΓ ht with Hlower | Hfailure
            · exact .inl Hlower
            · rcases (Hfailure.singleton heq hreg hoff hRec).eq_or_iterated_ambient_failure
                  heq hs hreg hoff hRec hΓ ht with Hlower | Hfailure'
              · exact .inl Hlower
              · have ES : .app ((ProofShape.mkApps (.const ``Eq.rec bodyLs) bodyPre).liftN 1) (etaArgument innerU) =
                    ProofShape.mkApps (.const ``Eq.rec bodyLs) (bodyPre.map (·.liftN 1) ++ [etaArgument innerU]) := by
                  simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append, ProofShape.mkApps]
                rcases (ES ▸ HPuniform).minimum_frontier heq hs hreg hoff hRec hΓ ht (ES ▸ HM) HE HCout with
                  Hlower | Hfront
                · exact .inl Hlower
                · exact .inr ⟨stage, cost, ls, pre, pending, _, _, _, k, cp, ct,
                    RC, hminAll, hcostExact, HL, hshort, HA, RP, HTpre, hk, RN, SD, RT, HBcompleted,
                    innerA, innerU, bodyLs, bodyPre, smaller, HM.eq_positive heq Hhead HE, hsmall, HM,
                    Hfailure', HPnested, HPuniform, Hfront, innerStage, innerB, RNinner, SDinner,
                    fun _ hr => HM.no_rigid_tail heq hs HCout hr⟩

end Lean4Lean.VEnv.Strengthening
