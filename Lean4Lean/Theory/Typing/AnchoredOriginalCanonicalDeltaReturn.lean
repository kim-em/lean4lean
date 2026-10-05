import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaType
import Lean4Lean.Theory.Typing.AnchoredOriginalDeltaBudgetSpend

/-! Return from two fixed canonical-RHS calls. The first computational answer
provides requested support and the actual right graded query. A second diagonal
answer at that retained raw query provides its support certificate. Both source
certificates stay at the computed formation of the SAME canonical RHS; the
caller receives a finite closed type wrapper rather than a cross-origin R call.
The alternating-order induction invoking those two calls is separate. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem footprint_empty {footprint : Footprint} (resources : footprint.Available (fun _ => [])) : footprint = [] := by
  cases footprint with
  | nil => rfl
  | cons entry tail => exact nomatch resources entry.1 entry.2 List.mem_cons_self

private theorem obsDepth_cast (same : before = after)
    (query : RichObs sourceEnv env U registry target node locals σ profile before) (current : Name → Bool) :
    (same ▸ query : RichObs sourceEnv env U registry target node locals σ profile after).nativeDepth current =
      query.nativeDepth current := by cases same; rfl

private theorem certDepth_cast (same : before = after)
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile before) (current : Name → Bool) :
    (same ▸ query : RichCert sourceEnv env U registry target node locals σ relevant profile after).nativeDepth current =
      query.nativeDepth current := by cases same; rfl

noncomputable def CanonicalDeltaPacket.returnRaw
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (raw : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw) :
    CanonicalDeltaPacket env U registry target strata name levels answer.rightQuery.raw where
  value := packet.value
  lookup := packet.lookup
  nameEq := packet.nameEq
  registered := packet.registered
  seedLevels := packet.seedLevels
  seedWF := packet.seedWF
  seedLength := packet.seedLength
  levelsWF := packet.levelsWF
  equivalent := packet.equivalent
  bodyClosed := packet.bodyClosed
  typeClosed := packet.typeClosed
  support := raw.support
  typeRealization := packet.bodyRealization
  bodyRealization := packet.bodyRealization
  certificate := footprint_empty raw.resources ▸ raw.certificate
  typed := raw.typed
  body := footprint_empty answer.rightQuery.resources ▸ answer.rightQuery.observation

theorem CanonicalDeltaPacket.returnRaw_depth
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (raw : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw)
    (current : Name → Bool) :
    (packet.returnRaw answer raw).nativeDepth current =
      max (answer.rightQuery.observation.nativeDepth current) (raw.certificate.nativeDepth current) +
        if current name then 1 else 0 := by
  simp only [returnRaw, CanonicalDeltaPacket.nativeDepth, obsDepth_cast, certDepth_cast]

/-- Pure semantic delta return at the requested support of the FIRST actual
body answer, including seed/displayed universe transport. -/
theorem CanonicalDeltaPacket.returnRelated
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile) :
    Related env U registry target (.const name levels) (.const name levels)
      (packet.value.type.instL levels) profile answer.support := by
  have delta : CanonicalHead.Trace registry (.const name packet.seedLevels) []
      (packet.value.value.instL packet.seedLevels) := by
    refine CanonicalHead.Trace.next (out := ⟨[], packet.value.value.instL packet.seedLevels⟩) ?_ .refl
    simp [CanonicalHead.step, CanonicalHead.spineStep, VExpr.getAppFnArgs,
      VExpr.getAppFnArgs.go, packet.lookup, packet.seedLength, packet.nameEq, VExpr.mkApps]
  have equality : env.IsDefEq U target (.const name packet.seedLevels)
      (packet.value.value.instL packet.seedLevels) (packet.value.type.instL packet.seedLevels) := by
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id packet.seedLength,
      packet.nameEq] using
      (IsDefEq.extra (Γ := target) packet.registered.2 packet.seedWF packet.seedLength)
  have body : Related env U registry target (packet.value.value.instL packet.seedLevels)
      (packet.value.value.instL packet.seedLevels) (packet.value.type.instL packet.seedLevels)
      profile answer.support := by
    simpa only [VDefVal.toDefEq, packet.bodyClosed.instL.subst_eq (σ := packet.bodyRealization) .zero,
      packet.typeClosed.instL.subst_eq (σ := packet.bodyRealization) .zero] using answer.related
  have seed : Related env U registry target (.const name packet.seedLevels) (.const name packet.seedLevels)
      (packet.value.type.instL packet.seedLevels) profile answer.support := by
    simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl,
      Profile.rename_refl] using
      Related.prependEndpoints (type := packet.value.type.instL packet.seedLevels)
        henv hscoped (.traced (CanonicalDataHead.Trace.ofLegacy delta))
        (.traced (CanonicalDataHead.Trace.ofLegacy delta)) (ProofInsertion.refl formed)
        (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using equality)
        (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using equality)
        (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl,
          Profile.rename_refl] using body)
  have code : TypeRelated env U registry target (packet.value.type.instL packet.seedLevels)
      (packet.value.type.instL packet.seedLevels) answer.support := by
    simpa only [VDefVal.toDefEq, packet.typeClosed.instL.subst_eq (σ := packet.bodyRealization) .zero] using answer.typeCode
  have same : List.Forall₂ (· ≈ ·) packet.seedLevels packet.seedLevels :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)
  have typeSame := EqUpToLevels.instL_expr packet.value.type packet.seedWF packet.seedWF same
  have typeShown := EqUpToLevels.instL_expr packet.value.type packet.seedWF packet.levelsWF packet.equivalent
  exact (seed.levels henv (.const packet.seedWF packet.levelsWF packet.equivalent)
    (.const packet.seedWF packet.levelsWF packet.equivalent)).convert henv answer.typed
      (code.levels henv typeSame typeShown)

/-- The returned raw query keeps the FIRST answer's actual general adapter;
the second call supplies only the needed raw support. -/
theorem CanonicalDeltaPacket.returnRawWithin
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichComputationalValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (raw : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw)
    (paid : Budgeted.HeadPaid name budgets)
    (queryBound : Budgeted.Within (Budgeted.spend name budgets) answer.rightQuery.observation.nativeDepth)
    (codeBound : Budgeted.Within (Budgeted.spend name budgets) raw.certificate.nativeDepth) :
    Budgeted.Within budgets (packet.returnRaw answer raw).nativeDepth := by
  have rebuilt := Budgeted.Within.rebuildDelta paid queryBound codeBound
  intro current fuel member
  rw [packet.returnRaw_depth answer raw]
  exact rebuilt current fuel member

/-- All three concrete output channels for a literal original constant
endpoint. Integration replaces these two prototype wrappers by the corresponding
positive rich constructors; no additional semantic source answer is needed. -/
structure CanonicalDeltaReturnResult
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ τ : Subst)
    (answer : RichComputationalValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile) where
  typeQuery : CanonicalDeltaTypeAt sourceEnv env U registry target strata caller.typeFormation.node
    locals σ true answer.support
  typeCode : TypeRelated env U registry target
    (assigned.subst σ) (assigned.subst σ) answer.support
  typed : profile.HasType answer.support
  related : Related env U registry target ((VExpr.const name levels).subst σ) ((VExpr.const name levels).subst τ)
    (assigned.subst σ) profile answer.support
  rightQuery : CanonicalDeltaAt sourceEnv env U registry target strata caller locals τ answer.rightQuery.raw
  adapter : GeneralNormalProfileAdapter env U registry target answer.rightQuery.raw
    (raiseProfile answer.rightQuery.rank answer.rightQuery.bound profile)

noncomputable def CanonicalDeltaPacket.assembleReturn
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (.const name levels) (packet.value.type.instL assignedLevels))
    (locals : List Nat) (σ τ : Subst)
    (answer : RichComputationalValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (raw : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw) :
    CanonicalDeltaReturnResult packet caller locals σ τ answer where
  typeQuery := packet.returnType answer.toRichSupportedValue assignedWF seedAssigned caller.typeFormation.node locals σ
  typeCode := packet.returnType_related henv answer.toRichSupportedValue assignedWF seedAssigned caller.typeFormation.node locals σ σ
  typed := answer.typed
  related := by
    have code : TypeRelated env U registry target
        (packet.value.type.instL packet.seedLevels) (packet.value.type.instL packet.seedLevels)
        answer.support := by
      simpa only [VDefVal.toDefEq, packet.typeClosed.instL.subst_eq (σ := packet.bodyRealization) .zero]
        using answer.typeCode
    have comparison := code.levels henv
      (EqUpToLevels.instL_expr packet.value.type packet.seedWF packet.levelsWF packet.equivalent)
      (EqUpToLevels.instL_expr packet.value.type packet.seedWF assignedWF seedAssigned)
    simpa only [VExpr.subst, packet.typeClosed.instL.subst_eq (σ := σ) .zero] using
      (packet.returnRelated henv hscoped formed answer.toRichSupportedValue).convert henv answer.typed comparison
  rightQuery := ⟨packet.returnRaw answer raw⟩
  adapter := answer.rightQuery.adapter

end Lean4Lean.AnchoredSource.Adapted
