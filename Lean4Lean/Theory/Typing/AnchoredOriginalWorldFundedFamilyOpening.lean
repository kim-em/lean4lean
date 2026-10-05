import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFundedFamilyHeaderData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank

/-! Execute the selected independent header with the enclosing unary bank.
The empty frame, its history, the source obligation, and the recursive-call
decrease are computed from the same funded header. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem WorldFundedFamilyHeader.openFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {frontier : List (World strata.rules.length)} {parent : World strata.rules.length}
    (selected : WorldFundedFamilyHeader strata U registry target name levels frontier parent)
    (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (callerPaid : Sponsored frontier [parent])
    (bank : WorldBoundedUnaryCallBank env U registry strata P (frontier ++ [parent])) :
    let node := EndpointState.ref (selected.header.origin.familyHeader selected.header.seedWF).reference
    let frame : OriginalRichFrame selected.header.origin.source env U registry target .nil
      [] selected.header.typeRealization selected.header.typeRealization (fun _ => []) := .nil
    ∃ data : WorldUnaryFrameData P selected.controls frontier frame .nil,
      Sponsored frontier [originalCallWorld selected.controls .fundamental node .nil] ∧
      WorldBoundedUnaryCallBank env U registry strata P
        (frontier ++ [originalCallWorld selected.controls .fundamental node .nil]) ∧
      ∃ answer : RichComputationalValue selected.header.origin.source env U registry target node
          [] selected.header.typeRealization selected.header.typeRealization (fun _ => []) selected.header.typeSupport,
        Nonempty (ControlledStoredQuery selected.controls frontier (.certificate answer.certificate)) ∧
        Nonempty (ControlledStoredQuery selected.controls frontier (.observation answer.rightQuery.observation)) := by
  dsimp only
  let node := EndpointState.ref (selected.header.origin.familyHeader selected.header.seedWF).reference
  let frame : OriginalRichFrame selected.header.origin.source env U registry target .nil
      [] selected.header.typeRealization selected.header.typeRealization (fun _ => []) := .nil
  let child := originalCallWorld selected.controls .fundamental node .nil
  have funded : CallBelow strata.rules.length (frontier ++ [child]) (frontier ++ [parent]) := by
    have step : CallBelow strata.rules.length [child] [parent] :=
      split_call (by intro world member; cases List.mem_singleton.mp member; exact selected.headerBelow)
    have prefixed : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ [child]) (sponsors ++ [parent]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact prefixed frontier
  have paid : Sponsored frontier [child] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, smaller⟩ := callerPaid parent (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans selected.headerBelow smaller⟩
  have below := selected.header.origin.sourceBelow.trans selected.header.below
  have data : WorldUnaryFrameData P selected.controls frontier frame .nil := by
    refine ⟨?_, ?_, ?_, .nil selected.controls, ?_⟩
    · simpa only [frame, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
        RawOriginalRichFrame.Ambient, and_true] using below
    · simpa only [frame, OriginalRichFrame.nil, RawOriginalRichFrame.AllSources, and_true] using
        sourceClosed _ below
    · intro query member
      simp only [frame, OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries, List.not_mem_nil] at member
    · exact ⟨(fun _ _ member => nomatch member), rfl, rfl⟩
  have closed : Valuation.AtomClosed (fun _ => []) := by
    intro index need member
    cases member
  let queryReady : ControlledStoredQuery selected.controls frontier
      (.observation (.code selected.header.typeCertificate)) := {
    annotation := .code selected.certificate.annotation
    within := by
      simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using selected.certificate.within
    sponsored := selected.certificate.sponsored }
  obtain ⟨answer, certificateReady, observationReady⟩ := (bank _ funded).computational node
    (EndpointProvenance.ofLocation .here .nil) selected.controls frame .nil .nil frontier
    (Nat.le_refl _) (Covered.refl _) rfl paid data closed formed .nil
    (.code selected.header.typeCertificate) (by intro index need member; cases member) queryReady
  exact ⟨data, paid, fun retained lower => bank retained (lower.trans funded),
    answer, certificateReady, observationReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
