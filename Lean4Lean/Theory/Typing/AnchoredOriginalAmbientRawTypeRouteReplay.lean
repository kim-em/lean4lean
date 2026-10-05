import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientParameterComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientPiDomainRouteStep

/-! Interpret the finite original history from the qualified mutual-induction
bank. Every query-selected intermediate frame retains positive hereditary
generation; no separate route-specific call supplier is required. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}

/-- Replay consumes exactly the smaller original clauses named by the raw
history, preserving the requested owner type-support and paired source
frames. Pi-domain edges use sort-true supports, as produced by owner F. -/
theorem RawGeneratedTypeRoute.replayAmbient
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    (generated : route.AmbientGenerated base commonCaps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit) (scheduled : route.schedule < limit)
    (incoming : AmbientBoundedParameterReply base commonCaps start left commonLeft commonRight
      (profile : Profile n) (environmentCost initial))
    (sorted : profile.HasType (.sort true)) :
    Nonempty (AmbientBoundedParameterReply base commonCaps start right commonLeft commonRight profile
      (environmentCost final)) := by
  match route with
  | .identity .. => exact ⟨incoming⟩
  | .same left right lf rf initial frame =>
    rw [schedule.eq_def] at scheduled
    simp only [Closure.cost] at scheduled
    exact incoming.reindexAt henv lf rf sorted frame.realization
      (generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])) frame.closed scheduled bank
  | .equality graph original forward ordered below initial =>
    rw [schedule.eq_def] at scheduled
    simp only [Closure.cost] at scheduled
    obtain ⟨result, _, _⟩ := incoming.equality graph original forward henv hscoped ordered formed sorted scheduled bank
    exact ⟨result⟩
  | .typedEquality graph original left expressionEq lf ordered below initial frame =>
    rw [schedule.eq_def] at scheduled
    exact incoming.typedEquality graph original left expressionEq henv hscoped lf ordered below formed {
      locals := frame.locals, available := frame.available, realization := frame.realization
      capped := (generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])).capped
      generation := generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])
      closed := frame.closed } sorted
      (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) scheduled)
      (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) scheduled) bank
  | .assigned left right lf rf initial frame =>
    rw [schedule.eq_def] at scheduled
    simp only [Closure.cost] at scheduled
    exact incoming.assignedAt henv lf rf sorted {
      locals := frame.locals, available := frame.available, realization := frame.realization
      capped := (generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])).capped
      generation := generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])
      closed := frame.closed } scheduled bank
  | .trans first second =>
    rw [schedule.eq_def] at scheduled
    obtain ⟨middle⟩ := first.replayAmbient generated.trans_left henv hscoped formed bank
      (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) scheduled) incoming sorted
    exact second.replayAmbient generated.trans_right henv hscoped formed bank
      (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) scheduled) middle sorted
  | .piDomain left right below child =>
    rw [schedule.eq_def] at scheduled
    have wellFormed := generated.wellFormed
    rw [WellFormed.eq_def] at wellFormed
    have childGenerated : child.AmbientGenerated base commonCaps :=
      ⟨wellFormed, by
        have ambient := generated.ambient
        rw [Ambient.eq_def] at ambient
        exact ambient,
        by simpa only [frames] using generated.frames⟩
    exact AmbientBoundedParameterReply.piDomainStep left right below henv hscoped formed
      (fun answer sorted => child.replayAmbient childGenerated henv hscoped formed bank scheduled answer sorted) incoming sorted
  | .applyPi (field := field) (major := major) (initial := initial) (domain := domain) (body := body)
      (function := function) (argument := argument) (result := result) (hu := hu) (hv := hv)
      (location := location) (sourceGraph := sourceGraph) (noBinders := noBinders)
      (headerInitial := headerInitial) (headerDomain := headerDomain) (headerBody := headerBody)
      (hcu := hcu) (hdv := hdv) (headerLocation := headerLocation) (headerGraph := headerGraph)
      (sourceOrdered := sourceOrdered) (headerOrdered := headerOrdered) (sourceBelow := sourceBelow)
      (headerBelow := headerBelow) (sourceFrame := sourceFrame) (headerFrame := headerFrame)
      (ownerInitial := ownerInitial) (sourceBound := sourceBound) (whole := whole)
      (claimedSeedReserve := claimedSeedReserve) =>
    let history : OriginalApplyPiHistory env registry target commonLeft commonRight
        (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph)
        (originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph) :=
      ⟨sourceOrdered, headerOrdered, sourceBelow, headerDomain, rfl, sourceFrame, headerFrame, whole⟩
    have wellFormed := generated.wellFormed
    rw [WellFormed.eq_def] at wellFormed
    have childGenerated : whole.AmbientGenerated base commonCaps :=
      ⟨wellFormed.1, by
        have ambient := generated.ambient
        rw [Ambient.eq_def] at ambient
        exact ambient, fun boxed member => generated.frames boxed (by
        rw [frames.eq_def]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))⟩
    have historyGenerated : history.AmbientGenerated base commonCaps := {
      source := generated.frames sourceFrame.box (by rw [frames.eq_def]; exact List.mem_cons_self)
      header := generated.frames headerFrame.box (by rw [frames.eq_def]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      whole := childGenerated }
    rw [schedule.eq_def] at scheduled
    have reserveEq : claimedSeedReserve = history.argumentSeedReserve := by
      simpa only [history, OriginalApplyPiHistory.argumentSeedReserve, OriginalApplyPiHistory.argumentDomainRoute,
        RawGeneratedTypeRoute.reserve, OriginalApplyPiHistory.final, originalNativePiRouteSide,
        EndpointState.dependencyOrigin] using wellFormed.2
    obtain ⟨answer⟩ := history.replayApplicationReplyStepAmbient (field := field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph historyGenerated noBinders sourceBound
      henv hscoped headerBelow formed bank
      (fun childScheduled {queryRank} {origin} {queryProfile} answer sorted => whole.replayAmbient childGenerated henv hscoped formed bank childScheduled answer sorted)
      scheduled incoming sorted
    exact ⟨by simpa only [OriginalApplyPiHistory.outputEnvironment, OriginalApplyPiHistory.destination,
      OriginalApplyPiHistory.final, history, reserveEq] using answer⟩
termination_by sizeOf route

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
