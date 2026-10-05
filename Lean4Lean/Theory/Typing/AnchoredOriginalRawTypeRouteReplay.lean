import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiDomainRouteStep

/-! Generated-frame evidence is separate from the finite raw alignment
history. Thus its actual frame leaves may be used as positive premises in
capture generation; semantic recursion remains solely in route replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}

private theorem environment_included {first second : List Closure}
    (included : ∀ closure ∈ first, closure ∈ second) : environmentCost first ≤ environmentCost second := by
  induction first with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    exact Nat.max_le.mpr ⟨environment_entry (included head List.mem_cons_self),
      ih (fun closure member => included closure (List.mem_cons_of_mem _ member))⟩

/-- Appending the route's actual closure ledger pays every original F/R
edge at a variable lookup. This theorem does NOT assert that any enclosing
projection already reserved the enlarged ledger. -/
theorem RawGeneratedTypeRoute.paid
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (origin : Origin) (environment : List Closure)
    (included : ∀ closure ∈ route.reserve, closure ∈ environment) :
    route.schedule < richSchedule .fundamental (Closure.close origin environment).cost := by
  have reserveBound := environment_included included
  have positivity := origin.weight_pos
  have parent : 1 + environmentCost environment ≤ (Closure.close origin environment).cost := by
    simpa only [Closure.cost, Nat.one_mul] using
      Nat.mul_le_mul_right (1 + environmentCost environment) positivity
  have schedule := route.schedule_le
  simp only [richSchedule, RichPhase.code] at schedule ⊢
  omega

theorem RawGeneratedTypeRoute.paid_appended
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (origin : Origin) (previous : List Closure) :
    route.schedule < richSchedule .fundamental (Closure.close origin (route.reserve ++ previous)).cost :=
  route.paid origin _ (fun _ member => List.mem_append_left _ member)

/-- Replay consumes exactly the smaller original clauses named by the raw
history, preserving the requested owner type-support and paired source
frames. Pi-domain edges use sort-true supports, as produced by owner F. -/
theorem RawGeneratedTypeRoute.replay
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    (generated : route.Generated base commonCaps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (calls : route.Calls base commonCaps limit) (scheduled : route.schedule < limit)
    (incoming : BoundedParameterReply base commonCaps start left commonLeft commonRight
      (profile : Profile n) (environmentCost initial))
    (sorted : profile.HasType (.sort true)) :
    Nonempty (BoundedParameterReply base commonCaps start right commonLeft commonRight profile
      (environmentCost final)) := by
  match route with
  | .identity .. => exact ⟨incoming⟩
  | .same left right lf rf initial frame =>
    rw [Calls.eq_def] at calls
    rw [schedule.eq_def] at scheduled
    simp only [Closure.cost] at scheduled
    exact incoming.reindexAt henv lf rf sorted frame.realization
      (generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])) frame.closed scheduled calls
  | .equality graph original forward ordered below initial =>
    rw [Calls.eq_def] at calls
    rw [schedule.eq_def] at scheduled
    simp only [Closure.cost] at scheduled
    obtain ⟨result, _, _⟩ := incoming.equality graph original forward henv ordered below formed sorted scheduled calls
    exact ⟨result⟩
  | .typedEquality graph original left expressionEq lf ordered below initial frame =>
    rw [Calls.eq_def] at calls
    rw [schedule.eq_def] at scheduled
    exact incoming.typedEquality graph original left expressionEq henv hscoped lf ordered below formed {
      locals := frame.locals, available := frame.available, realization := frame.realization
      capped := generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])
      closed := frame.closed } sorted
      (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) scheduled)
      (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) scheduled) calls.1 calls.2.1 calls.2.2
  | .assigned left right lf rf initial frame =>
    rw [Calls.eq_def] at calls
    rw [schedule.eq_def] at scheduled
    simp only [Closure.cost] at scheduled
    exact incoming.assignedAt henv lf rf sorted {
      locals := frame.locals, available := frame.available, realization := frame.realization
      capped := generated.frames frame.box (by simp [RawGeneratedTypeRoute.frames])
      closed := frame.closed } scheduled calls
  | .trans first second =>
    rw [Calls.eq_def] at calls
    rw [schedule.eq_def] at scheduled
    have wellFormed := generated.wellFormed
    rw [WellFormed.eq_def] at wellFormed
    have firstGenerated : first.Generated base commonCaps :=
      ⟨wellFormed.1, fun boxed member => generated.frames boxed
        (by simpa only [RawGeneratedTypeRoute.frames] using List.mem_append_left second.frames member)⟩
    have secondGenerated : second.Generated base commonCaps :=
      ⟨wellFormed.2, fun boxed member => generated.frames boxed
        (by simpa only [RawGeneratedTypeRoute.frames] using List.mem_append_right first.frames member)⟩
    obtain ⟨middle⟩ := first.replay firstGenerated henv hscoped formed calls.1
      (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) scheduled) incoming sorted
    exact second.replay secondGenerated henv hscoped formed calls.2
      (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) scheduled) middle sorted
  | .piDomain left right below child =>
    rw [Calls.eq_def] at calls
    rw [schedule.eq_def] at scheduled
    have wellFormed := generated.wellFormed
    rw [WellFormed.eq_def] at wellFormed
    have childGenerated : child.Generated base commonCaps :=
      ⟨wellFormed, by simpa only [frames] using generated.frames⟩
    exact BoundedParameterReply.piDomainStep left right below henv hscoped formed
      (fun answer sorted => child.replay childGenerated henv hscoped formed calls scheduled answer sorted) incoming sorted
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
    have childGenerated : whole.Generated base commonCaps :=
      ⟨wellFormed.1, fun boxed member => generated.frames boxed (by
        rw [frames.eq_def]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))⟩
    have historyGenerated : history.Generated base commonCaps := {
      source := generated.frames sourceFrame.box (by rw [frames.eq_def]; exact List.mem_cons_self)
      header := generated.frames headerFrame.box (by rw [frames.eq_def]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      whole := childGenerated }
    rw [Calls.eq_def] at calls
    rw [schedule.eq_def] at scheduled
    have reserveEq : claimedSeedReserve = history.argumentSeedReserve := by
      simpa only [history, OriginalApplyPiHistory.argumentSeedReserve, OriginalApplyPiHistory.argumentDomainRoute,
        RawGeneratedTypeRoute.reserve, OriginalApplyPiHistory.final, originalNativePiRouteSide,
        EndpointState.dependencyOrigin] using wellFormed.2
    obtain ⟨answer⟩ := history.replayApplicationReplyStep (field := field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph historyGenerated noBinders sourceBound
      henv hscoped headerBelow formed calls.2
      (fun childScheduled {queryRank} {origin} {queryProfile} answer sorted => whole.replay childGenerated henv hscoped formed calls.1 childScheduled answer sorted)
      scheduled incoming sorted
    exact ⟨by simpa only [OriginalApplyPiHistory.outputEnvironment, OriginalApplyPiHistory.destination,
      OriginalApplyPiHistory.final, history, reserveEq] using answer⟩
termination_by sizeOf route

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
