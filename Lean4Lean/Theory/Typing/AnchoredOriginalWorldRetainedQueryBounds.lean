import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedQueries
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance

/-! Bounds and positive opening provenance on the exact queries retained by
a generated frame. These are the query-owned dependencies which must survive
R-to-F continuations as well as ordinary visible frame dependencies. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable def StoredOriginalQuery.maximumDepth (policy : Name → Nat → Nat)
    (queries : List (StoredOriginalQuery env U registry target)) : Nat :=
  queries.foldr (fun query depth => max (query.headDepth policy) depth) 0

@[simp] theorem StoredOriginalQuery.maximumDepth_nil (policy : Name → Nat → Nat) :
    maximumDepth (env := env) (U := U) (registry := registry) (target := target) policy [] = 0 := rfl

@[simp] theorem StoredOriginalQuery.maximumDepth_cons (policy : Name → Nat → Nat)
    (query : StoredOriginalQuery env U registry target) (rest) :
    maximumDepth policy (query :: rest) = max (query.headDepth policy) (maximumDepth policy rest) := rfl

theorem StoredOriginalQuery.maximumDepth_append (policy : Name → Nat → Nat)
    (first second : List (StoredOriginalQuery env U registry target)) :
    maximumDepth policy (first ++ second) = max (maximumDepth policy first) (maximumDepth policy second) := by
  induction first with
  | nil => simp
  | cons query rest ih => simp only [List.cons_append, maximumDepth_cons, ih, Nat.max_assoc]

theorem StoredOriginalQuery.maximumDepth_flatMap (policy : Name → Nat → Nat)
    (entries : List α) (queries : α → List (StoredOriginalQuery env U registry target)) :
    maximumDepth policy (entries.flatMap queries) =
      (entries.map (fun entry => maximumDepth policy (queries entry))).foldr max 0 := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp only [List.flatMap_cons, maximumDepth_append, List.map_cons, List.foldr_cons, ih]

theorem StoredOriginalQuery.headDepth_le_maximumDepth (policy : Name → Nat → Nat)
    {query : StoredOriginalQuery env U registry target} {queries}
    (member : query ∈ queries) : query.headDepth policy ≤ maximumDepth policy queries := by
  induction queries with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem HeaderValueAlignment.storedQueries_depth
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) (policy : Name → Nat → Nat) :
    StoredOriginalQuery.maximumDepth policy answer.storedQueries = answer.headDepth policy := by
  simp only [storedQueries, StoredOriginalQuery.maximumDepth_cons, StoredOriginalQuery.maximumDepth_nil,
    StoredOriginalQuery.headDepth, Nat.max_zero, headDepth]

theorem HeaderRichTail.storedQueries_depth
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    (tail : HeaderRichTail header field major env registry target context locals σ τ available)
    (policy : Name → Nat → Nat) :
    StoredOriginalQuery.maximumDepth policy tail.storedQueries = tail.headDepth policy := by
  induction tail with
  | nil => rfl
  | skip _ _ _ _ _ ih => exact ih
  | push tail domain location lineage owner answer arguments needs bounded covered ih =>
    simp only [storedQueries, headDepth, StoredOriginalQuery.maximumDepth_append,
      HeaderValueAlignment.storedQueries_depth, ih]

theorem HeaderBinderFrame.storedQueries_depth
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (policy : Name → Nat → Nat) :
    StoredOriginalQuery.maximumDepth policy frame.storedQueries = frame.headDepth policy := by
  induction frame with
  | captured tail => exact tail.storedQueries_depth policy
  | bind tail domain location lineage certificate resources typed arguments needs bounded covered ih =>
    simp only [storedQueries, headDepth, StoredOriginalQuery.maximumDepth_cons, StoredOriginalQuery.headDepth, ih]

mutual
theorem RawOriginalRichFrame.storedQueries_depth
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (policy : Name → Nat → Nat) :
    StoredOriginalQuery.maximumDepth policy frame.storedQueries = frame.headDepth policy := by
  match frame with
  | .nil => simp only [RawOriginalRichFrame.storedQueries, RawOriginalRichFrame.headDepth, StoredOriginalQuery.maximumDepth_nil]
  | .header _ _ frame => simpa only [RawOriginalRichFrame.storedQueries, RawOriginalRichFrame.headDepth] using frame.storedQueries_depth policy
  | .bind tail _ certificate .. =>
    simp only [RawOriginalRichFrame.storedQueries, RawOriginalRichFrame.headDepth, StoredOriginalQuery.maximumDepth_cons,
      StoredOriginalQuery.headDepth, tail.storedQueries_depth policy]
  | .capture tail _ _ _ _ _ query _ certificate .. =>
    simp only [RawOriginalRichFrame.storedQueries, RawOriginalRichFrame.headDepth, StoredOriginalQuery.maximumDepth_cons,
      StoredOriginalQuery.headDepth, tail.storedQueries_depth policy]
  | .group tail _ _ _ entries =>
    simp only [RawOriginalRichFrame.storedQueries, RawOriginalRichFrame.headDepth, StoredOriginalQuery.maximumDepth_append,
      tail.storedQueries_depth policy, entries.storedQueries_depth policy]
  | .reserve frame _ => simpa only [RawOriginalRichFrame.storedQueries, RawOriginalRichFrame.headDepth] using frame.storedQueries_depth policy
  | .merge left right =>
    simp only [RawOriginalRichFrame.storedQueries, RawOriginalRichFrame.headDepth, StoredOriginalQuery.maximumDepth_append,
      left.storedQueries_depth policy, right.storedQueries_depth policy]
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntry.storedQueries_depth
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input)
    (policy : Name → Nat → Nat) :
    StoredOriginalQuery.maximumDepth policy entry.storedQueries = entry.headDepth policy := by
  match entry with
  | .mk _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ query _ answer =>
    simp only [RawRichGroupEntry.storedQueries, RawRichGroupEntry.headDepth, StoredOriginalQuery.maximumDepth_append,
      StoredOriginalQuery.maximumDepth_cons, StoredOriginalQuery.headDepth,
      frame.storedQueries_depth policy, answer.storedQueries_depth policy]
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

theorem RawRichGroupEntries.storedQueries_depth
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (policy : Name → Nat → Nat) :
    StoredOriginalQuery.maximumDepth policy entries.storedQueries = entries.headDepth policy := by
  match entries with
  | .nil => simp only [RawRichGroupEntries.storedQueries, RawRichGroupEntries.headDepth, StoredOriginalQuery.maximumDepth_nil]
  | .cons entry tail =>
    simp only [RawRichGroupEntries.storedQueries, RawRichGroupEntries.headDepth, StoredOriginalQuery.maximumDepth_append,
      entry.storedQueries_depth policy, tail.storedQueries_depth policy]
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

/-- The hereditary numerical bound measures precisely this finite collection
of retained queries, including the prior, seed, route, and owner histories. -/
theorem WorldGenerated.retainedQueries_depth
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls)
    (policy : Name → Nat → Nat) :
    StoredOriginalQuery.maximumDepth policy generated.retainedQueries = generated.retainedDepth policy := by
  induction generated with
  | weaken _ _ _ _ _ ih => exact ih
  | merge first second ih₁ ih₂ =>
    change StoredOriginalQuery.maximumDepth policy (first.retainedQueries ++ second.retainedQueries) =
      max (first.retainedDepth policy) (second.retainedDepth policy)
    rw [StoredOriginalQuery.maximumDepth_append, ih₁, ih₂]
  | identity ambient sources controls environment =>
    exact base.frame.raw.storedQueries_depth policy
  | empty => rfl
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    change max (certificate.headDepth policy) (StoredOriginalQuery.maximumDepth policy generated.retainedQueries) =
      max (certificate.headDepth policy) (generated.retainedDepth policy)
    rw [ih]
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    change max (query.headDepth policy) (max (certificate.headDepth policy)
      (StoredOriginalQuery.maximumDepth policy generated.retainedQueries)) =
      max (query.headDepth policy) (max (certificate.headDepth policy) (generated.retainedDepth policy))
    rw [ih]
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    change StoredOriginalQuery.maximumDepth policy
      ((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries ++
        (.observation seed.query :: seedGenerated.retainedQueries) ++ priorGenerated.retainedQueries ++
        ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries)) ++
        (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))) =
      max ((richGroupedEntriesRaw entries).headDepth policy) (max (generated.retainedDepth policy)
        (max (max (seed.query.headDepth policy) (seedGenerated.retainedDepth policy))
          (max (priorGenerated.retainedDepth policy)
            (max (((List.finRange history.route.frames.length).map (fun index => (historyGenerated index).retainedDepth policy)).foldr max 0)
              ((entries.attach.map (fun entry => (owners entry.val entry.property).retainedDepth policy)).foldr max 0)))))
    simp only [StoredOriginalQuery.maximumDepth_append, StoredOriginalQuery.maximumDepth_cons,
      StoredOriginalQuery.headDepth, RawRichGroupEntries.storedQueries_depth,
      tailIH, seedIH, priorIH, StoredOriginalQuery.maximumDepth_flatMap, historyIH, ownerIH, Nat.max_assoc]

theorem WorldGenerated.retainedQuery_bound
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls)
    (bounded : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => generated.retainedDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (query : StoredOriginalQuery env U registry target) (member : query ∈ generated.retainedQueries) :
    EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) := by
  intro control active
  have actual := StoredOriginalQuery.headDepth_le_maximumDepth
    (stratifiedHeadPolicy (strata.headOrdinal registry) control) member
  rw [generated.retainedQueries_depth] at actual
  exact Nat.le_trans actual (bounded control active)

def StoredOriginalQuery.Provenance (strata : EquationStratification env) :
    StoredOriginalQuery env U registry target → Type
  | .observation query => WorldObsProvenance strata query
  | .certificate query => WorldCertProvenance strata query

noncomputable def StoredOriginalQuery.Provenance.worlds
    {query : StoredOriginalQuery env U registry target} (annotation : query.Provenance strata) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match query, annotation with
  | .observation _, annotation => WorldObsProvenance.worlds annotation
  | .certificate _, annotation => WorldCertProvenance.worlds annotation

/-- Each annotation belongs to the exact enumerated stored query. -/
inductive RetainedQueryProvenance (strata : EquationStratification env) :
    List (StoredOriginalQuery env U registry target) → Type where
  | nil : RetainedQueryProvenance strata []
  | cons (annotation : query.Provenance strata) (tail : RetainedQueryProvenance strata rest) :
      RetainedQueryProvenance strata (query :: rest)

noncomputable def RetainedQueryProvenance.worlds
    (annotations : RetainedQueryProvenance strata queries) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotations with
  | .nil => []
  | .cons annotation tail => annotation.worlds ++ tail.worlds

def RetainedQueryProvenance.append
    (first : RetainedQueryProvenance strata left) (second : RetainedQueryProvenance strata right) :
    RetainedQueryProvenance strata (left ++ right) :=
  match first with
  | .nil => second
  | .cons annotation tail => .cons annotation (tail.append second)

@[simp] theorem RetainedQueryProvenance.worlds_append
    (first : RetainedQueryProvenance strata left) (second : RetainedQueryProvenance strata right) :
    (first.append second).worlds = first.worlds ++ second.worlds := by
  induction first with
  | nil => rfl
  | cons annotation tail ih => simp only [append, worlds, ih, List.append_assoc]

/-- Opening a stored query uses its own annotation and the already retained
sponsors; it does not add a duplicate sponsor to the measured call frontier. -/
theorem RetainedQueryProvenance.sponsored_member
    (annotations : RetainedQueryProvenance strata queries)
    (bounded : EquationWorldClosureOrder.Sponsored frontier annotations.worlds)
    (member : query ∈ queries) :
    ∃ annotation : query.Provenance strata,
      EquationWorldClosureOrder.Sponsored frontier annotation.worlds := by
  induction annotations with
  | nil => cases member
  | cons annotation tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨annotation, fun child present => bounded child (List.mem_append_left _ present)⟩
    · exact ih (fun child present => bounded child (List.mem_append_right _ present)) member

abbrev WorldGenerated.QueryProvenance
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) : Type :=
  RetainedQueryProvenance strata generated.retainedQueries

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
