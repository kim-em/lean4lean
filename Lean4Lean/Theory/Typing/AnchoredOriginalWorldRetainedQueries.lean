import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHeadDepth

/-! The actual queries retained by a generated frame, including dormant
histories. Numerical frame bounds alone cannot account for the foreign
originals inside these queries. This traversal exposes the exact stored
observers and certificates to the query-provenance invariant; it never
replaces them by an arbitrary list of world labels. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- Stored query fuel reachable through THIS positive generation witness,
including its retained owner, baseline, and history generations.

An identity base is deliberately opaque: its contribution is raw frame
`headDepth`, not the depth of a previous generation used to construct that
frame. `AmbientCaptureGenerated.headQueryInvariant` in
`AnchoredOriginalCapturedHeadQueryAmbient` eliminates the identity branch
without opening a capture; its public `headQuery` requires a capture graph.
Thus rebasing does not recover or reopen the old history witnesses.
`CappedGeneratedQueryReply.freezeBase` in `AnchoredOriginalGeneratedBaseFreeze`
returns only a query at the original base resources. A caller using that
sandbox must keep its original generation when returning; this definition
does not justify replacing that generation's hereditary bound by raw depth. -/
noncomputable def WorldGenerated.retainedDepth
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls)
    (policy : Name → Nat → Nat) : Nat := by
  induction generated with
  | weaken _ _ _ _ _ ih => exact ih
  | merge first second ih₁ ih₂ => exact max ih₁ ih₂
  | identity ambient sources controls environment => exact base.frame.headDepth policy
  | empty => exact 0
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact max (certificate.headDepth policy) ih
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    exact max (query.headDepth policy) (max (certificate.headDepth policy) ih)
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact max ((richGroupedEntriesRaw entries).headDepth policy) (max tailIH (max (max (seed.query.headDepth policy) seedIH) (max priorIH
      (max (((List.finRange history.route.frames.length).map (fun index => historyIH index)).foldr max 0)
        ((entries.attach.map (fun entry => ownerIH entry.val entry.property)).foldr max 0)))))

/-- Existential packaging changes neither an original node nor its query. -/
inductive StoredOriginalQuery (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) : Type where
  | observation
      {node : EndpointState sourceEnv U source expression assigned}
      (query : RichObs sourceEnv env U registry target node locals σ profile footprint) :
      StoredOriginalQuery env U registry target
  | certificate
      {node : EndpointState sourceEnv U source expression assigned}
      (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
      StoredOriginalQuery env U registry target

noncomputable def StoredOriginalQuery.headDepth (policy : Name → Nat → Nat) :
    StoredOriginalQuery env U registry target → Nat
  | .observation query => query.headDepth policy
  | .certificate query => query.headDepth policy

noncomputable def HeaderValueAlignment.storedQueries
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
    List (StoredOriginalQuery env U registry target) :=
  [.certificate answer.value.certificate, .certificate answer.aligned.certificate]

noncomputable def HeaderRichTail.storedQueries
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    (tail : HeaderRichTail header field major env registry target context locals σ τ available) :
    List (StoredOriginalQuery env U registry target) :=
  match tail with
  | .nil => []
  | .skip tail .. => tail.storedQueries
  | .push tail _ _ _ _ answer .. => answer.storedQueries ++ tail.storedQueries

noncomputable def HeaderBinderFrame.storedQueries
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available) :
    List (StoredOriginalQuery env U registry target) :=
  match frame with
  | .captured tail => tail.storedQueries
  | .bind tail _ _ _ certificate .. => .certificate certificate :: tail.storedQueries

mutual
noncomputable def RawOriginalRichFrame.storedQueries
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    List (StoredOriginalQuery env U registry target) :=
  match frame with
  | .nil => []
  | .header _ _ frame => frame.storedQueries
  | .bind tail _ certificate .. => .certificate certificate :: tail.storedQueries
  | .capture tail _ _ _ _ _ query _ certificate .. =>
      .observation query :: .certificate certificate :: tail.storedQueries
  | .group tail _ _ _ entries => entries.storedQueries ++ tail.storedQueries
  | .reserve frame _ => frame.storedQueries
  | .merge left right => left.storedQueries ++ right.storedQueries
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntry.storedQueries
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    List (StoredOriginalQuery env U registry target) :=
  match entry with
  | .mk _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ query _ answer =>
      frame.storedQueries ++ .observation query :: answer.storedQueries
termination_by sizeOf entry
decreasing_by all_goals simp_wf <;> omega

noncomputable def RawRichGroupEntries.storedQueries
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
    List (StoredOriginalQuery env U registry target) :=
  match entries with
  | .nil => []
  | .cons entry tail => entry.storedQueries ++ tail.storedQueries
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega
end

/-- Identity rebasing retains the queries actually in its base frame.
It cannot recover an old generation witness's dormant histories; a caller
returning from that sandbox must retain its original generation witness. -/
noncomputable def WorldGenerated.retainedQueries
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) :
    List (StoredOriginalQuery env U registry target) := by
  induction generated with
  | weaken _ _ _ _ _ ih => exact ih
  | merge first second ih₁ ih₂ => exact ih₁ ++ ih₂
  | identity ambient sources controls environment => exact base.frame.raw.storedQueries
  | empty => exact []
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact .certificate certificate :: ih
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    exact .observation query :: .certificate certificate :: ih
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact (richGroupedEntriesRaw entries).storedQueries ++ tailIH ++
      (.observation seed.query :: seedIH) ++ priorIH ++
      ((List.finRange history.route.frames.length).flatMap (fun index => historyIH index)) ++
      (entries.attach.flatMap (fun entry => ownerIH entry.val entry.property))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
