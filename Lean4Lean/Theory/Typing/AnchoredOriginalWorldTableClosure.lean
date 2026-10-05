import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration

/-! Hereditary resource-table closure for exact right-frame reconstruction.
A merged resource table being atom closed does not make either branch atom
closed. The evidence below follows the actual positive generation, including
its dormant seed, prior, route occurrences and selected owner frames. It is
created by the atomized bind/capture producers, not inferred from a final
merged table or from its numerical environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Every recursive frame table is closed under the literal singleton needs
used by query extraction. Bind and capture retain the actual head table. -/
noncomputable def WorldGenerated.TablesClosed
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) : Prop := by
  induction generated with
  | identity => exact base.available.AtomClosed
  | empty => exact True
  | weaken _ _ _ _ _ ih => exact ih
  | merge _ _ left right => exact left ∧ right
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact ih ∧ Valuation.AtomClosed (fun _ : Nat => needs)
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    exact ih ∧ Valuation.AtomClosed (fun _ : Nat => needs)
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact tailIH ∧ seedIH ∧ priorIH ∧
      (∀ index, historyIH index) ∧ (∀ entry member, ownerIH entry member)

theorem atomizedNeeds_closed (needs : List Need) :
    Valuation.AtomClosed (fun _ : Nat => needs ++ needs.flatMap Need.singletons) :=
  Valuation.atomize_closed (fun _ => needs)

theorem groupedNeeds_closed
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue) :
    Valuation.AtomClosed (fun _ : Nat => entries.needs) := by
  intro index need member selected selectedMember
  obtain ⟨entry, member, needed⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨entry, member,
    (Valuation.atomize_closed (fun _ => [⟨entry.rank, entry.input⟩]))
      0 need needed selected selectedMember⟩

private theorem push_closed {available : Valuation} {needs : List Need}
    (tail : available.AtomClosed) (head : Valuation.AtomClosed (fun _ : Nat => needs)) :
    (available.push needs).AtomClosed := by
  intro index need member selected selectedMember
  cases index with
  | zero => exact head 0 need member selected selectedMember
  | succ index => exact tail index need member selected selectedMember

/-- The current frame's closure follows from the hereditary witness; no
closure of a parent merge is used to infer closure of its children. -/
theorem WorldGenerated.TablesClosed.closed
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {generated : WorldGenerated strata P base caps left right graph frame controls}
    (closed : generated.TablesClosed) : available.AtomClosed := by
  induction generated with
  | identity => exact closed
  | empty => exact fun _ _ member => False.elim (List.not_mem_nil member)
  | weaken _ _ _ _ _ ih => exact ih closed
  | merge first second left right =>
    intro index need member selected selectedMember
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (left closed.1 index need member selected selectedMember)
    · exact List.mem_append_right _ (right closed.2 index need member selected selectedMember)
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact push_closed (ih closed.1) closed.2
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    exact push_closed (ih closed.1) closed.2
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact push_closed (tailIH closed.1) (groupedNeeds_closed entries)

/-- The operative bind producer supplies an atom-closed head, normally
`needs ++ needs.flatMap Need.singletons`, and the actual tail witness. -/
theorem WorldGenerated.TablesClosed.bind
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail controls}
    (closed : generated.TablesClosed)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (annotation : VExpr) (displayed : A.subst raw = annotation)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (headClosed : Valuation.AtomClosed (fun _ : Nat => needs)) :
    (WorldGenerated.bind generated baseline capacity domain annotation displayed certificate resources typed
      arguments needs bounded covered).TablesClosed := ⟨closed, headClosed⟩

/-- Capturing an argument uses the same closed-head evidence as bind; query
interpretation and the captured owner's world labels do not establish it. -/
theorem WorldGenerated.TablesClosed.capture
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph tail controls}
    (closed : generated.TablesClosed)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument) (lineage : location.contextDerivation initial = context)
    (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
    (queryAvailable : argumentFootprint.Available available) (queryBound : n ≤ k)
    (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput
      (raiseProfile k queryBound (input : Profile n)))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true support footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (headClosed : Valuation.AtomClosed (fun _ : Nat => needs)) :
    (WorldGenerated.capture generated baseline capacity domain initial argument location lineage query queryAvailable
      queryBound queryAdapter certificate resources typed arguments needs bounded covered).TablesClosed :=
  ⟨closed, headClosed⟩

theorem WorldGenerated.TablesClosed.merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {firstFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ firstAvailable}
    {secondFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ secondAvailable}
    {first : WorldGenerated strata P base commonCaps commonLeft commonRight graph firstFrame controls}
    {second : WorldGenerated strata P base commonCaps commonLeft commonRight graph secondFrame controls}
    (left : first.TablesClosed) (right : second.TablesClosed) :
    (WorldGenerated.merge first second).TablesClosed := ⟨left, right⟩

theorem WorldGenerated.tablesClosed_empty
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (common : List VExpr) (left right : Subst) (below : sourceEnv ≤ env)
    (source : P sourceEnv) (controls : OriginalWorldControls strata sourceEnv) :
    (WorldGenerated.empty (base := base) (commonCaps := caps)
      common left right below source controls).TablesClosed := trivial

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
