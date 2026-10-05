import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationStep
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameDepth

/-! A captured body carries finite actual argument queries. Their unfolding
control is a maximum, so splitting one query into many local needs consumes
no extra declaration fuel. All filters constrain the same returned capture. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
variable {available : Valuation}

noncomputable def RichArgumentSupply.nativeDepth (current : Name → Bool)
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs) : Nat :=
  match supply with
  | .nil => 0
  | .cons value tail => max (value.observation.nativeDepth current) (tail.nativeDepth current)

@[simp] theorem RichGradedResult.nativeDepth_localDemand (current : Name → Bool)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (need : Need) (bound : need.rank ≤ n)
    (included : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    (result.localDemand need bound included).observation.nativeDepth current =
      result.observation.nativeDepth current := rfl

/-- Every replacement is drawn from the same original argument output; no
new semantic interpretation is hidden in a local-demand projection. -/
theorem RichArgumentSupply.nativeDepth_fromResult (current : Name → Bool)
    (argument : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    (RichArgumentSupply.fromResult argument needs bounded covered).nativeDepth current ≤
      argument.observation.nativeDepth current := by
  induction needs with
  | nil => exact Nat.zero_le _
  | cons need rest ih =>
    simp only [RichArgumentSupply.fromResult, RichArgumentSupply.nativeDepth,
      RichGradedResult.nativeDepth_localDemand]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, ih _ _⟩

theorem RichArgumentSupply.lookup_allDepth
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs)
    (member : need ∈ needs) :
    ∃ value : RichGradedResult sourceEnv env U registry target node locals σ available need.profile,
      ∀ current, value.observation.nativeDepth current ≤ supply.nativeDepth current := by
  induction supply with
  | nil => cases member
  | cons value tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact ⟨value, fun _ => Nat.le_max_left _ _⟩
    · obtain ⟨value, bounded⟩ := ih member
      exact ⟨value, fun current => Nat.le_trans (bounded current) (Nat.le_max_right _ _)⟩

noncomputable def RichApplicationCapture.nativeDepth (current : Name → Bool)
    (capture : RichApplicationCapture sourceEnv env U registry target body argument locals σ available needs support) : Nat :=
  max (capture.certificate.nativeDepth current) (capture.replacements.nativeDepth current)

theorem RichNativeRow.captureResult_allDepth
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (row : RichNativeRow sourceEnv env U registry target domain body locals σ available (key : Key n) support)
    {argument : EndpointState sourceEnv U source a A}
    (argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available key.input)
    (answer : RichCodeTransferResult env U registry target body body (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (a.subst σ))
      (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) true support) :
    ∃ capture : RichApplicationCapture sourceEnv env U registry target body argument locals σ available
        (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) support,
      ∀ current, capture.nativeDepth current ≤
        max (answer.certificate.nativeDepth current) (argumentQuery.observation.nativeDepth current) := by
  have bounded : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      need.rank ≤ n := fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := fun need member atom present =>
    row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  obtain ⟨packed, outside, pack, included, resources⟩ :=
    Footprint.pack_available answer.resources bounded covered
  refine ⟨⟨answer.footprint, answer.certificate, answer.resources, n, packed, outside, pack, resources,
    RichArgumentSupply.fromResult argumentQuery answer.footprint.localNeeds
      (fun need member => (pack.localNeeds need member).1)
      (fun need member atom present => included atom ((pack.localNeeds need member).2 atom present))⟩, ?_⟩

  intro current
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans
    (RichArgumentSupply.nativeDepth_fromResult current argumentQuery _ _ _) (Nat.le_max_right _ _)⟩

theorem RichPiRowCertificate.captureResult_allDepth
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (row : RichPiRowCertificate env U registry target locals σ available true domain body (key : Key n) support)
    {argument : EndpointState sourceEnv U source a A}
    (argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available key.input)
    (answer : RichCodeTransferResult env U registry target body body (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (a.subst σ))
      (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) true support) :
    ∃ capture : RichApplicationCapture sourceEnv env U registry target body argument locals σ available
        (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) support,
      ∀ current, capture.nativeDepth current ≤
        max (answer.certificate.nativeDepth current) (argumentQuery.observation.nativeDepth current) := by
  have bounded : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      need.rank ≤ n := fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := fun need member atom present =>
    row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  obtain ⟨packed, outside, pack, included, resources⟩ :=
    Footprint.pack_available answer.resources bounded covered
  refine ⟨⟨answer.footprint, answer.certificate, answer.resources, n, packed, outside, pack, resources,
    RichArgumentSupply.fromResult argumentQuery answer.footprint.localNeeds
      (fun need member => (pack.localNeeds need member).1)
      (fun need member atom present => included atom ((pack.localNeeds need member).2 atom present))⟩, ?_⟩

  intro current
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans
    (RichArgumentSupply.nativeDepth_fromResult current argumentQuery _ _ _) (Nat.le_max_right _ _)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
