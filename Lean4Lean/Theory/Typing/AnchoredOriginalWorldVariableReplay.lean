import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiRebind
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContinuation

/-! Neutral resource replay constructs the replacement observer and its
annotation together. Closed original metadata is retained verbatim. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private replay_left replay_right replay_underBinder replay_pack replay_append from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichPiRebind
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private theorem congrArg2 (f : α → β → γ) {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

/-- A literal variable observation cannot open an original declaration.
This constructs its annotation from its syntax, including all finite views. -/
theorem neutralObsProvenance
    {strata : EquationStratification env}
    (query : Obs env U registry target locals σ (.bvar index) profile footprint) :
    ∃ annotation : WorldLegacyObsProvenance strata query,
      annotation.worlds = [] ∧ ∀ policy, query.headDepth policy = 0 := by
  match query with
  | .var .. => exact ⟨.var .., rfl, fun _ => by simp only [Obs.headDepth]⟩
  | .empty => exact ⟨.empty, rfl, fun _ => by simp only [Obs.headDepth]⟩
  | .union left right =>
    obtain ⟨la, lw, ld⟩ := neutralObsProvenance (strata := strata) left
    obtain ⟨ra, rw, rd⟩ := neutralObsProvenance (strata := strata) right
    refine ⟨.union left right la ra, ?_, ?_⟩
    · change la.worlds ++ ra.worlds = []
      rw [lw, rw]
      rfl
    · intro policy; rw [Obs.headDepth, ld, rd]; rfl
  | .pad child =>
    obtain ⟨a, w, d⟩ := neutralObsProvenance (strata := strata) child
    exact ⟨.pad child a, w, fun policy => by rw [Obs.headDepth]; exact d policy⟩
  | .unpad child =>
    obtain ⟨a, w, d⟩ := neutralObsProvenance (strata := strata) child
    exact ⟨.unpad child a, w, fun policy => by rw [Obs.headDepth]; exact d policy⟩
  | .view child view =>
    obtain ⟨a, w, d⟩ := neutralObsProvenance (strata := strata) child
    exact ⟨.view child view a, w, fun policy => by rw [Obs.headDepth]; exact d policy⟩
  | .rowShift child =>
    obtain ⟨a, w, d⟩ := neutralObsProvenance (strata := strata) child
    exact ⟨.rowShift child a, w, fun policy => by rw [Obs.headDepth]; exact d policy⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

/-- The finite replay spine is built from actual neutral observations. It
adds no original opening and has zero depth for every head policy. -/
theorem RecipeResourceTransfer.neutralProvenance
    {strata : EquationStratification env}
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint) :
    ∃ annotation : WorldRecipeResourceProvenance strata transfer,
      annotation.worlds = [] ∧ ∀ policy, transfer.headDepth policy = 0 := by
  induction transfer with
  | nil => exact ⟨.nil, rfl, fun _ => rfl⟩
  | cons query tail ih =>
    obtain ⟨head, headWorlds, headDepth⟩ := neutralObsProvenance (strata := strata) query
    obtain ⟨rest, restWorlds, restDepth⟩ := ih
    refine ⟨.cons head rest, ?_, ?_⟩
    · change head.worlds ++ rest.worlds = []
      rw [headWorlds, restWorlds]; rfl
    · intro policy
      rw [RecipeResourceTransfer.headDepth, headDepth policy, restDepth policy]
      rfl

mutual
theorem WorldLegacyObsProvenance.replayNeutral
    {strata : EquationStratification env}
    {query : Obs env U registry target locals σ expression profile required}
    (annotation : WorldLegacyObsProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : Obs env U registry target locals σ expression profile footprint,
      ∃ output : WorldLegacyObsProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | retained@(.delta ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | retained@(.native ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | retained@(.family ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | retained@(.constructor ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | .var _ _ index profile =>
    obtain ⟨fp, ⟨changed⟩, resources⟩ := supply index _ (List.mem_singleton_self _)
    obtain ⟨output, worlds, depth⟩ := neutralObsProvenance (strata := strata) changed
    refine ⟨fp, changed, output, resources, worlds, ?_⟩
    intro policy; rw [depth policy, Obs.headDepth]
  | .empty => exact ⟨[], .empty, .empty, (fun _ _ h => nomatch h), rfl, fun _ => rfl⟩
  | .sort relevant => exact ⟨[], .sort relevant, .sort relevant, (fun _ _ h => nomatch h), rfl, fun _ => rfl⟩
  | .app fn arg arguments admitted first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .app fn' arg' arguments admitted, .app fn' arg' arguments admitted fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [Obs.headDepth, Obs.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .lam domain guard body pack covered first second =>
    obtain ⟨df, domain', da, dr, dw, dd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨bf, body', ba, br, bw, bd⟩ := second.replayNeutral (replay_underBinder (replay_right supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    refine ⟨df ++ outside, .lam domain' guard body' pack' covered',
      .lam domain' guard body' pack' covered' da ba, replay_append dr external, ?_, ?_⟩
    · exact congrArg2 List.append dw bw
    · intro policy; rw [Obs.headDepth, Obs.headDepth]; exact congrArg2 max (dd policy) (bd policy)
  | .pi domain guard rows first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .pi fn' guard arg', .pi fn' guard arg' fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [Obs.headDepth, Obs.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .union left right first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .union fn' arg', .union fn' arg' fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [Obs.headDepth, Obs.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .pad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .pad changed, .pad changed output, resources, worlds, ?_⟩
    intro policy
    rw [Obs.headDepth, Obs.headDepth]
    exact depth policy
  | .unpad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .unpad changed, .unpad changed output, resources, worlds, ?_⟩
    intro policy
    rw [Obs.headDepth, Obs.headDepth]
    exact depth policy
  | .rowShift source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .rowShift changed, .rowShift changed output, resources, worlds, ?_⟩
    intro policy
    rw [Obs.headDepth, Obs.headDepth]
    exact depth policy
  | .view source view child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .view changed view, .view changed view output, resources, worlds, ?_⟩
    intro policy
    rw [Obs.headDepth, Obs.headDepth]
    exact depth policy
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldLegacyCertProvenance.replayNeutral
    {strata : EquationStratification env}
    {query : CodeCert env U registry target locals σ expression profile required}
    (annotation : WorldLegacyCertProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : CodeCert env U registry target locals σ expression profile footprint,
      ∃ output : WorldLegacyCertProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | .seed source formed child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .seed changed formed, .seed changed formed output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
  | .union left right first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .union fn' arg', .union fn' arg' fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [CodeCert.headDepth, CodeCert.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .pad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .pad changed, .pad changed output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
  | .unpad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .unpad changed, .unpad changed output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
  | .familyPad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .familyPad changed, .familyPad changed output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
  | .down source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .down changed, .down changed output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
  | .map view source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .map view changed, .map view changed output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
  | .select source member child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .select changed member, .select changed member output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
  | .focusMinimal source minimal bound child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .focusMinimal changed minimal bound, .focusMinimal changed minimal bound output, resources, worlds, ?_⟩
    intro policy
    rw [CodeCert.headDepth, CodeCert.headDepth]
    exact depth policy
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldLegacyRowsProvenance.replayNeutral
    {strata : EquationStratification env}
    {query : PiRows env U registry target locals σ A B ambient values required}
    (annotation : WorldLegacyRowsProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : PiRows env U registry target locals σ A B ambient values footprint,
      ∃ output : WorldLegacyRowsProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | .nil => exact ⟨[], .nil, .nil, (fun _ _ h => nomatch h), rfl, fun _ => rfl⟩
  | .cons guard body pack covered tail first second =>
    obtain ⟨bf, body', ba, br, bw, bd⟩ := first.replayNeutral (replay_underBinder (replay_left supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    obtain ⟨tf, tail', ta, tr, tw, td⟩ := second.replayNeutral (replay_right supply)
    refine ⟨outside ++ tf, .cons guard body' pack' covered' tail',
      .cons guard body' pack' covered' tail' ba ta, replay_append external tr, ?_, ?_⟩
    · exact congrArg2 List.append bw tw
    · intro policy; rw [PiRows.headDepth, PiRows.headDepth]; exact congrArg2 max (bd policy) (td policy)
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldSortableObsProvenance.replayNeutral
    {strata : EquationStratification env}
    {query : SortableObs env U registry target locals σ expression profile required}
    (annotation : WorldSortableObsProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : SortableObs env U registry target locals σ expression profile footprint,
      ∃ output : WorldSortableObsProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | retained@(.family ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | .legacy source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .legacy changed, .legacy changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableObs.headDepth, SortableObs.headDepth]
    exact depth policy
  | .code relevant source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .code relevant changed, .code relevant changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableObs.headDepth, SortableObs.headDepth]
    exact depth policy
  | .app fn arg arguments admitted first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .app fn' arg' arguments admitted, .app fn' arg' arguments admitted fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [SortableObs.headDepth, SortableObs.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .lam domain guard body pack covered first second =>
    obtain ⟨df, domain', da, dr, dw, dd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨bf, body', ba, br, bw, bd⟩ := second.replayNeutral (replay_underBinder (replay_right supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    refine ⟨df ++ outside, .lam domain' guard body' pack' covered',
      .lam domain' guard body' pack' covered' da ba, replay_append dr external, ?_, ?_⟩
    · exact congrArg2 List.append dw bw
    · intro policy; rw [SortableObs.headDepth, SortableObs.headDepth]; exact congrArg2 max (dd policy) (bd policy)
  | .union left right first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .union fn' arg', .union fn' arg' fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [SortableObs.headDepth, SortableObs.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .pad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .pad changed, .pad changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableObs.headDepth, SortableObs.headDepth]
    exact depth policy
  | .unpad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .unpad changed, .unpad changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableObs.headDepth, SortableObs.headDepth]
    exact depth policy
  | .rowShift source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .rowShift changed, .rowShift changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableObs.headDepth, SortableObs.headDepth]
    exact depth policy
  | .view source view child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .view changed view, .view changed view output, resources, worlds, ?_⟩
    intro policy
    rw [SortableObs.headDepth, SortableObs.headDepth]
    exact depth policy
  | .action source action child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .action changed action, .action changed action output, resources, worlds, ?_⟩
    intro policy
    rw [SortableObs.headDepth, SortableObs.headDepth]
    exact depth policy
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldSortableCertProvenance.replayNeutral
    {strata : EquationStratification env}
    {query : SortableCert env U registry target locals σ expression relevant profile required}
    (annotation : WorldSortableCertProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : SortableCert env U registry target locals σ expression relevant profile footprint,
      ∃ output : WorldSortableCertProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | .ofCode source formed child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .ofCode changed formed, .ofCode changed formed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .observe source formed child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .observe changed formed, .observe changed formed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .seed source formed child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .seed changed formed, .seed changed formed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .pi domain guard rows first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .pi fn' guard arg', .pi fn' guard arg' fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [SortableCert.headDepth, SortableCert.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .union left right first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .union fn' arg', .union fn' arg' fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [SortableCert.headDepth, SortableCert.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .pad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .pad changed, .pad changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .unpad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .unpad changed, .unpad changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .familyPad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .familyPad changed, .familyPad changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .down source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .down changed, .down changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .sortPad source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .sortPad changed, .sortPad changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .map view source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .map view changed, .map view changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .select source member child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .select changed member, .select changed member output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .focusMinimal source minimal bound child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .focusMinimal changed minimal bound, .focusMinimal changed minimal bound output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
  | .support action source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .support action changed, .support action changed output, resources, worlds, ?_⟩
    intro policy
    rw [SortableCert.headDepth, SortableCert.headDepth]
    exact depth policy
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldSortableRowsProvenance.replayNeutral
    {strata : EquationStratification env}
    {query : SortableRows env U registry target locals σ A B relevant ambient values required}
    (annotation : WorldSortableRowsProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : SortableRows env U registry target locals σ A B relevant ambient values footprint,
      ∃ output : WorldSortableRowsProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | .nil => exact ⟨[], .nil, .nil, (fun _ _ h => nomatch h), rfl, fun _ => rfl⟩
  | .cons guard body pack covered tail first second =>
    obtain ⟨bf, body', ba, br, bw, bd⟩ := first.replayNeutral (replay_underBinder (replay_left supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    obtain ⟨tf, tail', ta, tr, tw, td⟩ := second.replayNeutral (replay_right supply)
    refine ⟨outside ++ tf, .cons guard body' pack' covered' tail',
      .cons guard body' pack' covered' tail' ba ta, replay_append external tr, ?_, ?_⟩
    · exact congrArg2 List.append bw tw
    · intro policy; rw [SortableRows.headDepth, SortableRows.headDepth]; exact congrArg2 max (bd policy) (td policy)
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

end

mutual
theorem WorldCertProvenance.replayNeutral
    {strata : EquationStratification env}
    {node : EndpointState sourceEnv U source expression assigned}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile required}
    (annotation : WorldCertProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : RichCert sourceEnv env U registry target node locals σ relevant profile footprint,
      ∃ output : WorldCertProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | .recipe child =>
    obtain ⟨footprint, ⟨transfer⟩, resources⟩ := supply.transfer
    obtain ⟨transferData, worlds, depth⟩ := transfer.neutralProvenance (strata := strata)
    refine ⟨footprint, .recipe (.resources _ transfer),
      .recipe (.resources child transferData), resources, ?_, ?_⟩
    · change child.worlds ++ transferData.worlds = child.worlds
      rw [worlds, List.append_nil]
    · intro policy
      simp only [RichCert.headDepth, RichCodeRecipe.headDepth, depth policy, Nat.max_zero]

  | .legacy source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .legacy changed, .legacy changed output, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .observe child formed =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .observe changed formed, .observe output formed, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .route path child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .route path changed, .route path output, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .pad child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .pad changed, .pad output, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .down child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .down changed, .down output, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .map view child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .map view changed, .map view output, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .support action child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .support action changed, .support action output, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .select child member =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .select changed member, .select output member, resources, worlds, ?_⟩
    intro policy
    rw [RichCert.headDepth, RichCert.headDepth]
    exact depth policy
  | .union first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .union fn' arg', .union fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [RichCert.headDepth, RichCert.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .pi hu hv domain guard rows first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .pi hu hv fn' guard arg', .pi hu hv fn' guard arg' fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [RichCert.headDepth, RichCert.headDepth]; exact congrArg2 max (fd policy) (ad policy)
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldRowsProvenance.replayNeutral
    {strata : EquationStratification env}
    {query : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values required}
    (annotation : WorldRowsProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint,
      ∃ output : WorldRowsProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | .nil => exact ⟨[], .nil, .nil, (fun _ _ h => nomatch h), rfl, fun _ => rfl⟩
  | .cons guard body pack covered tail first second =>
    obtain ⟨bf, body', ba, br, bw, bd⟩ := first.replayNeutral (replay_underBinder (replay_left supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    obtain ⟨tf, tail', ta, tr, tw, td⟩ := second.replayNeutral (replay_right supply)
    refine ⟨outside ++ tf, .cons guard body' pack' covered' tail',
      .cons guard body' pack' covered' tail' ba ta, replay_append external tr, ?_, ?_⟩
    · exact congrArg2 List.append bw tw
    · intro policy; rw [RichRows.headDepth, RichRows.headDepth]; exact congrArg2 max (bd policy) (td policy)
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldObsProvenance.replayNeutral
    {strata : EquationStratification env}
    {node : EndpointState sourceEnv U source expression assigned}
    {query : RichObs sourceEnv env U registry target node locals σ profile required}
    (annotation : WorldObsProvenance strata query)
    (supply : VariableResourceReplay env U registry target locals σ available required) :
    ∃ footprint, ∃ changed : RichObs sourceEnv env U registry target node locals σ profile footprint,
      ∃ output : WorldObsProvenance strata changed,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, changed.headDepth policy = query.headDepth policy := by
  match annotation with
  | retained@(.rigidFamily ..) | retained@(.canonicalConst ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | retained@(.canonicalDelta ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | retained@(.family ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | retained@(.constructor ..) => exact ⟨[], _, retained, (fun _ _ h => nomatch h), (by simp_all only [namedPattern]), fun _ => rfl⟩
  | .var (i := index) (node := variableNode) =>
    obtain ⟨fp, ⟨changed⟩, resources⟩  := supply index _ (List.mem_singleton_self _)
    obtain ⟨output, worlds, depth⟩ := neutralObsProvenance (strata := strata) changed
    refine ⟨fp, RichObs.legacy (node := variableNode) (.legacy changed), .legacy _ (.legacy changed output), resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, SortableObs.headDepth, depth policy, RichObs.headDepth, SortableObs.headDepth, Obs.headDepth]
  | .empty (node := emptyNode) => exact ⟨[], RichObs.legacy (node := emptyNode) (.legacy .empty), .empty, (fun _ _ h => nomatch h), rfl, fun _ => rfl⟩
  | .sort (node := sortNode) relevant => exact ⟨[], RichObs.legacy (node := sortNode) (.legacy (.sort relevant)), .sort relevant, (fun _ _ h => nomatch h), rfl, fun _ => rfl⟩
  | .legacy source child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .legacy changed, .legacy changed output, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .code child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .code changed, .code output, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .route path child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .route path changed, .route path output, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .pad child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .pad changed, .pad output, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .unpad child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .unpad changed, .unpad output, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .view child view =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .view changed view, .view output view, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .action child action =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .action changed action, .action output action, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .select child member =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, .select changed member, .select output member, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth, RichObs.headDepth]
    exact depth policy
  | .union first second =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .union fn' arg', .union fa aa, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [RichObs.headDepth, RichObs.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .app hu hv first second arguments admitted =>
    obtain ⟨ff, fn', fa, fr, fw, fd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨af, arg', aa, ar, aw, ad⟩ := second.replayNeutral (replay_right supply)
    refine ⟨ff ++ af, .app hu hv fn' arg' arguments admitted, .app hu hv fa aa arguments admitted, replay_append fr ar, ?_, ?_⟩
    · exact congrArg2 List.append fw aw
    · intro policy; rw [RichObs.headDepth, RichObs.headDepth]; exact congrArg2 max (fd policy) (ad policy)
  | .lam hu hv domain guard body pack covered first second =>
    obtain ⟨df, domain', da, dr, dw, dd⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨bf, body', ba, br, bw, bd⟩ := second.replayNeutral (replay_underBinder (replay_right supply) pack _)
    obtain ⟨packed, outside, pack', covered', external⟩ := replay_pack pack covered br
    refine ⟨df ++ outside, .lam hu hv domain' guard body' pack' covered',
      .lam hu hv domain' guard body' pack' covered' da ba, replay_append dr external, ?_, ?_⟩
    · exact congrArg2 List.append dw bw
    · intro policy; rw [RichObs.headDepth, RichObs.headDepth]; exact congrArg2 max (dd policy) (bd policy)
  | .projection head nameEq member first second majorSite fieldSite typed alignment =>
    obtain ⟨mf, major', ma, mr, mw, md⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨ff, field', fa, fr, fw, fd⟩ := second.replayNeutral (replay_right supply)
    refine ⟨mf ++ ff, .projection head nameEq member major' field' typed alignment,
      .projection head nameEq member ma fa majorSite fieldSite typed alignment,
      replay_append mr fr, ?_, ?_⟩
    · change majorSite.worlds ++ fieldSite.worlds ++ ma.worlds ++ fa.worlds =
        majorSite.worlds ++ fieldSite.worlds ++ first.worlds ++ second.worlds
      rw [mw, fw]
    · intro policy; rw [RichObs.headDepth, RichObs.headDepth]; exact congrArg2 max (md policy) (fd policy)
  | .projectionSortable head nameEq member selected path sortable first second majorSite fieldSite typed =>
    obtain ⟨mf, major', ma, mr, mw, md⟩ := first.replayNeutral (replay_left supply)
    obtain ⟨ff, field', fa, fr, fw, fd⟩ := second.replayNeutral (replay_right supply)
    refine ⟨mf ++ ff, .projectionSortable head nameEq member major' selected path sortable field' typed,
      .projectionSortable head nameEq member selected path sortable ma fa majorSite fieldSite typed,
      replay_append mr fr, ?_, ?_⟩
    · change majorSite.worlds ++ fieldSite.worlds ++ ma.worlds ++ fa.worlds =
        majorSite.worlds ++ fieldSite.worlds ++ first.worlds ++ second.worlds
      rw [mw, fw]
    · intro policy; rw [RichObs.headDepth, RichObs.headDepth]; exact congrArg2 max (md policy) (fd policy)
  | .castProfile equal child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, _, .castProfile equal output, resources, worlds, ?_⟩
    intro policy
    cases equal
    exact depth policy
  | .lowerRaised child =>
    obtain ⟨fp, changed, output, resources, worlds, depth⟩ := child.replayNeutral supply
    refine ⟨fp, changed.lowerRaised, .lowerRaised output, resources, worlds, ?_⟩
    intro policy
    rw [RichObs.headDepth_lowerRaised, RichObs.headDepth_lowerRaised]
    exact depth policy
termination_by sizeOf annotation
decreasing_by
  all_goals simp_wf
  all_goals try rw [WorldObsProvenance.castProfile.sizeOf_spec]
  all_goals omega

end

/-- Rebind the exact original certificate and carry its existing opening
sites, with equal worlds and equal depth for every policy. -/
theorem WorldCertProvenance.rebindLocal
    {strata : EquationStratification env}
    {oldInput packed : Profile n} {newInput : Profile m}
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant result required)
    (annotation : WorldCertProvenance strata certificate)
    (replay : Obs env U registry target locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      ∃ changed : RichCert sourceEnv env U registry target node locals σ relevant result footprint,
      ∃ next : WorldCertProvenance strata changed,
      BinderPack m packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available ∧
      next.worlds = annotation.worlds ∧ ∀ policy, changed.headDepth policy = certificate.headDepth policy := by
  have localClosed := Valuation.push_atomized_closed closed [⟨m, newInput⟩]
  have supply : VariableResourceReplay env U registry target locals σ
      (Valuation.push (rowInputNeeds newInput) available) required := by
    clear certificate annotation
    induction pack with
    | nil => intro _ _ member; cases member
    | «local» need bound rest ih =>
      have inclusion : List.Subset (raiseProfile n bound need.profile) oldInput := by
        intro atom member
        apply covered atom (List.mem_append_left _ ?_)
        simpa only [Need.atGrade, dif_pos bound, Profile.atoms] using member
      obtain ⟨fp, ⟨selected⟩, selection⟩ := replay.subprofile inclusion
      have observation := selected.lower bound
      have resources := selection.available_closed replayAvailable localClosed
      have tail := ih (fun atom member => covered atom (List.mem_append_right _ member)) outsideAvailable
      intro index wanted member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact ⟨fp, ⟨observation⟩, resources⟩
      · exact tail index wanted member
    | external index need rest ih =>
      have tail := ih covered
        (fun i wanted member => outsideAvailable i wanted (List.mem_cons_of_mem _ member))
      intro i wanted member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        refine ⟨[(index + 1, need)], ⟨.var locals σ (index + 1) need.profile⟩, ?_⟩
        intro i wanted member
        cases List.mem_singleton.mp member
        exact outsideAvailable index need List.mem_cons_self
      · exact tail i wanted member
  obtain ⟨footprint, changed, next, resources, worlds, depth⟩ := annotation.replayNeutral supply
  obtain ⟨packed', outside', pack', covered', outsideAvailable'⟩ :=
    Footprint.pack_available resources
      (fun need member => (rowInputNeeds_bounded newInput need member).1)
      (fun need member => (rowInputNeeds_bounded newInput need member).2)
  exact ⟨footprint, outside', packed', changed, next, pack', covered', outsideAvailable', worlds, depth⟩

/-- The controlled answer names the same newly rebuilt certificate as its
computed pack. No opaque existential replay result is retroactively annotated. -/
theorem RichCert.rebind_local_controlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    {oldInput packed : Profile n} {newInput : Profile m}
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant result required)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (replay : Obs env U registry target locals σ (.bvar 0) oldInput replayFootprint)
    (replayAvailable : replayFootprint.Available (Valuation.push (rowInputNeeds newInput) available))
    (pack : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (outsideAvailable : outside.Available available)
    (closed : available.AtomClosed) :
    ∃ footprint outside' packed',
      ∃ changed : RichCert sourceEnv env U registry target node locals σ relevant result footprint,
      Nonempty (ControlledStoredQuery controls frontier (.certificate changed)) ∧
      BinderPack m packed' footprint outside' ∧
      (∀ atom ∈ packed'.atoms, atom ∈ newInput.atoms) ∧ outside'.Available available := by
  obtain ⟨fp, out, packed, changed, next, pack, covered, resources, worlds, depth⟩ :=
    ready.annotation.rebindLocal certificate replay replayAvailable pack covered outsideAvailable closed
  refine ⟨fp, out, packed, changed, ⟨⟨next, ?_, ?_⟩⟩, pack, covered, resources⟩
  · intro control active
    change changed.headDepth _ ≤ _
    rw [depth]
    exact ready.within control active
  · simpa only [StoredOriginalQuery.Provenance.worlds, worlds] using ready.sponsored

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
