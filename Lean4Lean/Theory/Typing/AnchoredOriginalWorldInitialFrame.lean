import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay

/-! Concrete empty-demand initial frames for adequacy. Every context domain is
an actual original formation; finite ancestry is constructed by the ordinary
reserved bind producer, with no interpretation call. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem emptyTableClosed : Valuation.AtomClosed (fun _ : Nat => ([] : List Need)) :=
  fun _ _ member => False.elim (List.not_mem_nil member)

private theorem subst_eta (σ : Subst) : σ.tail.cons σ.head = σ := by
  funext index
  cases index <;> rfl

private theorem emptyPush : Valuation.push [] (fun _ : Nat => ([] : List Need)) = (fun _ => []) := by
  funext index
  cases index <;> rfl

/-- The witnesses do not depend on the frontier. All stored certificates are
literal empty observations, so their query worlds and depths are zero. -/
theorem _root_.Lean4Lean.AnchoredSource.OriginalClosureMeasure.ContextDerivation.emptyWorldFrame
    {strata : EquationStratification env}
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv)
    (below : sourceEnv ≤ env)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    ∃ locals,
      ∃ frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ (fun _ => []),
      ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
        ∀ frontier, Nonempty (WorldUnaryFrameData (fun _ => True) controls frontier frame captured) := by
  induction context generalizing σ τ with
  | nil =>
    refine ⟨[], .nil, .nil, fun frontier => ⟨{
      ambient := ?_
      sources := ?_
      queries := ?_
      history := .nil controls
      historyReady := ?_ }⟩⟩
    · change RawOriginalRichFrame.Ambient .nil
      rw [RawOriginalRichFrame.Ambient.eq_def]
      exact ⟨below, trivial⟩
    · change RawOriginalRichFrame.AllSources (fun _ => True) .nil
      rw [RawOriginalRichFrame.AllSources.eq_def]
      exact ⟨trivial, trivial⟩
    · intro query member
      simp only [OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries] at member
      exact False.elim (List.not_mem_nil member)
    · exact ⟨emptyTableClosed, rfl, rfl⟩
  | @cons source A level tail domain ih =>
    cases substitutions with
    | cons tailSub domainType raw =>
      obtain ⟨locals, frame, captured, allReady⟩ := ih tailSub
      let certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ.tail true
          (.empty : Profile 0) [] := .legacy (.seed .empty (.empty (.sort true)))
      have resources : Footprint.Available [] (fun _ => []) := fun _ _ member => nomatch member
      have typed : (Profile.empty : Profile 0).HasType .empty := .empty .empty
      have arguments : Related env U registry target σ.head τ.head (A.subst σ.tail)
          (.empty : Profile 0) .empty := by
        apply Related.of_singletons
        intro atom member
        exact False.elim (List.not_mem_nil member)
      have bounded : ∀ need ∈ ([] : List Need), need.rank ≤ 0 := fun _ member => nomatch member
      have covered : ∀ need ∈ ([] : List Need), ∀ atom ∈ (need.atGrade 0).atoms,
          atom ∈ (Profile.empty : Profile 0).atoms := fun _ member => nomatch member
      let next := (OriginalRichFrame.bind frame domain certificate resources typed arguments
        [] bounded covered).reserve [.close (domain.dependencyOrigin controls.ordered)
          (frame.dependencyEnvironment controls.ordered)]
      let nextCaptured := reservedBindWorldEnvironment controls domain captured captured
      have ready : ∀ frontier, Nonempty (WorldUnaryFrameData (fun _ => True) controls frontier next nextCaptured) := by
        intro frontier
        obtain ⟨data⟩ := allReady frontier
        have certificateReady : ControlledStoredQuery controls frontier (.certificate certificate) := {
          annotation := .legacy _ (.seed _ _ .empty)
          within := by
            intro control active
            simpa only [certificate, StoredOriginalQuery.headDepth, RichCert.headDepth,
              SortableCert.headDepth, Obs.headDepth] using Nat.zero_le (controls.fuel control)
          sponsored := by intro child member; exact False.elim (List.not_mem_nil member) }
        exact data.bind tailSub domain certificate resources typed arguments [] bounded covered
          certificateReady emptyTableClosed
      have result : ∃ locals, ∃ frame : OriginalRichFrame sourceEnv env U registry target (.cons tail domain)
            locals (σ.tail.cons σ.head) (τ.tail.cons τ.head) (Valuation.push [] (fun _ => [])),
          ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
            ∀ frontier, Nonempty (WorldUnaryFrameData (fun _ => True) controls frontier frame captured) :=
          ⟨Locals.push locals, next, nextCaptured, ready⟩
      rw [subst_eta, subst_eta, emptyPush] at result
      exact result

/-- Initial identity data is computed from the actual well-formed context. -/
theorem initialWorldFrame
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata env)
    (formed : OnCtx Γ (env.IsType U)) :
    ∃ context : ContextDerivation env U Γ, ∃ locals,
      ∃ frame : OriginalRichFrame env env U registry Γ context locals .id .id (fun _ => []),
      ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
        ∀ frontier, Nonempty (WorldUnaryFrameData (fun _ => True) controls frontier frame captured) := by
  obtain ⟨context⟩ := ContextDerivation.reify (CtxStrong.strong controls.ordered formed)
  obtain ⟨locals, frame, captured, ready⟩ := context.emptyWorldFrame controls VEnv.LE.rfl
    (Ctx.SubstEq.id controls.ordered formed)
  exact ⟨context, locals, frame, captured, ready⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
