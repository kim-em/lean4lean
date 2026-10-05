import Lean4Lean.Theory.Typing.AnchoredOriginalWorldSortInversion

/-! The actual rank-one Pi observation connects the all-world unary interface
to semantic Pi inversion. Every initial frame, query and sponsor is computed;
there is no supplied interpretation answer or initial query certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Empty domain demand and no rows still expose both actual Pi components.
The ordinary Pi guard is the literal reflexive guard. -/
theorem piCodeOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (banks : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (original : Derivation env U Γ (.forallE A B) other assigned) :
    TypeRelated env U registry Γ (.forallE A B) other
      (Profile.pi A B (.empty : Profile 0) []) := by
  let controls := worldAdequacyControls strata henv
  obtain ⟨context, locals, frame, captured, allReady⟩ := initialWorldFrame (registry := registry) controls formed
  let node : EndpointState env U Γ (.forallE A B) assigned := .ref (.left original)
  let active := originalCallWorld controls .fundamental node captured
  let sponsor := originalCallWorld controls .expressionReindex node captured
  obtain ⟨data⟩ := allReady [sponsor]
  have guard : PiGuard env U Γ Subst.id A B A B := by
    simpa only [id_lift, subst_id] using (PiGuard.literal (env := env) (U := U) (Γ := Γ)
      (σ := Subst.id) (A := A) (B := B))
  let query : RichObs env env U registry Γ node locals Subst.id
      (Profile.pi A B (.empty : Profile 0) []) [] :=
    .legacy (.legacy (.pi (.seed .empty (.empty (.sort true))) guard .nil))
  have sorted : (Profile.pi A B (.empty : Profile 0) []).HasType (.sort true) :=
    Profile.HasType.pi_empty (.empty (.sort true)) true
  have smaller : WorldBelow strata.rules.length active sponsor := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have sponsored : Sponsored [sponsor] [active] := by
    intro world member
    cases List.mem_singleton.mp member
    exact ⟨sponsor, List.mem_singleton_self _, smaller⟩
  let ready : ControlledStoredQuery controls [sponsor] (.observation query) := {
    annotation := .legacy _ (.legacy _ (.pi _ _ _ (.seed _ _ .empty) .nil))
    within := by
      intro control _
      change query.headDepth _ ≤ _
      simp only [query, RichObs.headDepth, SortableObs.headDepth, Obs.headDepth,
        CodeCert.headDepth, PiRows.headDepth, Nat.max_self]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨answer, _⟩ := (banks ([sponsor] ++ [active])).equality original true
    (.ofLocation .here context) controls frame captured captured [sponsor]
    (Nat.le_refl _) (Covered.refl _) rfl sponsored data
    (fun _ _ member => False.elim (List.not_mem_nil member)) formed (Ctx.SubstEq.id henv formed)
    query (by intro index need member; cases member) ready
  have code := answer.related.code_of_sortable henv hscoped formed sorted
  simpa only [Bool.not_true, Bool.false_eq_true, reduceIte, subst_id] using code

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
