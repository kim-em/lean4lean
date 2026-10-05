import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSortRule

/-! Projection field demands may be empty while their assigned types must
still be compared. Retain a genuine sort observation at the field's literal
assigned sort, alongside its value support. This uses the actual assigned
type; it does not infer its universe from a recipe's exposed head. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable def assignedSortFlag (level : VLevel) : Bool := by
  classical
  exact decide (¬ level ≈ .zero)

theorem assignedSortFlag_relevant (level : VLevel) :
    Relevant level (assignedSortFlag level) := by
  classical
  by_cases zero : level ≈ .zero <;> simp [assignedSortFlag, Relevant, zero]

/-- Supplement the actual F answer without changing its requested value
profile. In particular, an empty value demand keeps a nonempty assigned-code
demand for subsequent C/history replay. -/
noncomputable def RichSupportedValue.withAssignedSort
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (context : ContextDerivation sourceEnv U source)
    (henv : env.Ordered)
    (answer : RichSupportedValue sourceEnv env U registry target node locals σ τ available (input : Profile n)) :
    RichSupportedValue sourceEnv env U registry target node locals σ τ available input := by
  let extra : Profile n := .sort (assignedSortFlag level)
  let seed : RichCert sourceEnv env U registry target node.typeFormation.node locals σ true extra [] :=
    .legacy (.seed (.sort (assignedSortFlag_relevant level))
      (Profile.HasType.sort (assignedSortFlag level)))
  have levelWF : level.WF U :=
    (node.sound.defeq.levelWF context.forget.levelWF).2.2
  have extraCode : TypeRelated env U registry target ((VExpr.sort level).subst σ)
      ((VExpr.sort level).subst σ) extra :=
    TypeRelated.literalSort henv levelWF levelWF rfl (assignedSortFlag_relevant level)
  have code : TypeRelated env U registry target ((VExpr.sort level).subst σ)
      ((VExpr.sort level).subst σ) (answer.support.union extra) := by
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun member => answer.typeCode.singleton member)
      (fun member => extraCode.singleton member)
  have typed := answer.typed.enlarge (Profile.le_union_left answer.support extra)
    (answer.typed.wf_type.union (Profile.WF.sort _))
  exact {
    support := answer.support.union extra
    footprint := answer.footprint ++ []
    certificate := .union answer.certificate seed
    resources := fun i need member => answer.resources i need (by simpa only [List.append_nil] using member)
    typed := typed
    related := answer.related.retag henv typed code
    typeCode := code }

theorem RichSupportedValue.withAssignedSort_hasSort
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (context : ContextDerivation sourceEnv U source) (henv : env.Ordered)
    (answer : RichSupportedValue sourceEnv env U registry target node locals σ τ available (input : Profile n)) :
    assignedSortFlag level ∈ (answer.withAssignedSort context henv).support.sortFlags := by
  change assignedSortFlag level ∈ (answer.support.union (.sort (assignedSortFlag level))).sortFlags
  rw [Profile.sortFlags_union, Profile.sortFlags_sort]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The additional seed has no retained opening sites and zero head depth.
The original support certificate and every one of its sponsors are retained. -/
theorem RichSupportedValue.withAssignedSort_controlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (context : ContextDerivation sourceEnv U source) (henv : env.Ordered)
    (answer : RichSupportedValue sourceEnv env U registry target node locals σ τ available (input : Profile n))
    (ready : ControlledStoredQuery controls frontier (.certificate answer.certificate)) :
    Nonempty (ControlledStoredQuery controls frontier
      (.certificate (answer.withAssignedSort context henv).certificate)) := by
  refine ⟨⟨.union ready.annotation (.legacy _ (.seed _ _ (.sort _))), ?_, ?_⟩⟩
  · intro control active
    simpa only [StoredOriginalQuery.headDepth, withAssignedSort, RichCert.headDepth,
      SortableCert.headDepth, Obs.headDepth, Nat.max_zero] using ready.within control active
  · change Sponsored frontier (ready.annotation.worlds ++ [])
    simpa only [List.append_nil] using ready.sponsored

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
