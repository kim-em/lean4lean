import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorFrameTransfer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionResidualCount

/-! # Relay a computed projection field to a smaller readout problem

When structure eta's type-field computation has a non-lambda endpoint, its
major history and zero/one terminal projection action can replace the expanded
body. A minimum then forbids reading the later pair's field within its smaller
projection budget. This reduces a hypothetical count obstruction; it does not
construct a strengthening counterexample or replay guarded substitutions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params] {D : Definitions}

/-- A typed pair projection reaches an output in the stated budget, but its
selected field has no path of at most that budget at any finite stage. This
records a hypothetical obstruction to counted readout, not its existence. -/
def PiInertPairProjectionBudgetFailure (D : Definitions) (Δ : List ProofShape)
    (family : Name) (info : VProjectionInfo) (field value out : ProofShape) (budget : Nat) : Prop :=
  TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) ∧
  (∃ stage, ScopedComputeCount (PiInertStage D stage) budget Δ
    (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out) ∧
  ∀ later j, j ≤ budget → ¬ ScopedComputeCount (PiInertStage D later) j Δ field out

/-- A budget failure at an exposed output supplies the actual remaining
constructor function-eta case. The source is realized at its closed family;
the no-readout clause excludes the other branch of the counted theorem. -/
theorem PiInertPairProjectionBudgetFailure.function_eta
    (H : PiInertPairProjectionBudgetFailure D Δ family info field value out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major) :
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
      GlobalPairFunctionEtaProjection D Γ family info
        (ProofShape.mkApps (.const info.ctorName []) [field, value]) out := by
  obtain ⟨HT, ⟨stage, R⟩, HN⟩ := H
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HT
  have RI : Primitive D (.proj family 0 (proofErase Γ m)) field := by
    rw [Em]
    exact .projIota hi (by simp [hp, hf]) (by simp [hp])
  have R' : ScopedComputeCount (PiInertStage D stage) budget (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out := by simpa only [EΓ, Em] using R
  rcases proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
    heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout hproj R' with ⟨later, j, hj, RJ⟩ | HE
  · exact (HN later j (by omega) (EΓ ▸ RJ)).elim
  · exact ⟨Γ, hΓ, EΓ, Em ▸ HE⟩

/-- A terminal type-field result in a globally minimum body/application/projection
execution produces a strictly smaller same-scope pair-readout failure. Its major
path is reused before substitution, and only its zero/one terminal action is
substituted. The budget gap accounts for the structure root and discarded work. -/
theorem pi_inert_terminal_projection_frame_smaller_failure
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (RM : ScopedComputeCount (PiInertStage D bodyStage) cm Ξ source major')
    (HF : (field = .proj family 0 major' ∧ cm ≤ fieldCost) ∨
      (Primitive D (.proj family 0 major') field ∧ cm+1 ≤ fieldCost))
    (HT : TypedSource Ξ
      (ProofShape.mkApps (.const info.ctorName []) [field, value']))
    (W : ContextSubstitution Ξ Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending) major)
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family 0 major) out)
    (hgap : fieldCost+cs+ck < cost)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Ξ source endpoint →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) endpoint k → cost ≤ j+k) :
    pending = [] ∧ cs+ck < cost ∧
      PiInertPairProjectionBudgetFailure D Δ family info
        (field.subst τ) (value'.subst τ) out (cs+ck) := by
  have EP := TypedSource.closed_constructor_image_pending_nil hi hp hz (by simp [hf]) HT W HNext
  have EI : (ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ =
      ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ] := by
    simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil]
  rw [EP, EI] at HNext RNext
  have HTimage : TypedSource Δ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ]) := by
    simpa only [ProofShape.mkApps] using HNext
  have RImage : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ]) major := by
    simpa only [ProofShape.mkApps] using RNext
  refine ⟨EP, by omega, HTimage, ⟨max nextStage observerStage,
    (RImage.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).proj.trans
      (RObserve.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩, ?_⟩
  intro later j hj RJ
  rcases HF with ⟨EF, HC⟩ | ⟨RI, HC⟩
  · have HK : PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) major' j := by
      rw [EP]
      refine ⟨later, 0, major'.subst τ, j, by omega, .beta .refl, later, ?_⟩
      simpa only [EF, ProofShape.subst] using RJ
    have HH := HM bodyStage cm major' j RM HK
    omega
  · have RIimage : Primitive D (.proj family 0 (major'.subst τ)) (field.subst τ) := RI.subst
    have HK : PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) major' (1+j) := by
      rw [EP]
      exact ⟨later, 0, major'.subst τ, 1+j, by omega, .beta .refl, later,
        (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RIimage))))).trans RJ⟩
    have HH := HM bodyStage cm major' (1+j) RM HK
    omega

/-- Every non-lambda endpoint of a sorted type-field projection admits the
strictly smaller pair-readout reduction. Both retained projections and selected
fields are covered, with all guarded computation staying before substitution. -/
theorem pi_inert_sorted_projection_frame_smaller_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HSort : ControlTyping Ξ (.proj family 0 source) (.sort u))
    (hout : ∀ A b args, field ≠ ProofShape.mkApps (.lam A b) args)
    (RF : ScopedComputeCount (PiInertStage D bodyStage) fieldCost Ξ (.proj family 0 source) field)
    (HT : TypedSource Ξ (ProofShape.mkApps (.const info.ctorName []) [field, value']))
    (W : ContextSubstitution Ξ Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending) major)
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family 0 major) out)
    (hgap : fieldCost+cs+ck < cost)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Ξ source endpoint →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) endpoint k → cost ≤ j+k) :
    pending = [] ∧ cs+ck < cost ∧
      PiInertPairProjectionBudgetFailure D Δ family info
        (field.subst τ) (value'.subst τ) out (cs+ck) := by
  obtain ⟨major', cm, RM, HF⟩ := pi_inert_sorted_projection_count_terminal heq hs HSort hout RF
  exact pi_inert_terminal_projection_frame_smaller_failure hi hp hf hz RM HF HT W HNext
    RNext RObserve hgap HM

/-- Native structure eta on an actual closed dependent pair writes its sorted
type projection as the first field. Both the shape and target typing are
derived from native recovery, without a substitution-stability hypothesis. -/
theorem proofErase_native_pair_structure_field
    (D : Definitions)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target) :
    ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) (.sort (.succ .zero)) ∧
    TypedSource (proofEraseCtx Γ) target ∧
    ∃ value, target = ProofShape.mkApps (.const info.ctorName [])
      [.proj family 0 (proofErase Γ m), value] := by
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have RI : Primitive D (.proj family 0 target) (.proj family 0 (proofErase Γ m)) :=
    proofErase_closed_structure_type_projection_primitive hstep hi (by omega) hΓ hm ht H
  obtain ⟨expanded, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_nativeMaskedStructureExpansion_descent hstep) hΓ hm rfl rfl (.base H)
  refine ⟨⟨Γ, .proj family 0 m, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩,
    ⟨Γ, expanded, _, hΓ, rfl, HE.hasType.2, EE⟩, ?_⟩
  obtain ⟨value, EV⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ HE.hasType.2
    (EE ▸ RI)
  exact ⟨value, EE.symm.trans EV⟩

/-- An actual native structure root followed by a constructor-component tail
with a non-lambda type-field endpoint reduces a global frame minimum to a
strictly smaller pair-readout failure. Only the component tail and actual
later execution are assumed; native recovery supplies its initial field and
typing. Lambda-headed field endpoints and later constructor roots remain open. -/
theorem pi_inert_native_structure_components_smaller_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (HC : ∃ fields, target = ProofShape.mkApps (.const info.ctorName []) fields ∧
      ScopedArgumentsCount (PiInertStage D bodyStage) (proofEraseCtx Γ) ca fields [field, value'])
    (hout : ∀ A b args, field ≠ ProofShape.mkApps (.lam A b) args)
    (W : ContextSubstitution (proofEraseCtx Γ) Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending) major)
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family 0 major) out)
    (hgap : ca+cs+ck < cost)
    (HM : ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ) (proofErase Γ m) endpoint →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) endpoint k → cost ≤ j+k) :
    pending = [] ∧ cs+ck < cost ∧
      PiInertPairProjectionBudgetFailure D Δ family info
        (field.subst τ) (value'.subst τ) out (cs+ck) := by
  obtain ⟨HSort, HTtarget, value, ET⟩ :=
    proofErase_native_pair_structure_field (D := D) hstep hi hp hf hz hadm hshape hΓ hm H
  obtain ⟨fields, EF, HA⟩ := HC
  have EFields := (ProofShape.const_spine_inj (EF.symm.trans ET)).2.2
  rw [EFields] at HA
  have RT : ScopedComputeCount (PiInertStage D bodyStage) ca (proofEraseCtx Γ) target
      (ProofShape.mkApps (.const info.ctorName []) [field, value']) := by
    rw [ET]
    simpa only [Nat.zero_add] using (ScopedComputeCount.beta BetaRed.refl).mkApps HA
  have HT := HTtarget.pi_inert_compute heq hs RT.forget
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RV last =>
      cases last
      exact pi_inert_sorted_projection_frame_smaller_failure heq hs hi hp hf hz HSort hout
        RF HT W HNext RNext RObserve (by omega) HM

end Lean4Lean.VEnv.Strengthening
