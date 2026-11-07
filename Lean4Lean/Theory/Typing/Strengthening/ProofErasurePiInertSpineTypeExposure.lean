import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertSpineApplicationOrigin

/-! # Read a constructor type argument through arbitrary stage-zero frames

The induction follows original application arguments or removes a whole
constant control frame at a strictly smaller checker depth. Computation
prefixes retain an original stable-spine history rather than requiring the
current endpoint to have a literal constructor head.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_app_fn
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeReadout
variable [Params] {D : Definitions}

/-- A nonempty argument vector has an actual sort assignment for its first
argument. Empty constructor prefixes impose no argument requirement. -/
def SpineFirstType (Δ : List ProofShape) : List ProofShape → Prop
  | [] => True
  | a :: _ => ∃ u, ControlTyping Δ a (.sort u)

/-- Compare just the first type argument, leaving later value arguments
unconstrained. Arity is recorded separately by the exposure result. -/
def SpineFirstCompare (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) : List ProofShape → List ProofShape → Prop
  | [], [] => True
  | a :: _, b :: _ => ComputedJointCompare Step Δ true a b
  | _, _ => False

private def SpineExposure (D : Definitions) (c : Name) (Δ : List ProofShape)
    (args : List ProofShape) (out : ProofShape) : Prop :=
  ∃ args', ScopedCompute (PiInertStage D 0) Δ out (ProofShape.mkApps (.const c []) args') ∧
    args.length = args'.length ∧ SpineFirstCompare (PiInertStage D 0) Δ args args'

private def OriginReadout (D : Definitions) (c : Name) (Δ : List ProofShape)
    (a b : ProofShape) : Prop :=
  ∀ args, TypedSource Δ (ProofShape.mkApps (.const c []) args) → SpineFirstType Δ args →
    ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c []) args) a →
    SpineExposure D c Δ args b

private theorem paths_first_compare (R : List.Forall₂ (ScopedCompute Step Δ) args args') :
    SpineFirstCompare Step Δ args args' := by
  cases R with
  | nil => trivial
  | cons R _ => exact .compute R .refl (.leaf .refl)

private theorem origin_refl (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c) : OriginReadout D c Δ a a := by
  intro args HT _ R
  obtain ⟨ls', args', HD, HL, HA⟩ := pi_inert_zero_stable_spine_frames heq hs @hroot HT R
  cases HL
  exact ⟨args', .beta HD.reduce, HA.length_eq, paths_first_compare HA⟩

private theorem origin_prefix (H : OriginReadout D c Δ a' b')
    (RA : ScopedCompute (PiInertStage D 0) Δ a a')
    (RB : ScopedCompute (PiInertStage D 0) Δ b b') : OriginReadout D c Δ a b := by
  intro args HT HX R
  obtain ⟨args', RY, HL, HC⟩ := H args HT HX (R.trans RA)
  exact ⟨args', RB.trans RY, HL, HC⟩

private theorem application_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (small : ∀ {a b}, ComputedJointCompareDepth (PiInertStage D 0) depth Δ false a b →
      TypedSource Δ a → TypedSource Δ b → OriginReadout D c Δ a b)
    (TA : TypedSource Δ (.app f x)) (TB : TypedSource Δ (.app g y))
    (HF : ComputedJointCompareDepth (PiInertStage D 0) depth Δ false f g)
    (hargs : ∀ u, ControlTyping Δ x (.sort u) →
      ComputedJointCompare (PiInertStage D 0) Δ true x y) :
    OriginReadout D c Δ (.app f x) (.app g y) := by
  intro args HT HX R
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  rcases pi_inert_zero_spine_application_origin heq hs @hroot HT R with
    ⟨pre, a, rfl, RF, RX⟩ | ⟨A, payload, rfl, RP, HP⟩
  · have HTP : TypedSource Δ (ProofShape.mkApps (.const c []) pre) := by
      apply (ScopedHole.appFn .hole a).typed
      simpa only [ProofShape.mkApps_snoc, ScopedHole.plug] using HT
    have HXP : SpineFirstType Δ pre := by
      cases pre with
      | nil => trivial
      | cons b bs => exact HX
    obtain ⟨args', RG, HL, HC⟩ := small HF (typed_app_fn TA) (typed_app_fn TB) pre HTP HXP RF
    refine ⟨args' ++ [y], ?_, by simpa only [List.length_append, List.length_singleton] using congrArg (· + 1) HL, ?_⟩
    · simpa only [ProofShape.mkApps_snoc] using ScopedCompute.app RG (ScopedCompute.refl (e := y))
    · cases pre with
      | nil =>
        have EE : args' = [] := by simpa using HL.symm
        subst args'
        obtain ⟨u, HX⟩ := HX
        exact .compute RX .refl (hargs u (HX.compute @hd RX))
      | cons a pre =>
        cases args' with
        | nil => simp at HL
        | cons b rest => exact HC
  · exact small (pi_inert_zero_constant_control_application_depth heq hs TA TB HP HF)
      (HT.pi_inert_compute heq hs RP) TB args HT HX RP

private theorem depth_origin_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (H : ComputedJointCompareDepth (PiInertStage D 0) depth Δ false a b)
    (TA : TypedSource Δ a) (TB : TypedSource Δ b) :
    OriginReadout D c Δ a b ∧ OriginReadout D c Δ b a := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have main : ∀ depth {Δ a b}, ComputedJointCompareDepth (PiInertStage D 0) depth Δ false a b →
      TypedSource Δ a → TypedSource Δ b →
      OriginReadout D c Δ a b ∧ OriginReadout D c Δ b a := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth smaller =>
      have inner : ∀ {k Δ kind a b}, ComputedJointCheckDepth (PiInertStage D 0) k Δ kind a b →
          k ≤ depth → kind = .compare false → TypedSource Δ a → TypedSource Δ b →
          OriginReadout D c Δ a b ∧ OriginReadout D c Δ b a := by
        intro k Δ kind a b H
        induction H with
        | leaf HL =>
          intro _ hk TA TB
          cases hk
          cases HL with
          | refl => exact ⟨origin_refl heq hs @hroot, origin_refl heq hs @hroot⟩
          | sort =>
            constructor <;> intro args HT HX R
            all_goals
              rcases pi_inert_zero_spine_head_shape heq hs @hroot HT R with ⟨_, E⟩ | ⟨f, x, E⟩ <;> cases E
          | const HL =>
            constructor <;> intro args HT HX R
            all_goals
              rcases pi_inert_zero_spine_head_shape heq hs @hroot HT R with ⟨rfl, E⟩ | ⟨f, x, E⟩
              · cases E; cases HL; exact ⟨[], .refl, rfl, True.intro⟩
              · cases E
        | @app childDepth Δ f g x y mode HF HX _ _ =>
          intro hn hk TA TB
          cases hk
          have small := fun {a b} (H : ComputedJointCompareDepth (PiInertStage D 0) childDepth Δ false a b) TA TB =>
            (smaller _ (by omega) H TA TB).1
          constructor
          · exact application_readout heq hs @hroot small TA TB HF (fun _ _ => HX.forget)
          · exact application_readout heq hs @hroot small TB TA (.symm HF) (fun _ _ => .symm HX.forget)
        | @appCarrier Δ f A B childDepth g x y mode RN HF HX _ _ =>
          intro hn hk TA TB
          cases hk
          have small := fun {a b} (H : ComputedJointCompareDepth (PiInertStage D 0) childDepth Δ false a b) TA TB =>
            (smaller _ (by omega) H TA TB).1
          constructor
          · apply application_readout heq hs @hroot small TA TB HF
            intro u SX
            have SY := inferred_application_argument_sort @hd TA TB SX HF.forget
            exact recovered_application_type_arguments_checked @hd TA SX SY RN HX.forget
          · apply application_readout heq hs @hroot small TB TA (.symm HF)
            intro u SY
            have SX := inferred_application_argument_sort @hd TB TA SY (.symm HF.forget)
            exact .symm (recovered_application_type_arguments_checked @hd TA SX SY RN HX.forget)
        | @appComputed Δ f A body childDepth g x y mode RF HF HX _ _ =>
          intro hn hk TA TB
          cases hk
          have small := fun {a b} (H : ComputedJointCompareDepth (PiInertStage D 0) childDepth Δ false a b) TA TB =>
            (smaller _ (by omega) H TA TB).1
          constructor
          · apply application_readout heq hs @hroot small TA TB HF
            intro u SX
            have SY := inferred_application_argument_sort @hd TA TB SX HF.forget
            exact computed_application_type_arguments_checked @hd TA SX SY RF HX.forget
          · apply application_readout heq hs @hroot small TB TA (.symm HF)
            intro u SY
            have SX := inferred_application_argument_sort @hd TB TA SY (.symm HF.forget)
            exact .symm (computed_application_type_arguments_checked @hd TA SX SY RF HX.forget)
        | compute RA RB HC ih =>
          intro hn hk TA TB
          have IH := ih hn hk (TA.pi_inert_compute heq hs RA) (TB.pi_inert_compute heq hs RB)
          exact ⟨origin_prefix IH.1 RA RB, origin_prefix IH.2 RB RA⟩
        | symm H ih =>
          intro hn hk TA TB
          exact (ih hn hk TB TA).symm
        | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
          intro hn hk TA TB
          constructor <;> intro args HT HX R
          all_goals
            rcases pi_inert_zero_spine_head_shape heq hs @hroot HT R with ⟨_, E⟩ | ⟨f, x, E⟩ <;> cases E
        | lamCommon | etaBodyL | etaBodyR | structFields |
            carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
            carrierSymm | carrierCompute | carrierReduce | carrierNested =>
          intro hn hk; cases hk
      intro Δ a b H TA TB
      exact inner H (Nat.le_refl _) rfl TA TB
  exact main depth H TA TB

/-- A computed source history from a core-stable constant spine suffices to
expose the arbitrary opposite endpoint at the same head and arity. The first
argument's actual sort typing preserves its comparison through all surviving
constant frames, including frames at proper prefixes and computed-domain
application rules. This is stage-zero inferred checking, not common-mode
constructor injectivity or general forward beta closure. -/
theorem pi_inert_zero_computed_spine_type_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c []) args))
    (HX : SpineFirstType Δ args) (TB : TypedSource Δ b)
    (R : ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c []) args) a)
    (H : ComputedJointCompare (PiInertStage D 0) Δ false a b) :
    ∃ args', ScopedCompute (PiInertStage D 0) Δ b (ProofShape.mkApps (.const c []) args') ∧
      args.length = args'.length ∧ SpineFirstCompare (PiInertStage D 0) Δ args args' := by
  obtain ⟨depth, HD⟩ := H.depth
  exact (depth_origin_readout heq hs @hroot HD (HT.pi_inert_compute heq hs R) TB).1 args HT HX R

/-- Inferred stage-zero comparison exposes a displayed binary constructor's
opposite endpoint and retains comparison of its first type argument. Arbitrary
internal constant expansions on either side are included by the depth argument. -/
theorem pi_inert_zero_binary_type_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : TypedSource Δ (.app (.app (.const c []) x) value)) (TB : TypedSource Δ b)
    (HX : ControlTyping Δ x (.sort u))
    (H : ComputedJointCompare (PiInertStage D 0) Δ false (.app (.app (.const c []) x) value) b) :
    ∃ y other, ScopedCompute (PiInertStage D 0) Δ b (.app (.app (.const c []) y) other) ∧
      ComputedJointCompare (PiInertStage D 0) Δ true x y := by
  obtain ⟨args', RY, HL, HC⟩ := pi_inert_zero_computed_spine_type_exposure heq hs @hroot
    (args := [x, value]) HT ⟨u, HX⟩ TB .refl H
  cases args' with
  | nil => simp at HL
  | cons y args' =>
    cases args' with
    | nil => simp at HL
    | cons other rest =>
      have E : rest = [] := by simpa using HL.symm
      subst rest
      exact ⟨y, other, RY, HC⟩

/-- For a displayed dependent-pair constructor, inferred stage-zero comparison
retains comparison of its selected type field with the other major's type
projection. The other major is exposed computationally inside the proof;
no shape or independent field-comparison premise is imposed on it. -/
theorem proofErase_pi_inert_zero_pair_selected_type_projection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (EX : proofErase Γ x = .app (.app (.const info.ctorName []) A) a)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) true
      A (.proj family 0 (proofErase Γ y)) := by
  have hstep : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
    intro Δ levels args out HR
    exact erased_level_recovered_stage_spine_levels heq (henv.projectionCtorRigid hi) hD 0 (Δ := Δ) HR
  have hproj := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
  have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ x)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 x, hΓ, rfl, hproj, if_neg (not_isProof_of_sort hΓ hproj)⟩
  have HA : ControlTyping (proofEraseCtx Γ) A (.sort (.succ .zero)) := by
    apply HT.compute (Step := PiInertStage D 0) @hstep
    rw [EX]
    exact .base (pi_inert_stage_core (.inl (.inl (.inl (.projIota hi (args := [A, a])
      (by simp [hp, hf]) (by simp [hp]))))))
  have TX : TypedSource (proofEraseCtx Γ) (proofErase Γ x) := ⟨Γ, x, _, hΓ, rfl, hx, rfl⟩
  have TY : TypedSource (proofEraseCtx Γ) (proofErase Γ y) := ⟨Γ, y, _, hΓ, rfl, hy, rfl⟩
  rw [EX] at TX
  obtain ⟨B, b, RY, HC⟩ := pi_inert_zero_binary_type_exposure heq hs @hroot TX TY HA
    (by simpa only [EX] using H)
  have RB : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (.proj family 0 (.app (.app (.const info.ctorName []) B) b)) B :=
    .base (pi_inert_stage_core (.inl (.inl (.inl (.projIota hi (args := [B, b])
      (by simp [hp, hf]) (by simp [hp]))))))
  exact .compute .refl ((ScopedCompute.proj RY).trans RB) HC

end Lean4Lean.VEnv.Strengthening
