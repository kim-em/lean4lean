import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionOrigin

/-! # Contract selected type projections through the full stage-zero checker

The source may compute arbitrarily before comparison. Retained projections
use inferred constructor-field exposure; selected fields pull back directly;
whole constant frames recurse at a strictly smaller structural checker depth.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private control_source sort_control_not_lam
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreProjectionContraction
open private sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params] {D : Definitions}

private theorem pair_select (hi : env.projections family info)
    (hp : info.nparams = 0) (hf : info.numFields = 2) :
    Primitive D (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) A :=
  .projIota hi (args := [A, value]) (by simp [hp, hf]) (by simp [hp])

private theorem pair_select_path (hi : env.projections family info)
    (hp : info.nparams = 0) (hf : info.numFields = 2) :
    ScopedCompute (PiInertStage D 0) Δ
      (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) A :=
  .base (pi_inert_stage_core (.inl (.inl (.inl (pair_select hi hp hf)))))

private def ProjectionReadout (D : Definitions) (family ctor : Name)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∀ {A value u}, ControlTyping Δ (.proj family 0 (.app (.app (.const ctor []) A) value)) (.sort u) →
    ScopedCompute (PiInertStage D 0) Δ (.proj family 0 (.app (.app (.const ctor []) A) value)) a →
    ComputedJointCompare (PiInertStage D 0) Δ true A b

private theorem readout_refl
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs) :
    ProjectionReadout D family info.ctorName Δ a a := by
  intro A value u HT R
  exact pi_inert_zero_selected_projection_residual_compare heq hs hi hD HT (pair_select hi hp hf) R

private theorem readout_prefix (H : ProjectionReadout D family ctor Δ a' b')
    (RA : ScopedCompute (PiInertStage D 0) Δ a a')
    (RB : ScopedCompute (PiInertStage D 0) Δ b b') : ProjectionReadout D family ctor Δ a b := by
  intro A value u HT R
  exact .compute .refl RB (H HT (R.trans RA))

private theorem readout_direct
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (H : ComputedJointCompare (PiInertStage D 0) Δ mode a b)
    (hproj : ∀ m, a ≠ .proj family 0 m)
    (happ : ∀ (A p x : ProofShape), a ≠ .app (.lam A (p.liftN 1)) x) :
    ProjectionReadout D family info.ctorName Δ a b := by
  intro A value u HT R
  rcases pi_inert_zero_selected_projection_origin heq hs hi hD (control_source HT)
      (pair_select hi hp hf) R with ⟨m, E, _⟩ | RF | ⟨B, payload, x, E, _, _⟩
  · exact (hproj m E).elim
  · exact .compute RF .refl H.common
  · exact (happ B payload x E).elim

private theorem readout_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (small : ∀ {a b u v}, ComputedJointCompareDepth (PiInertStage D 0) depth Δ false a b →
      ControlTyping Δ a (.sort u) → ControlTyping Δ b (.sort v) →
      ProjectionReadout D family info.ctorName Δ a b)
    (HA : ControlTyping Δ (.app f x) (.sort u)) (HB : ControlTyping Δ (.app g y) (.sort v))
    (HF : ComputedJointCompareDepth (PiInertStage D 0) depth Δ false f g)
    (H : ComputedJointCompare (PiInertStage D 0) Δ mode (.app f x) (.app g y)) :
    ProjectionReadout D family info.ctorName Δ (.app f x) (.app g y) := by
  intro A value w HT R
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  rcases pi_inert_zero_selected_projection_origin heq hs hi hD (control_source HT)
      (pair_select hi hp hf) R with ⟨m, E, _⟩ | RF | ⟨B, payload, arg, E, RP, HP⟩
  · cases E
  · exact .compute RF .refl H.common
  · cases E
    exact small (pi_inert_zero_constant_control_application_depth heq hs
      (control_source HA) (control_source HB) HP HF) (HT.compute @hd RP) HB HT RP

private theorem readout_projection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HB : ControlTyping Δ (.proj s i m') (.sort v))
    (HM : ComputedJointCompare (PiInertStage D 0) Δ false m m') :
    ProjectionReadout D family info.ctorName Δ (.proj s i m) (.proj s i m') := by
  intro A value u HT R
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  rcases pi_inert_zero_selected_projection_origin heq hs hi hD (control_source HT)
      (pair_select hi hp hf) R with ⟨major, E, RM⟩ | RF | ⟨B, payload, x, E, _, _⟩
  · cases E
    have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
      intro Ω levels args out HR
      exact erased_level_recovered_stage_spine_levels heq (henv.projectionCtorRigid hi) hD 0 (Δ := Ω) HR
    have HA := HT.compute @hd (pair_select_path hi hp hf)
    obtain ⟨args', RY, HL, HC⟩ := pi_inert_zero_computed_spine_type_exposure heq hs @hroot
      (args := [A, value]) ((ScopedHole.proj family 0 .hole).typed (control_source HT))
      ⟨u, HA⟩ ((ScopedHole.proj family 0 .hole).typed (control_source HB)) RM HM
    cases args' with
    | nil => simp at HL
    | cons B args' =>
      cases args' with
      | nil => simp at HL
      | cons other rest =>
        have EE : rest = [] := by simpa using HL.symm
        subst rest
        exact .compute .refl ((ScopedCompute.proj RY).trans (pair_select_path hi hp hf)) HC
  · exact .compute RF .refl (.proj HM)
  · cases E

private theorem depth_projection_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (H : ComputedJointCompareDepth (PiInertStage D 0) depth Δ mode a b)
    (HA : ControlTyping Δ a (.sort u)) (HB : ControlTyping Δ b (.sort v)) :
    ProjectionReadout D family info.ctorName Δ a b ∧ ProjectionReadout D family info.ctorName Δ b a := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have main : ∀ depth {Δ a b mode u v}, ComputedJointCompareDepth (PiInertStage D 0) depth Δ mode a b →
      ControlTyping Δ a (.sort u) → ControlTyping Δ b (.sort v) →
      ProjectionReadout D family info.ctorName Δ a b ∧ ProjectionReadout D family info.ctorName Δ b a := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth smaller =>
      have inner : ∀ {k Δ kind a b}, ComputedJointCheckDepth (PiInertStage D 0) k Δ kind a b →
          k ≤ depth → ∀ mode, kind = .compare mode → ∀ u v,
          ControlTyping Δ a (.sort u) → ControlTyping Δ b (.sort v) →
          ComputedJointCompare (PiInertStage D 0) Δ mode a b →
          ProjectionReadout D family info.ctorName Δ a b ∧ ProjectionReadout D family info.ctorName Δ b a := by
        intro k Δ kind a b H
        induction H with
        | leaf HL =>
          intro _ mode hk u v HA HB whole
          cases hk
          cases HL with
          | refl => exact ⟨readout_refl heq hs hi hp hf hD, readout_refl heq hs hi hp hf hD⟩
          | sort | const =>
            constructor
            · exact readout_direct heq hs hi hp hf hD whole
                (by intro m E; cases E) (by intro A p x E; cases E)
            · exact readout_direct heq hs hi hp hf hD (.symm whole)
                (by intro m E; cases E) (by intro A p x E; cases E)
          | etaL HE =>
            obtain ⟨_, _, E, _⟩ := HE.shape
            exact (sort_control_not_lam (E ▸ HA)).elim
          | etaR HE =>
            obtain ⟨_, _, E, _⟩ := HE.shape
            exact (sort_control_not_lam (E ▸ HB)).elim
        | @app childDepth Δ f g x y mode HF HX _ _ =>
          intro hn mode hk u v HA HB whole
          cases hk
          have small : ∀ {a b u v}, ComputedJointCompareDepth (PiInertStage D 0) childDepth Δ false a b →
              ControlTyping Δ a (.sort u) → ControlTyping Δ b (.sort v) →
              ProjectionReadout D family info.ctorName Δ a b := by
            intro a b u v H HA HB
            exact (smaller _ (by omega) H HA HB).1
          exact ⟨readout_application heq hs hi hp hf hD small HA HB HF whole,
            readout_application heq hs hi hp hf hD small HB HA (.symm HF) (.symm whole)⟩
        | @appCarrier Δ f A B childDepth g x y mode RN HF HX _ _ =>
          intro hn mode hk u v HA HB whole
          cases hk
          have small : ∀ {a b u v}, ComputedJointCompareDepth (PiInertStage D 0) childDepth Δ false a b →
              ControlTyping Δ a (.sort u) → ControlTyping Δ b (.sort v) →
              ProjectionReadout D family info.ctorName Δ a b := by
            intro a b u v H HA HB
            exact (smaller _ (by omega) H HA HB).1
          exact ⟨readout_application heq hs hi hp hf hD small HA HB HF whole,
            readout_application heq hs hi hp hf hD small HB HA (.symm HF) (.symm whole)⟩
        | @appComputed Δ f A body childDepth g x y mode RF HF HX _ _ =>
          intro hn mode hk u v HA HB whole
          cases hk
          have small : ∀ {a b u v}, ComputedJointCompareDepth (PiInertStage D 0) childDepth Δ false a b →
              ControlTyping Δ a (.sort u) → ControlTyping Δ b (.sort v) →
              ProjectionReadout D family info.ctorName Δ a b := by
            intro a b u v H HA HB
            exact (smaller _ (by omega) H HA HB).1
          exact ⟨readout_application heq hs hi hp hf hD small HA HB HF whole,
            readout_application heq hs hi hp hf hD small HB HA (.symm HF) (.symm whole)⟩
        | proj HM _ =>
          intro hn mode hk u v HA HB whole
          exact ⟨readout_projection heq hs hi hp hf hD HB HM.forget,
            readout_projection heq hs hi hp hf hD HA (.symm HM.forget)⟩
        | compute RA RB HC ih =>
          intro hn mode hk u v HA HB whole
          cases hk
          have IH := ih hn _ rfl u v (HA.compute @hd RA) (HB.compute @hd RB) HC.forget
          exact ⟨readout_prefix IH.1 RA RB, readout_prefix IH.2 RB RA⟩
        | symm HC ih =>
          intro hn mode hk u v HA HB whole
          cases hk
          exact (ih hn _ rfl v u HB HA HC.forget).symm
        | forallE | forallSorted =>
          intro hn mode hk u v HA HB whole
          constructor
          · exact readout_direct heq hs hi hp hf hD whole
              (by intro m E; cases E) (by intro A p x E; cases E)
          · exact readout_direct heq hs hi hp hf hD (.symm whole)
              (by intro m E; cases E) (by intro A p x E; cases E)
        | lam | lamSorted | lamCommon | etaBodyL | etaLams =>
          intro hn mode hk u v HA HB whole
          exact (sort_control_not_lam HA).elim
        | etaBodyR =>
          intro hn mode hk u v HA HB whole
          exact (sort_control_not_lam HB).elim
        | structFields hi' hz' hp' hf' =>
          intro hn mode hk u v HA HB whole
          obtain ⟨Γ, e, hΓ, _, ht, Ee⟩ := HA
          exact (sort_not_constructor hΓ ht hi' hz' hp' hf' Ee).elim
        | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
            carrierSymm | carrierCompute | carrierReduce | carrierNested =>
          intro hn mode hk; cases hk
      intro Δ a b mode u v H HA HB
      exact inner H (Nat.le_refl _) mode rfl u v HA HB H.forget
  exact main depth H HA HB

/-- Contract the selected type field through an arbitrary stage-zero source
computation and full comparison of actual types. Both checking modes and every
recursive carrier-argument rule are covered. The target endpoint is arbitrary;
there is no assumed projection-selection law or general beta closure. -/
theorem pi_inert_zero_computed_pair_projection_contract
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) (.sort u))
    (HB : ControlTyping Δ b (.sort v))
    (R : ScopedCompute (PiInertStage D 0) Δ
      (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) a)
    (H : ComputedJointCompare (PiInertStage D 0) Δ mode a b) :
    ComputedJointCompare (PiInertStage D 0) Δ true A b := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  obtain ⟨depth, HD⟩ := H.depth
  exact (depth_projection_readout heq hs hi hp hf hD HD (HT.compute @hd R) HB).1 HT R

/-- A displayed dependent-pair type projection can be contracted inside the
full stage-zero comparison, including arbitrary internal computation prefixes. -/
theorem pi_inert_zero_pair_type_projection_contract
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) (.sort u))
    (HB : ControlTyping Δ b (.sort v))
    (H : ComputedJointCompare (PiInertStage D 0) Δ mode
      (.proj family 0 (.app (.app (.const info.ctorName []) A) value)) b) :
    ComputedJointCompare (PiInertStage D 0) Δ true A b :=
  pi_inert_zero_computed_pair_projection_contract heq hs hi hp hf hD HT HB .refl H

end Lean4Lean.VEnv.Strengthening
