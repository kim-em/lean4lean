import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreProjectionContraction

/-! # Constructor fields through surviving stage-zero wrappers

Constant expansions may remain at the endpoint of a constructor computation.
Removing their tracked head frames exposes the same constructor with computed
arguments. This records a finite beta path, without normalizing the arguments
or assuming closure of the comparison checker under beta reduction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private control_realize
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeReadout
open private variable_readout_pair
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertVariableReadout
variable [Params] {D : Definitions}

/-- Administrative expansion at a proper spine prefix can be bypassed with
pending arguments and an arbitrary endpoint. Surviving wrappers are recorded
as head deletions; no non-lambda condition is imposed on the output. -/
theorem pi_inert_expansion_prefix_count_bypass_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps target pending))
    (H : ConstantExpansion source target ∨ NativeIdentityExpansion Recovery Δ source target)
    (RT : ScopedComputeCount (PiInertStage D n) cost Δ (ProofShape.mkApps target pending) out) :
    ∃ lower k, k ≤ cost ∧
      ScopedComputeCount (PiInertStage D n) k Δ (ProofShape.mkApps source pending) lower ∧
      AdministrativeHeadDeletion out lower := by
  rcases H with H | H
  · cases H with
    | intro _ =>
      obtain ⟨lower, k, hk, RK, HK⟩ :=
        (ConstantHeadDeletion.drop.mkApps pending).compute heq hs HT RT
      exact ⟨lower, k, hk, RK, .constant HK⟩
  · cases H with
    | intro _ =>
      obtain ⟨lower, k, hk, RK, HK⟩ :=
        (IdentityHeadDeletion.drop.mkApps pending).compute RT
      exact ⟨lower, k, hk, RK, .identity HK⟩

private theorem stable_spine_frames_count
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c ls) args))
    (R : ScopedComputeCount (PiInertStage D 0) cost Δ (ProofShape.mkApps (.const c ls) args) out) :
    ∃ ls' args', AdministrativeHeadDeletion out (ProofShape.mkApps (.const c ls') args') ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) args args' := by
  induction cost using Nat.strongRecOn generalizing out with
  | ind cost ih =>
    rcases R.const_spine_or_cut @hroot with ⟨ls', args', rfl, HL, HA⟩ |
        ⟨ls', pre, pending, target, cp, ct, HC, _, _, RP, HR, HN, RT⟩
    · exact ⟨ls', args', .refl, HL, HA⟩
    have HT' : TypedSource Δ (ProofShape.mkApps target pending) := by
      apply HT.pi_inert_compute heq hs
      refine RP.forget.trans ?_
      rw [ProofShape.mkApps_append]
      exact ((ScopedComputeCount.base HR).mkApps .refl).forget
    rcases HR.1 with HR | HR
    · exact (HN HR).elim
    · obtain ⟨lower, k, hk, RK, HK⟩ := pi_inert_expansion_prefix_count_bypass_frames
        heq hs HT' (Recovery := PiInertStage D 0) (.inl HR) RT
      rw [← ProofShape.mkApps_append] at RK
      obtain ⟨lastLevels, lastArgs, HD, HL, HA⟩ := ih (cp + k) (by omega) (RP.trans RK)
      exact ⟨lastLevels, lastArgs, HK.trans HD, HL, HA⟩

/-- Every stage-zero computation from a core-stable constant spine exposes
that same head after finitely many administrative endpoint deletions. Argument
paths stay at stage zero in the original scope. Outputs may be lambda-headed;
there is no confluence or normalization premise. -/
theorem pi_inert_zero_stable_spine_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c ls) args))
    (R : ScopedCompute (PiInertStage D 0) Δ (ProofShape.mkApps (.const c ls) args) out) :
    ∃ ls' args', AdministrativeHeadDeletion out (ProofShape.mkApps (.const c ls') args') ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute (PiInertStage D 0) Δ) args args' := by
  obtain ⟨cost, RC⟩ := R.count
  exact stable_spine_frames_count heq hs @hroot HT RC

/-- Selection survives an arbitrary stage-zero constructor-major path modulo
administrative endpoint deletion. The same argument index is preserved and
the original selected field computes to the new one at the same stage. -/
theorem pi_inert_zero_constructor_selection_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : TypedSource Δ m)
    (RI : Primitive D (.proj family i m) field)
    (R : ScopedCompute (PiInertStage D 0) Δ m out) :
    ∃ major selected, AdministrativeHeadDeletion out major ∧
      Primitive D (.proj family i major) selected ∧
      ScopedCompute (PiInertStage D 0) Δ field selected := by
  cases RI with
  | projIota hi' hl hg =>
    cases henv.ordered.projections_unique hi hi'
    have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
      intro Ω levels params target HR
      exact erased_level_recovered_stage_spine_levels heq (henv.projectionCtorRigid hi) hD 0
        (Δ := Ω) HR
    obtain ⟨ls', args', HD, _, HA⟩ := pi_inert_zero_stable_spine_frames heq hs @hroot HT R
    obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hg
    have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
    have RF := HA.getElem_of (info.nparams + i) hj hj'
    rw [HE] at RF
    exact ⟨_, _, HD, .projIota hi (HA.length_eq.symm.trans hl)
      (List.getElem?_eq_some_iff.2 ⟨hj', rfl⟩), RF⟩

/-- A sorted projection that can immediately select a field commutes with
any stage-zero computation up to a finite beta tail and at most one final
projection iota. The field side retains stage zero and the original scope.
This is a computation square, not forward closure of checker comparisons. -/
theorem pi_inert_zero_selected_projection_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.proj family i m) (.sort u))
    (RI : Primitive D (.proj family i m) field)
    (R : ScopedCompute (PiInertStage D 0) Δ (.proj family i m) out) :
    ∃ selected middle, ScopedCompute (PiInertStage D 0) Δ field selected ∧
      BetaRed out middle ∧ (middle = selected ∨ Primitive D middle selected) := by
  have HM : TypedSource Δ m := by
    apply (ScopedHole.proj family i .hole).typed
    obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := HT
    exact ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩
  obtain ⟨major, lower, HD, RM, RR⟩ := pi_inert_sorted_projection_terminal_frames heq hs HT R
  rcases RR.keep_or_primitive (D := D) with rfl | RR
  · obtain ⟨last, selected, HDM, RI', RF⟩ :=
      pi_inert_zero_constructor_selection_frames heq hs hi hD HM RI RM
    exact ⟨selected, _, RF, HD.reduce.trans (.proj HDM.reduce), .inr RI'⟩
  · have hout : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
      cases RR with
      | projIota =>
        intro A b rest E
        have HC := congrArg ProofShape.constHead E
        simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HC
        cases HC
    obtain ⟨selected, RI', RF⟩ :=
      pi_inert_zero_constructor_selection_residual heq hs hi hD HM RI hout RM
    have E := RI'.projection_deterministic RR
    exact ⟨selected, lower, RF, HD.reduce, .inl E.symm⟩

/-- Every residual of a selectable sorted projection still compares with its
selected field at stage zero. The square supplies computations of both sides
to a shared result; general forward comparison closure is not needed. -/
theorem pi_inert_zero_selected_projection_residual_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.proj family i m) (.sort u))
    (RI : Primitive D (.proj family i m) field)
    (R : ScopedCompute (PiInertStage D 0) Δ (.proj family i m) out) :
    ComputedJointCompare (PiInertStage D 0) Δ mode field out := by
  obtain ⟨selected, middle, RF, RB, HE⟩ :=
    pi_inert_zero_selected_projection_square heq hs hi hD HT RI R
  have RO : ScopedCompute (PiInertStage D 0) Δ out selected := by
    rcases HE with rfl | RI'
    · exact .beta RB
    · exact (ScopedCompute.beta RB).trans (.base (pi_inert_stage_core (.inl (.inl (.inl RI')))))
  exact .compute RF RO (.leaf .refl)

/-- Both terminal projection choices compare along a directed stage-zero major
path. Either end may retain or select its field, and arbitrary wrappers may
occur in the path. Unlike the common-major join argument, this directed case
needs no typed core confluence, even when the selected field is not normal. -/
theorem pi_inert_zero_projection_results_of_major_path
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.proj family i m) (.sort u))
    (R : ScopedCompute (PiInertStage D 0) Δ m m')
    (RL : ProjectionResult family i m left) (RR : ProjectionResult family i m' right) :
    ComputedJointCompare (PiInertStage D 0) Δ mode left right := by
  have RT : ScopedCompute (PiInertStage D 0) Δ (.proj family i m) right := by
    apply (ScopedCompute.proj R).trans
    exact RR.compute.in_pi_inert_stage
  rcases RL.keep_or_primitive (D := D) with rfl | RL
  · exact .compute RT .refl (.leaf .refl)
  · exact pi_inert_zero_selected_projection_residual_compare heq hs hi hD HT RL RT

/-- At a literal variable output the square is exact: neither beta nor a
projection primitive can move the variable. Selecting the original field
therefore preserves and reflects stage-zero readout of that variable. -/
theorem pi_inert_zero_selected_projection_variable_path_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.proj family i m) (.sort u))
    (RI : Primitive D (.proj family i m) field) :
    ScopedCompute (PiInertStage D 0) Δ (.proj family i m) (.bvar j) ↔
      ScopedCompute (PiInertStage D 0) Δ field (.bvar j) := by
  constructor
  · intro R
    obtain ⟨selected, middle, RF, RB, HE⟩ :=
      pi_inert_zero_selected_projection_square heq hs hi hD HT RI R
    have E : middle = .bvar j :=
      (show ScopedCompute (PiInertStage D 0) Δ (.bvar j) middle from .beta RB).pi_inert_bvar_fixed
    subst middle
    rcases HE with rfl | HE
    · exact RF
    · cases HE
  · intro R
    exact (ScopedCompute.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans R

/-- Selection preserves and reflects the full stage-zero comparison with a
sort-typed variable, in either checker mode. Both endpoint typings are actual;
there is no assumed field-selection certificate or beta-closure principle.
The arbitrary opposite-endpoint comparison remains a separate open task. -/
theorem pi_inert_zero_selected_projection_variable_compare_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : ControlTyping Δ (.proj family i m) (.sort u))
    (HV : ControlTyping Δ (.bvar j) (.sort v))
    (RI : Primitive D (.proj family i m) field) :
    ComputedJointCompare (PiInertStage D 0) Δ mode (.proj family i m) (.bvar j) ↔
      ComputedJointCompare (PiInertStage D 0) Δ mode field (.bvar j) := by
  constructor
  · intro H
    obtain ⟨Γ, b, hΓ, EΓ, hb, Eb⟩ := HV
    obtain ⟨a, ha, Ea⟩ := control_realize HT hΓ EΓ
    have R := (variable_readout_pair heq hs H hΓ ha hb EΓ Ea Eb).2 j rfl
    have RF := (pi_inert_zero_selected_projection_variable_path_iff heq hs hi hD HT RI).1 R
    exact .compute RF .refl (.leaf .refl)
  · intro H
    exact .compute (.base (pi_inert_stage_core (.inl (.inl (.inl RI))))) .refl H

end Lean4Lean.VEnv.Strengthening
