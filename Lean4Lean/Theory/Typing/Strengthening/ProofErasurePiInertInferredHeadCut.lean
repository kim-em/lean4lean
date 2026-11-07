import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRigidSortFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpineCutReadout

/-! # Inferred comparison cuts at inert variable and lambda heads

Computation and symmetry can obscure the rule comparing a displayed lambda.
The cut below retains both actual computation paths and the complete terminal
lambda rule, including its body context and sorted-domain witnesses. It does
not replace inferred comparison by a common reduct or assume application
closure. A rigid-sort source body retains its frame tree at the cut.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The non-computational rules that can compare two displayed lambdas in
inferred mode. Symmetry retains which annotation scopes the body child. -/
inductive InferredLambdaTerminal (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) : ProofShape → ProofShape → ProofShape → ProofShape → Prop where
  | refl : InferredLambdaTerminal Step Δ A b A b
  | lam : ComputedJointCompare Step Δ false A C →
      ComputedJointCompare Step (A :: Δ) false b d → InferredLambdaTerminal Step Δ A b C d
  | sorted : DomainSort Δ A u → DomainSort Δ C u →
      ComputedJointCompare Step Δ true A C →
      ComputedJointCompare Step (A :: Δ) false b d → InferredLambdaTerminal Step Δ A b C d
  | eta : ComputedJointCompare Step Δ false A C →
      (EtaHead (.lam A b) (.lam C d) ∨ EtaHead (.lam C d) (.lam A b)) →
      InferredLambdaTerminal Step Δ A b C d
  | symm : InferredLambdaTerminal Step Δ A b C d → InferredLambdaTerminal Step Δ C d A b

/-- A terminal cut retains the original recursive comparison certificate. -/
theorem InferredLambdaTerminal.compare (H : InferredLambdaTerminal Step Δ A b C d) :
    ComputedJointCompare Step Δ false (.lam A b) (.lam C d) := by
  induction H with
  | refl => exact .leaf .refl
  | lam HD HB => exact .lam HD HB
  | sorted SA SC HD HB => exact .lamSorted SA SC HD HB
  | eta HD HE => exact .etaLams HD HE
  | symm _ ih => exact .symm ih

private theorem inferred_lambda_cut
    (H : ComputedJointCheck (PiInertStage D n) Δ kind a b)
    (hk : kind = .compare false)
    (HL : (∃ A body, a = .lam A body) ∨ ∃ C body, b = .lam C body) :
    ∃ A x C y, ScopedCompute (PiInertStage D n) Δ a (.lam A x) ∧
      ScopedCompute (PiInertStage D n) Δ b (.lam C y) ∧
      InferredLambdaTerminal (PiInertStage D n) Δ A x C y := by
  induction H with
  | leaf H =>
    cases hk
    cases H with
    | refl =>
      rcases HL with ⟨A, x, rfl⟩ | ⟨A, x, rfl⟩ <;>
        exact ⟨A, x, A, x, .refl, .refl, .refl⟩
    | sort | const => rcases HL with ⟨_, _, E⟩ | ⟨_, _, E⟩ <;> cases E
  | lam HD HB => exact ⟨_, _, _, _, .refl, .refl, .lam HD (by cases hk; exact HB)⟩
  | lamSorted SA SC HD HB => exact ⟨_, _, _, _, .refl, .refl, .sorted SA SC HD (by cases hk; exact HB)⟩
  | etaLams HD HE => exact ⟨_, _, _, _, .refl, .refl, .eta HD HE⟩
  | compute RA RB HC ih =>
    obtain ⟨A, x, C, y, RX, RY, HC⟩ := ih hk (by
      rcases HL with ⟨A, x, E⟩ | ⟨C, y, E⟩
      · obtain ⟨A', x', E', _⟩ := (E ▸ RA).pi_inert_lam_domain
        exact .inl ⟨A', x', E'⟩
      · obtain ⟨C', y', E', _⟩ := (E ▸ RB).pi_inert_lam_domain
        exact .inr ⟨C', y', E'⟩)
    exact ⟨A, x, C, y, RA.trans RX, RB.trans RY, HC⟩
  | symm HC ih =>
    obtain ⟨A, x, C, y, RX, RY, HT⟩ := ih hk HL.symm
    exact ⟨C, y, A, x, RY, RX, .symm HT⟩
  | app | appCarrier | appComputed | proj | forallE | forallSorted =>
    rcases HL with ⟨_, _, E⟩ | ⟨_, _, E⟩ <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- An inferred comparison with one displayed lambda computes both endpoints
to a terminal lambda rule. No source or target typing premise is required. -/
theorem ProofShape.ComputedJointCompare.pi_inert_lambda_cut
    (H : ComputedJointCompare (PiInertStage D n) Δ false (.lam A b) g) :
    ∃ A' b' C d, ScopedCompute (PiInertStage D n) Δ (.lam A b) (.lam A' b') ∧
      ScopedCompute (PiInertStage D n) Δ g (.lam C d) ∧
      InferredLambdaTerminal (PiInertStage D n) Δ A' b' C d :=
  inferred_lambda_cut H rfl (.inl ⟨A, b, rfl⟩)

/-- A rigid-sort source body keeps its exact frame data through the comparison
cut. The opposite body remains connected by the actual terminal lambda rule;
no transport of that body's computation across annotations is assumed. -/
theorem RigidSortFrames.inferred_lambda_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HB : RigidSortFrames c (A :: Δ) b)
    (H : ComputedJointCompare (PiInertStage D n) Δ false (.lam A b) g) :
    ∃ A' b' C d, ScopedCompute (PiInertStage D n) Δ (.lam A b) (.lam A' b') ∧
      ScopedCompute (PiInertStage D n) Δ g (.lam C d) ∧
      RigidSortFrames c (A' :: Δ) b' ∧
      InferredLambdaTerminal (PiInertStage D n) Δ A' b' C d := by
  obtain ⟨A', b', C, d, RL, RR, HT⟩ := H.pi_inert_lambda_cut
  obtain ⟨A'', b'', E, HB'⟩ := HB.lambda_compute heq hs hc hD RL
  cases E
  exact ⟨A', b', C, d, RL, RR, HB', HT⟩

private theorem inferred_variable_paths
    (H : ComputedJointCheck (PiInertStage D n) Δ kind a b)
    (hk : kind = .compare false) (HE : a = .bvar i ∨ b = .bvar i) :
    ScopedCompute (PiInertStage D n) Δ a (.bvar i) ∧
      ScopedCompute (PiInertStage D n) Δ b (.bvar i) := by
  induction H with
  | leaf H =>
    cases hk
    cases H with
    | refl => rcases HE with rfl | rfl <;> exact ⟨.refl, .refl⟩
    | sort | const => rcases HE with E | E <;> cases E
  | compute RA RB HC ih =>
    obtain ⟨RL, RR⟩ := ih hk (by
      rcases HE with E | E
      · exact .inl ((E ▸ RA).pi_inert_bvar_fixed)
      · exact .inr ((E ▸ RB).pi_inert_bvar_fixed))
    exact ⟨RA.trans RL, RB.trans RR⟩
  | symm HC ih => exact (ih hk HE.symm).symm
  | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
    rcases HE with E | E <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- Inferred comparison against an inert variable supplies a directed path
from the opposite endpoint to that exact variable, at the same stage. -/
theorem ProofShape.ComputedJointCompare.pi_inert_bvar_exposure
    (H : ComputedJointCompare (PiInertStage D n) Δ false (.bvar i) b) :
    ScopedCompute (PiInertStage D n) Δ b (.bvar i) :=
  (inferred_variable_paths H rfl (.inl rfl)).2

/-- Common-mode comparison of actual types inherits variable exposure. This
is the typed case needed by identity-wrapper bodies, rather than an untyped
promotion of every common-mode comparison to inferred checking. -/
theorem proofErase_pi_inert_type_variable_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) (Ea : proofErase Γ a = .bvar i) :
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ b) (.bvar i) := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht HR.1
  have HI := proofErase_computed_joint_types_inferred hd hΓ ha hb H
  rw [Ea] at HI
  exact HI.pi_inert_bvar_exposure

/-- Raw lambda comparison cannot be replaced by inferred body comparison,
even at identical annotations: the eta rule permits a proof-marker argument.
The long body beta-returns to proof and cannot compute to the identity's bound
variable at any Pi-inert stage. This refutes an untyped shortcut only; the
intended sort-valued comparison analysis must retain actual endpoint typings. -/
theorem pi_inert_raw_identity_body_counterexample (A : ProofShape) :
    let body := ProofShape.app ((ProofShape.lam A (.bvar 0)).liftN 1) .proof
    ComputedJointCompare (PiInertStage D n) Δ false (.lam A (.bvar 0)) (.lam A body) ∧
      BetaRed body .proof ∧
      ¬ ComputedJointCompare (PiInertStage D n) (A :: Δ) false (.bvar 0) body := by
  dsimp only
  have EL : (ProofShape.lam A (.bvar 0)).liftN 1 = .lam (A.liftN 1) (.bvar 0) := by
    simp only [ProofShape.liftN, liftVar, Nat.zero_lt_succ, ↓reduceIte]
  refine ⟨.etaLams (.leaf .refl) (.inr .proof), ?_, ?_⟩
  · rw [EL]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons] using
      (ProofShape.BetaRed.beta (A := A.liftN 1) (b := .bvar 0) (a := .proof))
  · intro HB
    have R := HB.pi_inert_bvar_exposure
    rw [EL] at R
    rcases R.pi_inert_identity_or_eliminate with ⟨A', e', E, _, _⟩ | R
    · cases E
    · cases R.pi_inert_proof_fixed

end Lean4Lean.VEnv.Strengthening
