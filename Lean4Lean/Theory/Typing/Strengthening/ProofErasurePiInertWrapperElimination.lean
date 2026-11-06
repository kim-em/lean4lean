import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCompositionBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineFirstBeta

/-! # Removing identity wrappers from Pi-inert computations

A lambda root cannot expand in this relation, and its identity body stays a
variable even while its annotation changes. Once the wrapper is consumed,
the original argument retains a computation to the exact final output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private lambda_spine_app lambda_spine_lam lambda_spine_not_primitive beta_lambda_spine
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineFirstBeta
variable [Params]

/-- Pi-inert primitives cannot rewrite a displayed lambda. -/
theorem pi_inert_stage_no_lam (H : PiInertStage D n Δ (.lam A b) out) : False := by
  rcases H.2 with H | ⟨u, H⟩
  · exact H
  · cases H

/-- A lambda-headed application likewise has no Pi-inert root primitive. -/
theorem pi_inert_stage_no_lam_app (H : PiInertStage D n Δ (.app (.lam A b) x) out) : False := by
  rcases H.2 with H | ⟨u, H⟩
  · exact H
  · cases H

/-- Lambda computation retains its outer constructor and exact domain path.
No body transport across changed annotations is asserted. -/
theorem ProofShape.ScopedCompute.pi_inert_lam_domain
    (R : ScopedCompute (PiInertStage D n) Δ (.lam A b) out) :
    ∃ A' b', out = .lam A' b' ∧ ScopedCompute (PiInertStage D n) Δ A A' := by
  generalize E : ProofShape.lam A b = source at R
  induction R using ScopedCompute.rootBeta_induction generalizing A b with
  | refl => exact ⟨A, b, E.symm, .refl⟩
  | base H => exact (pi_inert_stage_no_lam (E ▸ H)).elim
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A', b', rfl, RA⟩ := ih₁ E
    obtain ⟨A'', b'', EO, RA'⟩ := ih₂ rfl
    exact ⟨A'', b'', EO, RA.trans RA'⟩
  | lam RA _ => cases E; exact ⟨_, _, rfl, RA⟩
  | beta | app | proj | forallE => cases E

/-- An identity lambda keeps its body fixed through arbitrary Pi-inert
computation, including arbitrary computation of its annotation. -/
theorem ProofShape.ScopedCompute.pi_inert_identity_lam
    (R : ScopedCompute (PiInertStage D n) Δ (.lam A (.bvar 0)) out) :
    ∃ A', out = .lam A' (.bvar 0) ∧ ScopedCompute (PiInertStage D n) Δ A A' := by
  generalize E : ProofShape.lam A (.bvar 0) = source at R
  induction R using ScopedCompute.rootBeta_induction generalizing A with
  | refl => exact ⟨A, E.symm, .refl⟩
  | base H => exact (pi_inert_stage_no_lam (E ▸ H)).elim
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A', rfl, RA⟩ := ih₁ E
    obtain ⟨A'', EO, RA'⟩ := ih₂ rfl
    exact ⟨A'', EO, RA.trans RA'⟩
  | lam RA RB =>
    cases E
    obtain rfl := RB.pi_inert_bvar_fixed
    exact ⟨_, rfl, RA⟩
  | beta | app | proj | forallE => cases E

/-- Before its first head beta, a lambda application retains separate function
and argument paths. Afterwards the exact contractum retains the full tail.
Sort-root primitives are allowed away from the application boundary. -/
theorem ProofShape.ScopedCompute.pi_inert_lambda_app_or_beta
    (R : ScopedCompute (PiInertStage D n) Δ (.app (.lam A b) x) out) :
    (∃ A' b' x', out = .app (.lam A' b') x' ∧
      ScopedCompute (PiInertStage D n) Δ (.lam A b) (.lam A' b') ∧
      ScopedCompute (PiInertStage D n) Δ x x') ∨
    (∃ A' b' x', ScopedCompute (PiInertStage D n) Δ (.lam A b) (.lam A' b') ∧
      ScopedCompute (PiInertStage D n) Δ x x' ∧
      ScopedCompute (PiInertStage D n) Δ (b'.inst x') out) := by
  generalize E : ProofShape.app (.lam A b) x = source at R
  induction R using ScopedCompute.rootBeta_induction generalizing A b x with
  | refl => exact .inl ⟨A, b, x, E.symm, .refl, .refl⟩
  | base H => exact (pi_inert_stage_no_lam_app (E ▸ H)).elim
  | beta => cases E; exact .inr ⟨_, _, _, .refl, .refl, .refl⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨A', b', x', rfl, RF, RX⟩ | ⟨A', b', x', RF, RX, RT⟩
    · rcases ih₂ rfl with ⟨A'', b'', x'', EO, RF', RX'⟩ | ⟨A'', b'', x'', RF', RX', RT⟩
      · exact .inl ⟨A'', b'', x'', EO, RF.trans RF', RX.trans RX'⟩
      · exact .inr ⟨A'', b'', x'', RF.trans RF', RX.trans RX', RT⟩
    · exact .inr ⟨A', b', x', RF, RX, RT.trans R₂⟩
  | app RF RX =>
    cases E
    obtain ⟨A', b', EO, _⟩ := RF.pi_inert_lam_domain
    subst EO
    exact .inl ⟨_, _, _, rfl, RF, RX⟩
  | proj | lam | forallE => cases E

/-- Either the identity wrapper remains, with separately computed annotation
and argument, or the original argument computes directly to the final output.
This is exact at the original restricted stage and needs no typing premise. -/
theorem ProofShape.ScopedCompute.pi_inert_identity_or_eliminate
    (R : ScopedCompute (PiInertStage D n) Δ (.app (.lam A (.bvar 0)) e) out) :
    (∃ A' e', out = .app (.lam A' (.bvar 0)) e' ∧
      ScopedCompute (PiInertStage D n) Δ A A' ∧ ScopedCompute (PiInertStage D n) Δ e e') ∨
    ScopedCompute (PiInertStage D n) Δ e out := by
  rcases R.pi_inert_lambda_app_or_beta with
    ⟨A', b', e', EO, RF, RE⟩ | ⟨A', b', e', RF, RE, RT⟩
  · obtain ⟨A'', EF, RA⟩ := RF.pi_inert_identity_lam
    cases EF
    exact .inl ⟨_, _, EO, RA, RE⟩
  · obtain ⟨A'', EF, _⟩ := RF.pi_inert_identity_lam
    cases EF
    exact .inr (RE.trans (by simpa only [ProofShape.inst, ProofShape.subst,
      ProofShape.Subst.liftN, ProofShape.Subst.one, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using RT))

/-- A final output with no identity-application shape forces wrapper removal.
Conversely a direct path can always be preceded by the wrapper's beta step. -/
theorem ProofShape.ScopedCompute.pi_inert_identity_iff
    (hout : ∀ A' e', out ≠ .app (.lam A' (.bvar 0)) e') :
    ScopedCompute (PiInertStage D n) Δ (.app (.lam A (.bvar 0)) e) out ↔
      ScopedCompute (PiInertStage D n) Δ e out := by
  constructor
  · intro R
    rcases R.pi_inert_identity_or_eliminate with ⟨A', e', E, _, _⟩ | R
    · exact (hout A' e' E).elim
    · exact R
  · intro R
    have RB : ScopedCompute (PiInertStage D n) Δ (.app (.lam A (.bvar 0)) e) e :=
      .beta (by simpa only [ProofShape.inst, ProofShape.subst, ProofShape.Subst.liftN,
        ProofShape.Subst.one, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using (BetaRed.beta (A := A) (b := .bvar 0) (a := e)))
    exact RB.trans R

/-- Until its first head beta, a lambda spine only computes its function and
arguments. After that beta the exact contractum with its pending arguments
computes to the original output. All argument paths and the tail are retained. -/
theorem ProofShape.ScopedCompute.pi_inert_lambda_spine_or_beta
    (R : ScopedCompute (PiInertStage D n) Δ (ProofShape.mkApps (.lam A b) args) out) :
    (∃ A' b' args', out = ProofShape.mkApps (.lam A' b') args' ∧
      ScopedCompute (PiInertStage D n) Δ (.lam A b) (.lam A' b') ∧ List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args args') ∨
    (∃ A' b' x' xs', ScopedCompute (PiInertStage D n) Δ (.lam A b) (.lam A' b') ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args (x' :: xs') ∧ ScopedCompute (PiInertStage D n) Δ (ProofShape.mkApps (b'.inst x') xs') out) := by
  generalize E : ProofShape.mkApps (.lam A b) args = source at R
  induction R generalizing A b args with
  | base H =>
    rcases H.2 with HP | ⟨u, HS⟩
    · exact (lambda_spine_not_primitive A b args (E ▸ HP)).elim
    · have ES := E.trans HS
      cases args using List.snoc_induction with
      | nil => cases ES
      | snoc args a => rw [mkApps_snoc] at ES; cases ES
  | beta H =>
    cases E
    rcases beta_lambda_spine H with ⟨A', b', args', EO, RF, RX⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
    · exact .inl ⟨A', b', args', EO, .beta RF, RX.imp (fun _ _ H => .beta H)⟩
    · exact .inr ⟨A', b', x', xs', .beta RF, RX.imp (fun _ _ H => .beta H), .beta RT⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨A', b', args', rfl, RF, RX⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
    · rcases ih₂ rfl with ⟨A'', b'', args'', EO, RF', RX'⟩ | ⟨A'', b'', x'', xs'', RF', RX', RT⟩
      · exact .inl ⟨A'', b'', args'', EO, RF.trans RF',
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') RX RX'⟩
      · exact .inr ⟨A'', b'', x'', xs'', RF.trans RF',
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') RX RX', RT⟩
    · exact .inr ⟨A', b', x', xs', RF, RX, RT.trans R₂⟩
  | app RF RX ihf ihx =>
    rename_i fOut x xOut
    obtain ⟨args₀, rfl, rfl⟩ := lambda_spine_app E
    rcases ihf rfl with ⟨A', b', args', rfl, RF', RX'⟩ | ⟨A', b', x', xs', RF', RX', RT⟩
    · exact .inl ⟨A', b', args' ++ [_], mkApps_snoc.symm, RF', RX'.append' (.cons RX .nil)⟩
    · refine .inr ⟨A', b', x', xs' ++ [xOut], RF', ?_, ?_⟩
      · exact RX'.append' (.cons RX .nil)
      · rw [mkApps_snoc]
        exact .app RT .refl
  | lam RA RB =>
    obtain ⟨rfl, rfl, rfl⟩ := lambda_spine_lam E
    exact .inl ⟨_, _, [], rfl, .lam RA RB, .nil⟩
  | proj | forallE =>
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [mkApps_snoc] at E; cases E

/-- An exposed carrier cannot retain a lambda at the head of its spine. -/
theorem ProofShape.CarrierExposure.not_lambda_spine (H : CarrierExposure out) :
    ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args := by
  intro A b args E
  cases H with
  | record =>
    have EC := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at EC
    cases EC
  | function =>
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [mkApps_snoc] at E; cases E

/-- Identity expansion at a proper function prefix can be removed while
retaining computations of all pending arguments and the exact final output.
The output condition holds for Eq prefixes and all exposed carriers. -/
theorem ProofShape.ScopedCompute.pi_inert_identity_spine_eliminate
    (hout : ∀ A' b' args', out ≠ ProofShape.mkApps (.lam A' b') args')
    (R : ScopedCompute (PiInertStage D n) Δ
      (ProofShape.mkApps (.app (.lam A (.bvar 0)) e) args) out) :
    ScopedCompute (PiInertStage D n) Δ (ProofShape.mkApps e args) out := by
  change ScopedCompute (PiInertStage D n) Δ (ProofShape.mkApps (.lam A (.bvar 0)) (e :: args)) out at R
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', b', args', EO, _, _⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
  · exact (hout A' b' args' EO).elim
  · obtain ⟨A'', EF, _⟩ := RF.pi_inert_identity_lam
    cases EF
    cases RX with
    | cons RE RX =>
      apply (RE.mkApps RX).trans
      simpa only [ProofShape.inst, ProofShape.subst, ProofShape.Subst.liftN,
        ProofShape.Subst.one, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using RT

end Lean4Lean.VEnv.Strengthening
