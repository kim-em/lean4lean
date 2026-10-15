import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPairedApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots

/-! # Reading annotations from scoped self-application comparisons

Finite computation can change and duplicate diagonal annotations, but cannot
change the bound-variable self-application body. Comparing the resulting loops
therefore supplies a comparison of their original annotations. The result is
uniform over primitives with constant or projection heads, including core and
singleton-prefix computation; it does not require fixed annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape

/-- A diagonal function with a retained self-application body. -/
def diagonal (A : ProofShape) : ProofShape := .lam A (.app (.bvar 0) (.bvar 0))
/-- Self-application of two identical annotated diagonals. -/
def selfLoop (A : ProofShape) : ProofShape := .app (diagonal A) (diagonal A)

private theorem scoped_normal_fixed
    (R : ScopedCompute Step Δ a b) (hn : ∀ Δ, NormalSyntax (Step Δ) a) : b = a := by
  induction R with
  | base H => exact ((hn _).no_step H).elim
  | beta H => exact H.fixed_of_normal (hn [])
  | trans _ _ ih₁ ih₂ =>
    have E := ih₁ hn
    exact (ih₂ (E.symm ▸ hn)).trans E
  | app _ _ ihf iha =>
    exact congr (congrArg ProofShape.app (ihf (fun Δ => (hn Δ).2.2.1)))
      (iha (fun Δ => (hn Δ).2.2.2))
  | proj _ ih => exact congrArg _ (ih (fun Δ => (hn Δ).2))
  | lam _ _ ihA ihb =>
    exact congr (congrArg ProofShape.lam (ihA (fun Δ => (hn Δ).2.1)))
      (ihb (fun Δ => (hn Δ).2.2))
  | forallE _ _ ihA ihb =>
    exact congr (congrArg ProofShape.forallE (ihA (fun Δ => (hn Δ).2.1)))
      (ihb (fun Δ => (hn Δ).2.2))

private theorem body_normal {Step : List ProofShape → ProofShape → ProofShape → Prop}
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a) (Δ) :
    NormalSyntax (Step Δ) (.app (.bvar 0) (.bvar 0)) := by
  exact ⟨fun _ H => hhead H, (fun _ _ H => nomatch H),
    ⟨fun _ H => hhead H, trivial⟩, ⟨fun _ H => hhead H, trivial⟩⟩

private theorem beta_diagonal_inv (R : BetaRed (diagonal A) out) :
    ∃ A', out = diagonal A' ∧ BetaRed A A' := by
  obtain ⟨A', b', E, RA, RB⟩ := R.lam_inv
  have EB := RB.fixed_of_normal (body_normal (Step := fun _ _ _ => False) (fun H => H.elim) [])
  exact ⟨A', E.trans (congrArg (ProofShape.lam A') EB), RA⟩

/-- Computation of a diagonal changes only its annotation, even across changes
of the binder context. No typing or context-conversion hypothesis is needed. -/
theorem ScopedCompute.diagonal_inv
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (diagonal A) out) :
    ∃ A', out = diagonal A' ∧ ScopedCompute Step Δ A A' := by
  generalize E : diagonal A = source at R
  induction R generalizing A with
  | base H => exact (E ▸ hhead H).elim
  | beta H =>
    cases E
    obtain ⟨A', HE, HA⟩ := beta_diagonal_inv H
    exact ⟨A', HE, .beta HA⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, rfl, RA⟩ := ih₁ E
    obtain ⟨A₂, HE, RB⟩ := ih₂ rfl
    exact ⟨A₂, HE, RA.trans RB⟩
  | lam RA RB =>
    cases E
    have EB := scoped_normal_fixed RB (body_normal hhead)
    exact ⟨_, congrArg (ProofShape.lam _) EB, RA⟩
  | app | proj | forallE => cases E

private theorem beta_loop_residual
    (R : BetaRed source out)
    (EA : ScopedCompute Step Δ D A) (EB : ScopedCompute Step Δ D B)
    (E : source = .app (diagonal A) (diagonal B)) :
    ∃ A' B', out = .app (diagonal A') (diagonal B') ∧
      ScopedCompute Step Δ D A' ∧ ScopedCompute Step Δ D B' := by
  induction R generalizing A B with
  | refl => exact ⟨A, B, E, EA, EB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, E₁, HA, HB⟩ := ih₁ EA EB E
    exact ih₂ HA HB E₁
  | app RF RX =>
    cases E
    obtain ⟨A', rfl, RA⟩ := beta_diagonal_inv RF
    obtain ⟨B', rfl, RB⟩ := beta_diagonal_inv RX
    exact ⟨A', B', rfl, EA.trans (.beta RA), EB.trans (.beta RB)⟩
  | beta =>
    cases E
    refine ⟨B, B, ?_, EB, EB⟩
    simp [diagonal, ProofShape.inst, ProofShape.liftN_zero]
  | proj | lam | forallE => cases E

private theorem loop_residual
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ source out)
    (EA : ScopedCompute Step Δ D A) (EB : ScopedCompute Step Δ D B)
    (E : source = .app (diagonal A) (diagonal B)) :
    ∃ A' B', out = .app (diagonal A') (diagonal B') ∧
      ScopedCompute Step Δ D A' ∧ ScopedCompute Step Δ D B' := by
  induction R generalizing A B with
  | base H => exact (E ▸ hhead H).elim
  | beta H => exact beta_loop_residual H EA EB E
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, E₁, HA, HB⟩ := ih₁ EA EB E
    exact ih₂ HA HB E₁
  | app RF RX =>
    cases E
    obtain ⟨A', rfl, RA⟩ := RF.diagonal_inv hhead
    obtain ⟨B', rfl, RB⟩ := RX.diagonal_inv hhead
    exact ⟨A', B', rfl, EA.trans RA, EB.trans RB⟩
  | proj | lam | forallE => cases E

/-- Every finite computation of a self-application loop retains two diagonals.
Both resulting annotations compute from the original annotation, even when beta
has discarded one diagonal and duplicated the other arbitrarily many times. -/
theorem ScopedCompute.selfLoop_inv
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (selfLoop A) out) :
    ∃ A' B', out = .app (diagonal A') (diagonal B') ∧
      ScopedCompute Step Δ A A' ∧ ScopedCompute Step Δ A B' :=
  loop_residual hhead R .refl .refl rfl

private theorem no_lift_zero (f : ProofShape) : f.liftN 1 ≠ .bvar 0 := by
  cases f <;> simp [ProofShape.liftN, liftVar]

private theorem no_eta_diagonal (H : EtaHead (diagonal A) f) : False := by
  generalize E : diagonal A = a at H
  cases H with
  | boundVar => exact no_lift_zero _ (ProofShape.app.inj (ProofShape.lam.inj E).2).1.symm
  | proof => cases (ProofShape.app.inj (ProofShape.lam.inj E).2).2

private theorem no_constructor_diagonal
    (E : diagonal A = mkApps (.const c ls) args) : False := by
  have H := congrArg constHead E
  simp only [constHead_mkApps, diagonal, constHead] at H
  cases H

private theorem no_constructor_loop
    (E : .app (diagonal A) (diagonal B) = mkApps (.const c ls) args) : False := by
  have H := congrArg constHead E
  simp only [constHead_mkApps, diagonal, constHead] at H
  cases H

variable [Params]
/-- Inferred comparison of diagonal functions exposes their annotations in
common mode. All computations inside the certificate are retained as annotation
paths; no normality of either annotation is required. -/
theorem ScopedCompare.diagonal_annotations
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ScopedCompare Step Δ mode (diagonal A) (diagonal B)) (hm : mode = false) :
    ScopedCompare Step Δ true A B := by
  generalize EA : diagonal A = a at H
  generalize EB : diagonal B = b at H
  induction H generalizing A B with
  | leaf H =>
    cases H with
    | refl => cases ProofShape.lam.inj (EA.trans EB.symm) |>.1; exact .refl
    | sort | const => cases EA
    | etaL | etaR => cases hm
  | lam HD HB => cases EA; cases EB; exact HD.common
  | lamSorted _ _ HD HB => cases EA; cases EB; exact HD
  | etaLams HD HE =>
    cases EA; cases EB
    exact (HE.elim no_eta_diagonal no_eta_diagonal).elim
  | compute RA RB HC ih =>
    obtain ⟨A', E₁, HA⟩ := (EA ▸ RA).diagonal_inv hhead
    obtain ⟨B', E₂, HB⟩ := (EB ▸ RB).diagonal_inv hhead
    exact .compute HA HB (ih hm E₁.symm E₂.symm)
  | symm HC ih => exact (ih hm EB EA).symm
  | structFields => exact (no_constructor_diagonal EA).elim
  | lamCommon | etaBodyL | etaBodyR => cases hm
  | app | proj | forallE | forallSorted => cases EA

private theorem compare_loops
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ScopedCompare Step Δ mode a b)
    (HA : ScopedCompute Step Δ D A) (HB : ScopedCompute Step Δ D B)
    (HC : ScopedCompute Step Δ E C) (HF : ScopedCompute Step Δ E F)
    (EA : a = .app (diagonal A) (diagonal B))
    (EB : b = .app (diagonal C) (diagonal F)) : ScopedCompare Step Δ true D E := by
  induction H generalizing D E A B C F with
  | leaf H =>
    cases H with
    | refl =>
      have E := ProofShape.lam.inj (ProofShape.app.inj (EA.symm.trans EB)).1 |>.1
      exact .compute HA HC (E ▸ ScopedCompare.refl)
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.symm.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.symm.trans E
  | app Hf Hx =>
    cases EA; cases EB
    exact .compute HA HC (Hf.diagonal_annotations hhead rfl)
  | compute Ra Rb H ih =>
    obtain ⟨A', B', EA', HA', HB'⟩ := loop_residual hhead Ra HA HB EA
    obtain ⟨C', F', EB', HC', HF'⟩ := loop_residual hhead Rb HC HF EB
    exact ih HA' HB' HC' HF' EA' EB'
  | symm H ih => exact (ih HC HF HA HB EB EA).symm
  | structFields => exact (no_constructor_loop EA.symm).elim
  | etaBodyR => cases EB
  | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA

/-- Comparing self-application loops in either mode recovers common comparison
of their original annotations. This includes arbitrary finite computation and
recursive eta/structure certificates in the comparison. -/
theorem ScopedCompare.selfLoop_annotations
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ScopedCompare Step Δ mode (selfLoop A) (selfLoop B)) :
    ScopedCompare Step Δ true A B :=
  compare_loops hhead H .refl .refl .refl .refl rfl rfl

end ProofShape
end Lean4Lean.VEnv.Strengthening
