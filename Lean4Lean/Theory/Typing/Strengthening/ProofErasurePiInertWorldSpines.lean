import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCoreWorlds
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnchoredCarrier

/-! # Retaining dependent recovery along variable application spines

Application must return more than a carrier history when its result will be
applied again. Variable spines retain inferred comparison and native recovery
with an ordinary-core output tail. These components extend through another
argument without converting an arbitrary function history into action.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- A neutral application has independent head and argument core paths.
Only the head is protected; earlier arguments may contain arbitrary redexes. -/
theorem ProofShape.AnchoredCarrier.level_core_app_inv
    (HF : AnchoredCarrier 0 f) (R : Compute (ErasedLevelCore D) (.app f x) out) :
    ∃ f' x', out = .app f' x' ∧ Compute (ErasedLevelCore D) f f' ∧
      Compute (ErasedLevelCore D) x x' := by
  obtain ⟨i, args, _, rfl⟩ := HF
  rw [← ProofShape.mkApps_snoc] at R
  obtain ⟨args', E, HA⟩ := R.level_core_bvar_spine
  have spine {as bs : List ProofShape} (H : List.Forall₂ (Compute (ErasedLevelCore D)) as bs)
      {a b} (R : Compute (ErasedLevelCore D) a b) :
      Compute (ErasedLevelCore D) (ProofShape.mkApps a as) (ProofShape.mkApps b bs) := by
    induction H generalizing a b with
    | nil => exact R
    | cons H _ ih => exact ih (.app R H)
  induction args' using List.snoc_induction with
  | nil => have hlen := HA.length_eq; simp at hlen
  | snoc args' x' _ =>
    obtain ⟨HP, HX⟩ := (Lean4Lean.List.Forall₂.append_of_right (by rfl)).mp HA
    cases HX with
    | cons RX Hnil =>
      cases Hnil
      exact ⟨_, _, E.trans ProofShape.mkApps_snoc, spine HP .refl, RX⟩

/-- Native recovery follows every ordinary-core residual of the expression.
Its chosen type may reduce by ordinary core computation; it is not required
to remain the exact syntactic recovery output. -/
def PiInertRecoveryResidual (D : Definitions) (n : Nat)
    (Δ : List ProofShape) (e T : ProofShape) : Prop :=
  ∀ {e'}, Compute (ErasedLevelCore D) e e' → ∃ T',
    ScopedTypeRecovery (PiInertStage D n) Δ e' T' ∧ Compute (ErasedLevelCore D) T T'

/-- Recovery residuals in every certified variable world. The type tail is
retained inside each future, allowing subsequent dependent application. -/
structure PiInertWorldRecovery (D : Definitions) (n : Nat)
    (Δ : List ProofShape) (e T : ProofShape) : Prop where
  base : PiInertRecoveryResidual D n Δ e T
  future : ∀ {Δ' τ}, PiInertCoreWorld D Δ Δ' τ →
    PiInertRecoveryResidual D n Δ' (e.subst τ) (T.subst τ)

/-- Inferred comparison with independent endpoint residuals in every core
world. This is stronger than carrier-only evidence at a supplied function type. -/
structure PiInertWorldComparison (D : Definitions) (n : Nat)
    (Δ : List ProofShape) (a b : ProofShape) : Prop where
  base : PiInertInterpret D n (.compare false) Δ a b
  future : ∀ {Δ' τ}, PiInertCoreWorld D Δ Δ' τ →
    PiInertInterpret D n (.compare false) Δ' (a.subst τ) (b.subst τ)

/-- Recovery moves by composition of the allowed worlds. -/
theorem PiInertWorldRecovery.move (H : PiInertWorldRecovery D n Δ e T)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertWorldRecovery D n Δ' (e.subst τ) (T.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.compose V)

/-- Inferred comparisons retain the same future restriction after moving. -/
theorem PiInertWorldComparison.move (H : PiInertWorldComparison D n Δ a b)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertWorldComparison D n Δ' (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.compose V)

/-- Stage enlargement preserves the ordinary-core recovery tail. -/
theorem PiInertWorldRecovery.raise (hle : n ≤ m) (H : PiInertWorldRecovery D n Δ e T) :
    PiInertWorldRecovery D m Δ e T := by
  have go {Δ e T} (H : PiInertRecoveryResidual D n Δ e T) : PiInertRecoveryResidual D m Δ e T := by
    intro e' R
    obtain ⟨T', HT, RT⟩ := H R
    exact ⟨T', HT.mono (fun H => pi_inert_stage_mono hle H), RT⟩
  refine ⟨fun R => go H.base R, ?_⟩
  intro Δ' τ W e' R
  exact go (H.future W) R

/-- Stage enlargement preserves every independent comparison residual. -/
theorem PiInertWorldComparison.raise (hle : n ≤ m) (H : PiInertWorldComparison D n Δ a b) :
    PiInertWorldComparison D m Δ a b := by
  refine ⟨?_, ?_⟩
  · intro a' b' RA RB
    exact (H.base RA RB).mono (fun R => pi_inert_stage_mono hle R)
  · intro Δ' τ W a' b' RA RB
    exact (H.future W RA RB).mono (fun R => pi_inert_stage_mono hle R)

/-- A retained type computation consumes the recovery tail at its source.
The result keeps the new type's ordinary-core tail for later application. -/
theorem PiInertRecoveryResidual.convert (H : PiInertRecoveryResidual D n Δ e T)
    (R : PiInertInterpret D n .compute Δ T U) : PiInertRecoveryResidual D n Δ e U := by
  intro e' RE
  obtain ⟨T', HT, RT⟩ := H RE
  obtain ⟨shared, RS, RU⟩ := R.2 RT
  exact ⟨shared, HT.convert RS, RU⟩

/-- Certified type computation transports recovery in all core worlds. No
arbitrary definitional type equality is claimed to supply that computation. -/
theorem PiInertWorldRecovery.convert (H : PiInertWorldRecovery D n Δ e T)
    (R : PiInertWorldComputation D n Δ T U) : PiInertWorldRecovery D n Δ e U := by
  refine ⟨fun RE => PiInertRecoveryResidual.convert H.base R.base RE, ?_⟩
  intro Δ' τ W e' RE
  exact PiInertRecoveryResidual.convert (H.future W) (R.future W) RE

/-- A neutral application's selected dependent type follows both codomain
computation and argument computation. No common reduct of two distinct
arguments, nor any type-recovery premise for the argument, is required. -/
theorem PiInertRecoveryResidual.app (HF : AnchoredCarrier 0 f)
    (H : PiInertRecoveryResidual D n Δ f (.forallE A B)) :
    PiInertRecoveryResidual D n Δ (.app f x) (B.inst x) := by
  intro out R
  obtain ⟨f', x', rfl, RF, RX⟩ := HF.level_core_app_inv R
  obtain ⟨T', HT, RT⟩ := H RF
  obtain ⟨A', B', rfl, _, RB⟩ := RT.pi_parts (fun R => erased_level_core_no_pi R)
  refine ⟨B'.inst x', .app HT, ?_⟩
  have RB' : Compute (ErasedLevelCore D) (B.inst x) (B'.inst x) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      RB.subst (fun H => erased_level_core_subst H) (σ := ProofShape.Subst.one x)
  exact RB'.trans (RX.inst_argument (fun H => level_lift H) B')

/-- Certified variable worlds preserve the neutral head invariant. -/
theorem PiInertCoreWorld.anchored (W : PiInertCoreWorld D Δ Δ' τ)
    (H : AnchoredCarrier 0 f) : AnchoredCarrier 0 (f.subst τ) := by
  apply H.subst
  intro i _
  obtain ⟨j, Ej, _⟩ := W.lookup i
  exact ⟨j, Nat.zero_le _, Ej⟩

/-- Neutral recovery extends by an argument in every world, preserving the
exact selected dependent type up to the retained ordinary-core tail. -/
theorem PiInertWorldRecovery.app (HF : AnchoredCarrier 0 f)
    (H : PiInertWorldRecovery D n Δ f (.forallE A B)) :
    PiInertWorldRecovery D n Δ (.app f x) (B.inst x) := by
  refine ⟨fun R => PiInertRecoveryResidual.app HF H.base R, ?_⟩
  intro Δ' τ W
  simp only [ProofShape.subst, ProofShape.subst_inst]
  intro out R
  exact PiInertRecoveryResidual.app (W.anchored HF) (H.future W) R

/-- A neutral pair extends its inferred comparison by carrier-related
arguments. Recovery and domain residuals use the same computed Pi, while the
two heads and arguments may independently follow ordinary-core paths. -/
theorem pi_inert_neutral_app_interpret
    (HF : AnchoredCarrier 0 f) (HG : AnchoredCarrier 0 g)
    (HR : PiInertRecoveryResidual D n Δ f (.forallE A B))
    (HC : PiInertInterpret D n (.compare false) Δ f g)
    (HX : PiInertCarrierResidual D n Δ A x y) :
    PiInertInterpret D n (.compare false) Δ (.app f x) (.app g y) := by
  intro left right RL RR
  obtain ⟨f', x', rfl, RF, RX⟩ := HF.level_core_app_inv RL
  obtain ⟨g', y', rfl, RG, RY⟩ := HG.level_core_app_inv RR
  obtain ⟨T', HT, RT⟩ := HR RF
  obtain ⟨A', B', rfl, RA, _⟩ := RT.pi_parts (fun R => erased_level_core_no_pi R)
  exact .appCarrier HT (HC RF RG) (HX RA RX RY)

/-- The inferred application comparison retains its full core-world clause. -/
theorem PiInertWorldComparison.app
    (HF : AnchoredCarrier 0 f) (HG : AnchoredCarrier 0 g)
    (HR : PiInertWorldRecovery D n Δ f (.forallE A B))
    (HC : PiInertWorldComparison D n Δ f g)
    (HX : PiInertWorldHistory D n Δ A x y) :
    PiInertWorldComparison D n Δ (.app f x) (.app g y) := by
  refine ⟨pi_inert_neutral_app_interpret HF HG HR.base HC.base HX.base, ?_⟩
  intro Δ' τ W left right RL RR
  exact pi_inert_neutral_app_interpret (W.anchored HF) (W.anchored HG)
    (HR.future W) (HC.future W) (HX.future W) RL RR

/-- Inferred evidence supplies a carrier history at any selected carrier.
This direction does not recover inferred evidence from a carrier history. -/
theorem PiInertWorldComparison.history (H : PiInertWorldComparison D n Δ a b) :
    PiInertWorldHistory D n Δ C a b := by
  refine ⟨fun _ RA RB => .carrierChecked (ComputedJointCompare.common (H.base RA RB)), ?_⟩
  intro Δ' τ W C' a' b' _ RA RB
  exact .carrierChecked (ComputedJointCompare.common (H.future W RA RB))

/-- A neutral value pair retains the selected left native type, inferred
comparison and variable heads. The selected type need not be a literal Pi.
Every component is preserved when a further argument is supplied below. -/
structure PiInertWorldNeutral (D : Definitions) (n : Nat)
    (Δ : List ProofShape) (f g T : ProofShape) : Prop where
  left : AnchoredCarrier 0 f
  right : AnchoredCarrier 0 g
  recovery : PiInertWorldRecovery D n Δ f T
  comparison : PiInertWorldComparison D n Δ f g

/-- Neutral pairs move through the allowed variable worlds. -/
theorem PiInertWorldNeutral.move (H : PiInertWorldNeutral D n Δ f g T)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertWorldNeutral D n Δ' (f.subst τ) (g.subst τ) (T.subst τ) :=
  ⟨W.anchored H.left, W.anchored H.right, H.recovery.move W, H.comparison.move W⟩

/-- Neutral pairs raise all computational components to one common stage. -/
theorem PiInertWorldNeutral.raise (hle : n ≤ m) (H : PiInertWorldNeutral D n Δ f g T) :
    PiInertWorldNeutral D m Δ f g T :=
  ⟨H.left, H.right, H.recovery.raise hle, H.comparison.raise hle⟩

/-- Retained computation changes the selected recovered type without changing
the neutral comparison. Arbitrary assigned-type conversion remains separate. -/
theorem PiInertWorldNeutral.convert (H : PiInertWorldNeutral D n Δ f g T)
    (R : PiInertWorldComputation D n Δ T U) : PiInertWorldNeutral D n Δ f g U :=
  ⟨H.left, H.right, H.recovery.convert R, H.comparison⟩

/-- Application returns the whole neutral package, including dependent
recovery. Thus a function-valued result can later accept another argument. -/
theorem PiInertWorldNeutral.app (H : PiInertWorldNeutral D n Δ f g (.forallE A B))
    (HX : PiInertWorldHistory D n Δ A x y) :
    PiInertWorldNeutral D n Δ (.app f x) (.app g y) (B.inst x) := by
  have extend {e} (H : AnchoredCarrier 0 e) (x : ProofShape) : AnchoredCarrier 0 (.app e x) := by
    obtain ⟨i, args, hi, rfl⟩ := H
    exact ⟨i, args ++ [x], hi, ProofShape.mkApps_snoc.symm⟩
  exact ⟨extend H.left x, extend H.right y, H.recovery.app H.left,
    PiInertWorldComparison.app H.left H.right H.recovery H.comparison HX⟩

/-- A retained neutral Pi supplies application action in all variable worlds.
The returned history is read from a constructed neutral package, so this is
not a whole-function-history-to-action principle. -/
theorem PiInertWorldNeutral.action (H : PiInertWorldNeutral D n Δ f g (.forallE A B)) :
    PiInertWorldAction D Δ A B f g := by
  refine ⟨?_⟩
  intro Δ' τ x y stage W HX
  have H' := (H.move W).raise (Nat.le_max_left n stage)
  have K := H'.app (HX.raise (Nat.le_max_right n stage))
  exact ⟨max n stage, K.comparison.history⟩

/-- Neutral pairs retain image action at their selected type, including every
later computed Pi exposure. The recovery tail composes with the supplied
computation, and the resulting action still returns core-world histories. -/
theorem PiInertWorldNeutral.image_action (H : PiInertWorldNeutral D n Δ f g T) :
    PiInertWorldImageAction D Δ f g T := by
  refine ⟨?_⟩
  intro Δ' τ stage A B W R
  exact (((H.move W).raise (Nat.le_max_left n stage)).convert
    (R.raise (Nat.le_max_right n stage))).action

/-- Every raw native variable constructs the complete neutral package at
stage zero. Future oracle conversion uses its reverse retained certificate
and returns a core reduct of the old substituted native type. -/
theorem pi_inert_native_variable_world_neutral :
    PiInertWorldNeutral D 0 Δ (.bvar i) (.bvar i) (contextOracle Δ i) := by
  refine ⟨⟨i, [], Nat.zero_le i, rfl⟩, ⟨i, [], Nat.zero_le i, rfl⟩, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro e' R
      obtain rfl := R.level_core_bvar_fixed
      exact ⟨_, .bvar, .refl⟩
    · intro Δ' τ W e' R
      obtain ⟨j, Ej, _, HR⟩ := W.lookup i
      simp only [ProofShape.subst, Ej] at R
      obtain rfl := R.level_core_bvar_fixed
      obtain ⟨shared, RS, RT⟩ := HR.base.2 .refl
      exact ⟨shared, .convert .bvar RS, RT⟩
  · refine ⟨?_, ?_⟩
    · intro a b RA RB
      obtain rfl := RA.level_core_bvar_fixed
      obtain rfl := RB.level_core_bvar_fixed
      exact .leaf .refl
    · intro Δ' τ W a b RA RB
      obtain ⟨j, Ej, _⟩ := W.lookup i
      simp only [ProofShape.subst, Ej] at RA RB
      obtain rfl := RA.level_core_bvar_fixed
      obtain rfl := RB.level_core_bvar_fixed
      exact .leaf .refl

/-- A finite dependent argument sequence retains each computational Pi
exposure and its argument history. The next selected type is instantiated at
the left argument; it need not already have Pi syntax. -/
inductive PiInertWorldArguments (D : Definitions) (n : Nat) (Δ : List ProofShape) :
    ProofShape → List ProofShape → List ProofShape → ProofShape → Prop where
  | nil : PiInertWorldArguments D n Δ T [] [] T
  | cons : PiInertWorldComputation D n Δ T (.forallE A B) →
      PiInertWorldHistory D n Δ A x y →
      PiInertWorldArguments D n Δ (B.inst x) xs ys U →
      PiInertWorldArguments D n Δ T (x::xs) (y::ys) U

/-- Every finite dependent sequence preserves the whole neutral package.
In particular the final value retains image action when it is later exposed
as a function, instead of stopping at its carrier-history component. -/
theorem PiInertWorldArguments.run (H : PiInertWorldArguments D n Δ T xs ys U)
    (N : PiInertWorldNeutral D n Δ f g T) :
    PiInertWorldNeutral D n Δ (ProofShape.mkApps f xs) (ProofShape.mkApps g ys) U := by
  induction H generalizing f g with
  | nil => exact N
  | cons R HX _ ih => exact ih ((N.convert R).app HX)

/-- Actual non-proof application reconstructs the exact erased dependent
result and returns the entire neutral package. The actual equality premises
justify common typing of the two applications, while the two semantic inputs
can come from the original smaller strong children at a shared finite stage.
Proof-valued applications erase to proof and are not claimed to stay neutral. -/
theorem PiInertWorldNeutral.apply_actual_nonproof
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.IsDefEq univs Γ f g (.forallE A B))
    (hX : env.IsDefEq univs Γ x y A) (hn : ¬ IsProof Γ (.app f x))
    (H : PiInertWorldNeutral D n (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B)))
    (HX : PiInertWorldHistory D n (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertWorldNeutral D n (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) (proofErase Γ (B.inst x)) := by
  have hApp := hF.appDF hX
  have hn' : ¬ IsProof Γ (.app g y) := fun hp =>
    hn (isProof_of_common_type hΓ hApp.hasType.2 hApp.hasType.1 hp)
  obtain ⟨v, hPi⟩ := hF.hasType.1.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨w, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  rw [EP] at H
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
    show proofErase Γ (.app g y) = .app _ _ from if_neg hn',
    proofErase_instN hΓA hX.hasType.1 Ctx.InstN.zero hB]
  exact H.app HX

end Lean4Lean.VEnv.Strengthening
