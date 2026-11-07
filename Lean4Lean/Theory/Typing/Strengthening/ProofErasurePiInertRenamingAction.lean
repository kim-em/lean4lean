import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertVariableActionBoundary

/-! # Function action with explicit renaming futures

Both the action and its returned carrier history admit exact variable
renamings only. Arbitrary substitution images must retain their own action;
they do not enter through an unrestricted nested history clause. Native
variables construct this action directly, including after computed Pi
exposure of their native type. This supplies an identity environment and a
binder-extension rule, not a fundamental theorem for strong derivations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- Independent carrier and endpoint core residuals, retained after every
exact context renaming. Arbitrary typed substitution is deliberately absent
from this predicate, including from its nested result uses below. -/
structure PiInertRenamingHistory (D : Definitions) (stage : Nat)
    (Δ : List ProofShape) (C a b : ProofShape) : Prop where
  base : PiInertCarrierResidual D stage Δ C a b
  future : ∀ {Δ' τ}, ContextRenaming Δ Δ' τ →
    PiInertCarrierResidual D stage Δ' (C.subst τ) (a.subst τ) (b.subst τ)

/-- Completed histories provide renaming histories. No converse promotion or
arbitrary-substitution closure is asserted for the weaker evidence. -/
theorem PiInertCarrierHistory.renaming_history
    (H : PiInertCarrierHistory D n Δ C a b) : PiInertRenamingHistory D n Δ C a b :=
  ⟨H.base, fun W => H.future W.interpretation⟩

/-- Exact renamings compose, so the returned evidence keeps the same future
restriction at every later world. -/
theorem PiInertRenamingHistory.rename (H : PiInertRenamingHistory D n Δ C a b)
    (W : ContextRenaming Δ Δ' τ) :
    PiInertRenamingHistory D n Δ' (C.subst τ) (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.compose V)

/-- Raising a finite checker stage changes neither the allowed futures nor
the three independent core residuals. -/
theorem PiInertRenamingHistory.raise (hle : n ≤ m) (H : PiInertRenamingHistory D n Δ C a b) :
    PiInertRenamingHistory D m Δ C a b := by
  refine ⟨fun RC RA RB => (H.base RC RA RB).mono (fun R => pi_inert_stage_mono hle R), ?_⟩
  intro Δ' τ W C' a' b' RC RA RB
  exact (H.future W RC RA RB).mono (fun R => pi_inert_stage_mono hle R)

/-- The neutral application case already preserves all independent core
residuals. A variable head remains a variable and the two argument paths feed
the supplied domain residual. No future substitution is used or synthesized. -/
theorem PiInertCarrierResidual.native_application
    (R : ScopedTypeRecovery (PiInertStage D n) Δ (.bvar i) (.forallE A B))
    (H : PiInertCarrierResidual D n Δ A x y) :
    PiInertCarrierResidual D n Δ C (.app (.bvar i) x) (.app (.bvar i) y) := by
  intro C' left right _ RL RR
  obtain ⟨x', rfl, RX⟩ := RL.level_core_bvar_app_inv
  obtain ⟨y', rfl, RY⟩ := RR.level_core_bvar_app_inv
  exact .carrierChecked (.appCarrier R (.leaf .refl) (H .refl RX RY))

/-- Native variable application has full renaming evidence at the input
stage. Exact oracle transport renames recovery, and the input history supplies
the argument residuals in that world. The result carrier may be dependent. -/
theorem PiInertRenamingHistory.native_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (PiInertStage D n) Δ (.bvar i) (.forallE A B))
    (H : PiInertRenamingHistory D n Δ A x y) :
    PiInertRenamingHistory D n Δ C (.app (.bvar i) x) (.app (.bvar i) y) := by
  refine ⟨PiInertCarrierResidual.native_application R H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨j, Ej, _⟩ := W.lookup i
  have R' := R.rename (pi_inert_stage_rename heq hs n) W
  simp only [ProofShape.subst, Ej] at R' ⊢
  intro C' a' b' RC RA RB
  exact PiInertCarrierResidual.native_application R' (H.future W) RC RA RB

/-- Action under exact context renamings, consuming and returning renaming
histories. Output stages may depend on the world and argument pair. Raw
application keeps the left dependent carrier; actual typing is supplied by
clients when erasures of actual applications are reconstructed. -/
structure PiInertRenamingAction (D : Definitions) (Δ : List ProofShape)
    (A B f g : ProofShape) : Prop where
  act : ∀ {Δ' τ x y stage}, ContextRenaming Δ Δ' τ →
    PiInertRenamingHistory D stage Δ' (A.subst τ) x y →
    ∃ n, PiInertRenamingHistory D n Δ' ((B.subst τ.lift).inst x)
      (.app (f.subst τ) x) (.app (g.subst τ) y)

/-- Action itself preserves exact renaming, without changing the restriction
inside the argument and result histories. -/
theorem PiInertRenamingAction.rename
    (H : PiInertRenamingAction D Δ A B f g) (W : ContextRenaming Δ Δ' τ) :
    PiInertRenamingAction D Δ' (A.subst τ) (B.subst τ.lift) (f.subst τ) (g.subst τ) := by
  refine ⟨?_⟩
  intro Δ'' υ x y stage V HX
  have HX' : PiInertRenamingHistory D stage Δ'' (A.subst (τ.comp υ)) x y := by
    simpa only [ProofShape.subst_subst] using HX
  obtain ⟨n, HN⟩ := H.act (W.compose V) HX'
  exact ⟨n, by simpa only [ProofShape.subst_subst, ProofShape.Subst.comp_lift] using HN⟩

/-- A native variable with an actually recovered Pi constructs action. Its
recovery stage and the supplied argument stage combine by max. No action
assumption about arbitrary substituted functions enters this variable seed. -/
theorem pi_inert_native_variable_renaming_action
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (PiInertStage D stage) Δ (.bvar i) (.forallE A B)) :
    PiInertRenamingAction D Δ A B (.bvar i) (.bvar i) := by
  refine ⟨?_⟩
  intro Δ' τ x y n W HX
  obtain ⟨j, Ej, _⟩ := W.lookup i
  have R' := R.rename (pi_inert_stage_rename heq hs stage) W
  simp only [ProofShape.subst, Ej] at R' ⊢
  exact ⟨max stage n, PiInertRenamingHistory.native_application heq hs
    (R'.mono (pi_inert_stage_mono (Nat.le_max_left stage n)))
    (HX.raise (Nat.le_max_right stage n))⟩

/-- The action retained by a substitution image at its substituted native
type. Every Pi reached by actual finite computation in any later renaming
world must have action. Non-Pi syntax is not treated as a vacuous literal-Pi
test: aliases, beta wrappers and future Pi exposures are included. Construction
for arbitrary actual images remains a separate interpretation obligation. -/
structure PiInertImageAction (D : Definitions) (Δ : List ProofShape) (e T : ProofShape) : Prop where
  expose : ∀ {Δ' τ stage A B}, ContextRenaming Δ Δ' τ →
    ScopedCompute (PiInertStage D stage) Δ' (T.subst τ) (.forallE A B) →
    PiInertRenamingAction D Δ' A B (e.subst τ) (e.subst τ)

/-- The retained image obligation transports by composing exact renamings.
Pi exposure happens in the final world and need not reflect to an older one. -/
theorem PiInertImageAction.rename
    (H : PiInertImageAction D Δ e T) (W : ContextRenaming Δ Δ' τ) :
    PiInertImageAction D Δ' (e.subst τ) (T.subst τ) := by
  refine ⟨?_⟩
  intro Δ'' υ stage A B V R
  have R' : ScopedCompute (PiInertStage D stage) Δ'' (T.subst (τ.comp υ)) (.forallE A B) := by
    simpa only [ProofShape.subst_subst] using R
  have HA : PiInertRenamingAction D Δ'' A B (e.subst (τ.comp υ)) (e.subst (τ.comp υ)) :=
    H.expose (W.compose V) R'
  simpa only [ProofShape.subst_subst] using HA

/-- Every native variable has the full image obligation, including computed
Pi exposures of an arbitrary native type in each later world. This is the
constructive variable seed unavailable for unrestricted completed histories. -/
theorem pi_inert_native_variable_image_action
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    PiInertImageAction D Δ (.bvar i) (contextOracle Δ i) := by
  refine ⟨?_⟩
  intro Δ' τ stage A B W R
  obtain ⟨j, Ej, ET⟩ := W.lookup i
  have RR : ScopedTypeRecovery (PiInertStage D stage) Δ' (.bvar j) (.forallE A B) :=
    (show ScopedTypeRecovery (PiInertStage D stage) Δ' (.bvar j) (contextOracle Δ' j)
      from .bvar).convert (ET.symm ▸ R)
  simpa only [ProofShape.subst, Ej] using pi_inert_native_variable_renaming_action heq hs RR

/-- Semantic image data accompanies an ordinary typed context substitution.
The action of every raw image is retained at the substituted native type.
This is a sufficient image condition; no fundamental theorem constructing it
for arbitrary terms, or preservation under arbitrary composition, is asserted. -/
structure PiInertActionSubstitution (D : Definitions)
    (Δ Δ' : List ProofShape) (σ : ProofShape.Subst) : Prop where
  typed : ContextSubstitution Δ Δ' σ
  images : ∀ i, PiInertImageAction D Δ' (σ i) ((contextOracle Δ i).subst σ)

/-- Identity has retained image action without a general function theorem.
Each raw variable starts from its native oracle and actual Pi computation. -/
theorem PiInertActionSubstitution.identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    PiInertActionSubstitution D Δ Δ ProofShape.Subst.id := by
  refine ⟨ContextRenaming.identity.interpretation, ?_⟩
  intro i
  rw [ProofShape.subst_id]
  exact pi_inert_native_variable_image_action heq hs

/-- Renaming a target transports the ordinary interpretation and every image
action. No arbitrary-image composition theorem is smuggled into this step. -/
theorem PiInertActionSubstitution.rename
    (H : PiInertActionSubstitution D Δ Δ' σ) (W : ContextRenaming Δ' Δ'' τ) :
    PiInertActionSubstitution D Δ Δ'' (σ.comp τ) := by
  refine ⟨ContextSubstitution.comp H.typed W.interpretation, ?_⟩
  intro i
  simpa only [ProofShape.Subst.comp, ProofShape.subst_subst] using (H.images i).rename W

/-- Extending a source binder requires both its ordinary typed interpretation
and the new image's action at the substituted declaration. Tail obligations
reduce to the original native assignments by lift/substitution cancellation.
The new image evidence is explicit, rather than inferred from its typing. -/
theorem PiInertActionSubstitution.cons
    (H : PiInertActionSubstitution D Δ Δ' σ)
    (W : ContextSubstitution (T::Δ) Δ' (σ.cons x))
    (HX : PiInertImageAction D Δ' x (T.subst σ)) :
    PiInertActionSubstitution D (T::Δ) Δ' (σ.cons x) := by
  refine ⟨W, ?_⟩
  intro i
  cases i with
  | zero => simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.cons,
      ProofShape.lift_subst_cons] using HX
  | succ i => simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.cons,
      ProofShape.lift_subst_cons] using H.images i

/-- Actual sort evidence constructs the exact fresh-variable renaming needed
to lift an interpreted environment under a binder. -/
theorem pi_inert_action_binder_renaming (S : DomainSort Δ A u) :
    ContextRenaming Δ (A::Δ) (fun i => .bvar (i+1)) := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := S
  have W := ContextRenaming.of_liftN hΓ
    (show OnCtx (a::Γ) (env.IsType univs) from ⟨hΓ, u, ha⟩) Ctx.LiftN.one
  simpa only [proofEraseCtx, EΓ, Ea, liftVar_base'] using W

/-- The genuine binder-lifting case is constructive: rename all old images,
then add the new native variable with its proved action. The ordinary typed
substitution uses its existing binder rule. No arbitrary function image or
completed-history-to-action law is assumed. -/
theorem PiInertActionSubstitution.lift
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertActionSubstitution D Δ Δ' σ) (S : DomainSort Δ T u) :
    PiInertActionSubstitution D (T::Δ) (T.subst σ :: Δ') σ.lift := by
  let τ : ProofShape.Subst := fun i => .bvar (i+1)
  have W : ContextRenaming Δ' (T.subst σ :: Δ') τ :=
    pi_inert_action_binder_renaming (ContextSubstitution.sort H.typed S)
  have EC : (σ.comp τ).cons (.bvar 0) = σ.lift := by
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      simp only [ProofShape.Subst.cons, ProofShape.Subst.comp, ProofShape.Subst.lift]
      simpa only [liftVar_base'] using (subst_bvar_liftN (n := 1) (k := 0) (σ i))
  have HT : T.subst (σ.comp τ) = (T.subst σ).liftN 1 := by
    rw [← ProofShape.subst_subst]
    simpa only [liftVar_base'] using (subst_bvar_liftN (n := 1) (k := 0) (T.subst σ))
  have HX : PiInertImageAction D (T.subst σ :: Δ') (.bvar 0) (T.subst (σ.comp τ)) := by
    rw [HT]
    exact pi_inert_native_variable_image_action heq hs
  have Hcons := (H.rename W).cons (EC.symm ▸ ContextSubstitution.cons H.typed) HX
  simpa only [EC] using Hcons

end Lean4Lean.VEnv.Strengthening
