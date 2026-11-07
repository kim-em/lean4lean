import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertPairedAction

/-! # Variable worlds with certified native-type conversion

Exact renaming alone does not cover the computed binder annotation in function
carrier residuals. These worlds still map variables only to variables, but
their native types may differ by bidirectional stage-zero computation evidence.
Composition transports the retained type evidence, never arbitrary term action.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erasedTypeOracle_outOfBounds
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredWeakening
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- Canonical Eq supplies a typed proof marker even for the default oracle
entries beyond a context's length. No inhabitant of an arbitrary binder is
assumed: the representative is a closed reflexive equality proof. -/
theorem typed_proof_source_of_canonical_eq
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) :
    TypedSource (proofEraseCtx Γ) .proof := by
  have hα : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have ha : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hp := HasType.eqReflApp heq (by trivial) hα ha
  have hE := HasType.eqApp heq (by trivial) hα ha ha
  exact ⟨Γ, _, _, hΓ, rfl, hp, proofErase_eq_proof.2 ⟨_, hp, hE⟩⟩

/-- Every oracle entry of an actual context has a typed representative.
Valid entries use their declared type; default proof entries use canonical Eq.
This supports total oracle transport without pretending default entries are
valid variable declarations. -/
theorem typed_context_oracle_source
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) (i : Nat) :
    TypedSource (proofEraseCtx Γ) (contextOracle (proofEraseCtx Γ) i) := by
  rw [proofEraseCtx_oracle]
  by_cases hi : i < Γ.length
  · obtain ⟨A, hl⟩ := Lookup.ofLt hi
    obtain ⟨u, hA⟩ := IsType.lookup henv hΓ hl
    rw [erasedTypeOracle_valid hΓ hl]
    exact ⟨Γ, A, _, hΓ, rfl, hA, rfl⟩
  · rw [erasedTypeOracle_outOfBounds (by omega)]
    exact typed_proof_source_of_canonical_eq heq hΓ

/-- A variable-only interpreted world map whose native oracle assignments
agree up to retained stage-zero computation in both directions. These are
type certificates, not an unrestricted substitution rule for term histories.
The fixed zero stage excludes guarded positive-stage conversion assumptions. -/
structure PiInertCoreWorld (D : Definitions)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop where
  typed : ContextSubstitution Δ Δ' τ
  lookup : ∀ i, ∃ j, τ i = .bvar j ∧
    PiInertEvidence D 0 .compute Δ' ((contextOracle Δ i).subst τ) (contextOracle Δ' j) ∧
    PiInertEvidence D 0 .compute Δ' (contextOracle Δ' j) ((contextOracle Δ i).subst τ)

/-- Exact renaming is a core world when its target oracle has actual typed
representatives. The type evidence is reflexive and retains all core residuals. -/
theorem PiInertCoreWorld.of_exact
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (W : ContextRenaming Δ Δ' τ)
    (HT : ∀ j, TypedSource Δ' (contextOracle Δ' j)) : PiInertCoreWorld D Δ Δ' τ := by
  refine ⟨W.interpretation, ?_⟩
  intro i
  obtain ⟨j, Ej, ET⟩ := W.lookup i
  have HR : PiInertEvidence D 0 .compute Δ' (contextOracle Δ' j) (contextOracle Δ' j) :=
    .of_core_join hc (HT j) (HT j) .refl
  exact ⟨j, Ej, by rwa [← ET], by rwa [← ET]⟩

/-- An actual source context and its interpreted exact renaming supply the
required target realization automatically, including its default entries. -/
theorem PiInertCoreWorld.of_exact_actual
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (W : ContextRenaming (proofEraseCtx Γ) Δ' τ) :
    PiInertCoreWorld D (proofEraseCtx Γ) Δ' τ := by
  obtain ⟨Γ', σ, hΓ', EΓ', _, _⟩ := W.interpretation hΓ rfl
  exact .of_exact hc W (fun j => by simpa only [EΓ'] using typed_context_oracle_source heq hΓ' j)

/-- Core worlds compose because their native-type certificates already
transport under ordinary interpreted substitution. The composed term images
remain variables, and no term-action closure is invoked. -/
theorem PiInertCoreWorld.compose (W : PiInertCoreWorld D Δ Δ' σ)
    (V : PiInertCoreWorld D Δ' Δ'' τ) : PiInertCoreWorld D Δ Δ'' (σ.comp τ) := by
  refine ⟨ContextSubstitution.comp W.typed V.typed, ?_⟩
  intro i
  obtain ⟨j, Ej, HL, HR⟩ := W.lookup i
  obtain ⟨k, Ek, KL, KR⟩ := V.lookup j
  refine ⟨k, by simp only [ProofShape.Subst.comp, Ej, ProofShape.subst, Ek], ?_, ?_⟩
  · simpa only [ProofShape.subst_subst] using (HL.substitute V.typed).trans KL
  · simpa only [ProofShape.subst_subst] using KR.trans (HR.substitute V.typed)

/-- A world extends under an actual sorted binder. Old native-type
certificates weaken; the fresh variable uses reflexive native-type evidence.
Both contexts retain the same substituted binder annotation. -/
theorem PiInertCoreWorld.cons
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (W : PiInertCoreWorld D Δ Δ' τ) (S : DomainSort Δ A u) :
    PiInertCoreWorld D (A::Δ) (A.subst τ :: Δ') τ.lift := by
  have ST := ContextSubstitution.sort W.typed S
  have V := pi_inert_action_binder_renaming ST
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := ST
  have hΓA : OnCtx (a::Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
  have EC : proofEraseCtx (a::Γ) = A.subst τ :: Δ' := by simp only [proofEraseCtx, EΓ, Ea]
  have HT : TypedSource (A.subst τ :: Δ') (contextOracle (A.subst τ :: Δ') 0) := by
    simpa only [EC] using typed_context_oracle_source heq hΓA 0
  have H0 : PiInertEvidence D 0 .compute (A.subst τ :: Δ')
      (contextOracle (A.subst τ :: Δ') 0) (contextOracle (A.subst τ :: Δ') 0) :=
    .of_core_join hc HT HT .refl
  refine ⟨ContextSubstitution.cons W.typed, ?_⟩
  intro i
  cases i with
  | zero =>
    refine ⟨0, rfl, ?_, ?_⟩
    all_goals simpa only [contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift] using H0
  | succ i =>
    obtain ⟨j, Ej, HL, HR⟩ := W.lookup i
    have EL (e : ProofShape) : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
      simpa only [liftVar_base'] using subst_bvar_liftN (n := 1) (k := 0) e
    refine ⟨j+1, ?_, ?_, ?_⟩
    · simp only [ProofShape.Subst.lift, Ej, ProofShape.liftN, liftVar_base']
    · simpa only [contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, EL]
        using HL.substitute V.interpretation
    · simpa only [contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, EL]
        using HR.substitute V.interpretation

/-- Ordinary core reduction of a realized binder annotation constructs a
core world with identity term images. Only the newest native type changes;
the other oracle entries agree literally. This is precisely the context move
needed by independent Pi-carrier residuals. -/
theorem PiInertCoreWorld.core_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (S : DomainSort Δ A u)
    (R : Compute (ErasedLevelCore D) A A') :
    PiInertCoreWorld D (A::Δ) (A'::Δ) ProofShape.Subst.id := by
  have W : ContextSubstitution (A::Δ) (A'::Δ) ProofShape.Subst.id :=
    ContextSubstitution.core_binder hs R
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := S
  have hΓA : OnCtx (a::Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
  have EC : proofEraseCtx (a::Γ) = A::Δ := by simp only [proofEraseCtx, EΓ, Ea]
  obtain ⟨Γ', σ, hΓ', EΓ', _, _⟩ := W hΓA EC
  have HL (i) : TypedSource (A'::Δ) (contextOracle (A::Δ) i) := by
    have H : TypedSource (A::Δ) (contextOracle (A::Δ) i) := by
      simpa only [EC] using typed_context_oracle_source heq hΓA i
    simpa only [ProofShape.subst_id] using H.subst W
  have HR (i) : TypedSource (A'::Δ) (contextOracle (A'::Δ) i) := by
    simpa only [EΓ'] using typed_context_oracle_source heq hΓ' i
  refine ⟨W, ?_⟩
  intro i
  have J : ComputeJoin (ErasedLevelCore D) (contextOracle (A::Δ) i) (contextOracle (A'::Δ) i) := by
    cases i with
    | zero => exact .of_compute (R.liftN (fun H => level_lift H))
    | succ i => exact .refl
  refine ⟨i, rfl, ?_, ?_⟩
  · simpa only [ProofShape.subst_id] using PiInertEvidence.of_core_join hc (HL i) (HR i) J
  · simpa only [ProofShape.subst_id] using PiInertEvidence.of_core_join hc (HR i) (HL i) J.symm

/-- Carrier evidence retained under variable worlds with certified native-type
conversion. Independent core residuals remain part of every world, but arbitrary
function images cannot enter through the future clause. -/
structure PiInertWorldHistory (D : Definitions) (stage : Nat)
    (Δ : List ProofShape) (C a b : ProofShape) : Prop where
  base : PiInertCarrierResidual D stage Δ C a b
  future : ∀ {Δ' τ}, PiInertCoreWorld D Δ Δ' τ →
    PiInertCarrierResidual D stage Δ' (C.subst τ) (a.subst τ) (b.subst τ)

/-- Full substitution evidence restricts to core worlds; the converse is not
assumed, including for histories returned by application. -/
theorem PiInertCarrierHistory.world_history (H : PiInertCarrierHistory D n Δ C a b) :
    PiInertWorldHistory D n Δ C a b := ⟨H.base, fun W => H.future W.typed⟩

/-- Composing variable worlds retains exactly the same future discipline. -/
theorem PiInertWorldHistory.move (H : PiInertWorldHistory D n Δ C a b)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertWorldHistory D n Δ' (C.subst τ) (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.compose V)

/-- Stage enlargement preserves the fixed class of variable futures. -/
theorem PiInertWorldHistory.raise (hle : n ≤ m) (H : PiInertWorldHistory D n Δ C a b) :
    PiInertWorldHistory D m Δ C a b := by
  refine ⟨fun RC RA RB => (H.base RC RA RB).mono (fun R => pi_inert_stage_mono hle R), ?_⟩
  intro Δ' τ W C' a' b' RC RA RB
  exact (H.future W RC RA RB).mono (fun R => pi_inert_stage_mono hle R)

/-- On an actual context the new history supplies the earlier renaming
history, so its Eq-probe descent readout remains available. -/
theorem PiInertWorldHistory.renaming_history
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PiInertWorldHistory D n (proofEraseCtx Γ) C a b) :
    PiInertRenamingHistory D n (proofEraseCtx Γ) C a b :=
  ⟨H.base, fun W => H.future (.of_exact_actual heq hc hΓ W)⟩

/-- Retained directed computation with only variable-world futures. The
ordinary-core output tail is essential when a native oracle changes: a bare
directed computation path supplies no commutation with that change. -/
structure PiInertWorldComputation (D : Definitions) (stage : Nat)
    (Δ : List ProofShape) (a b : ProofShape) : Prop where
  base : PiInertInterpret D stage .compute Δ a b
  future : ∀ {Δ' τ}, PiInertCoreWorld D Δ Δ' τ →
    PiInertInterpret D stage .compute Δ' (a.subst τ) (b.subst τ)

/-- Existing hereditary computation provides variable-world computation. -/
theorem PiInertEvidence.world_computation (H : PiInertEvidence D n .compute Δ a b) :
    PiInertWorldComputation D n Δ a b := ⟨H.base, fun W => H.future W.typed⟩

/-- Computation moves through the same composed variable worlds as histories. -/
theorem PiInertWorldComputation.move (H : PiInertWorldComputation D n Δ a b)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertWorldComputation D n Δ' (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.compose V)

/-- Raising a computation stage retains the typed output and core tail. -/
theorem PiInertWorldComputation.raise (hle : n ≤ m)
    (H : PiInertWorldComputation D n Δ a b) : PiInertWorldComputation D m Δ a b :=
  ⟨H.base.raise hle, fun W => (H.future W).raise hle⟩

/-- Sequential computation composes through ordinary output residuals, with
no confluence assumption about the guarded checker stage. -/
theorem PiInertWorldComputation.trans (H : PiInertWorldComputation D n Δ a b)
    (K : PiInertWorldComputation D n Δ b c) : PiInertWorldComputation D n Δ a c :=
  ⟨H.base.trans K.base, fun W => (H.future W).trans (K.future W)⟩

/-- A retained computation from the native type to a Pi suffices for neutral
application, even when its common output has reduced the Pi domain. The
argument's independent carrier residual consumes precisely that domain path. -/
theorem PiInertInterpret.native_application
    (R : PiInertInterpret D n .compute Δ (contextOracle Δ i) (.forallE A B))
    (H : PiInertCarrierResidual D n Δ A x y) :
    PiInertCarrierResidual D n Δ C (.app (.bvar i) x) (.app (.bvar i) y) := by
  obtain ⟨shared, RP, RT⟩ := R.2 .refl
  obtain ⟨A', B', rfl, RD, _⟩ := RT.pi_parts (fun R => erased_level_core_no_pi R)
  intro C' left right _ RL RR
  obtain ⟨x', rfl, RX⟩ := RL.level_core_bvar_app_inv
  obtain ⟨y', rfl, RY⟩ := RR.level_core_bvar_app_inv
  exact .carrierChecked (.appCarrier (.convert .bvar RP) (.leaf .refl) (H RD RX RY))

/-- Native application retains all core worlds. At each future variable,
the reverse native-type certificate is composed with the supplied Pi
computation; no generic checker context-conversion law is invoked. -/
theorem PiInertWorldHistory.native_application
    (R : PiInertWorldComputation D n Δ (contextOracle Δ i) (.forallE A B))
    (H : PiInertWorldHistory D n Δ A x y) :
    PiInertWorldHistory D n Δ C (.app (.bvar i) x) (.app (.bvar i) y) := by
  refine ⟨R.base.native_application H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨j, Ej, _, HR⟩ := W.lookup i
  have RF := ((HR.raise (Nat.zero_le n)).base).trans (R.future W)
  simp only [ProofShape.subst, Ej] at RF ⊢
  intro C' a' b' RC RA RB
  exact RF.native_application (H.future W) RC RA RB

/-- Independent computation of a Pi carrier can reduce its binder annotation.
The certified core-binder world moves the body history to that annotation
without requiring closure under arbitrary term substitution. -/
theorem PiInertWorldHistory.function_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (S : DomainSort Δ A u)
    (H : PiInertWorldHistory D n (A :: Δ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    PiInertCarrierResidual D n Δ (.forallE A B) a b := by
  intro C p q RC RA RB
  obtain ⟨A', B', rfl, RD, RT⟩ := RC.pi_parts (fun R => erased_level_core_no_pi R)
  have H' := H.move (PiInertCoreWorld.core_binder heq hs hc S RD)
  simp only [ProofShape.subst_id] at H'
  exact .carrierFunction (S.level_core hs RD)
    (H'.base RT (.app (RA.liftN (fun R => level_lift R)) .refl)
      (.app (RB.liftN (fun R => level_lift R)) .refl))

/-- Function extensionality now retains the restricted future clause itself.
World extension under the sorted binder and core-binder conversion account
for both future renaming and independent carrier reduction. -/
theorem PiInertWorldHistory.function
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (S : DomainSort Δ A u)
    (H : PiInertWorldHistory D n (A :: Δ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    PiInertWorldHistory D n Δ (.forallE A B) a b := by
  refine ⟨H.function_residual heq hs hc S, ?_⟩
  intro Δ' τ W
  have H' := H.move (W.cons heq hc S)
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at H'
  intro C p q RC RA RB
  exact PiInertWorldHistory.function_residual heq hs hc (ContextSubstitution.sort W.typed S) H' RC RA RB

/-- Certified carrier computation pulls back a history without enlarging its
future worlds. Both computations retain the output residual consumed here. -/
theorem PiInertWorldHistory.carrier_prefix
    (R : PiInertWorldComputation D n Δ C E) (H : PiInertWorldHistory D n Δ E a b) :
    PiInertWorldHistory D n Δ C a b :=
  ⟨PiInertCarrierResidual.carrier_prefix R.base H.base,
    fun W => PiInertCarrierResidual.carrier_prefix (R.future W) (H.future W)⟩

/-- Endpoint computations retain independent core paths and the same restricted
future class. This can prefix typed beta steps to a supplied body history. -/
theorem PiInertWorldHistory.prefixes
    (RA : PiInertWorldComputation D n Δ a a')
    (RB : PiInertWorldComputation D n Δ b b') (H : PiInertWorldHistory D n Δ C a' b') :
    PiInertWorldHistory D n Δ C a b :=
  ⟨PiInertCarrierResidual.prefixes RA.base RB.base H.base,
    fun W => PiInertCarrierResidual.prefixes (RA.future W) (RB.future W) (H.future W)⟩

/-- Application action consumes and returns histories with core-world futures.
The dependent result is indexed by the left argument. Actual clients must
separately supply typing; completeness for arbitrary functions is not assumed. -/
structure PiInertWorldAction (D : Definitions) (Δ : List ProofShape)
    (A B f g : ProofShape) : Prop where
  act : ∀ {Δ' τ x y stage}, PiInertCoreWorld D Δ Δ' τ →
    PiInertWorldHistory D stage Δ' (A.subst τ) x y →
    ∃ n, PiInertWorldHistory D n Δ' ((B.subst τ.lift).inst x)
      (.app (f.subst τ) x) (.app (g.subst τ) y)

/-- Native variables construct action from retained Pi computation. Native
type conversion and argument evidence combine at the maximum input stage;
the result still admits only variable images in its own future worlds. -/
theorem pi_inert_native_variable_world_action
    (R : PiInertWorldComputation D stage Δ (contextOracle Δ i) (.forallE A B)) :
    PiInertWorldAction D Δ A B (.bvar i) (.bvar i) := by
  refine ⟨?_⟩
  intro Δ' τ x y n W HX
  obtain ⟨j, Ej, _, HR⟩ := W.lookup i
  have RF := ((HR.raise (Nat.zero_le stage)).world_computation).trans (R.move W)
  simp only [ProofShape.subst, Ej] at RF ⊢
  exact ⟨max stage n, PiInertWorldHistory.native_application
    (RF.raise (Nat.le_max_left stage n)) (HX.raise (Nat.le_max_right stage n))⟩

/-- An image pair supplies action whenever its native type has a retained
computation to a Pi in a later core world. Unlike raw Pi-path exposure, the
premise records the core commutation required by native oracle conversion.
General strong-derivation coverage of this obligation remains unproved. -/
structure PiInertWorldImageAction (D : Definitions) (Δ : List ProofShape)
    (a b T : ProofShape) : Prop where
  expose : ∀ {Δ' τ stage A B}, PiInertCoreWorld D Δ Δ' τ →
    PiInertWorldComputation D stage Δ' (T.subst τ) (.forallE A B) →
    PiInertWorldAction D Δ' A B (a.subst τ) (b.subst τ)

/-- The native variable image satisfies every retained computational Pi
exposure. Its oracle conversion certificate composes with that computation
before the constructive application rule is used. -/
theorem pi_inert_native_variable_world_image_action :
    PiInertWorldImageAction D Δ (.bvar i) (.bvar i) (contextOracle Δ i) := by
  refine ⟨?_⟩
  intro Δ' τ stage A B W R
  obtain ⟨j, Ej, _, HR⟩ := W.lookup i
  have RF := ((HR.raise (Nat.zero_le stage)).world_computation).trans R
  simpa only [ProofShape.subst, Ej] using pi_inert_native_variable_world_action RF

end Lean4Lean.VEnv.Strengthening
