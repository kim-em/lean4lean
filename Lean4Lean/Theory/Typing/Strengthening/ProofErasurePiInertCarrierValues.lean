import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldValues

/-! # Carrier-only subsingletons join the typed value interpretation

Neutral-returning values retain inferred comparison, but that excludes distinct
variables at subsingleton carriers. A separate structural subsingleton case
preserves carrier evidence and dependent application without inventing an
inferred head comparison. Typed ordinary-core type prefixes preserve this
evidence through beta wrappers. General type-conversion coverage is not assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private value_inst_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldValues
variable [Params] {D : Definitions}

/-- Two explicit sources of typed application evidence, closed under typed
ordinary-core type prefixes. The subsingleton constructor does not require
endpoint comparison or neutral reducts. -/
inductive PiInertCarrierValue (D : Definitions) (n : Nat)
    (Δ : List ProofShape) (a b : ProofShape) : ProofShape → Prop where
  | neutral : PiInertWorldValue D n Δ a b T → PiInertCarrierValue D n Δ a b T
  | subsingleton : TypedSource Δ a → TypedSource Δ b → SubsingletonCarrier T →
      PiInertCarrierValue D n Δ a b T
  | coreType : TypedSource Δ T → Compute (ErasedLevelCore D) T U →
      PiInertCarrierValue D n Δ a b U → PiInertCarrierValue D n Δ a b T

/-- Every constructor retains actual source typing independently of the raw
selected carrier. -/
theorem PiInertCarrierValue.sources (H : PiInertCarrierValue D n Δ a b T) :
    TypedSource Δ a ∧ TypedSource Δ b := by
  induction H with
  | neutral H => exact ⟨H.leftSource, H.rightSource⟩
  | subsingleton HA HB _ => exact ⟨HA, HB⟩
  | coreType _ _ _ ih => exact ih

/-- Values move through variable worlds. Structural subsingletons substitute
directly; neutral values and type prefixes retain their explicit core paths. -/
theorem PiInertCarrierValue.move (H : PiInertCarrierValue D n Δ a b T)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertCarrierValue D n Δ' (a.subst τ) (b.subst τ) (T.subst τ) := by
  induction H generalizing Δ' τ with
  | neutral H => exact .neutral (H.move W)
  | subsingleton HA HB HS => exact .subsingleton (HA.subst W.typed) (HB.subst W.typed) (HS.subst τ)
  | coreType HT R _ ih =>
    exact .coreType (HT.subst W.typed) (R.subst (fun H => erased_level_core_subst H)) (ih W)

/-- Stage enlargement leaves the structural branch unchanged. -/
theorem PiInertCarrierValue.raise (hle : n ≤ m) (H : PiInertCarrierValue D n Δ a b T) :
    PiInertCarrierValue D m Δ a b T := by
  induction H with
  | neutral H => exact .neutral (H.raise hle)
  | subsingleton HA HB HS => exact .subsingleton HA HB HS
  | coreType HT R _ ih => exact .coreType HT R ih

/-- Each case constructs a full core-world history at its selected carrier.
The structural branch uses its own carrier rule, never inferred comparison. -/
theorem PiInertCarrierValue.history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertCarrierValue D n Δ a b T) : PiInertWorldHistory D n Δ T a b := by
  induction H with
  | neutral H => exact H.history hs hc
  | subsingleton _ _ HS => exact (PiInertCarrierHistory.subsingleton heq hRigid HS).world_history
  | coreType HT R _ ih =>
    exact ih.carrier_prefix (PiInertEvidence.core_source hs hc HT R).world_computation

/-- Typed core predecessors preserve both cases. In the structural case the
carrier supplies equality for the new endpoints directly. -/
theorem PiInertCarrierValue.prefixes (H : PiInertCarrierValue D n Δ a' b' T)
    (HA : TypedSource Δ a) (HB : TypedSource Δ b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertCarrierValue D n Δ a b T := by
  induction H with
  | neutral H => exact .neutral (H.prefixes HA HB RA RB)
  | subsingleton _ _ HS => exact .subsingleton HA HB HS
  | coreType HT R _ ih => exact .coreType HT R ih

/-- Independent endpoint core reductions retain the selected carrier and the
appropriate application evidence. Actual target typing follows by core replay. -/
theorem PiInertCarrierValue.reducts
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertCarrierValue D n Δ a b T)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertCarrierValue D n Δ a' b' T := by
  induction H with
  | neutral H => exact .neutral (H.reducts hs hc RA RB)
  | subsingleton HA HB HS =>
    exact .subsingleton (PiInertEvidence.core_source (n := 0) hs hc HA RA).base.1
      (PiInertEvidence.core_source (n := 0) hs hc HB RB).base.1 HS
  | coreType HT R _ ih => exact .coreType HT R ih

/-- An ordinary-core type reduction transports either case. The source type
typing is explicit for constructing the neutral branch's computation evidence.
No guarded or arbitrary definitional conversion is asserted here. -/
theorem PiInertCarrierValue.core_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Δ T) (R : Compute (ErasedLevelCore D) T U)
    (H : PiInertCarrierValue D n Δ a b T) : PiInertCarrierValue D n Δ a b U := by
  induction H generalizing U with
  | neutral H => exact .neutral (H.convert (PiInertEvidence.core_source hs hc HT R).world_computation)
  | subsingleton HA HB HS => exact .subsingleton HA HB (HS.level_core_compute heq hRigid R)
  | coreType HT0 RT _ ih =>
    obtain ⟨Γ, e, A, hΓ, _, he, Ee⟩ := HT0
    obtain ⟨shared, RU, RV⟩ := hc hΓ he (Ee ▸ R) (Ee ▸ RT)
    have HU := (PiInertEvidence.core_source (n := 0) hs hc HT R).base.1
    have HV := (PiInertEvidence.core_source (n := 0) hs hc HT RT).base.1
    exact .coreType HU RU (ih HV RV)

/-- Typed ordinary-core joins transport the combined value in both
directions, including beta wrappers of structural subsingleton types. -/
theorem pi_inert_carrier_value_core_join_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Δ T) (HU : TypedSource Δ U)
    (R : ComputeJoin (ErasedLevelCore D) T U) :
    PiInertCarrierValue D n Δ a b T ↔ PiInertCarrierValue D n Δ a b U := by
  obtain ⟨shared, RT, RU⟩ := R
  exact ⟨fun H => .coreType HU RU (H.core_type heq hs hc hRigid HT RT),
    fun H => .coreType HT RT (H.core_type heq hs hc hRigid HU RU)⟩

/-- A core reduct of a carrier consumes the corresponding prefix in the
original history, retaining every variable-world future. -/
theorem PiInertWorldHistory.carrier_reduct (H : PiInertWorldHistory D n Δ A x y)
    (R : Compute (ErasedLevelCore D) A A') : PiInertWorldHistory D n Δ A' x y := by
  refine ⟨fun RC RX RY => H.base (R.trans RC) RX RY, ?_⟩
  intro Δ' τ W C left right RC RX RY
  exact H.future W ((R.subst (fun H => erased_level_core_subst H)).trans RC) RX RY

/-- A structural subsingleton Pi has a structurally subsingleton codomain. -/
theorem ProofShape.SubsingletonCarrier.pi_body
    (H : SubsingletonCarrier (.forallE A B)) : SubsingletonCarrier B := by
  generalize E : ProofShape.forallE A B = C at H
  cases H with
  | unit =>
    have HE := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead, ProofShape.constHead_mkApps] at HE
    cases HE
  | forallE H => cases E; exact H

/-- Application retains a value at the exact left dependent result, including
ordinary-core type prefixes. Typing of that selected result is supplied for
codomain-prefix transport. The structural subsingleton branch needs neither
inferred head comparison nor argument comparison. -/
theorem PiInertCarrierValue.app
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertCarrierValue D n Δ a b (.forallE A B))
    (HX : PiInertWorldHistory D n Δ A x y)
    (HA : TypedSource Δ (.app a x)) (HB : TypedSource Δ (.app b y))
    (HT : TypedSource Δ (B.inst x)) :
    PiInertCarrierValue D n Δ (.app a x) (.app b y) (B.inst x) := by
  generalize E : ProofShape.forallE A B = T at H
  induction H generalizing A B x y with
  | neutral H => cases E; exact .neutral (H.app HX HA HB)
  | subsingleton _ _ HS =>
    cases E
    apply PiInertCarrierValue.subsingleton HA HB
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      HS.pi_body.subst (ProofShape.Subst.one x)
  | coreType _ RT _ ih =>
    cases E
    obtain ⟨A', B', rfl, RD, RB⟩ := RT.pi_parts (fun R => erased_level_core_no_pi R)
    have RI : Compute (ErasedLevelCore D) (B.inst x) (B'.inst x) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        RB.subst (fun H => erased_level_core_subst H) (σ := ProofShape.Subst.one x)
    have HT' := (PiInertEvidence.core_source (n := 0) hs hc HT RI).base.1
    exact .coreType HT RI (ih (HX.carrier_reduct RD) HA HB HT' rfl)

/-- Application action for the combined carrier values. Inputs and outputs
retain both admissible cases; the relation is not restricted back to inferred
comparison when a function or its result is structurally subsingleton. -/
structure PiInertTypedCarrierAction (D : Definitions) (Δ : List ProofShape)
    (A B f g : ProofShape) : Prop where
  act : ∀ {Δ' τ x y stage}, PiInertCoreWorld D Δ Δ' τ →
    PiInertCarrierValue D stage Δ' x y (A.subst τ) →
    TypedSource Δ' (.app (f.subst τ) x) → TypedSource Δ' (.app (g.subst τ) y) →
    TypedSource Δ' ((B.subst τ.lift).inst x) →
    ∃ n, PiInertCarrierValue D n Δ' (.app (f.subst τ) x) (.app (g.subst τ) y)
      ((B.subst τ.lift).inst x)

/-- Both function-value cases construct typed action. Argument histories are
read at the selected domain and stages combine only by maximum. -/
theorem PiInertCarrierValue.typed_action
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertCarrierValue D n Δ f g (.forallE A B)) :
    PiInertTypedCarrierAction D Δ A B f g := by
  refine ⟨?_⟩
  intro Δ' τ x y stage W HX HA HB HT
  have HF := (H.move W).raise (Nat.le_max_left n stage)
  have HY := (HX.history heq hs hc hRigid).raise (Nat.le_max_right n stage)
  exact ⟨max n stage, HF.app hs hc HY HA HB HT⟩

/-- Typed action composes its variable worlds. Source application typing is
supplied at the final world. -/
theorem PiInertTypedCarrierAction.move (H : PiInertTypedCarrierAction D Δ A B f g)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertTypedCarrierAction D Δ' (A.subst τ) (B.subst τ.lift) (f.subst τ) (g.subst τ) := by
  refine ⟨?_⟩
  intro Δ'' υ x y stage V HX HA HB HT
  simp only [ProofShape.subst_subst] at HX HA HB HT
  rw [← ProofShape.Subst.comp_lift] at HT
  obtain ⟨n, HN⟩ := H.act (W.compose V) HX HA HB HT
  exact ⟨n, by simpa only [ProofShape.subst_subst, ProofShape.Subst.comp_lift] using HN⟩

/-- Identity retains either input case through typed beta prefixes, including
distinct subsingleton variables that have no neutral-returning value witness. -/
theorem pi_inert_identity_typed_carrier_action :
    PiInertTypedCarrierAction D Δ A (A.liftN 1) (.lam A (.bvar 0)) (.lam A (.bvar 0)) := by
  refine ⟨?_⟩
  intro Δ' τ x y stage W HX HA HB _
  simp only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.lift_subst_lift, value_inst_lift] at HA HB ⊢
  have beta (x : ProofShape) : Compute (ErasedLevelCore D) (.app (.lam (A.subst τ) (.bvar 0)) x) x := by
    apply ProofShape.Compute.beta
    simpa only [ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
      (ProofShape.BetaRed.beta (A := A.subst τ) (b := .bvar 0) (a := x))
  exact ⟨stage, HX.prefixes HA HB (beta x) (beta y)⟩

/-- The higher-order evaluator now accepts either neutral-returning functions
or carrier-only subsingleton functions. It returns the corresponding whole
carrier value after typed beta, so iterated subsingleton results retain action. -/
theorem pi_inert_evaluator_typed_carrier_action
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HX : PiInertWorldHistory D n Δ A x x) :
    PiInertTypedCarrierAction D Δ (.forallE A B) ((B.inst x).liftN 1)
      (.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1)))
      (.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1))) := by
  refine ⟨?_⟩
  intro Δ' τ f g stage W HF HA HB HT
  simp only [ProofShape.lift_subst_lift, value_inst_lift, ProofShape.subst_inst] at HT
  have beta (f : ProofShape) : Compute (ErasedLevelCore D)
      (.app ((ProofShape.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1))).subst τ) f)
      (.app f (x.subst τ)) := by
    have E : ((ProofShape.app (.bvar 0) (x.liftN 1)).subst τ.lift).inst f = .app f (x.subst τ) := by
      simp only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.lift_subst_lift,
        ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero]
      exact congrArg (ProofShape.app f) (value_inst_lift (x.subst τ) f)
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := (ProofShape.forallE A B).subst τ))
  have HTA := (PiInertEvidence.core_source (n := 0) hs hc HA (beta f)).base.1
  have HTB := (PiInertEvidence.core_source (n := 0) hs hc HB (beta g)).base.1
  have HN := (HF.raise (Nat.le_max_right n stage)).app
    hs hc ((HX.move W).raise (Nat.le_max_left n stage)) HTA HTB HT
  refine ⟨max n stage, ?_⟩
  simpa only [ProofShape.lift_subst_lift, value_inst_lift, ProofShape.subst_inst] using
    HN.prefixes HA HB (beta f) (beta g)

/-- Actual non-proof application reconstructs the exact erased dependent
carrier for either value case. Common typing comes from the original function
and argument equality premises; no inferred head equality is extracted. -/
theorem PiInertCarrierValue.apply_actual_nonproof
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.IsDefEq univs Γ f g (.forallE A B))
    (hX : env.IsDefEq univs Γ x y A) (hn : ¬ IsProof Γ (.app f x))
    (H : PiInertCarrierValue D n (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B)))
    (HX : PiInertWorldHistory D n (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertCarrierValue D n (proofEraseCtx Γ)
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
  have HT : TypedSource (proofEraseCtx Γ) (proofErase Γ (B.inst x)) :=
    ⟨Γ, _, _, hΓ, rfl, hB.instN henv Ctx.InstN.zero hX.hasType.1, rfl⟩
  rw [proofErase_instN hΓA hX.hasType.1 Ctx.InstN.zero hB] at HT
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
    show proofErase Γ (.app g y) = .app _ _ from if_neg hn',
    proofErase_instN hΓA hX.hasType.1 Ctx.InstN.zero hB]
  exact H.app hs hc HX ⟨Γ, _, _, hΓ, rfl, hApp.hasType.1, if_neg hn⟩
    ⟨Γ, _, _, hΓ, rfl, hApp.hasType.2, if_neg hn'⟩ HT

/-- The added case is needed even for actual strongly equal functions. Two
distinct variables of type S -> S, for a closed positive empty structure S,
have carrier values at zero but no old neutral-returning values at any stage.
This is a separation of interpretation classes, not a strengthening counterexample. -/
theorem pi_inert_carrier_value_function_separation
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    let F := VExpr.forallE (.const family ls) (.const family ls)
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧
      env.IsDefEqStrong univs Γ (.bvar 0) (.bvar 1) F ∧
      PiInertCarrierValue D 0 (proofEraseCtx Γ)
        (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) (proofErase Γ F) ∧
      ∀ n, ¬ PiInertWorldValue D n (proofEraseCtx Γ)
        (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) (proofErase Γ F) := by
  dsimp only
  let S := VExpr.const family ls
  let F := VExpr.forallE S S
  have hu := hS.sort_r henv (show OnCtx ([] : List VExpr) (env.IsType univs) from trivial)
  have hF : env.HasType univs [] F (.sort (.succ u)) :=
    (IsDefEq.sortDF (l := .imax (.succ u) (.succ u)) ⟨hu, hu⟩ hu VLevel.imax_self).defeq
      (HasType.forallE hS (hS.weak0 henv.ordered))
  let Γ := [F, F]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hF⟩, _, hF.weak0 henv.ordered⟩
  have hFΓ : env.HasType univs Γ F (.sort (.succ u)) := hF.weak0 henv.ordered
  have h0 : env.HasType univs Γ (.bvar 0) F := .bvar .zero
  have h1 : env.HasType univs Γ (.bvar 1) F := .bvar (.succ .zero)
  have E0 : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_proof_at_positive_type hΓ hFΓ h0)
  have E1 : proofErase Γ (.bvar 1) = .bvar 1 := if_neg (not_proof_at_positive_type hΓ hFΓ h1)
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S::Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have HS : SubsingletonCarrier (proofErase Γ F) := by
    rw [show proofErase Γ F = .forallE (proofErase Γ S) (proofErase (S::Γ) S) from
      if_neg (not_isProof_of_sort hΓ hFΓ),
      show proofErase Γ S = .const family ls from if_neg (not_isProof_of_sort hΓ hSΓ),
      show proofErase (S::Γ) S = .const family ls from
        if_neg (not_isProof_of_sort hΓS (hS.weak0 henv.ordered))]
    exact .forallE (.unit hi hx hz (ps := []) hp.symm)
  have HE : env.IsDefEq univs Γ (.bvar 0) (.bvar 1) F :=
    proofErase_subsingleton_carrier_descend (n := 0) (k := 0) hΓ h0 h1
      (by simpa only [ProofShape.liftN_zero] using HS)
  refine ⟨Γ, hΓ, HE.strong henv.orderedStrong hΓ,
    .subsingleton ⟨Γ, _, _, hΓ, rfl, h0, rfl⟩ ⟨Γ, _, _, hΓ, rfl, h1, rfl⟩ HS, ?_⟩
  intro n H
  rw [E0, E1] at H
  have E := H.bvar_injective hs hc
  cases E

end Lean4Lean.VEnv.Strengthening
