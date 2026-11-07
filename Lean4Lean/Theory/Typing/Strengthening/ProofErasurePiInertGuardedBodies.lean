import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedTrees

/-! # Paired body interpretation with recursive guarded interfaces

Finite variable requirements carry recursive interface trees. Binder entry
lifts their annotations explicitly, and fresh arguments use type-only supply.
The interpretation uses two actual typed substitutions, not arbitrary
substitution closure of the retained carrier histories.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tree_comp_assoc tree_cons_comp tree_id_comp tree_comp_id tree_lift_cons
  tree_shift_cons tree_inst from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedTrees
open private weak_subst from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandBinders
open private erase_lam_inv erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- A typed raw lambda receives the carrier assigned to its body. Realization
uses the written actual binder and erasure reflection; it does not infer body
typing from unrelated raw source witnesses. -/
theorem ProofShape.TypedAt.lam_body
    (HF : TypedSource Δ (.lam A b)) (HB : TypedAt (A::Δ) b B) :
    TypedAt Δ (.lam A b) (.forallE A B) := by
  obtain ⟨Γ, f, F, hΓ, EΓ, hf, Ef⟩ := HF
  obtain ⟨C, b₀, rfl, hn, EC, Eb⟩ := erase_lam_inv Ef
  obtain ⟨⟨u, hC⟩, B₀, hb⟩ := hf.lam_inv henv hΓ
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hnb : b ≠ .proof := fun E => hn ((proofErase_eq_proof.1 (Eb.trans E)).lam hΓ hC)
  have HB' : TypedAt (proofEraseCtx (C::Γ)) b B := by
    simpa only [proofEraseCtx, EC, EΓ] using HB
  obtain ⟨B₁, hb₁, EB⟩ := HB'.realize_term hΓC hb Eb hnb
  have hl := HasType.lam hC hb₁
  obtain ⟨_, hPi⟩ := hl.isType henv hΓ
  refine ⟨Γ, .lam C b₀, .forallE C B₁, hΓ, EΓ, hl, Ef, ?_⟩
  rw [show proofErase Γ (.forallE C B₁) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi), EC, EB]

/-- Assigned Pi domains can be aligned by a same-sort domain history. This
transports actual typing, not recursive interface action or a core Pi join. -/
theorem ProofShape.TypedAt.pi_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedAt Δ f (.forallE C B)) (SA : DomainSort Δ A u) (SC : DomainSort Δ C u)
    (HD : PiInertDemandBase D Δ A C (.sort u)) : TypedAt Δ f (.forallE A B) := by
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf, Ef, EF⟩ := H
  obtain ⟨C₀, B₀, rfl, _, EC, EB⟩ := erase_forallE_inv EF
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨v, hC⟩, ⟨w, hB⟩⟩ := hPi.forallE_inv henv.ordered
  obtain ⟨A₀, hA, EA⟩ := SA.realize hΓ
  have hCu := SC.realize_type hΓ hC rfl EC
  have ES : proofErase Γ (.sort u) = .sort u :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (hA.sort_r henv hΓ)))
  have HE : env.IsDefEq univs Γ A₀ C₀ (.sort u) :=
    PiInertDemandBase.actual_defeq heq hs hΓ hA hCu
      (by simpa only [EA, EC, ES] using HD)
  have HP := IsDefEq.forallEDF HE.symm hB
  have hΓC : OnCtx (C₀::Γ) (env.IsType univs) := ⟨hΓ, v, hC⟩
  have EB' : proofErase (A₀::Γ) B₀ = B :=
    (proofErase_defeqCtx hΓC (.succ .zero HE.symm) hB).symm.trans EB
  refine ⟨Γ, f₀, .forallE A₀ B₀, hΓ, rfl, HP.defeq hf, Ef, ?_⟩
  rw [show proofErase Γ (.forallE A₀ B₀) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ HP.hasType.2), EA, EB']

/-- Finite variable requirements interpreted at the left annotation map.
Each right image is actually assigned the left substituted native carrier. -/
def PiInertGuardedImages (D : Definitions) (Δ Λ : List ProofShape)
    (σ τ : ProofShape.Subst) (uses : List (Nat × PiInertGuardedTree)) : Prop :=
  ∀ i p, (i, p) ∈ uses → PiInertGuardedTreeValue p σ D Λ
    (σ i) (τ i) ((contextOracle Δ i).subst σ)

/-- Lift old requirements under a binder, including their interface syntax,
and add the fresh input tree. These trees do not introduce self-dependence
of the fresh argument's input requirement. -/
def PiInertGuardedTree.bindUses (p : PiInertGuardedTree)
    (uses : List (Nat × PiInertGuardedTree)) : List (Nat × PiInertGuardedTree) :=
  (0, p.subst (fun i => .bvar (i+1))) ::
    uses.map (fun (i, q) => (i+1, q.subst (fun i => .bvar (i+1))))

/-- Paired old images move through the same core world. -/
theorem PiInertGuardedImages.move (H : PiInertGuardedImages D Δ Λ σ τ uses)
    (W : PiInertCoreWorld D Λ Ξ κ) : PiInertGuardedImages D Δ Ξ (σ.comp κ) (τ.comp κ) uses := by
  intro i p hi
  simpa only [ProofShape.Subst.comp, ProofShape.subst_subst] using (H i p hi).move W

/-- A supplied recursive input tree extends paired images under the written
binder. Lifting each requirement's syntax removes dependence on the new image. -/
theorem PiInertGuardedImages.cons_pair
    (H : PiInertGuardedImages D Δ Λ σ τ uses)
    (HX : PiInertGuardedTreeValue p σ D Λ x y (A.subst σ)) :
    PiInertGuardedImages D (A::Δ) Λ (σ.cons x) (τ.cons y) (p.bindUses uses) := by
  intro i q hi
  rcases List.mem_cons.1 hi with E | hi
  · cases E
    simpa only [PiInertGuardedTreeValue.subst_iff, tree_shift_cons,
      ProofShape.Subst.cons, contextOracle, TypeOracle.cons, ProofShape.lift_subst_cons] using HX
  · obtain ⟨⟨j, r⟩, hj, E⟩ := List.mem_map.1 hi
    cases E
    simpa only [PiInertGuardedTreeValue.subst_iff, tree_shift_cons,
      ProofShape.Subst.cons, contextOracle, TypeOracle.cons, ProofShape.lift_subst_cons] using H j r hj

/-- Fresh paired images construct their recursive requirement from type-only
supply. Old images only move through the target weakening world. -/
theorem PiInertGuardedImages.binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Λ (A.subst σ) u)
    (supply : PiInertGuardedTreeSupply p σ D Λ (A.subst σ))
    (H : PiInertGuardedImages D Δ Λ σ τ uses) :
    PiInertGuardedImages D (A::Δ) (A.subst σ :: Λ) (σ.etaLift u) (τ.etaLift u) (p.bindUses uses) := by
  have W := PiInertCoreWorld.weakening heq hc S
  have HX := pi_inert_fresh_guarded_tree heq hs hc hRigid S supply
  have arg : PiInertGuardedTreeValue p (σ.comp (fun i => .bvar (i+1))) D
      (A.subst σ :: Λ) (etaArgument u) (etaArgument u) (A.subst (σ.comp (fun i => .bvar (i+1)))) := by
    simpa only [← ProofShape.subst_subst, weak_subst] using HX
  exact (H.move W).cons_pair arg

/-- A term interpreter retains one original assignment and runs under paired
typed substitutions satisfying its finite recursively guarded requirements. -/
structure PiInertGuardedInterpretation (D : Definitions) (Δ : List ProofShape)
    (uses : List (Nat × PiInertGuardedTree)) (e T : ProofShape) (p : PiInertGuardedTree) : Prop where
  assigned : TypedAt Δ e T
  run : ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
    PiInertGuardedImages D Δ Λ σ τ uses →
    PiInertGuardedTreeValue p σ D Λ (e.subst σ) (e.subst τ) (T.subst σ)

/-- Type-only supply under paired environments. Supplying this certificate
does not assume equality or action of the lambda being constructed. -/
structure PiInertGuardedSupplyInterpretation (D : Definitions) (Δ : List ProofShape)
    (uses : List (Nat × PiInertGuardedTree)) (T : ProofShape) (p : PiInertGuardedTree) : Prop where
  run : ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
    PiInertGuardedImages D Δ Λ σ τ uses → PiInertGuardedTreeSupply p σ D Λ (T.subst σ)

/-- Ordinary finite-demand leaves need no guarded type exposure supply. -/
theorem PiInertGuardedSupplyInterpretation.plain :
    PiInertGuardedSupplyInterpretation D Δ uses T (.plain p) := ⟨fun _ _ _ => trivial⟩

/-- A retained full typed-substitution computation supplies a guarded call
with an ordinary result leaf under arbitrary paired interpreted environments.
This is a proved exposure constructor, not a premise about function action. -/
theorem PiInertGuardedSupplyInterpretation.call_plain
    (R : PiInertEvidence D n .compute Δ T (.forallE A B)) :
    PiInertGuardedSupplyInterpretation D Δ uses T (.call A B p (.plain q)) := by
  refine ⟨?_⟩
  intro Λ σ τ WL WR images
  refine ⟨⟨n, ?_⟩, ?_⟩
  · exact (R.substitute WL).world_computation
  · intro Ξ κ x W HX
    trivial

/-- A variable consumes its exact selected requirement. -/
theorem PiInertGuardedInterpretation.bvar
    (H : TypedAt Δ (.bvar i) (contextOracle Δ i)) :
    PiInertGuardedInterpretation D Δ [(i, p)] (.bvar i) (contextOracle Δ i) p := by
  refine ⟨H, ?_⟩
  intro Λ σ τ WL WR images
  exact images i p (by simp)

/-- A variable may consume one member of a larger finite requirement list. -/
theorem PiInertGuardedInterpretation.bvar_from
    (H : TypedAt Δ (.bvar i) (contextOracle Δ i)) (hi : (i, p) ∈ uses) :
    PiInertGuardedInterpretation D Δ uses (.bvar i) (contextOracle Δ i) p := by
  refine ⟨H, ?_⟩
  intro Λ σ τ WL WR images
  exact images i p hi

/-- An interpreted old term lifts under a new binder with its complete tree.
The arbitrary paired substitutions restrict to old variables by composition
with the original typed weakening, rather than moving a value through them. -/
theorem PiInertGuardedInterpretation.weak
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    {p : PiInertGuardedTree}
    (S : DomainSort Δ A u) (H : PiInertGuardedInterpretation D Δ uses e T q) :
    PiInertGuardedInterpretation D (A::Δ) (p.bindUses uses) (e.liftN 1) (T.liftN 1)
      (q.subst (fun i => .bvar (i+1))) := by
  have W := PiInertCoreWorld.weakening heq hc S
  refine ⟨by simpa only [weak_subst] using H.assigned.subst W.typed, ?_⟩
  intro Λ σ τ WL WR images
  have PL : ContextSubstitution Δ Λ (ProofShape.Subst.comp (fun i => .bvar (i+1)) σ) :=
    ContextSubstitution.comp W.typed WL
  have PR : ContextSubstitution Δ Λ (ProofShape.Subst.comp (fun i => .bvar (i+1)) τ) :=
    ContextSubstitution.comp W.typed WR
  have old : PiInertGuardedImages D Δ Λ
      (ProofShape.Subst.comp (fun i => .bvar (i+1)) σ) (ProofShape.Subst.comp (fun i => .bvar (i+1)) τ) uses := by
    intro i r hi
    have image := images (i+1) (r.subst (fun i => .bvar (i+1)))
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨(i, r), hi, rfl⟩))
    simpa only [PiInertGuardedTreeValue.subst_iff, contextOracle, TypeOracle.cons,
      ← weak_subst, ProofShape.subst_subst, ProofShape.Subst.comp, ProofShape.subst] using image
  simpa only [PiInertGuardedTreeValue.subst_iff, ← weak_subst, ProofShape.subst_subst] using
    H.run PL PR old

/-- A substitution-invariant assigned term interprets its ground leaf. -/
theorem PiInertGuardedInterpretation.closed
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : TypedAt Δ e T) (stable : ∀ σ, e.subst σ = e) :
    PiInertGuardedInterpretation D Δ [] e T (.plain .ground) := by
  refine ⟨H, ?_⟩
  intro Λ σ τ WL WR images
  have HA := H.subst WL
  rw [stable σ] at HA
  rw [stable σ, stable τ]
  exact ⟨HA, HA, PiInertDemandBase.refl hc HA.sources.1 HA.sources.2⟩

/-- Application consumes the full recursive input tree, even when the
function's selected carrier is an opaque alias. Its dependent result tree is
instantiated at the left syntactic argument. -/
theorem PiInertGuardedInterpretation.app
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HF : PiInertGuardedInterpretation D Δ fs f C (.call A B p q))
    (HX : PiInertGuardedInterpretation D Δ xs x A p)
    (HApp : TypedAt Δ (.app f x) (B.inst x)) :
    PiInertGuardedInterpretation D Δ (fs ++ xs) (.app f x) (B.inst x) (q.subst (.one x)) := by
  refine ⟨HApp, ?_⟩
  intro Λ σ τ WL WR images
  have F := HF.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi))
  have X := HX.run WL WR (fun i p hi => images i p (List.mem_append_right _ hi))
  have result := F.app heq hc X (HApp.sources.1.subst WL) (HApp.sources.1.subst WR)
  simpa only [PiInertGuardedTreeValue.subst_iff, ProofShape.Subst.one,
    tree_cons_comp, tree_id_comp, ProofShape.subst, ProofShape.subst_inst, tree_inst] using result

/-- Shared requirements can serve both application children, including several
uses of the same fresh variable. No duplicate image evidence is manufactured. -/
theorem PiInertGuardedInterpretation.app_shared
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HF : PiInertGuardedInterpretation D Δ uses f C (.call A B p q))
    (HX : PiInertGuardedInterpretation D Δ uses x A p)
    (HApp : TypedAt Δ (.app f x) (B.inst x)) :
    PiInertGuardedInterpretation D Δ uses (.app f x) (B.inst x) (q.subst (.one x)) := by
  have H := HF.app heq hc HX HApp
  refine ⟨HApp, ?_⟩
  intro Λ σ τ WL WR images
  exact H.run WL WR (fun i p hi => images i p ((List.mem_append.1 hi).elim id id))

/-- A type computing to a substitution-invariant output has a paired ground
interpretation. Full typed-substitution computation supplies both paths;
their common output supplies comparison without ordinary-core exposure. -/
theorem PiInertGuardedInterpretation.computed_closed_type
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HT : TypedAt Δ T (.sort u)) (R : PiInertEvidence D n .compute Δ T U)
    (stable : ∀ σ, U.subst σ = U) :
    PiInertGuardedInterpretation D Δ [] T (.sort u) (.plain .ground) := by
  refine ⟨HT, ?_⟩
  intro Λ σ τ WL WR images
  have RL := R.substitute WL
  have RR := R.substitute WR
  rw [stable σ] at RL
  rw [stable τ] at RR
  have comparison : PiInertEvidence D n (.compare true) Λ (T.subst σ) (T.subst τ) := RL.join hc RR
  have HL := HT.subst WL
  have HR := HT.subst WR
  exact ⟨HL, HR, HL.sources.1, HR.sources.1, HL.sources.2, n,
    comparison.carrier_history.world_history⟩

/-- Lambda abstraction interprets an arbitrary recursively interpreted body.
The fresh requirement and all old trees have explicitly lifted annotations.
Domain history aligns the right binder and result typing; type-only supply
constructs the fresh input tree. Neither ground lambda equality nor lambda
application action is assumed. General inference of these requirements and
supplies from unrestricted strong derivations remains a separate obligation. -/
theorem PiInertGuardedInterpretation.lam
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u)
    (HD : PiInertGuardedInterpretation D Δ ds A (.sort u) (.plain .ground))
    (HS : PiInertGuardedSupplyInterpretation D Δ ss A p)
    (HB : PiInertGuardedInterpretation D (A::Δ) (p.bindUses uses) b B q)
    (HF : TypedAt Δ (.lam A b) (.forallE A B)) :
    PiInertGuardedInterpretation D Δ (ds ++ (ss ++ uses)) (.lam A b) (.forallE A B)
      (.call A B p q) := by
  refine ⟨HF, ?_⟩
  intro Λ σ τ WL WR images
  have domain := HD.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi))
  have supply := HS.run WL WR (fun i p hi =>
    images i p (List.mem_append_right _ (List.mem_append_left _ hi)))
  have old : PiInertGuardedImages D Δ Λ σ τ uses := fun i p hi =>
    images i p (List.mem_append_right _ (List.mem_append_right _ hi))
  have SL := ContextSubstitution.sort WL S
  have SR := ContextSubstitution.sort WR S
  obtain ⟨m, HA⟩ := domain.base.ground.history
  have VL : ContextSubstitution (A::Δ) (A.subst σ :: Λ) σ.lift := WL.cons
  have VR : ContextSubstitution (A::Δ) (A.subst σ :: Λ) τ.lift :=
    ContextSubstitution.paired_lift heq hs WL WR S HA
  have body := HB.run (ContextSubstitution.eta_lift VL S) (ContextSubstitution.eta_lift VR S)
    (old.binder heq hs hc hRigid SL supply)
  have bodyBase := body.base
  rw [HB.assigned.sources.1.subst_etaLift S VL, HB.assigned.sources.1.subst_etaLift S VR,
    HB.assigned.sources.2.subst_etaLift S VL] at bodyBase
  have WB : ContextSubstitution (A.subst σ :: Λ) (A.subst τ :: Λ) ProofShape.Subst.id :=
    HA.binder_context heq hs SL SR
  have rightBody : TypedAt (A.subst τ :: Λ) (b.subst τ.lift) (B.subst σ.lift) := by
    simpa only [ProofShape.subst_id] using bodyBase.right.subst WB
  have rightOwn := TypedAt.lam_body
    (by simpa only [ProofShape.subst] using HF.sources.1.subst WR) rightBody
  have right := rightOwn.pi_domain heq hs SL SR domain.base.ground
  have left := HF.subst WL
  obtain ⟨n, history⟩ := bodyBase.ground.history
  have test := PiInertEvidence.raw_lambda_test (n := n) hs hc S HF.sources.1
  have HL := test.substitute VL
  have HR := test.substitute VR
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at HL HR
  have ground := (history.prefixes HL.world_computation HR.world_computation).function heq hs hc SL
  refine ⟨⟨left, ?_, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · simpa only [ProofShape.subst] using right
  · exact ⟨HF.sources.1.subst WL, HF.sources.1.subst WR, HF.sources.2.subst WL, n, ground⟩
  · exact (PiInertEvidence.of_core_join hc left.sources.2 left.sources.2 .refl).world_computation
  · intro Ξ κ x y W HX HLeft HRight
    have PL : ContextSubstitution Δ Ξ (σ.comp κ) := ContextSubstitution.comp WL W.typed
    have PR : ContextSubstitution Δ Ξ (τ.comp κ) := ContextSubstitution.comp WR W.typed
    simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at HLeft HRight ⊢
    have BL : ContextSubstitution (A::Δ) Ξ ((σ.comp κ).cons x) :=
      ContextSubstitution.lambda_argument PL HLeft
    have BR : ContextSubstitution (A::Δ) Ξ ((τ.comp κ).cons y) :=
      ContextSubstitution.lambda_argument PR HRight
    have result := HB.run BL BR ((old.move W).cons_pair HX)
    have FL := left.subst W.typed
    have FR := right.subst W.typed
    simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at FL FR
    obtain ⟨TX, TL⟩ := FL.app_parts HLeft
    have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HRight
    rw [tree_inst] at TL TR
    have beta (υ : ProofShape.Subst) (z : ProofShape) : Compute (ErasedLevelCore D)
        (.app (.lam (A.subst υ) (b.subst υ.lift)) z) (b.subst (υ.cons z)) :=
      tree_inst b υ z ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := A.subst υ))
    exact result.prefixes heq hs hc TL TR (beta (σ.comp κ) x) (beta (τ.comp κ) y)

/-- Actual identity abstraction retains any supplied recursive input tree,
including guarded calls at an opaque selected type. Its body interpretation
is constructed from the fresh variable, and positive typing derives all raw
lambda/source equations. No identity action or equality is assumed. -/
theorem pi_inert_actual_guarded_identity_interpretation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort (.succ u)))
    (HD : PiInertGuardedInterpretation D (proofEraseCtx Γ) ds
      (proofErase Γ A) (.sort (.succ u)) (.plain .ground))
    (HS : PiInertGuardedSupplyInterpretation D (proofEraseCtx Γ) ss (proofErase Γ A) p) :
    PiInertGuardedInterpretation D (proofEraseCtx Γ) (ds ++ ss)
      (.lam (proofErase Γ A) (.bvar 0)) (.forallE (proofErase Γ A) ((proofErase Γ A).liftN 1))
      (.call (proofErase Γ A) ((proofErase Γ A).liftN 1) p (p.subst (fun i => .bvar (i+1)))) := by
  have hu := hA.sort_r henv hΓ
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hPi : env.HasType univs Γ (.forallE A A.lift) (.sort (.succ u)) :=
    (IsDefEq.sortDF (l := .imax (.succ u) (.succ u)) ⟨hu, hu⟩ hu VLevel.imax_self).defeq
      (HasType.forallE hA (hA.weak henv))
  have hf : env.HasType univs Γ (.lam A (.bvar 0)) (.forallE A A.lift) := .lam hA (.bvar .zero)
  have hv : env.HasType univs (A::Γ) (.bvar 0) A.lift := .bvar .zero
  have EV : proofErase (A::Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_proof_at_positive_type hΓA (hA.weak henv) hv)
  have EA : proofErase (A::Γ) A.lift = (proofErase Γ A).liftN 1 :=
    proofErase_liftN hΓ hΓA Ctx.LiftN.one hA
  have HF : TypedAt (proofEraseCtx Γ) (.lam (proofErase Γ A) (.bvar 0))
      (.forallE (proofErase Γ A) ((proofErase Γ A).liftN 1)) := by
    refine ⟨Γ, .lam A (.bvar 0), .forallE A A.lift, hΓ, rfl, hf, ?_, ?_⟩
    · rw [show proofErase Γ (.lam A (.bvar 0)) = .lam _ _ from
        if_neg (not_proof_at_positive_type hΓ hPi hf), EV]
    · rw [show proofErase Γ (.forallE A A.lift) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ hPi), EA]
  have HV : TypedAt (proofErase Γ A :: proofEraseCtx Γ) (.bvar 0) ((proofErase Γ A).liftN 1) :=
    ⟨A::Γ, .bvar 0, A.lift, hΓA, rfl, hv, EV, EA⟩
  have HB : PiInertGuardedInterpretation D (proofErase Γ A :: proofEraseCtx Γ)
      (p.bindUses []) (.bvar 0) ((proofErase Γ A).liftN 1) (p.subst (fun i => .bvar (i+1))) := by
    exact PiInertGuardedInterpretation.bvar HV
  simpa only [List.append_nil] using PiInertGuardedInterpretation.lam
    heq hs hc hRigid (DomainSort.of_typed hΓ hA) HD HS HB HF

/-- Empty image requirements read out the supported recursive value at the
identity environment. Interpretation still quantifies over arbitrary paired
typed substitutions; this readout does not weaken that claim. -/
theorem PiInertGuardedInterpretation.empty_value
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedInterpretation D Δ [] e T p) :
    PiInertGuardedTreeValue p ProofShape.Subst.id D Δ e e T := by
  have W := PiInertCoreWorld.identity_source heq hc H.assigned.sources.1
  simpa only [ProofShape.subst_id] using H.run W.typed W.typed (fun _ _ h => nomatch h)

/-- A positive actual alias with a retained computation to a closed Pi
interface constructs an identity interpreter under every paired typed
substitution. Both domain interpretation and fresh call supply are proved
from that computation; neither is an extra semantic hypothesis. The selected
alias need not have any ordinary-core Pi exposure. -/
theorem pi_inert_actual_computed_identity_interpretation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort (.succ u)))
    (R : PiInertEvidence D n .compute (proofEraseCtx Γ) (proofErase Γ C) (.forallE A B))
    (stable : ∀ σ, (ProofShape.forallE A B).subst σ = .forallE A B) :
    PiInertGuardedInterpretation D (proofEraseCtx Γ) []
      (.lam (proofErase Γ C) (.bvar 0)) (.forallE (proofErase Γ C) ((proofErase Γ C).liftN 1))
      (.call (proofErase Γ C) ((proofErase Γ C).liftN 1) (.call A B p (.plain q))
        ((PiInertGuardedTree.call A B p (.plain q)).subst (fun i => .bvar (i+1)))) := by
  have HC : TypedAt (proofEraseCtx Γ) (proofErase Γ C) (.sort (.succ u)) :=
    ⟨Γ, C, .sort (.succ u), hΓ, rfl, hC, rfl,
      if_neg (not_isProof_of_sort hΓ (HasType.sort (hC.sort_r henv hΓ)))⟩
  have HD := PiInertGuardedInterpretation.computed_closed_type hc HC R stable
  have HS : PiInertGuardedSupplyInterpretation D (proofEraseCtx Γ) [] (proofErase Γ C)
      (.call A B p (.plain q)) := .call_plain R
  exact pi_inert_actual_guarded_identity_interpretation heq hs hc hRigid hΓ hC HD HS

end Lean4Lean.VEnv.Strengthening
