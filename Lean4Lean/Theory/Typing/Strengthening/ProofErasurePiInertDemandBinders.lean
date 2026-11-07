import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandBodies
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLambdaCarrier

/-! # Paired demand environments under related binders

A retained type history can justify ordinary typed binder conversion without
being a core computation or a core world. Fresh proof arguments and ordinary
variables both carry finite demands. These are binder steps for paired body
interpretation, not a coverage theorem for all strong lambda derivations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private domain_sort_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params] {D : Definitions}

/-- A non-proof raw application cannot have the proof marker as its head.
Actual function proofness would make the whole application a proof too. -/
theorem ProofShape.TypedSource.not_proof_app (H : TypedSource Δ (.app .proof x)) : False := by
  obtain ⟨Γ, e, T, hΓ, _, ht, Ee⟩ := H
  obtain ⟨f, a, rfl, hn, Ef, _⟩ := erase_app_inv Ee
  obtain ⟨A, B, hf, ha⟩ := ht.app_inv henv hΓ
  exact hn (IsProof.app_fn hΓ hf ha (proofErase_eq_proof.1 Ef))

/-- The proof marker carries every finite demand when its endpoint and
selected carrier have actual sources. Arrow tests have no typed application
source, so no computational function behavior is fabricated for a proof. -/
theorem pi_inert_proof_demand_value
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HP : TypedSource Δ .proof) (HT : TypedSource Δ T) :
    PiInertDemandValue p D Δ .proof .proof T := by
  induction p with
  | ground => exact PiInertDemandBase.refl hc HP HT
  | both p q ihp ihq => exact ⟨ihp, ihq⟩
  | arrow p q =>
    refine ⟨PiInertDemandBase.refl hc HP HT, ?_⟩
    intro Λ σ A B x y W HType J HX HL HR HE
    exact HL.not_proof_app.elim

/-- Every sorted fresh argument has all finite demands at its native carrier.
This includes a proof marker for a Prop domain, and a native variable otherwise. -/
theorem pi_inert_fresh_demand_value
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u) :
    PiInertDemandValue p D (A::Δ) (etaArgument u) (etaArgument u) (A.liftN 1) := by
  obtain ⟨Γ, C, hΓ, EΓ, hC, EC⟩ := S
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have Ev := proofErase_fresh_argument hΓ hC
  have ET := proofErase_liftN hΓ hΓC Ctx.LiftN.one hC
  have HA : TypedSource (A::Δ) (etaArgument u) :=
    ⟨C::Γ, .bvar 0, C.lift, hΓC, by simp only [proofEraseCtx, EC, EΓ], .bvar .zero, Ev⟩
  have HT : TypedSource (A::Δ) (A.liftN 1) :=
    ⟨C::Γ, C.lift, .sort u, hΓC, by simp only [proofEraseCtx, EC, EΓ], hC.weak henv,
      ET.trans (congrArg (fun e => e.liftN 1) EC)⟩
  classical
  by_cases hu : u ≈ .zero
  · simp only [etaArgument, if_pos hu] at HA ⊢
    exact pi_inert_proof_demand_value hc HA HT
  · simp only [etaArgument, if_neg hu] at HA ⊢
    have HV : PiInertWorldValue D 0 (A::Δ) (.bvar 0) (.bvar 0) (A.liftN 1) :=
      pi_inert_native_variable_world_neutral.value HA HA
    exact (PiInertCarrierValue.neutral HV).demand heq hs hc hRigid HT

/-- A sorted binder gives the exact weakening core world used to move old
image demands. This world still maps every old variable to a variable. -/
theorem PiInertCoreWorld.weakening
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (S : DomainSort Δ A u) :
    PiInertCoreWorld D Δ (A::Δ) (fun i => .bvar (i+1)) := by
  have W := pi_inert_action_binder_renaming S
  obtain ⟨Γ, C, hΓ, EΓ, _, _⟩ := S
  rw [← EΓ] at W ⊢
  exact .of_exact_actual heq hc hΓ W

/-- Carrier-history symmetry preserves the restricted future class. -/
theorem PiInertWorldHistory.symm (H : PiInertWorldHistory D n Δ T a b) :
    PiInertWorldHistory D n Δ T b a := by
  refine ⟨fun RT RA RB => .carrierSymm (H.base RT RB RA), ?_⟩
  intro Λ σ W T' a' b' RT RA RB
  exact .carrierSymm (H.future W RT RB RA)

/-- A retained same-sort type history interprets ordinary binder conversion.
Its conclusion is a typed context substitution, not a core world or a core
join of the two domains. General checker-context transport is not asserted. -/
theorem PiInertWorldHistory.binder_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SA : DomainSort Δ A u) (SB : DomainSort Δ B u)
    (H : PiInertWorldHistory D n Δ (.sort u) A B) :
    ContextSubstitution (A::Δ) (B::Δ) ProofShape.Subst.id := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons C Γ =>
    obtain ⟨hΓ, v, hC⟩ := hΓ
    obtain ⟨EC, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨E, hE, EE⟩ := (EΓ ▸ SB).realize hΓ
    have hCu := domain_sort_raw SA hΓ hC EΓ EC
    have ES : proofErase Γ (.sort u) = .sort u :=
      if_neg (not_isProof_of_sort hΓ (HasType.sort (hE.sort_r henv hΓ)))
    have HE : env.IsDefEq univs Γ C E (.sort u) :=
      proofErase_computed_joint_carrier_reflect
        (fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
          hΓ hΓ' W ht (pi_inert_stage_embed R)) hΓ hCu hE
        (by simpa only [ES, EC, EE, EΓ] using H.base .refl .refl .refl)
    have W : ContextSubstitution (proofEraseCtx (C::Γ)) (proofEraseCtx (E::Γ)) ProofShape.Subst.id :=
      ContextSubstitution.of_defeqCtx hΓ (.succ .zero HE)
    have HW := W (show OnCtx (C::Γ) (env.IsType univs) from ⟨hΓ, v, hC⟩) rfl
    simpa only [proofEraseCtx, EE, EΓ] using HW

/-- The right interpretation of a paired environment can enter the left
substituted binder using its supplied type history. This uses ordinary typed
context conversion; it does not upgrade the conversion to a core-world map. -/
theorem ProofShape.ContextSubstitution.paired_lift
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (WL : ContextSubstitution Δ Λ σ) (WR : ContextSubstitution Δ Λ τ)
    (S : DomainSort Δ A u)
    (H : PiInertWorldHistory D n Λ (.sort u) (A.subst σ) (A.subst τ)) :
    ContextSubstitution (A::Δ) (A.subst σ :: Λ) τ.lift := by
  have V : ContextSubstitution (A.subst τ :: Λ) (A.subst σ :: Λ) ProofShape.Subst.id :=
    H.symm.binder_context heq hs (ContextSubstitution.sort WR S) (ContextSubstitution.sort WL S)
  have Q : ContextSubstitution (A::Δ) (A.subst σ :: Λ) (τ.lift.comp ProofShape.Subst.id) :=
    ContextSubstitution.comp WR.cons V
  have E : τ.lift.comp ProofShape.Subst.id = τ.lift := by
    funext i
    exact ProofShape.subst_id _
  rw [E] at Q
  intro Γ hΓ EΓ
  exact Q hΓ EΓ

omit [Params] in
private theorem weak_subst (e : ProofShape) :
    e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
  have E := (ProofShape.liftN_subst (n := 1) (k := 0) e ProofShape.Subst.id).symm
  rw [ProofShape.subst_id] at E
  simpa only [ProofShape.Subst.id, ProofShape.liftN, liftVar_base'] using E

/-- Lift an old substitution and supply the sort-classified erased fresh
argument at index zero. Old images are only weakened, not reinterpreted. -/
noncomputable def ProofShape.Subst.etaLift (σ : ProofShape.Subst) (u : VLevel) : ProofShape.Subst :=
  (σ.comp (fun i => .bvar (i+1))).cons (etaArgument u)

omit [Params] in
/-- The new image is exactly the fresh variable or proof marker. -/
theorem ProofShape.Subst.etaLift_zero {σ : ProofShape.Subst} : σ.etaLift u 0 = etaArgument u := rfl

omit [Params] in
/-- Old images under the binder are their ordinary weakenings. -/
theorem ProofShape.Subst.etaLift_succ {σ : ProofShape.Subst} : σ.etaLift u (i+1) = (σ i).liftN 1 :=
  weak_subst _

omit [Params] in
/-- An old term ignores the new image; its type substitutes and then weakens. -/
theorem ProofShape.subst_lift_etaLift (e : ProofShape) :
    (e.liftN 1).subst (σ.etaLift u) = (e.subst σ).liftN 1 := by
  simp only [ProofShape.Subst.etaLift, ProofShape.lift_subst_cons, ← ProofShape.subst_subst, weak_subst]

/-- Sort classification changes only the erased fresh-variable agreement.
A proof-valued variable imposes no agreement obligation. -/
theorem ErasedSubstAgreement.eta_lift {σ : ProofShape.Subst}
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ES : ErasedSubstAgreement (A::Γ) Γ₀ ρ σ.lift) :
    ErasedSubstAgreement (A::Γ) Γ₀ ρ (σ.etaLift u) := by
  intro i T hl hn
  cases i with
  | zero =>
    have hu : ¬ u ≈ .zero := fun hu => hn ((isProof_fresh_iff hΓ hA).2 hu)
    rw [ProofShape.Subst.etaLift_zero, show etaArgument u = .bvar 0 from if_neg hu]
    exact ES hl hn
  | succ i =>
    rw [ProofShape.Subst.etaLift_succ]
    exact ES hl hn

/-- An ordinary lifted interpretation admits the sort-classified fresh image.
If the source binder is a proposition, its fresh variable is erased and the
substitution agreement has no retained-variable obligation at index zero. -/
theorem ProofShape.ContextSubstitution.eta_lift {σ : ProofShape.Subst}
    (W : ContextSubstitution (A::Δ) Λ σ.lift) (S : DomainSort Δ A u) :
    ContextSubstitution (A::Δ) Λ (σ.etaLift u) := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons C Γ =>
    obtain ⟨hΓ, v, hC⟩ := hΓ
    obtain ⟨EC, EΓ⟩ := List.cons.inj EΓ
    have hCu := domain_sort_raw S hΓ hC EΓ EC
    obtain ⟨Γ₀, ρ, hΓ₀, EΓ₀, WS, ES⟩ :=
      W (show OnCtx (C::Γ) (env.IsType univs) from ⟨hΓ, v, hC⟩)
        (by simp only [proofEraseCtx, EC, EΓ])
    refine ⟨Γ₀, ρ, hΓ₀, EΓ₀, WS, ?_⟩
    exact ES.eta_lift hΓ hCu

/-- On an actually typed body, the proof-aware fresh image has the same
result as the ordinary lifted substitution. Both raw maps share one actual
typed realization, so this asserts no equality for arbitrary raw syntax. -/
theorem ProofShape.TypedSource.subst_etaLift {σ : ProofShape.Subst}
    (H : TypedSource (A::Δ) e) (S : DomainSort Δ A u)
    (W : ContextSubstitution (A::Δ) Λ σ.lift) :
    e.subst (σ.etaLift u) = e.subst σ.lift := by
  obtain ⟨Γ, t, T, hΓ, EΓ, ht, Et⟩ := H
  cases Γ with
  | nil => cases EΓ
  | cons C Γ =>
    obtain ⟨hΓ, v, hC⟩ := hΓ
    obtain ⟨EC, EΓ⟩ := List.cons.inj EΓ
    have hCu := domain_sort_raw S hΓ hC EΓ EC
    obtain ⟨Γ₀, ρ, hΓ₀, _, WS, ES⟩ :=
      W (show OnCtx (C::Γ) (env.IsType univs) from ⟨hΓ, v, hC⟩)
        (by simp only [proofEraseCtx, EC, EΓ])
    have E := (proofErase_subst_with hΓ₀ WS ht (ES.eta_lift hΓ hCu)).symm.trans
      (proofErase_subst_with hΓ₀ WS ht ES)
    simpa only [Et] using E

/-- Both typed interpretations enter the same left binder, with the correct
proof erasure for the fresh image. The right context conversion consumes the
retained domain history; no ordinary-core join is required. -/
theorem ProofShape.ContextSubstitution.paired_eta_lift
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (WL : ContextSubstitution Δ Λ σ) (WR : ContextSubstitution Δ Λ τ)
    (S : DomainSort Δ A u)
    (H : PiInertWorldHistory D n Λ (.sort u) (A.subst σ) (A.subst τ)) :
    ContextSubstitution (A::Δ) (A.subst σ :: Λ) (σ.etaLift u) ∧
      ContextSubstitution (A::Δ) (A.subst σ :: Λ) (τ.etaLift u) := by
  exact ⟨ContextSubstitution.eta_lift WL.cons S,
    ContextSubstitution.eta_lift (ContextSubstitution.paired_lift heq hs WL WR S H) S⟩

/-- Remove the freshly bound uses and renumber the old ones. Duplicate old
uses with different demand trees are retained separately. -/
def PiInertDemand.tailUses : List (Nat × PiInertDemand) → List (Nat × PiInertDemand)
  | [] => []
  | (0, _) :: uses => PiInertDemand.tailUses uses
  | (i+1, p) :: uses => (i, p) :: PiInertDemand.tailUses uses

omit [Params] in
/-- Every nonfresh use is present in the renumbered old requirements. -/
theorem PiInertDemand.mem_tailUses (H : (i+1, p) ∈ uses) :
    (i, p) ∈ PiInertDemand.tailUses uses := by
  induction uses with
  | nil => cases H
  | cons jr uses ih =>
    obtain ⟨j, r⟩ := jr
    rcases List.mem_cons.1 H with E | tail
    · cases E; exact List.mem_cons_self
    · cases j with
      | zero => exact ih tail
      | succ => exact List.mem_cons_of_mem _ (ih tail)

/-- A finite paired image environment lifts under a fresh binder. Old images
may be arbitrary demand values; they move through the target weakening core
world. The new variable or proof image satisfies every fresh demand. -/
theorem PiInertDemandImages.binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Λ (A.subst σ) u)
    (H : PiInertDemandImages D Δ Λ σ τ (PiInertDemand.tailUses uses)) :
    PiInertDemandImages D (A::Δ) (A.subst σ :: Λ) (σ.etaLift u) (τ.etaLift u) uses := by
  have W := PiInertCoreWorld.weakening heq hc S
  intro i p hi
  cases i with
  | zero =>
    simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.etaLift_zero,
      ProofShape.subst_lift_etaLift] using pi_inert_fresh_demand_value (p := p) heq hs hc hRigid S
  | succ i =>
    have HV := (H i p (PiInertDemand.mem_tailUses hi)).move W
    simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.etaLift_succ,
      ProofShape.subst_lift_etaLift, weak_subst] using HV

/-- Application-body requirements extend through related substituted domains.
The domain consumes a ground history, while old variable images retain their
full finite demands. The two interpretations share the left target binder;
no core join of the substituted domains is assumed. -/
theorem PiInertDemandTree.requirements_under_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u) (H : PiInertDemandTree D (A::Δ) b B) (q : PiInertDemand) :
    ∃ uses : List (Nat × PiInertDemand),
      ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
        PiInertDemandValue .ground D Λ (A.subst σ) (A.subst τ) (.sort u) →
        PiInertDemandImages D Δ Λ σ τ (PiInertDemand.tailUses uses) →
        PiInertDemandValue q D (A.subst σ :: Λ)
          (b.subst (σ.etaLift u)) (b.subst (τ.etaLift u)) (B.subst (σ.etaLift u)) := by
  obtain ⟨uses, _, run⟩ := H.requirements heq hs hc q
  refine ⟨uses, ?_⟩
  intro Λ σ τ WL WR HD images
  obtain ⟨n, history⟩ := HD.base.history
  obtain ⟨VL, VR⟩ := ContextSubstitution.paired_eta_lift heq hs WL WR S history
  exact run VL VR (images.binder heq hs hc hRigid (ContextSubstitution.sort WL S))

/-- The paired binder theorem also returns ordinary lambda-body syntax.
Proof-aware image demands and ordinary lifted syntax agree on typed sources. -/
theorem PiInertDemandTree.requirements_under_lift
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u) (H : PiInertDemandTree D (A::Δ) b B) (q : PiInertDemand) :
    ∃ uses : List (Nat × PiInertDemand),
      ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
        PiInertDemandValue .ground D Λ (A.subst σ) (A.subst τ) (.sort u) →
        PiInertDemandImages D Δ Λ σ τ (PiInertDemand.tailUses uses) →
        PiInertDemandValue q D (A.subst σ :: Λ)
          (b.subst σ.lift) (b.subst τ.lift) (B.subst σ.lift) := by
  obtain ⟨uses, run⟩ := H.requirements_under_binder heq hs hc hRigid S q
  refine ⟨uses, ?_⟩
  intro Λ σ τ WL WR HD images
  have HV := run WL WR HD images
  obtain ⟨n, history⟩ := HD.base.history
  have VL : ContextSubstitution (A::Δ) (A.subst σ :: Λ) σ.lift := WL.cons
  have VR : ContextSubstitution (A::Δ) (A.subst σ :: Λ) τ.lift :=
    ContextSubstitution.paired_lift heq hs WL WR S history
  rw [H.sources.1.subst_etaLift S VL, H.sources.1.subst_etaLift S VR,
    H.sources.2.subst_etaLift S VL] at HV
  exact HV

/-- Testing a raw lambda with an actual source returns its body in its written
binder, with a proof marker exactly when that binder is a proposition. -/
theorem PiInertEvidence.raw_lambda_test
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (S : DomainSort Δ A u) (H : TypedSource Δ (.lam A b)) :
    PiInertEvidence D n .compute (A::Δ)
      (.app ((ProofShape.lam A b).liftN 1) (etaArgument u)) b := by
  obtain ⟨Γ, f, T, hΓ, EΓ, hf, Ef⟩ := H
  obtain ⟨C, body, rfl, hn, EC, Eb⟩ := erase_lam_inv Ef
  obtain ⟨⟨v, hC⟩, B, hb⟩ := hf.lam_inv henv hΓ
  have hCu := domain_sort_raw S hΓ hC EΓ EC
  have HTest := PiInertEvidence.lambda_test (D := D) (stage := n) hs hc hΓ hCu (HasType.lam hCu hb)
  rw [proofErase_eta_body hΓ hCu (HasType.lam hCu hb) hn] at HTest
  simpa only [proofEraseCtx, EΓ, EC, Eb, Ef] using HTest

/-- Paired interpretation closes the ground lambda comparison, including
related written domains and arbitrary old images satisfying the finite uses.
This is a ground result for application-tree bodies; the full arrow demand
is constructed separately by paired_lambda_value. -/
theorem PiInertDemandTree.paired_lambda_ground
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u) (H : PiInertDemandTree D (A::Δ) b B)
    (HF : TypedSource Δ (.lam A b)) (HT : TypedSource Δ (.forallE A B)) :
    ∃ uses : List (Nat × PiInertDemand),
      ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
        PiInertDemandValue .ground D Λ (A.subst σ) (A.subst τ) (.sort u) →
        PiInertDemandImages D Δ Λ σ τ (PiInertDemand.tailUses uses) →
        PiInertDemandValue .ground D Λ ((ProofShape.lam A b).subst σ)
          ((ProofShape.lam A b).subst τ) ((ProofShape.forallE A B).subst σ) := by
  obtain ⟨uses, run⟩ := H.requirements_under_lift heq hs hc hRigid S .ground
  refine ⟨uses, ?_⟩
  intro Λ σ τ WL WR HD images
  obtain ⟨n, HB⟩ := (run WL WR HD images).base.history
  obtain ⟨m, HA⟩ := HD.base.history
  have VL : ContextSubstitution (A::Δ) (A.subst σ :: Λ) σ.lift := WL.cons
  have VR : ContextSubstitution (A::Δ) (A.subst σ :: Λ) τ.lift :=
    ContextSubstitution.paired_lift heq hs WL WR S HA
  have test := PiInertEvidence.raw_lambda_test (n := n) hs hc S HF
  have HL := test.substitute VL
  have HR := test.substitute VR
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at HL HR
  have HE := (HB.prefixes HL.world_computation HR.world_computation).function
    heq hs hc (ContextSubstitution.sort WL S)
  exact ⟨HF.subst WL, HF.subst WR, HT.subst WL, n, HE⟩

/-- Arbitrary paired old image demands and collected fresh argument demands
combine into the body's image environment. No variable-only world assumption
is imposed on the old images in this step. -/
theorem PiInertDemandImages.cons_pair
    (H : PiInertDemandImages D Δ Λ σ τ (PiInertDemand.tailUses uses))
    (HX : PiInertDemandValue (.all (PiInertDemand.headUses uses)) D Λ x y (A.subst σ)) :
    PiInertDemandImages D (A::Δ) Λ (σ.cons x) (τ.cons y) uses := by
  intro i p hi
  cases i with
  | zero =>
    simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.cons,
      ProofShape.lift_subst_cons] using HX.of_all (PiInertDemand.mem_headUses hi)
  | succ i =>
    simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.cons,
      ProofShape.lift_subst_cons] using H i p (PiInertDemand.mem_tailUses hi)

/-- Finite old image requirements move through a target core world. Images
can be arbitrary higher-order values: the world restricts their future use,
not their original syntax. -/
theorem PiInertDemandImages.move
    (H : PiInertDemandImages D Δ Λ σ τ uses) (W : PiInertCoreWorld D Λ Ξ κ) :
    PiInertDemandImages D Δ Ξ (σ.comp κ) (τ.comp κ) uses := by
  intro i p hi
  simpa only [ProofShape.Subst.comp, ProofShape.subst_subst] using (H i p hi).move W

/-- Paired lambda interpretation retains the full requested result demand.
A finite list supplies old image demands, and a finite intersection supplies
the new argument demands. Related substituted domains justify the ground
comparison; typed whole applications justify each later paired body call.
This covers application-tree bodies, not all nested lambda syntax. -/
theorem PiInertDemandTree.paired_lambda_value
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u) (H : PiInertDemandTree D (A::Δ) b B)
    (HF : TypedSource Δ (.lam A b)) (HT : TypedSource Δ (.forallE A B)) (q : PiInertDemand) :
    ∃ (uses : List (Nat × PiInertDemand)) (p : PiInertDemand),
      ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
        PiInertDemandValue .ground D Λ (A.subst σ) (A.subst τ) (.sort u) →
        PiInertDemandImages D Δ Λ σ τ uses →
        PiInertDemandValue (.arrow p q) D Λ ((ProofShape.lam A b).subst σ)
          ((ProofShape.lam A b).subst τ) ((ProofShape.forallE A B).subst σ) := by
  obtain ⟨groundUses, groundRun⟩ := H.paired_lambda_ground heq hs hc hRigid S HF HT
  obtain ⟨bodyUses, _, bodyRun⟩ := H.requirements heq hs hc q
  refine ⟨PiInertDemand.tailUses groundUses ++ PiInertDemand.tailUses bodyUses,
    .all (PiInertDemand.headUses bodyUses), ?_⟩
  intro Λ σ τ WL WR HD images
  have ground := groundRun WL WR HD
    (fun i p hi => images i p (List.mem_append_left _ hi))
  refine ⟨ground.base, ?_⟩
  intro Ξ κ C E x y W HP J HX HL HR HResult
  have VL : ContextSubstitution Δ Ξ (σ.comp κ) := ContextSubstitution.comp WL W.typed
  have VR : ContextSubstitution Δ Ξ (τ.comp κ) := ContextSubstitution.comp WR W.typed
  simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at J HL HR
  obtain ⟨JD, JB⟩ := J.level_core_pi_parts
  have HDA := HD.base.leftSource.subst W.typed
  rw [ProofShape.subst_subst] at HDA
  have HArg := HX.core_join hs hc HDA JD.symm
  have BL : ContextSubstitution (A::Δ) Ξ ((σ.comp κ).cons x) :=
    ContextSubstitution.lambda_argument VL HL
  have BR : ContextSubstitution (A::Δ) Ξ ((τ.comp κ).cons y) :=
    ContextSubstitution.lambda_argument VR HR
  have old : PiInertDemandImages D Δ Λ σ τ (PiInertDemand.tailUses bodyUses) :=
    fun i p hi => images i p (List.mem_append_right _ hi)
  have bodyImages := (old.move W).cons_pair HArg
  have HB := bodyRun BL BR bodyImages
  have JE : ComputeJoin (ErasedLevelCore D) (B.subst ((σ.comp κ).cons x)) (E.inst x) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.subst_subst, ProofShape.Subst.lift_comp_one] using
      JB.subst (fun R => erased_level_core_subst R) (σ := ProofShape.Subst.one x)
  have beta (υ : ProofShape.Subst) (z : ProofShape) : Compute (ErasedLevelCore D)
      (.app (.lam (A.subst υ) (b.subst υ.lift)) z) (b.subst (υ.cons z)) := by
    have E : (b.subst υ.lift).inst z = b.subst (υ.cons z) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
        ProofShape.subst_subst, ProofShape.Subst.lift_comp_one]
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := A.subst υ))
  simpa only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] using
    (HB.core_join hs hc HResult JE).prefixes hs hc HL HR (beta (σ.comp κ) x) (beta (τ.comp κ) y)

/-- Actual paired lambda bodies produce a history with only core-world futures.
The written domains may differ from each other and from the assigned domain.
This constructs the ground comparison; higher demand action is separate. -/
theorem PiInertWorldHistory.actual_lambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B))
    (H : PiInertWorldHistory D stage (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) c)) :
    PiInertWorldHistory D stage (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
      (proofErase Γ (.lam C b)) (proofErase Γ (.lam E c)) := by
  by_cases hp : IsProof Γ (.lam C b)
  · have hq := isProof_of_common_type hΓ hf hg hp
    have HC : PiInertEvidence D stage (.compare true) (proofEraseCtx Γ)
        (proofErase Γ (.lam C b)) (proofErase Γ (.lam C b)) :=
      (PiInertEvidence.core hs hc hΓ hf .refl).join hc (PiInertEvidence.core hs hc hΓ hf .refl)
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hq]
    rw [proofErase_eq_proof.2 hp] at HC
    exact HC.carrier_history.world_history
  have hq : ¬ IsProof Γ (.lam E c) := fun hq => hp (isProof_of_common_type hΓ hg hf hq)
  have HB := PiInertWorldHistory.prefixes
    (PiInertEvidence.lambda_test hs hc hΓ hA hf).world_computation
    (PiInertEvidence.lambda_test hs hc hΓ hA hg).world_computation H
  rw [proofEraseCtx, proofErase_eta_body hΓ hA hf hp, proofErase_eta_body hΓ hA hg hq] at HB
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
  exact HB.function heq hs hc (DomainSort.of_typed hΓ hA)

end Lean4Lean.VEnv.Strengthening
