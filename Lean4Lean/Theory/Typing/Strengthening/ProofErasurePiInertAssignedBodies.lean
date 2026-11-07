import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDirectedBodies

/-! # Directed lambda action at an assigned domain

Written lambda annotations may differ from the assigned Pi domain. Ordinary
typing conversion aligns the body realizations; semantic histories are built
in the assigned binder and are never transported through a non-core world.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private tree_cons_comp tree_id_comp tree_inst
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedTrees
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Retyping a raw lambda body under its assigned domain retypes the whole
lambda, even when its written domain differs. Only ordinary typing and Pi
injectivity are used; this does not transport semantic body evidence. -/
theorem ProofShape.TypedAt.lam_body_at
    (HF : TypedAt Δ (.lam C b) (.forallE A B₀)) (HB : TypedAt (A::Δ) b B) :
    TypedAt Δ (.lam C b) (.forallE A B) := by
  obtain ⟨Γ, f, F, hΓ, EΓ, hf, Ef, EF⟩ := HF
  obtain ⟨C₀, b₀, rfl, hn, EC, Eb⟩ := erase_lam_inv Ef
  obtain ⟨A₀, B₁, rfl, _, EA, EB₁⟩ := erase_forallE_inv EF
  obtain ⟨B₂, HE, hb⟩ := hf.lam_inv_forallE henv hΓ
  obtain ⟨⟨u, HD⟩, _, _⟩ := HE.forallE_inv henv hΓ
  have hΓC : OnCtx (C₀::Γ) (env.IsType univs) := ⟨hΓ, u, HD.hasType.1⟩
  have hΓA : OnCtx (A₀::Γ) (env.IsType univs) := ⟨hΓ, u, HD.hasType.2⟩
  have W : IsDefEqCtx env univs Γ (C₀::Γ) (A₀::Γ) := .succ .zero HD
  have hbA := hb.defeqDFC henv W
  have EbA := (proofErase_defeqCtx hΓC W hb).symm.trans Eb
  have hnb : b ≠ .proof := fun E =>
    hn ((proofErase_eq_proof.1 (Eb.trans E)).lam hΓ HD.hasType.1)
  have HB' : TypedAt (proofEraseCtx (A₀::Γ)) b B := by
    simpa only [proofEraseCtx, EA, EΓ] using HB
  obtain ⟨B₃, hb₃, EB₃⟩ := HB'.realize_term hΓA hbA EbA hnb
  obtain ⟨v, hB₃⟩ := hb₃.isType henv hΓA
  have hbC := hb₃.defeqDFC henv (.succ .zero HD.symm)
  have hl := HasType.lam HD.hasType.1 hbC
  have HP := IsDefEq.forallEDF HD.symm hB₃
  have hf' := HP.symm.defeq hl
  refine ⟨Γ, .lam C₀ b₀, .forallE A₀ B₃, hΓ, EΓ, hf', Ef, ?_⟩
  rw [show proofErase Γ (.forallE A₀ B₃) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE HD.hasType.2 hB₃)), EA, EB₃]

/-- The fresh beta test returns the raw body under the assigned Pi domain,
including when the written annotation differs. Context conversion is used
only to identify erasure of the actual body. -/
theorem PiInertEvidence.raw_lambda_assigned_test
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (S : DomainSort Δ A u) (H : TypedAt Δ (.lam C b) (.forallE A B)) :
    PiInertEvidence D n .compute (A::Δ)
      (.app ((ProofShape.lam C b).liftN 1) (etaArgument u)) b := by
  obtain ⟨Γ, f, F, hΓ, EΓ, hf, Ef, EF⟩ := H
  obtain ⟨C₀, b₀, rfl, hn, EC, Eb⟩ := erase_lam_inv Ef
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv EF
  obtain ⟨B₁, HE, hb⟩ := hf.lam_inv_forallE henv hΓ
  obtain ⟨⟨v, HD⟩, _, _⟩ := HE.forallE_inv henv hΓ
  have hΓC : OnCtx (C₀::Γ) (env.IsType univs) := ⟨hΓ, v, HD.hasType.1⟩
  have EbA := (proofErase_defeqCtx hΓC (.succ .zero HD) hb).symm.trans Eb
  have hA := S.realize_type hΓ HD.hasType.2 EΓ EA
  have test := PiInertEvidence.lambda_test (D := D) (stage := n) hs hc hΓ hA hf
  rw [proofErase_eta_body hΓ hA hf hn] at test
  simpa only [proofEraseCtx, EΓ, EA, EbA, Ef] using test

/-- Full recursive lambda action at a common assigned Pi, with arbitrary
written annotations on both endpoints. Fresh tests and future argument
substitutions use the assigned binder. Domain self interpretation, input
supply, and the directed body interpretation remain explicit hypotheses. -/
theorem PiInertDirectedPairInterpretation.lam_assigned
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u)
    (HD : PiInertGuardedInterpretation D Δ ds A (.sort u) (.plain .ground))
    (HS : PiInertGuardedSupplyInterpretation D Δ ss A p)
    (HB : PiInertDirectedPairInterpretation D (A::Δ) (p.bindUses uses) b c B B q)
    (HF : TypedAt Δ (.lam C b) (.forallE A B))
    (HG : TypedAt Δ (.lam E c) (.forallE A B)) :
    PiInertDirectedPairInterpretation D Δ (ds ++ (ss ++ uses))
      (.lam C b) (.lam E c) (.forallE A B) (.forallE A B) (.call A B p q) := by
  refine ⟨HF, HG, ?_⟩
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
  rw [HB.left.sources.1.subst_etaLift S VL, HB.right.sources.1.subst_etaLift S VR,
    HB.left.sources.2.subst_etaLift S VL] at bodyBase
  have WB : ContextSubstitution (A.subst σ :: Λ) (A.subst τ :: Λ) ProofShape.Subst.id :=
    HA.binder_context heq hs SL SR
  have rightBody : TypedAt (A.subst τ :: Λ) (c.subst τ.lift) (B.subst σ.lift) := by
    simpa only [ProofShape.subst_id] using bodyBase.right.subst WB
  have rightOwn := TypedAt.lam_body_at
    (by simpa only [ProofShape.subst] using HG.subst WR) rightBody
  have right := rightOwn.pi_domain heq hs SL SR domain.base.ground
  have left := HF.subst WL
  obtain ⟨n, history⟩ := bodyBase.ground.history
  have testL := PiInertEvidence.raw_lambda_assigned_test (n := n) hs hc S HF
  have testR := PiInertEvidence.raw_lambda_assigned_test (n := n) hs hc S HG
  have HL := testL.substitute VL
  have HR := testR.substitute VR
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at HL HR
  have ground := (history.prefixes HL.world_computation HR.world_computation).function heq hs hc SL
  refine ⟨⟨left, ?_, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · simpa only [ProofShape.subst] using right
  · exact ⟨HF.sources.1.subst WL, HG.sources.1.subst WR, HF.sources.2.subst WL, n, ground⟩
  · exact (PiInertEvidence.of_core_join hc left.sources.2 left.sources.2 .refl).world_computation
  · intro Ξ κ x y W HX HLeft HRight
    have PL : ContextSubstitution Δ Ξ (σ.comp κ) := ContextSubstitution.comp WL W.typed
    have PR : ContextSubstitution Δ Ξ (τ.comp κ) := ContextSubstitution.comp WR W.typed
    simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at HLeft HRight ⊢
    have FL := left.subst W.typed
    have FR := right.subst W.typed
    have GR := HG.subst PR
    simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at FL FR GR
    obtain ⟨TX, TL⟩ := FL.app_parts HLeft
    obtain ⟨TY, _⟩ := GR.app_parts HRight
    have BL : ContextSubstitution (A::Δ) Ξ ((σ.comp κ).cons x) :=
      ContextSubstitution.cons_assigned PL TX
    have BR : ContextSubstitution (A::Δ) Ξ ((τ.comp κ).cons y) :=
      ContextSubstitution.cons_assigned PR TY
    have result := HB.run BL BR ((old.move W).cons_pair HX)
    have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HRight
    rw [tree_inst] at TL TR
    have beta (domain body : ProofShape) (υ : ProofShape.Subst) (z : ProofShape) :
        Compute (ErasedLevelCore D)
          (.app (.lam (domain.subst υ) (body.subst υ.lift)) z) (body.subst (υ.cons z)) :=
      tree_inst body υ z ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := domain.subst υ))
    exact result.prefixes heq hs hc TL TR (beta C b (σ.comp κ) x) (beta E c (τ.comp κ) y)


/-- The separately retained right assignment can change without changing a
run: the run already assigns its right image the left substituted carrier. -/
theorem PiInertDirectedPairInterpretation.right_assignment
    (H : PiInertDirectedPairInterpretation D Δ uses a b T U p)
    (HB : TypedAt Δ b V) : PiInertDirectedPairInterpretation D Δ uses a b T V p :=
  ⟨H.left, HB, H.run⟩

/-- The complete original lamDF case with different written domains. Each
body direction stays in its original rank-k child's context. Actual context
conversion identifies erased bodies, while the semantic runs use their own
assigned binders. Both native Pi interfaces and arbitrary recursive profiles
are retained. Construction of domain interpretations, supplies, and body
directions from general strong children remains open. -/
theorem StrongBounded.paired_lam_assigned
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (domainChild : StrongBounded env univs k Γ A C (.sort u))
    (bodyTypeA : StrongBounded env univs k (A::Γ) B B (.sort v))
    (bodyTypeC : StrongBounded env univs k (C::Γ) B B (.sort v))
    (bodyChildA : StrongBounded env univs k (A::Γ) b c B)
    (bodyChildC : StrongBounded env univs k (C::Γ) b c B)
    (HA : PiInertGuardedInterpretation D (proofEraseCtx Γ) ds (proofErase Γ A)
      (.sort u) (.plain .ground))
    (HC : PiInertGuardedInterpretation D (proofEraseCtx Γ) es (proofErase Γ C)
      (.sort u) (.plain .ground))
    (HL : PiInertGuardedSupplyInterpretation D (proofEraseCtx Γ) ls (proofErase Γ A) p)
    (HR : PiInertGuardedSupplyInterpretation D (proofEraseCtx Γ) rs (proofErase Γ C) r)
    (HB : PiInertDirectedPairInterpretation D (proofEraseCtx (A::Γ)) (p.bindUses bs)
      (proofErase (A::Γ) b) (proofErase (A::Γ) c)
      (proofErase (A::Γ) B) (proofErase (A::Γ) B) q)
    (HK : PiInertDirectedPairInterpretation D (proofEraseCtx (C::Γ)) (r.bindUses cs)
      (proofErase (C::Γ) c) (proofErase (C::Γ) b)
      (proofErase (C::Γ) B) (proofErase (C::Γ) B) s) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ)
      ((ds ++ (ls ++ bs)) ++ (es ++ (rs ++ cs)))
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam C c))
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C B))
      (.call (proofErase Γ A) (proofErase (A::Γ) B) p q)
      (.call (proofErase Γ C) (proofErase (C::Γ) B) r s) := by
  have HD := domainChild.strong.defeq
  have hA := HD.hasType.1
  have hC := HD.hasType.2
  have hBA := bodyTypeA.strong.defeq.hasType.1
  have hBC := bodyTypeC.strong.defeq.hasType.1
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have HE := (StrongBounded.lamDF (hA.sort_r henv hΓ) (hBA.sort_r henv hΓA)
    domainChild bodyTypeA bodyTypeC bodyChildA bodyChildC).strong.defeq
  have HP := IsDefEq.forallEDF HD hBA
  have FL := TypedAt.of_typed hΓ HE.hasType.1
  have GR := TypedAt.of_typed hΓ (HasType.lam hC bodyChildC.strong.defeq.hasType.2)
  have GL := TypedAt.of_typed hΓ HE.hasType.2
  have FR := TypedAt.of_typed hΓ (HP.defeq HE.hasType.1)
  have ETA : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hBA))
  have ETC : proofErase Γ (.forallE C B) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) B) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hC hBC))
  by_cases hn : IsProof Γ (.lam A b)
  · have hn' := (isProof_congr hΓ HE).1 hn
    rw [proofErase_eq_proof.2 hn, ETA] at FL
    rw [proofErase_eq_proof.2 hn', ETC] at GR
    rw [proofErase_eq_proof.2 hn, proofErase_eq_proof.2 hn', ETA, ETC]
    exact ((PiInertDirectedPairInterpretation.proof_call hc FL).right_assignment GR).paired
      ((PiInertDirectedPairInterpretation.proof_call hc GR).right_assignment FL)
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have EL : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A::Γ) b) := if_neg hn
  have ER : proofErase Γ (.lam C c) = .lam (proofErase Γ C) (proofErase (C::Γ) c) := if_neg hn'
  have Eb := proofErase_defeqCtx hΓA (.succ .zero HD) bodyChildA.strong.defeq.hasType.1
  have Ec := proofErase_defeqCtx hΓA (.succ .zero HD) bodyChildA.strong.defeq.hasType.2
  rw [EL, ETA] at FL
  rw [ER, ETC] at GR
  rw [ER, ETA, ← Ec] at GL
  rw [EL, ETC, Eb] at FR
  have forward := HB.lam_assigned heq hs hc hRigid (.of_typed hΓ hA) HA HL FL GL
  have backward := HK.lam_assigned heq hs hc hRigid (.of_typed hΓ hC) HC HR GR FR
  have FRown : TypedAt (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (C::Γ) b))
      (.forallE (proofErase Γ A) (proofErase (A::Γ) B)) := by
    simpa only [Eb] using FL
  have backward' := backward.right_assignment FRown
  rw [EL, ER, ETA, ETC, ← Ec]
  exact (forward.right_assignment (by simpa only [Ec] using GR)).paired
    (by simpa only [← Eb, ← Ec] using backward')

end Lean4Lean.VEnv.Strengthening
