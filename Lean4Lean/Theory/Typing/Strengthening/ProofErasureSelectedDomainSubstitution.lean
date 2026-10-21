import Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery

/-! # Preserving a selected domain after substitution of types

The failure branch of native recovery retains the original selected output
through a sort-rooted recovery path. Thus a function with a selected Pi either
retains native recovery or computes to a lambda at that exact raw domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
variable [Params]

/-- Retained images recover exactly or have a literal assigned sort and its
actual typing. The literal sort condition retains the selected recovery type;
semantic equality to a sort alone is not this condition. -/
def ExactSortOrRecoveringImages
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery Step (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨
    ∃ u, (contextOracle (proofEraseCtx Γ) i).subst τ = .sort u ∧
      env.HasType univs Γ₀ (σ i) (.sort u)

/-- The literal-sort image condition extends under typed binders at stage
zero, preserving exact lookup outputs. -/
theorem ExactSortOrRecoveringImages.cons
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (H : ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ) :
    ExactSortOrRecoveringImages (ErasedJointStage D 0) (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inl
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) :=
      fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    rcases H hl hn₀ with R | ⟨v, ET, hv⟩
    · apply Or.inl
      have RL := R.rename (Step' := ErasedJointStage D 0) (fun H _ => erased_iota_primitive_subst H) (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
        subst_bvar_liftN, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · refine .inr ⟨v, ?_, hv.weak henv⟩
      simp only [proofEraseCtx, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ET, ProofShape.liftN]

private theorem rooted_not_structure (H : SortRootedRecovery D Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s ls) args)) : False := by
  obtain ⟨m, HR⟩ := H.rooted
  rcases HR.expose hΓ ht with ⟨u, hu⟩ | ⟨A, b, _, _, _, R⟩
  · have HE := hu.uniqU henv hΓ ht
    exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ (HasType.sort (hu.isType henv hΓ |>.choose_spec.sort_inv henv)))
  · have HE := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
    obtain ⟨⟨_, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
    have HC := (HasType.lam hA hb).uniqU henv hΓ HE.hasType.2
    obtain ⟨_, hPi⟩ := (HasType.lam hA hb).isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HC.typeChain henv hΓ hPi)

/-- Recovery at stage zero survives exactly, or its selected output is retained
by a finite sort-rooted recovery. This includes all recovery constructors. -/
theorem proofErase_joint_zero_recovery_subst_or_sortRecovery
    (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀) (source.subst τ) (out.subst τ) ∨
      ∃ n, SortRootedRecovery D Γ₀ (e.subst σ) (out.subst τ) n := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  induction R generalizing Γ Γ₀ σ τ e T with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    rcases HI hl hn with R | ⟨u, ET, hu⟩
    · exact .inl (EΓ ▸ R)
    · apply Or.inr
      rw [← EΓ, ET]
      exact ⟨0, .type hu⟩
  | sort hu => exact .inl (.sort hu)
  | const hc hw hn =>
    apply Or.inl
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    have W' := W.lift henv.ordered hA
    have ES' : ErasedSubstAgreement (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift :=
      ES.lift hΓ₀ W hA
    rcases ih hΓA W' ES' hb (by simp only [proofEraseCtx, EA, EΓ]) Eb
        (HI.cons hΓ₀ W ES hA) with R | ⟨n, H⟩
    · apply Or.inl
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
        ScopedTypeRecovery.lam R
    · apply Or.inr
      refine ⟨n + 1, ?_⟩
      simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES, EA] using
        SortRootedRecovery.lam H
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    rcases ih hΓ₀ W ES hf EΓ Ef HI with R | ⟨n, H⟩
    · apply Or.inl
      rw [ProofShape.subst_inst]
      exact .app R
    · apply Or.inr
      refine ⟨n + 1, ?_⟩
      simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES, Ea] using
        SortRootedRecovery.app (a := a.subst σ) H
  | @forallE Δ A u B v RA RB =>
    have HR : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) (.sort (.imax u v)) := by
      simpa only [EΓ, Ee] using ScopedTypeRecovery.forallE RA RB
    obtain ⟨T', heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht HR
    obtain rfl := erase_sort_inv ET
    exact .inr ⟨0, .type (heT.subst henv.orderedStrong W hΓ₀)⟩
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, hjInfo, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hm.hasType.2 EΓ Em HI with R | ⟨n, H⟩
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at R
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) R
    · exact (rooted_not_structure H hΓ₀ hjInfo (by
        simpa only [VExpr.subst_mkApps, VExpr.subst] using
          hm.hasType.2.subst henv.orderedStrong W hΓ₀)).elim
  | convert R RC ih =>
    have RC' := (forget_scope RC).subst (σ := τ) (fun H => erased_iota_primitive_subst H)
    rcases ih hΓ₀ W ES ht EΓ Ee HI with R' | ⟨n, H⟩
    · exact .inl (.convert R' (RC'.scoped (fun H => .base H)))
    · exact .inr ⟨n + 1, .convert H RC'⟩

/-- A retained function with a selected Pi either retains exact native
recovery or computes to a lambda with that exact substituted domain. The
second branch needs no semantic conversion of the argument guard. -/
theorem proofErase_joint_zero_function_subst_selected_domain
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (HI : ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B)) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (f.subst σ)) (.forallE (A.subst τ) (B.subst τ.lift)) ∨
    ∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (f.subst σ)) (.lam (A.subst τ) body) := by
  rcases proofErase_joint_zero_recovery_subst_or_sortRecovery hs R hΓ₀ W ES hf rfl rfl HI with
    HR | ⟨n, H⟩
  · exact .inl (by rwa [proofErase_subst_with hΓ₀ W hf ES])
  · exact .inr (H.selected_domain hΓ₀ (hf.subst henv.orderedStrong W hΓ₀)
      (mt (isProof_subst hΓ₀ W hf).1 hn))

/-- Substitution of an arbitrary type satisfies the exact-sort alternative
at the removed binder, and lookup recovery at every retained variable. -/
theorem ExactSortOrRecoveringImages.inst_type
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p (.sort u)) :
    ExactSortOrRecoveringImages Step (.sort u :: Γ) Γ
      (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase Γ p)) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
    .sort (hp.isType henv hΓ |>.choose_spec.sort_inv henv)
  have EU : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  intro i A hl _
  cases hl with
  | zero =>
    refine .inr ⟨u, ?_, hp⟩
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, EU,
      ProofShape.liftN, ProofShape.subst]
  | succ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .bvar

/-- Substituting any type, including any proposition, into a retained function
at stage zero preserves native Pi recovery or exposes exactly its selected
domain. Neither recovery of the image nor beta stability is assumed. -/
theorem proofErase_joint_zero_function_inst_type_selected_domain
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.sort u))
    (hf : env.HasType univs (.sort u :: Γ) f (.forallE C E))
    (hn : ¬ IsProof (.sort u :: Γ) f)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (.sort u :: Γ))
      (proofErase (.sort u :: Γ) f) (.forallE A B)) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (f.inst p)) ((ProofShape.forallE A B).inst (proofErase Γ p)) ∨
    ∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (f.inst p)) (.lam (A.inst (proofErase Γ p)) body) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
    .sort (hp.isType henv hΓ |>.choose_spec.sort_inv henv)
  have hΓU : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, _, hU⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := .sort u)).substEq hΓU hp
  have ES : ErasedSubstAgreement (.sort u :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓU hp
  have HH := proofErase_joint_zero_function_subst_selected_domain hs hΓ W ES hf hn
    (ExactSortOrRecoveringImages.inst_type hΓ hp) R
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN, ProofShape.subst] using HH

/-- The application recovery premise is repaired by ordinary application or
the computed-domain rule, using the exact existing target argument guard.
The target function comparison and carrier guard are premises: this theorem
does not assert their recursive substitution closure. -/
theorem proofErase_joint_zero_application_subst_domain_cover
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (HI : ExactSortOrRecoveringImages (ErasedJointStage D 0) Γ Γ₀ σ τ)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B))
    (HF : JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ₀) false
      (proofErase Γ₀ (f.subst σ)) g)
    (HX : JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ₀) (A.subst τ) x y) :
    JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ₀) mode
      (.app (proofErase Γ₀ (f.subst σ)) x) (.app g y) ∨
    ComputedLambdaApplication (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (.app (proofErase Γ₀ (f.subst σ)) x) (.app g y) := by
  rcases proofErase_joint_zero_function_subst_selected_domain hs hΓ₀ W ES hf hn HI R with
    HR | ⟨body, RF⟩
  · exact .inl (.appCarrier HR HF HX)
  · exact .inr (.intro RF HF HX)

end Lean4Lean.VEnv.Strengthening
