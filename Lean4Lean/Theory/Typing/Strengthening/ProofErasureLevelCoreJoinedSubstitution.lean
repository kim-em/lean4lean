import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNativeReduction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-! # Joined native substitution with universe conversion

Images recover ordinary reducts of their assigned carriers in the level core.
Every source level-core recovery then substitutes with an ordinary output
residual. Conversion uses level-core confluence and universe postponement;
application and projection retain exact ordinary head inversion.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelCoreNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private forall_parts projection_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNativeReduction
variable [Params] {D : Definitions}

/-- Each retained image natively recovers a reduct of its assigned carrier.
Native certificates use the level core, while the residual is ordinary.
The following image construction also accepts arbitrary common level reducts. -/
def Images
    (D : Definitions)
    (Γ Γ₀ : List VExpr) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ∃ out, ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ₀) (τ i) out ∧
      Compute (ErasedIotaPrimitive D) ((contextOracle (proofEraseCtx Γ) i).subst τ) out

/-- Native recovery up to a reduct extends under arbitrary typed binders. -/
theorem Images.cons
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (H : Images D Γ Γ₀ τ) :
    Images D (A :: Γ) (A.subst σ :: Γ₀) τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    refine ⟨_, ?_, .refl⟩
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := fun _ => ErasedLevelCore D)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) :=
      fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    obtain ⟨out, R, RC⟩ := H hl hn₀
    refine ⟨out.liftN 1, ?_, ?_⟩
    · have RL := R.rename (Step' := fun _ => ErasedLevelCore D)
        (fun H _ => erased_level_core_subst H) (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
        subst_bvar_liftN, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · simpa only [proofEraseCtx, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
        RC.liftN (fun H => erased_iota_primitive_liftN H)

/-- A value whose assigned carrier computes to a native recovered output
supplies all images for its single substitution. -/
theorem Images.inst
    (R : ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ p) out)
    (RC : Compute (ErasedIotaPrimitive D) (proofErase Γ T) out) :
    Images D (T :: Γ) Γ (ProofShape.Subst.one (proofErase Γ p)) := by
  intro i A hl _
  cases hl with
  | zero =>
    refine ⟨out, ?_, ?_⟩
    · simpa only [ProofShape.Subst.one, ProofShape.Subst.cons] using R
    · simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id] using RC
  | succ hl =>
    refine ⟨_, .bvar, ?_⟩
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .refl

/-- Pointwise common level-core reducts suffice for all simultaneous images.
Universe postponement constructs the ordinary residual in the image invariant. -/
theorem Images.of_joins
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (H : ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
      ∃ out, ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ₀) (τ i) out ∧
        ComputeJoin (ErasedLevelCore D) ((contextOracle (proofEraseCtx Γ) i).subst τ) out) :
    Images D Γ Γ₀ τ := by
  intro i A hl hn
  obtain ⟨out, RN, HJ⟩ := H hl hn
  obtain ⟨_, hA⟩ := (show env.HasType univs Γ (.bvar i) A from .bvar hl).isType henv W.wf
  have EA : proofErase Γ₀ (A.subst σ) = (contextOracle (proofEraseCtx Γ) i).subst τ := by
    rw [proofErase_subst_with hΓ₀ W hA ES, proofEraseCtx_oracle, erasedTypeOracle_valid W.wf hl]
  obtain ⟨native, Rnative, RC⟩ := of_join hs hlevels hcon hΓ₀
    (hA.subst henv.orderedStrong W hΓ₀) RN (EA ▸ HJ)
  exact ⟨native, Rnative, by simpa only [EA] using RC⟩

/-- Simultaneous images may themselves use mixed expansion in native recovery.
A common level-core reduct with each assigned carrier discharges the image
invariant; exact recovery of the assigned syntax is unnecessary. -/
theorem Images.of_mixed_joins
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (H : ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
      ∃ out, ScopedTypeRecovery (ErasedLevelCoreExpansion D Recovery) (proofEraseCtx Γ₀) (τ i) out ∧
        ComputeJoin (ErasedLevelCore D) ((contextOracle (proofEraseCtx Γ) i).subst τ) out) :
    Images D Γ Γ₀ τ := by
  intro i A hl hn
  obtain ⟨out, RN, HJ⟩ := H hl hn
  obtain ⟨_, hA⟩ := (show env.HasType univs Γ (.bvar i) A from .bvar hl).isType henv W.wf
  have EA : proofErase Γ₀ (A.subst σ) = (contextOracle (proofEraseCtx Γ) i).subst τ := by
    rw [proofErase_subst_with hΓ₀ W hA ES, proofEraseCtx_oracle, erasedTypeOracle_valid W.wf hl]
  have EE := ES hl hn
  obtain ⟨native, Rnative, RC⟩ := expansion_recovery_align hs hlevels hcon hD hc hr hΓ₀
    (W.lookup hl).hasType.1 (by simpa only [EE] using RN) (EA ▸ HJ)
  exact ⟨native, by simpa only [EE] using Rnative, by simpa only [EA] using RC⟩

/-- Every native recovery survives a typed substitution whose images recover
common reducts of their assigned carriers. The selected output may compute
further; no exact recovery at its unreduced syntax is asserted. -/
theorem recovery_subst
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : Images D Γ Γ₀ τ) :
    ∃ out', ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ₀) (source.subst τ) out' ∧
      Compute (ErasedIotaPrimitive D) (out.subst τ) out' := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) :=
    erased_level_core_descent hs
  induction R generalizing Γ Γ₀ σ τ e T with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    exact EΓ ▸ HI hl hn
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact ⟨_, .const hc hw hn, .refl⟩
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    obtain ⟨out', HR, RC⟩ := ih hΓA (W.lift henv.ordered hA) (ES.lift hΓ₀ W hA)
      hb (by simp only [proofEraseCtx, EA, EΓ]) Eb (HI.cons hΓ₀ W ES hA)
    refine ⟨_, ?_, .forallE .refl RC⟩
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
      ScopedTypeRecovery.lam HR
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv W.wf
    obtain ⟨out', HR, RC⟩ := ih hΓ₀ W ES hf EΓ Ef HI
    obtain ⟨A', B', rfl, _, RB⟩ := forall_parts RC
    refine ⟨_, .app HR, ?_⟩
    rw [ProofShape.subst_inst]
    simpa only [ProofShape.inst_eq_subst] using RB.subst (fun H => erased_iota_primitive_subst H)
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, CA⟩ := ihA hΓ₀ W ES hA EΓ EA HI
    have EoutA := (CA.scoped (Δ := proofEraseCtx Γ₀) (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outA
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    obtain ⟨outB, HB, CB⟩ := ihB hΓA (W.lift henv.ordered hA) (ES.lift hΓ₀ W hA)
      hB (by simp only [proofEraseCtx, EA, EΓ]) EB (HI.cons hΓ₀ W ES hA)
    have EoutB := (CB.scoped (Δ := proofEraseCtx Γ₀) (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outB
    refine ⟨_, .forallE HA ?_, .refl⟩
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA] using HB
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    obtain ⟨out', HR, RC⟩ := ih hΓ₀ W ES hm.hasType.2 EΓ Em HI
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at RC
    have RC' := RC.scoped (Δ := proofEraseCtx Γ₀) (Step' := fun _ => ErasedIotaPrimitive D) (fun H => .base H)
    obtain ⟨args', rfl, Hargs⟩ := RC'.const_spine (fun H =>
      erased_iota_primitive_no_rigid (henv.projectionRigid hi)
        (hD (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
    refine ⟨_, .proj hi HT hj (Hargs.length_eq.symm.trans (by simpa only [List.length_map] using hlen)) HR, ?_⟩
    rw [projectionType_subst HT hj (by omega)]
    exact projection_compute (Hargs.imp (fun _ _ H => H.core_forget))
  | convert R RC ih =>
    obtain ⟨out', HR, HC⟩ := ih hΓ₀ W ES ht EΓ Ee HI
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨_, hA⟩ := heA.isType henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have EA' := proofErase_subst_with hΓ₀ W hA ES
    rw [EA] at EA'
    have RC' := RC.core_forget.subst (σ := τ) (fun H => erased_level_core_subst H)
    obtain ⟨shared, Hnew, Hold⟩ := proofErase_level_core_confluent hs hlevels hcon hc hΓ₀ hA'
      (by simpa only [EA'] using HC.mono (Step' := ErasedLevelCore D) (fun H => Or.inl H))
      (by simpa only [EA'] using RC')
    obtain ⟨Aout, HAout, EAout⟩ := proofErase_scoped_compute_realize hstep W.wf hA EΓ EA RC
    have Eout := proofErase_subst_with hΓ₀ W HAout.hasType.2 ES
    rw [EAout] at Eout
    obtain ⟨native, RN, Rcore⟩ := pullback hs hlevels hcon hΓ₀
      (HAout.hasType.2.subst henv.orderedStrong W hΓ₀)
      (HR.convert (Hnew.scoped (fun H => .base H))) (Eout ▸ Hold)
    exact ⟨native, RN, by simpa only [Eout] using Rcore⟩

/-- Mixed native recovery substitutes through joined level-core images. Both
replacement and substitution leave ordinary forward residuals of the selected
output, so they compose without a backward ordinary-conversion assumption. -/
theorem expansion_recovery_joined_subst
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (HI : Images D Γ Γ₀ τ)
    (R : ScopedTypeRecovery (ErasedLevelCoreExpansion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (e.subst σ)) out' ∧ Compute (ErasedIotaPrimitive D) (out.subst τ) out' := by
  obtain ⟨native, RN, RC⟩ := expansion_recovery hs hlevels hcon hD hc hr W.wf ht R
  obtain ⟨out', RN', RC'⟩ := recovery_subst hs hlevels hD hc hcon RN hΓ₀ W ES ht rfl rfl HI
  rw [← proofErase_subst_with hΓ₀ W ht ES] at RN'
  exact ⟨out', RN', (RC.subst (fun H => erased_iota_primitive_subst H)).trans RC'⟩

end Lean4Lean.VEnv.Strengthening.LevelCoreNative
