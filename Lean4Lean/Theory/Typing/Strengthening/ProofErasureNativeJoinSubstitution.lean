import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeJoinFramework
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeSubstitution

/-! # Substitution with both family alignment and joined native types

Each retained image can use exact recovery or family alignment at a reduct of
its assigned output. The invariant lifts under binders and survives every
native recovery constructor, including projection and conversion.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private projection_compute from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
variable [Params]
variable {hq : QuotRegistered env} {F : List VExpr → VExpr → Prop}
variable [NativeFamilyFramework.InputLaws (definitions hq) F]

/-- Every retained variable image recovers its assigned output exactly or
recovers an actual carrier aligned to a reduct of that assigned output. -/
def Images
    (hq : QuotRegistered env) (F : List VExpr → VExpr → Prop)
    (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨
    Recovery hq F Γ₀ (σ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ)

/-- The aligned native image condition extends under typed binders at stage
zero, preserving exact lookup outputs. -/
theorem Images.cons
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (H : Images hq F Γ Γ₀ σ τ) :
    Images hq F (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inl
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := fun _ => Step hq)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) :=
      fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    rcases H hl hn₀ with R | HR
    · apply Or.inl
      have RL := R.rename (Step' := fun _ => Step hq) (fun H _ => erased_iota_primitive_subst H) (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
        subst_bvar_liftN, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · apply Or.inr
      simpa only [proofEraseCtx, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift, VExpr.Subst.lift] using
        HR.weaken hΓ₀ hΓA

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- Single substitution of an aligned native value satisfies the enlarged image
condition at its exact assigned erasure. -/
theorem Images.inst
    (H : Recovery hq F Γ p (proofErase Γ T)) :
    Images hq F (T :: Γ) Γ
      (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase Γ p)) := by
  intro i A hl _
  cases hl with
  | zero =>
    apply Or.inr
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, VExpr.Subst.one, VExpr.Subst.cons] using H
  | succ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .bvar

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- Every finite-family image certificate is retained, at every family level. -/
theorem Images.of_aligned
    (HI : NativeFamilyFramework.Images (definitions hq) F Γ Γ₀ σ τ) :
    Images hq F Γ Γ₀ σ τ := by
  intro i A hl hn
  rcases HI hl hn with R | H
  · exact .inl R
  · exact .inr (.of_aligned H)

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- The common-reduct image law embeds using actual typed substitution to
interpret each image. It does not need a finite input-family certificate. -/
theorem Images.of_joined
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : JoinedNative.Images hq Γ Γ₀ τ) :
    Images hq F Γ Γ₀ σ τ := by
  intro i A hl hn
  obtain ⟨out, R, RC⟩ := HI hl hn
  have ht := (show env.HasType univs Γ (.bvar i) A from .bvar hl).subst henv.orderedStrong W hΓ₀
  exact .inr (.of_joined hΓ₀ ht (by simpa only [ES hl hn] using R) RC .refl)

omit [NativeFamilyFramework.InputLaws (definitions hq) F] in
/-- Literal sort selection supplies some actual native sort on both branches;
alignment may change its level while preserving an actual typing witness. -/
private theorem native_or_aligned_sort
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort v))
    (H : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) (.sort u) ∨
      Recovery hq F Γ e (.sort u)) :
    ∃ w, env.HasType univs Γ e (.sort w) ∧
      ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) (.sort w) := by
  rcases H with R | H
  · have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
      ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
    obtain ⟨T, he, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht R
    obtain rfl := erase_sort_inv ET
    exact ⟨u, he, R⟩
  · exact H.sort hΓ ht

/-- Recovery at stage zero survives exactly, or its selected output is retained
by a family-aligned native carrier at a reduct. This includes all constructors. -/
theorem recovery_subst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ScopedTypeRecovery (fun _ => Step hq) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : Images hq F Γ Γ₀ σ τ) :
    ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ₀) (source.subst τ) (out.subst τ) ∨
      Recovery hq F Γ₀ (e.subst σ) (out.subst τ) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  induction R generalizing Γ Γ₀ σ τ e T with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    rcases HI hl hn with R | HR
    · exact .inl (EΓ ▸ R)
    · exact .inr (EΓ ▸ HR)
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
        (HI.cons hΓ₀ W ES hA) with R | H
    · apply Or.inl
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
        ScopedTypeRecovery.lam R
    · apply Or.inr
      simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES, EA] using
        Recovery.lam H hΓ₀ (hA.subst henv.orderedStrong W hΓ₀)
          (mt (isProof_subst hΓ₀ W ht).1 (by intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee))
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    rcases ih hΓ₀ W ES hf EΓ Ef HI with R | H
    · apply Or.inl
      rw [ProofShape.subst_inst]
      exact .app R
    · apply Or.inr
      simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES, Ea] using
        Recovery.app H hΓ₀ (ht.subst henv.orderedStrong W hΓ₀)
          (mt (isProof_subst hΓ₀ W ht).1 (by intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee))
  | @forallE Δ A u B v RA RB ihA ihB =>
    obtain ⟨X, Y, rfl, _, EX, EY⟩ := erase_forallE_inv Ee
    obtain ⟨⟨vX, hX⟩, _, hY⟩ := ht.forallE_inv henv
    have hΓX : OnCtx (X.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, vX, hX.subst henv.orderedStrong W hΓ₀⟩
    have HA := ihA hΓ₀ W ES hX EΓ EX HI
    have HB := ihB hΓX (W.lift henv.ordered hX) (ES.lift hΓ₀ W hX) hY
      (by simp only [proofEraseCtx, EX, EΓ]) EY (HI.cons hΓ₀ W ES hX)
    have HA' : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (X.subst σ)) (.sort u) ∨
        Recovery hq F Γ₀ (X.subst σ) (.sort u) := by
      simpa only [← EX, proofErase_subst_with hΓ₀ W hX ES, ProofShape.subst] using HA
    have HB' : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx (X.subst σ :: Γ₀))
        (proofErase (X.subst σ :: Γ₀) (Y.subst σ.lift)) (.sort v) ∨
        Recovery hq F (X.subst σ :: Γ₀) (Y.subst σ.lift) (.sort v) := by
      simpa only [← EY, proofErase_subst_with hΓX (W.lift henv.ordered hX)
        hY (ES.lift hΓ₀ W hX), ProofShape.subst] using HB
    obtain ⟨u', hX', RX⟩ := native_or_aligned_sort hΓ₀
      (hX.subst henv.orderedStrong W hΓ₀) HA'
    obtain ⟨v', hY', RY⟩ := native_or_aligned_sort hΓX
      (hY.subst henv.orderedStrong (W.lift henv.ordered hX) hΓX) HB'
    have hPi := HasType.forallE hX' hY'
    apply Or.inr
    apply Recovery.of_aligned
    refine ⟨_, hPi, .family .sort, ?_⟩
    simp only [VExpr.subst]
    rw [show proofErase Γ₀ (.forallE (X.subst σ) (Y.subst σ.lift)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ₀ hPi)]
    obtain ⟨_, hsort⟩ := hPi.isType henv hΓ₀
    rw [show proofErase Γ₀ (.sort (.imax u' v')) = .sort _ from if_neg (not_isProof_of_sort hΓ₀ hsort)]
    exact .forallE RX RY
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, hjInfo, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hm.hasType.2 EΓ Em HI with R | H
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at R
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) R
    · obtain ⟨mid, R, RC⟩ := H.projection_recovery hΓ₀ (ht.subst henv.orderedStrong W hΓ₀)
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at RC
      have RC' := RC.scoped (Δ := proofEraseCtx Γ₀) (Step' := fun _ => Step hq) (fun H => .base H)
      obtain ⟨args', rfl, Hargs⟩ := RC'.const_spine (fun H =>
        erased_iota_primitive_no_rigid (henv.projectionRigid hi)
          (no_rigid hq (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
      have HR := ScopedTypeRecovery.proj hi HT hj
        (Hargs.length_eq.symm.trans (by simpa only [List.length_map] using hlen)) R
      rw [proofErase_subst_with hΓ₀ W hm.hasType.2 ES, Em] at HR
      have EP := proofErase_subst_with hΓ₀ W ht ES
      rw [Ee] at EP
      simp only [ProofShape.subst] at EP
      rw [← EP] at HR
      apply Or.inr
      apply (Recovery.of_native hΓ₀ (ht.subst henv.orderedStrong W hΓ₀) HR).backward
      rw [projectionType_subst HT hj (by omega)]
      simpa only [proofErase_subst_with hΓ₀ W hm.hasType.2 ES, Em] using
        projection_compute hq (m := proofErase Γ₀ (m.subst σ))
          (Hargs.imp (fun _ _ H => forget_scope H))
  | convert R RC ih =>
    have RC' := (forget_scope RC).subst (σ := τ) (fun H => erased_iota_primitive_subst H)
    rcases ih hΓ₀ W ES ht EΓ Ee HI with R' | H
    · exact .inl (.convert R' (RC'.scoped (fun H => .base H)))
    · obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht
        (by simpa only [EΓ, Ee] using R)
      obtain ⟨_, hA⟩ := heA.isType henv W.wf
      have EA' := proofErase_subst_with hΓ₀ W hA ES
      rw [EA] at EA'
      apply Or.inr
      exact (show Recovery hq F Γ₀ (e.subst σ) (proofErase Γ₀ (A.subst σ)) from
        EA' ▸ H).convert hcon hΓ₀ (hA.subst henv.orderedStrong W hΓ₀)
          (by simpa only [EA'] using RC')

/-- A selected function recovery after aligned native substitution consumes
its transported argument guard to rebuild the application at the actual
recovered domain. No footprint or argument-recovery premise is required. -/
theorem application_subst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hf : env.HasType univs Γ f (.forallE C E)) (_hn : ¬ IsProof Γ f)
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HI : Images hq F Γ Γ₀ σ τ)
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B))
    (HF : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ₀) false
      (proofErase Γ₀ (f.subst σ)) g)
    (HX : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ₀)
      (A.subst τ) (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ))) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ₀) mode
      (.app (proofErase Γ₀ (f.subst σ)) (proofErase Γ₀ (x.subst σ)))
      (.app g (proofErase Γ₀ (y.subst σ))) := by
  rcases recovery_subst hcon R hΓ₀ W ES hf rfl rfl HI with
    HR | H
  · exact .appCarrier (by simpa only [proofErase_subst_with hΓ₀ W hf ES, ProofShape.subst] using HR) HF HX
  · have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
      ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
    obtain ⟨C', E', hf', hx', hy', EC, EE⟩ :=
      proofErase_scoped_function_recovery_arguments hstep W.wf hf hx hy R
    obtain ⟨_, hPi⟩ := hf'.isType henv W.wf
    obtain ⟨⟨uC, hC'⟩, _, hE'⟩ := hPi.forallE_inv henv
    exact H.application_checked hcon hΓ₀ (hf'.subst henv.orderedStrong W hΓ₀)
      (hx'.subst henv.orderedStrong W hΓ₀) (hy'.subst henv.orderedStrong W hΓ₀)
      (by rw [proofErase_subst_with hΓ₀ W hC' ES, EC])
      (by rw [proofErase_subst_with (show OnCtx (C'.subst σ :: Γ₀) (env.IsType univs) from
        ⟨hΓ₀, uC, hC'.subst henv.orderedStrong W hΓ₀⟩)
        (W.lift henv.ordered hC') hE' (ES.lift hΓ₀ W hC'), EE]) HF HX

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
