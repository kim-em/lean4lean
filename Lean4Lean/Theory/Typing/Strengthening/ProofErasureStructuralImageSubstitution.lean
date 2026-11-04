import Lean4Lean.Theory.Typing.Strengthening.StructuralFamilyRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePathImageSubstitution

/-! # Recovery under substitution of structural families

Exceptional images retain a structural-family path. Its application case
consumes the recursive guard and may convert its function carrier; no exact
assigned-domain exposure is required for the new structural leaf.
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

/-- Binder insertion preserves a selected structural-family recovery path. -/
theorem StructuralFamilyRecovery.weakenPath (H : StructuralFamilyRecovery D cut Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (ht : env.HasType univs Γ e T) :
    StructuralFamilyRecovery D (cut + 1) (A :: Γ) (e.liftN 1) (out.liftN 1) n := by
  have W := substEq_of_thinning hΓ (Ctx.Lift'.skip (A := A) .refl)
  have ES : ErasedSubstAgreement Γ (A :: Γ) (fun i => .bvar (i + 1))
      (fun i => .bvar (liftVar 1 i 0)) := by
    intro i B hl hn
    have hx : env.HasType univs Γ (.bvar i) B := .bvar hl
    have EE := proofErase_liftN hΓ hΓA Ctx.LiftN.one hx
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn] at EE
    simpa [VExpr.liftN, ProofShape.liftN, liftVar, Nat.add_comm] using EE
  have WH : PreservesCarrierHeads cut (cut + 1) (fun i => .bvar (liftVar 1 i 0)) := by
    intro i hi
    exact ⟨1 + i, by omega, by simp [liftVar]⟩
  have HH := H.subst hΓA W ES ht WH
  have ET : out.subst (fun i => .bvar (liftVar 1 i 0)) = out.liftN 1 :=
    subst_bvar_liftN out
  simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift',
    ET] using HH

/-- Retained images recover exactly or carry a finite structural-family path with
the exact assigned output. This includes lambda-valued images whose bodies
are types; no recovery of those bodies is required. -/
def StructuralOrRecoveringImages
    (D : PureObservation.Definitions) (cut : Nat)
    (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨
    ∃ n, StructuralFamilyRecovery D cut Γ₀ (σ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) n

/-- The structural-family image condition extends under typed binders at stage
zero, preserving exact lookup outputs. -/
theorem StructuralOrRecoveringImages.cons
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (H : StructuralOrRecoveringImages D cut Γ Γ₀ σ τ) :
    StructuralOrRecoveringImages D (cut + 1) (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
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
    rcases H hl hn₀ with R | ⟨n, HR⟩
    · apply Or.inl
      have RL := R.rename (Step' := ErasedJointStage D 0) (fun H _ => erased_iota_primitive_subst H) (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
        subst_bvar_liftN, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · refine .inr ⟨n, ?_⟩
      simpa only [proofEraseCtx, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift, VExpr.Subst.lift] using
        HR.weakenPath hΓ₀ hΓA (W.lookup hl).hasType.1

/-- The previous finite structural-family image condition embeds at any cutoff. -/
theorem PathOrRecoveringImages.structural
    (H : PathOrRecoveringImages D Γ Γ₀ σ τ) :
    StructuralOrRecoveringImages D cut Γ Γ₀ σ τ := by
  intro i A hl hn
  rcases H hl hn with R | ⟨n, HR⟩
  · exact .inl R
  · exact .inr ⟨n, HR.anchored.structural⟩

/-- The full previous anchored image class embeds, retaining each exact
selected output and finite recovery rank. -/
theorem AnchoredOrRecoveringImages.structural
    (H : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ) :
    StructuralOrRecoveringImages D cut Γ Γ₀ σ τ := by
  intro i A hl hn
  rcases H hl hn with R | ⟨n, HR⟩
  · exact .inl R
  · exact .inr ⟨n, HR.structural⟩

/-- Single substitution of a structural-family value satisfies the enlarged image
condition at its exact assigned erasure. -/
theorem StructuralOrRecoveringImages.inst
    (H : StructuralFamilyRecovery D cut Γ p (proofErase Γ T) n) :
    StructuralOrRecoveringImages D cut (T :: Γ) Γ
      (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase Γ p)) := by
  intro i A hl _
  cases hl with
  | zero =>
    apply Or.inr
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, VExpr.Subst.one, VExpr.Subst.cons] using Exists.intro n H
  | succ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .bvar

/-- A retained projection whose major lost exact native recovery still has a
projection-closed result along a finite structural path. The selected raw major type
is required not to be a protected neutral; projection recovery supplies this
from its rigid owner head. -/
theorem StructuralFamilyRecovery.projection_image (H : StructuralFamilyRecovery D cut Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T)
    (hn : ¬ IsProof Γ (.proj s i e))
    (Hout : ¬ AnchoredCarrier cut out) : InstanceProjectionImage Γ (.proj s i e) := by
  obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  have htMajor := hm.hasType.2
  rcases H.expose hΓ htMajor with HT | HN | ⟨A, u, hf, _, _⟩ | ⟨X, Y, hfN, _, _, _⟩ | ⟨X, Y, b, u, v, hf, _, _, _⟩ | ⟨A, b, _, _, _, _, _, R, _, _⟩
  · exact HT.projection hΓ ht hn
  · exact (Hout HN).elim
  · have HE := hf.uniqU henv hΓ htMajor
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hPi)).elim
  · have HE := hfN.uniqU henv hΓ htMajor
    obtain ⟨_, hPi⟩ := hfN.isType henv hΓ
    exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hPi)).elim
  · have HE := hf.uniqU henv hΓ htMajor
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hPi)).elim
  · have HE := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ htMajor
    obtain ⟨⟨_, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
    have HC := (HasType.lam hA hb).uniqU henv hΓ HE.hasType.2
    obtain ⟨_, hPi⟩ := (HasType.lam hA hb).isType henv hΓ
    exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HC.typeChain henv hΓ hPi)).elim

/-- Recovery at stage zero survives exactly, or its selected output is retained
by a finite structural-family recovery. This includes all recovery constructors. -/
theorem proofErase_joint_zero_recovery_subst_structuralImages
    (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : StructuralOrRecoveringImages D cut Γ Γ₀ σ τ) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀) (source.subst τ) (out.subst τ) ∨
      ∃ n, StructuralFamilyRecovery D cut Γ₀ (e.subst σ) (out.subst τ) n := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  induction R generalizing Γ Γ₀ σ τ e T cut with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    rcases HI hl hn with R | ⟨n, HR⟩
    · exact .inl (EΓ ▸ R)
    · exact .inr ⟨n, EΓ ▸ HR⟩
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
        StructuralFamilyRecovery.lam H
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
        StructuralFamilyRecovery.app (a := a.subst σ) H
  | @forallE Δ A u B v RA RB =>
    have HR : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) (.sort (.imax u v)) := by
      simpa only [EΓ, Ee] using ScopedTypeRecovery.forallE RA RB
    obtain ⟨T', heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht HR
    obtain rfl := erase_sort_inv ET
    exact .inr ⟨0, .type (heT.subst henv.orderedStrong W hΓ₀)⟩
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _hjInfo, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hm.hasType.2 EΓ Em HI with R | ⟨n, H⟩
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at R
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) R
    · apply Or.inr
      refine ⟨0, .instanceProjection ?_⟩
      exact H.projection_image hΓ₀ (ht.subst henv.orderedStrong W hΓ₀)
        (mt (isProof_subst hΓ₀ W ht).1 hn) (by
          rintro ⟨i, args, _, HE⟩
          have HC := congrArg ProofShape.constHead HE
          simp only [ProofShape.subst_mkApps, ProofShape.subst,
            ProofShape.constHead_mkApps, ProofShape.constHead] at HC
          cases HC)
  | convert R RC ih =>
    have RC' := (forget_scope RC).subst (σ := τ) (fun H => erased_iota_primitive_subst H)
    rcases ih hΓ₀ W ES ht EΓ Ee HI with R' | ⟨n, H⟩
    · exact .inl (.convert R' (RC'.scoped (fun H => .base H)))
    · exact .inr ⟨n + 1, .convert H RC'⟩

/-- A selected function recovery after structural-family substitution consumes
its transported argument guard to rebuild the application. This uses actual
substituted argument typings and permits a different written lambda domain. -/
theorem proofErase_joint_zero_function_subst_structural_application
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HI : StructuralOrRecoveringImages D cut Γ Γ₀ σ τ)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B))
    (HF : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ₀) false
      (proofErase Γ₀ (f.subst σ)) g)
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (A.subst τ) (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ))) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ₀) mode
      (.app (proofErase Γ₀ (f.subst σ)) (proofErase Γ₀ (x.subst σ)))
      (.app g (proofErase Γ₀ (y.subst σ))) := by
  rcases proofErase_joint_zero_recovery_subst_structuralImages hs R hΓ₀ W ES hf rfl rfl HI with
    HR | ⟨n, H⟩
  · exact .appCarrier (by simpa only [proofErase_subst_with hΓ₀ W hf ES, ProofShape.subst] using HR) HF HX
  · exact H.application hs hΓ₀ (hf.subst henv.orderedStrong W hΓ₀)
      (mt (isProof_subst hΓ₀ W hf).1 hn)
      (hx.subst henv.orderedStrong W hΓ₀) (hy.subst henv.orderedStrong W hΓ₀) HF HX

end Lean4Lean.VEnv.Strengthening
