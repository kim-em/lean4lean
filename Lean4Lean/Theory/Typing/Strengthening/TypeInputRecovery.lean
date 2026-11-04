import Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInputImage

/-! # Independent recovery paths through callable and projectable images

This finite path is below selected-domain carrier conversion in the dependency
graph. It preserves the original selected output, follows actual typed call and
projection trees, and computes exposed lambdas at the exact selected domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private core_forall_parts from Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A path ending in a callable/projectable image, with its selected raw type retained.
The computation relation is the context-independent stage-zero core. -/
inductive TypeInputRecovery (D : PureObservation.Definitions) :
    List VExpr → VExpr → ProofShape → Nat → Prop where
  | atom : TypeInputImage Γ e → TypeInputRecovery D Γ e out 0
  | lam : TypeInputRecovery D (A :: Γ) b B n →
      TypeInputRecovery D Γ (.lam A b) (.forallE (proofErase Γ A) B) (n + 1)
  | app : TypeInputRecovery D Γ f (.forallE A B) n →
      TypeInputRecovery D Γ (.app f a) (B.inst (proofErase Γ a)) (n + 1)
  | convert : TypeInputRecovery D Γ e T n → Compute (ErasedIotaPrimitive D) T U →
      TypeInputRecovery D Γ e U (n + 1)

/-- Typed substitution preserves both the rank and the exact selected output.
No recovery of any substitution image is required for this fragment. -/
theorem TypeInputRecovery.subst (H : TypeInputRecovery D Γ e out n)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T) :
    TypeInputRecovery D Γ₀ (e.subst σ) (out.subst τ) n := by
  induction H generalizing Γ₀ σ τ T with
  | atom h => exact .atom (h.subst hΓ₀ W)
  | @lam A Γ b B n H ih =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have ES' : ErasedSubstAgreement (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift :=
      ES.lift hΓ₀ W hA
    simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES] using
      TypeInputRecovery.lam (ih ⟨hΓ₀, u, hA'⟩ (W.lift henv.ordered hA) ES' hb)
  | @app Γ f A B n a H ih =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES] using
      TypeInputRecovery.app (a := a.subst σ) (ih hΓ₀ W ES hf)
  | convert H R ih =>
    exact .convert (ih hΓ₀ W ES ht) (R.subst (fun H => erased_iota_primitive_subst H))

/-- Head exposure retains computation from the exposed Pi to the selected
output. Application consumes a smaller body path and one conversion node;
the rank remains strictly below the original application path. -/
theorem TypeInputRecovery.expose (H : TypeInputRecovery D Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    TypeInputImage Γ e ∨
      ∃ A b B m, m < n ∧ TypeInputRecovery D (A :: Γ) b B m ∧
        VExpr.BetaRed e (.lam A b) ∧
        Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ A) B) out := by
  induction n using Nat.strongRecOn generalizing Γ e out T with
  | ind n ih =>
    cases H with
    | atom h => exact .inl h
    | lam H => exact .inr ⟨_, _, _, _, by omega, H, .refl, .refl⟩
    | @convert Γ e source k out H R =>
      rcases ih k (by omega) H hΓ ht with HS | ⟨A, b, B, m, hm, HB, RB, RT⟩
      · exact .inl HS
      · exact .inr ⟨A, b, B, m, by omega, HB, RB, RT.trans R⟩
    | @app Γ f X Y k a H =>
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
      rcases ih k (by omega) H hΓ hf with hs | ⟨A, b, B, m, hm, HB, RF, RT⟩
      · exact .inl (hs.application hΓ ht)
      obtain ⟨_, _, EE, _, RB⟩ := core_forall_parts RT
      obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
      have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
      obtain ⟨⟨u, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
      have hfPi := (HE.toU.of_r henv hΓ (HasType.lam hA hb)).hasType.1
      have hxA := argument_at_displayed_domain hΓ hf hfPi hx
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have WS := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA hxA
      have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one a)
          (ProofShape.Subst.one (proofErase Γ a)) := erasedSubstAgreement_one hΓA hxA
      have Hinst : TypeInputRecovery D Γ (b.inst a) (B.inst (proofErase Γ a)) m := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
          ProofShape.Subst.liftN] using HB.subst hΓ WS ES hb
      have RBinst : Compute (ErasedIotaPrimitive D) (B.inst (proofErase Γ a))
          (Y.inst (proofErase Γ a)) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB.subst
          (σ := ProofShape.Subst.one (proofErase Γ a)) (fun H => erased_iota_primitive_subst H)
      have R : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have HE' := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
      rcases ih (m + 1) (by omega) (Hinst.convert RBinst) hΓ HE'.hasType.2 with
        hv | ⟨C, body, B', j, hj, Hbody, RB', RT'⟩
      · exact .inl (hv.back hΓ HE')
      · exact .inr ⟨C, body, B', j, by omega, Hbody, R.trans RB', RT'⟩

/-- A retained function either has a certified elimination tree or computes
to a lambda with exactly the selected raw domain. The final annotation
change uses the retained Pi-domain computation, not semantic carrier conversion. -/
theorem TypeInputRecovery.selected_domain
    (H : TypeInputRecovery D Γ f (.forallE A B) n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE C E))
    (hn : ¬ IsProof Γ f) :
    TypeInputImage Γ f ∨ ∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.lam A body) := by
  rcases H.expose hΓ hf with hs | ⟨X, b, Y, _, _, _, RF, RT⟩
  · exact .inl hs
  apply Or.inr
  obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
  obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
  have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have RB := proofErase_beta_forward hΓ hf RF
  rw [show proofErase Γ (.lam X b) = .lam _ _ from if_neg hn'] at RB
  exact ⟨_, (ScopedCompute.beta RB).trans (.lam (RA.scoped (fun H => .base H)) .refl)⟩


/-- A retained projection of a certified path follows a typed field child.
The exposed-lambda alternative contradicts the actual rigid major typing. -/
theorem TypeInputRecovery.projection_image (H : TypeInputRecovery D Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T)
    (hn : ¬ IsProof Γ (.proj s i e)) : TypeInputImage Γ (.proj s i e) := by
  obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
  rcases H.expose hΓ hm.hasType.2 with HI | ⟨A, b, _, _, _, _, R, _⟩
  · exact HI.projection_image hΓ ht hn
  · have HE := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hm.hasType.2
    obtain ⟨⟨_, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
    have HC := (HasType.lam hA hb).uniqU henv hΓ HE.hasType.2
    obtain ⟨_, hPi⟩ := (HasType.lam hA hb).isType henv hΓ
    exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HC.typeChain henv hΓ hPi)).elim

/-- A selected application consumes the transported argument guard. Callable
leaves promote it using actual type arguments; exposed lambdas retain the exact
selected domain. This proof does not use SelectedLambdaDomain. -/
theorem TypeInputRecovery.application (hs : D.Sound env univs)
    (H : TypeInputRecovery D Γ f (.forallE A B) n)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (EC : proofErase Γ C = A)
    (HF : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false (proofErase Γ f) g)
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      A (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (.app (proofErase Γ f) (proofErase Γ x)) (.app g (proofErase Γ y)) := by
  rcases H.selected_domain hΓ hf hn with HI | ⟨body, R⟩
  · exact HI.application_checked
      (ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs))
      hΓ hf hx hy EC HF HX
  · exact .appComputed R HF HX

end Lean4Lean.VEnv.Strengthening
