import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortImageRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Sort-rooted paths retaining their selected type

The finite path carries its recovered output and every ordinary-core type
conversion. This permits head exposure to retain computation from the
exposed lambda's Pi type to the original selected output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A path ending in an actual type, with its selected raw type retained.
The computation relation is the context-independent stage-zero core. -/
inductive SortRootedRecovery (D : PureObservation.Definitions) :
    List VExpr → VExpr → ProofShape → Nat → Prop where
  | type : env.HasType univs Γ e (.sort u) → SortRootedRecovery D Γ e (.sort u) 0
  | lam : SortRootedRecovery D (A :: Γ) b B n →
      SortRootedRecovery D Γ (.lam A b) (.forallE (proofErase Γ A) B) (n + 1)
  | app : SortRootedRecovery D Γ f (.forallE A B) n →
      SortRootedRecovery D Γ (.app f a) (B.inst (proofErase Γ a)) (n + 1)
  | convert : SortRootedRecovery D Γ e T n → Compute (ErasedIotaPrimitive D) T U →
      SortRootedRecovery D Γ e U (n + 1)

/-- Forgetting the selected type yields the previous finite path fragment. -/
theorem SortRootedRecovery.rooted (H : SortRootedRecovery D Γ e out n) :
    ∃ m, SortRooted Γ e m := by
  induction H with
  | type h => exact ⟨0, .type h⟩
  | lam _ ih => obtain ⟨m, H⟩ := ih; exact ⟨m + 1, .lam H⟩
  | app _ ih => obtain ⟨m, H⟩ := ih; exact ⟨m + 1, .app H⟩
  | convert _ _ ih => exact ih

/-- Typed substitution preserves both the rank and the exact selected output.
No recovery of any substitution image is required for this fragment. -/
theorem SortRootedRecovery.subst (H : SortRootedRecovery D Γ e out n)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T) :
    SortRootedRecovery D Γ₀ (e.subst σ) (out.subst τ) n := by
  induction H generalizing Γ₀ σ τ T with
  | type h => exact .type (h.subst henv.orderedStrong W hΓ₀)
  | @lam A Γ b B n H ih =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have ES' : ErasedSubstAgreement (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift :=
      ES.lift hΓ₀ W hA
    simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES] using
      SortRootedRecovery.lam (ih ⟨hΓ₀, u, hA'⟩ (W.lift henv.ordered hA) ES' hb)
  | @app Γ f A B n a H ih =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES] using
      SortRootedRecovery.app (a := a.subst σ) (ih hΓ₀ W ES hf)
  | convert H R ih =>
    exact .convert (ih hΓ₀ W ES ht) (R.subst (fun H => erased_iota_primitive_subst H))

private theorem core_forall_parts
    (R : Compute (ErasedIotaPrimitive D) (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ Compute (ErasedIotaPrimitive D) A A' ∧
      Compute (ErasedIotaPrimitive D) B B' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (E ▸ erased_iota_primitive_head H).elim
  | beta H =>
    obtain ⟨A', B', HE, HA, HB⟩ := beta_forallE_parts (E ▸ H)
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, HA, HB⟩ := ih₁ E
    obtain ⟨A₂, B₂, HE, HA', HB'⟩ := ih₂ rfl
    exact ⟨_, _, HE, HA.trans HA', HB.trans HB'⟩
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA, HB⟩
  | app | proj | lam => cases E

/-- Head exposure retains computation from the exposed Pi to the selected
output. Application consumes a smaller body path and one conversion node;
the rank remains strictly below the original application path. -/
theorem SortRootedRecovery.expose (H : SortRootedRecovery D Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    env.IsType univs Γ e ∨
      ∃ A b B m, m < n ∧ SortRootedRecovery D (A :: Γ) b B m ∧
        VExpr.BetaRed e (.lam A b) ∧
        Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ A) B) out := by
  induction n using Nat.strongRecOn generalizing Γ e out T with
  | ind n ih =>
    cases H with
    | type h => exact .inl ⟨_, h⟩
    | lam H => exact .inr ⟨_, _, _, _, by omega, H, .refl, .refl⟩
    | @convert Γ e source k out H R =>
      rcases ih k (by omega) H hΓ ht with HS | ⟨A, b, B, m, hm, HB, RB, RT⟩
      · exact .inl HS
      · exact .inr ⟨A, b, B, m, by omega, HB, RB, RT.trans R⟩
    | @app Γ f X Y k a H =>
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
      rcases ih k (by omega) H hΓ hf with ⟨_, hs⟩ | ⟨A, b, B, m, hm, HB, RF, RT⟩
      · exact ((hs.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
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
      have Hinst : SortRootedRecovery D Γ (b.inst a) (B.inst (proofErase Γ a)) m := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
          ProofShape.Subst.liftN] using HB.subst hΓ WS ES hb
      have RBinst : Compute (ErasedIotaPrimitive D) (B.inst (proofErase Γ a))
          (Y.inst (proofErase Γ a)) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB.subst
          (σ := ProofShape.Subst.one (proofErase Γ a)) (fun H => erased_iota_primitive_subst H)
      have R : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have HE' := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
      rcases ih (m + 1) (by omega) (Hinst.convert RBinst) hΓ HE'.hasType.2 with
        ⟨v, hv⟩ | ⟨C, body, B', j, hj, Hbody, RB', RT'⟩
      · exact .inl ⟨v, (HE'.toU.of_r henv hΓ hv).hasType.1⟩
      · exact .inr ⟨C, body, B', j, by omega, Hbody, R.trans RB', RT'⟩

/-- At a retained function with a selected Pi output, finite computation
exposes a lambda with exactly that selected raw domain. The final annotation
change uses the retained Pi-domain computation, not semantic carrier conversion. -/
theorem SortRootedRecovery.selected_domain
    (H : SortRootedRecovery D Γ f (.forallE A B) n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE C E))
    (hn : ¬ IsProof Γ f) :
    ∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.lam A body) := by
  rcases H.expose hΓ hf with ⟨_, hs⟩ | ⟨X, b, Y, _, _, _, RF, RT⟩
  · exact ((hs.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
  obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
  have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have RB := proofErase_beta_forward hΓ hf RF
  rw [show proofErase Γ (.lam X b) = .lam _ _ from if_neg hn'] at RB
  exact ⟨_, (ScopedCompute.beta RB).trans (.lam (RA.scoped (fun H => .base H)) .refl)⟩

end Lean4Lean.VEnv.Strengthening
