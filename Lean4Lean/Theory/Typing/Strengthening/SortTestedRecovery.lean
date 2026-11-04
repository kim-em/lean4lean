import Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortSpecialization

/-! # Selected recovery paths with a shared typed interpretation

The interpretation is part of every path index and lifts under lambda binders.
Leaves become types in that one interpretation. Transport uses an actual typed
commuting substitution square; arbitrary existential specialization witnesses
are never assumed substitution closed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private core_forall_parts
  from Lean4Lean.Theory.Typing.Strengthening.SortRootedRecovery
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A finite recovery path with its original selected raw output, indexed by
a single test context and substitution. Lambda children use the lifted test. -/
inductive SortTestedRecovery (D : PureObservation.Definitions) :
    List VExpr → List VExpr → VExpr.Subst → VExpr → ProofShape → Nat → Prop where
  | atom : env.HasType univs Γt (e.subst σ) (.sort u) →
      SortTestedRecovery D Γ Γt σ e out 0
  | lam : SortTestedRecovery D (A :: Γ) (A.subst σ :: Γt) σ.lift b B n →
      SortTestedRecovery D Γ Γt σ (.lam A b) (.forallE (proofErase Γ A) B) (n + 1)
  | app : SortTestedRecovery D Γ Γt σ f (.forallE A B) n →
      SortTestedRecovery D Γ Γt σ (.app f a) (B.inst (proofErase Γ a)) (n + 1)
  | convert : SortTestedRecovery D Γ Γt σ e T n → Compute (ErasedIotaPrimitive D) T U →
      SortTestedRecovery D Γ Γt σ e U (n + 1)

/-- A typed commuting square transports the whole path, retaining its rank and
exact substituted selected output. The post-map on test contexts transports the
leaf typing; it is not a hypothesized checking or recovery theorem. -/
theorem SortTestedRecovery.subst_square (H : SortTestedRecovery D Γ Γt σ e out n)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt σ σ Γ)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.SubstEq env univs Γ' ρ ρ Γ)
    (hΓt' : OnCtx Γt' (env.IsType univs)) (WP : Ctx.SubstEq env univs Γt' δ δ Γt)
    (ES : ErasedSubstAgreement Γ Γ' ρ τ)
    (square : σ.comp δ = ρ.comp σ') (ht : env.HasType univs Γ e T) :
    SortTestedRecovery D Γ' Γt' σ' (e.subst ρ) (out.subst τ) n := by
  induction H generalizing Γ' Γt' ρ τ δ σ' T with
  | atom h =>
    apply SortTestedRecovery.atom
    have h' := h.subst henv.orderedStrong WP hΓt'
    simpa only [VExpr.subst_subst, square, VExpr.subst] using h'
  | @lam A Γ σ Γt b B n H ih =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hAT := hA.subst henv.orderedStrong WT hΓt
    have hA' := hA.subst henv.orderedStrong W hΓ'
    have EA : (A.subst σ).subst δ = (A.subst ρ).subst σ' := by
      simp only [VExpr.subst_subst, square]
    have ES' : ErasedSubstAgreement (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift := ES.lift hΓ' W hA
    have square' : σ.lift.comp δ.lift = ρ.lift.comp σ'.lift := by
      rw [← VExpr.Subst.comp_lift, ← VExpr.Subst.comp_lift, square]
    have HH := ih (Γ' := A.subst ρ :: Γ') (Γt' := (A.subst σ).subst δ :: Γt')
      (σ' := σ'.lift) ⟨hΓt, u, hAT⟩ (WT.lift henv.ordered hA)
      ⟨hΓ', u, hA'⟩ (W.lift henv.ordered hA)
      ⟨hΓt', u, hAT.subst henv.orderedStrong WP hΓt'⟩
      (WP.lift henv.ordered hAT) ES' square' hb
    rw [EA] at HH
    simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ' W hA ES] using
      SortTestedRecovery.lam HH
  | @app Γ Γt σ f A B n a H ih =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ' W ha ES] using
      SortTestedRecovery.app (a := a.subst ρ) (ih hΓt WT hΓ' W hΓt' WP ES square hf)
  | convert H R ih =>
    exact .convert (ih hΓt WT hΓ' W hΓt' WP ES square ht)
      (R.subst (fun H => erased_iota_primitive_subst H))

/-- Contracting a local binder keeps the enclosing test interpretation. The
post-map substitutes the tested argument in the lifted test context, so the
commuting square is proved rather than imposed on the caller. -/
theorem SortTestedRecovery.inst (H : SortTestedRecovery D (A :: Γ)
    (A.subst σ :: Γt) σ.lift b out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓt : OnCtx Γt (env.IsType univs))
    (WT : Ctx.SubstEq env univs Γt σ σ Γ)
    (hA : env.HasType univs Γ A (.sort u))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs (A :: Γ) b B) :
    SortTestedRecovery D Γ Γt σ (b.inst a) (out.inst (proofErase Γ a)) n := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hAT := hA.subst henv.orderedStrong WT hΓt
  have hΓAT : OnCtx (A.subst σ :: Γt) (env.IsType univs) := ⟨hΓt, u, hAT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA ha
  have WP := (Ctx.InstN.zero (Γ₀ := Γt) (e₀ := a.subst σ) (A₀ := A.subst σ)).substEq
    hΓAT (ha.subst henv.orderedStrong WT hΓt)
  have square : σ.lift.comp (VExpr.Subst.one (a.subst σ)) = (VExpr.Subst.one a).comp σ := by
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      change (σ i).lift.subst (VExpr.Subst.one (a.subst σ)) = σ i
      rw [VExpr.Subst.one, VExpr.lift_subst_cons, VExpr.subst_id]
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using H.subst_square hΓAT (WT.lift henv.ordered hA)
      hΓ W hΓt WP (erasedSubstAgreement_one hΓA ha) square hb

/-- Head exposure retains computation from the exposed Pi to the selected
output. Application consumes a smaller body path and one conversion node;
the rank remains strictly below the original application path. -/
theorem SortTestedRecovery.expose (H : SortTestedRecovery D Γ Γt σ e out n)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt σ σ Γ)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    SortSpecialization Γ e ∨
      ∃ A b B m, m < n ∧ SortTestedRecovery D (A :: Γ) (A.subst σ :: Γt) σ.lift b B m ∧
        VExpr.BetaRed e (.lam A b) ∧
        Compute (ErasedIotaPrimitive D) (.forallE (proofErase Γ A) B) out := by
  induction n using Nat.strongRecOn generalizing Γ Γt σ e out T with
  | ind n ih =>
    cases H with
    | atom h => exact .inl ⟨Γt, σ, _, hΓt, WT, h⟩
    | lam H => exact .inr ⟨_, _, _, _, by omega, H, .refl, .refl⟩
    | @convert Γ Γt σ e source k out H R =>
      rcases ih k (by omega) H hΓt WT hΓ ht with HS | ⟨A, b, B, m, hm, HB, RB, RT⟩
      · exact .inl HS
      · exact .inr ⟨A, b, B, m, by omega, HB, RB, RT.trans R⟩
    | @app Γ Γt σ f X Y k a H =>
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
      rcases ih k (by omega) H hΓt WT hΓ hf with hs | ⟨A, b, B, m, hm, HB, RF, RT⟩
      · exact (hs.not_function hf).elim
      obtain ⟨_, _, EE, _, RB⟩ := core_forall_parts RT
      obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
      have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
      obtain ⟨⟨u, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
      have hfPi := (HE.toU.of_r henv hΓ (HasType.lam hA hb)).hasType.1
      have hxA := argument_at_displayed_domain hΓ hf hfPi hx
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have Hinst := HB.inst hΓ hΓt WT hA hxA hb
      have RBinst : Compute (ErasedIotaPrimitive D) (B.inst (proofErase Γ a))
          (Y.inst (proofErase Γ a)) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB.subst
          (σ := ProofShape.Subst.one (proofErase Γ a)) (fun H => erased_iota_primitive_subst H)
      have R : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have HE' := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
      rcases ih (m + 1) (by omega) (Hinst.convert RBinst) hΓt WT hΓ HE'.hasType.2 with
        HS | ⟨C, body, B', j, hj, Hbody, RB', RT'⟩
      · exact .inl (HS.back HE')
      · exact .inr ⟨C, body, B', j, by omega, Hbody, R.trans RB', RT'⟩

/-- At a retained function with a selected Pi output, finite computation
exposes a lambda with exactly that selected raw domain. The final annotation
change uses the retained Pi-domain computation, not semantic carrier conversion. -/
theorem SortTestedRecovery.selected_domain
    (H : SortTestedRecovery D Γ Γt σ f (.forallE A B) n)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt σ σ Γ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE C E))
    (hn : ¬ IsProof Γ f) :
    ∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.lam A body) := by
  rcases H.expose hΓt WT hΓ hf with hs | ⟨X, b, Y, _, _, _, RF, RT⟩
  · exact (hs.not_function hf).elim
  obtain ⟨_, _, EE, RA, _⟩ := core_forall_parts RT
  obtain ⟨rfl, rfl⟩ := ProofShape.forallE.inj EE
  have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have RB := proofErase_beta_forward hΓ hf RF
  rw [show proofErase Γ (.lam X b) = .lam _ _ from if_neg hn'] at RB
  exact ⟨_, (ScopedCompute.beta RB).trans (.lam (RA.scoped (fun H => .base H)) .refl)⟩

end Lean4Lean.VEnv.Strengthening
