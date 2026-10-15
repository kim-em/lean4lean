import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecovery

/-! # Contextual recovery descends through binder insertion

The upper context is the erasure of the actual upper realization. Recovery
reconstructs a lower typing and lower result erasure, including at converted
types. This does not assert a recovery certificate in the smaller context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv ProofShape.liftN_sort_inv ProofShape.liftN_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private erased_lift_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryDescent
variable [Params]

/-- Source-typed contextual recovery reconstructs its whole result below an
arbitrary block insertion. Contextual conversion uses the actual upper context
at each binder, and every recovered type has an original typed representative. -/
theorem proofErase_scoped_typeRecovery_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ht : env.HasType univs Γ e T) (hΔ : proofEraseCtx Γ' = Δ)
    (R : ProofShape.ScopedTypeRecovery Step Δ ((proofErase Γ e).liftN n k) out) :
    ∃ A, env.HasType univs Γ e A ∧ (proofErase Γ A).liftN n k = out := by
  generalize Ee : (proofErase Γ e).liftN n k = source at R
  induction R generalizing Γ Γ' k e T with
  | bvar =>
    obtain ⟨i, rfl, rfl⟩ := erased_lift_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    have H := ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W hl
    refine ⟨A, .bvar hl, ?_⟩
    rw [← hΔ, proofEraseCtx_oracle]
    exact H.symm
  | sort hu =>
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv Ee)
    refine ⟨_, .sort hu, ?_⟩
    rw [show proofErase Γ (.sort (.succ _)) = .sort (.succ _) from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .succ _) hu))]
    rfl
  | const hc hw hn =>
    obtain rfl := erase_const_inv (ProofShape.liftN_const_inv Ee)
    have hc0 := HasType.const (Γ := []) hc hw hn
    obtain ⟨_, hT⟩ := hc0.isType henv (by trivial)
    refine ⟨_, .const hc hw hn, ?_⟩
    rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ,
      proofErase_closed_liftN ((henv.ordered.closedC hc).instL.mono (Nat.zero_le _))]
  | lam _ ih =>
    obtain ⟨_, _, Es, EA, Eb⟩ := ProofShape.liftN_lam_inv Ee
    obtain ⟨A, b, rfl, _, EAA, Ebb⟩ := erase_lam_inv Es
    rw [← EAA] at EA
    rw [← Ebb] at Eb
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨B, hB, EB⟩ := ih hΓA hΓA' W.succ hb
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, EA]) Eb
    refine ⟨.forallE A B, .lam hA hB, ?_⟩
    obtain ⟨_, hPi⟩ := (HasType.lam hA hB).isType henv hΓ
    simp only [proofErase, if_neg (not_isProof_of_sort hΓ hPi), ProofShape.liftN, EA, EB]
  | app _ ih =>
    obtain ⟨_, _, Es, Ef, Ea⟩ := ProofShape.liftN_app_inv Ee
    obtain ⟨f, a, rfl, _, Eff, Eaa⟩ := erase_app_inv Es
    rw [← Eff] at Ef
    rw [← Eaa] at Ea
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨F, hfF, EF⟩ := ih hΓ hΓ' W hf hΔ Ef
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hCA⟩, _⟩ := (hf.uniqU henv hΓ hfF).forallE_inv henv hΓ
    have haA := hCA.defeq ha
    obtain ⟨⟨u, hA⟩, _, hB⟩ := (hfF.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    refine ⟨B.inst a, .app hfF haA, ?_⟩
    rw [proofErase_instN hΓA haA Ctx.InstN.zero hB]
    simpa only [Nat.add_zero, EB, Ea] using
      (ProofShape.liftN_instN (proofErase (A :: Γ) B) (proofErase Γ a) n k 0)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv Ee
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨S, hAu, ES⟩ := ihA hΓ hΓ' W hA hΔ EA
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv ES)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hAu⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hAu.weakN henv W⟩
    obtain ⟨S, hBv, ES⟩ := ihB hΓA hΓA' W.succ hB
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hAu, hΔ, EA]) EB
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv ES)
    refine ⟨_, .forallE hAu hBv, ?_⟩
    rw [show proofErase Γ (.sort (.imax _ _)) = .sort (.imax _ _) from
      if_neg (not_isProof_of_sort hΓ
        (HasType.sort (l := .imax _ _) ⟨hAu.sort_r henv hΓ, hBv.sort_r henv hΓA⟩))]
    rfl
  | proj hi HT hj hlen R ih =>
    rename_i s info ls doms result j argsRaw
    obtain ⟨_, Es, Em⟩ := ProofShape.liftN_proj_inv Ee
    obtain ⟨m, rfl, hn, Emm⟩ := erase_proj_inv Es
    rw [← Emm] at Em
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨F, hmF, EF⟩ := ih hΓ hΓ' W hm.hasType.2 hΔ Em
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv EF
    obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv Es
    obtain ⟨hj', F, hproj, E⟩ := proofErase_projection_at_recovered_family hΓ hi HT ht hn hmF
    refine ⟨F, hproj, ?_⟩
    have E' : proofErase Γ F = ProofShape.projectionType s info doms j hj
        (args.map (proofErase Γ)) (proofErase Γ m) := by
      simpa only [ProofShape.projectionType, List.map_take] using E
    rw [E', ProofShape.projectionType_liftN HT hj (by
      have hh := congrArg List.length Eargs
      simp only [List.length_map] at hh ⊢
      omega), ← Eargs, Em]
  | convert _ RC ih =>
    obtain ⟨A, heA, EA⟩ := ih hΓ hΓ' W ht hΔ Ee
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    obtain ⟨A', HAA, EA'⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W hA hΔ (EA ▸ RC)
    exact ⟨A', HAA.defeq heA, EA'⟩


/-- At the original context, contextual recovery reconstructs a source typing
whose result has exactly the recovered erasure. -/
theorem proofErase_scoped_typeRecovery_replay (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ A, env.HasType univs Γ e A ∧ proofErase Γ A = out := by
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  simpa only [ProofShape.liftN_zero] using proofErase_scoped_typeRecovery_descend hstep
    hΓ hΓ W ht rfl (by simpa only [ProofShape.liftN_zero] using R)

/-- A recovered Pi supplies lower original domain/codomain representatives and
an actual lower Pi typing, without inverse typing weakening. -/
theorem proofErase_scoped_recovered_pi_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hf : env.HasType univs Γ f T)
    (R : ProofShape.ScopedTypeRecovery Step (proofEraseCtx Γ')
      ((proofErase Γ f).liftN n k) (.forallE A B)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      (proofErase Γ D).liftN n k = A ∧ (proofErase (D :: Γ) C).liftN n (k+1) = B := by
  obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W hf rfl R
  obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
  obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Es
  exact ⟨D, C, hfF, by simpa only [← ED] using EA, by simpa only [← EC] using EB⟩

end Lean4Lean.VEnv.Strengthening
