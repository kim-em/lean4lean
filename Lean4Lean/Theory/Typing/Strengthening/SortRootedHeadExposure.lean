import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedLambdaApplication

/-! # Finite head exposure above sort-typed leaves

This fragment follows only function positions, lambda bodies and projection
receivers until reaching a sort-typed term. The leaf and all arguments may be
non-normalizing. Typed members nevertheless either have a sort type themselves
or beta-reduce to a lambda. The rank counts the tracked path, not term size;
ordinary typed substitution preserves it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A finite elimination/body path ending in an arbitrary type. No reduction
or recovery certificate is required of the leaf, annotations or arguments.
The natural number counts only constructors on this path. -/
inductive SortRooted : List VExpr → VExpr → Nat → Prop where
  | type : env.HasType univs Γ e (.sort u) → SortRooted Γ e 0
  | lam : SortRooted (A :: Γ) b n → SortRooted Γ (.lam A b) (n + 1)
  | app : SortRooted Γ f n → SortRooted Γ (.app f a) (n + 1)
  | proj : SortRooted Γ m n → SortRooted Γ (.proj s i m) (n + 1)

/-- Typed substitution preserves the tracked path rank, even if the images
have no recovery certificates and their sizes are unbounded. -/
theorem SortRooted.subst (H : SortRooted Γ e n)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ht : env.HasType univs Γ e T) : SortRooted Γ₀ (e.subst σ) n := by
  induction H generalizing Γ₀ σ T with
  | type h => exact .type (h.subst henv.orderedStrong W hΓ₀)
  | lam H ih =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    exact .lam (ih ⟨hΓ₀, u, hA'⟩ (W.lift henv.ordered hA) hb)
  | app H ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv W.wf
    exact .app (ih hΓ₀ W hf)
  | proj H ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    exact .proj (ih hΓ₀ W hm.hasType.2)

/-- A typed member of the fragment is a type or exposes a lambda by finite
beta computation. The exposed body has strictly smaller path rank. This is
not normalization of its type leaf, arguments, annotations or lambda body. -/
theorem SortRooted.expose (H : SortRooted Γ e n)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    (∃ u, env.HasType univs Γ e (.sort u)) ∨
      ∃ A b m, m < n ∧ SortRooted (A :: Γ) b m ∧ VExpr.BetaRed e (.lam A b) := by
  induction n using Nat.strongRecOn generalizing Γ e T with
  | ind n ih =>
    cases H with
    | type h => exact .inl ⟨_, h⟩
    | lam H => exact .inr ⟨_, _, _, by omega, H, .refl⟩
    | @app Γ f k a H =>
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
      rcases ih k (by omega) H hΓ hf with ⟨_, hsort⟩ | ⟨A, b, m, hm, HB, RF⟩
      · exact ((hsort.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
      have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
      obtain ⟨⟨u, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
      have hfPi := (HE.toU.of_r henv hΓ (HasType.lam hA hb)).hasType.1
      have hxA := argument_at_displayed_domain hΓ hf hfPi hx
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have WS := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA hxA
      have Hinst : SortRooted Γ (b.inst a) m := by
        simpa only [VExpr.instN_eq] using HB.subst hΓ WS hb
      have R : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have HE' := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
      rcases ih m (by omega) Hinst hΓ HE'.hasType.2 with
        ⟨v, hv⟩ | ⟨C, body, j, hj, Hbody, RB⟩
      · exact .inl ⟨v, (HE'.toU.of_r henv hΓ hv).hasType.1⟩
      · exact .inr ⟨C, body, j, by omega, Hbody, R.trans RB⟩
    | @proj Γ m k s i H =>
      obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      have hmajor := hm.hasType.2
      rcases ih k (by omega) H hΓ hmajor with ⟨u, hu⟩ | ⟨A, b, _, _, _, R⟩
      · have HE := hu.uniqU henv hΓ hmajor
        exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
          (HE.typeChain henv hΓ (HasType.sort (hu.isType henv hΓ |>.choose_spec.sort_inv henv)))).elim
      · have HE := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hmajor
        obtain ⟨⟨_, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
        have HC := (HasType.lam hA hb).uniqU henv hΓ HE.hasType.2
        obtain ⟨_, hPi⟩ := (HasType.lam hA hb).isType henv hΓ
        exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
          (HC.typeChain henv hΓ hPi)).elim

/-- At a function type the sort alternative is impossible, so this fragment
always supplies a lambda by beta alone, without native type recovery. -/
theorem SortRooted.function_expose (H : SortRooted Γ f n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B)) :
    ∃ C b m, m < n ∧ SortRooted (C :: Γ) b m ∧ VExpr.BetaRed f (.lam C b) := by
  rcases H.expose hΓ hf with ⟨_, hs⟩ | H
  · exact ((hs.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim
  · exact H

/-- A retained function in the fragment supplies the literal erased lambda
needed by computed-domain application checking, in any primitive relation.
Beta alone constructs the computation certificate. -/
theorem SortRooted.erased_function_expose (H : SortRooted Γ f n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (hn : ¬ IsProof Γ f) :
    ∃ C b, ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) := by
  obtain ⟨C, b, _, _, _, R⟩ := H.function_expose hΓ hf
  have HE := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have RB := proofErase_beta_forward hΓ hf R
  rw [show proofErase Γ (.lam C b) = .lam _ _ from if_neg hn'] at RB
  exact ⟨C, b, .beta RB⟩

end Lean4Lean.VEnv.Strengthening
