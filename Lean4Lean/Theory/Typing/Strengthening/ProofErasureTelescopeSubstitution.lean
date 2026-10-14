import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixArguments
import Lean4Lean.Theory.Typing.PrefixUnfolding.Simultaneous

/-! # Typed substitution through erased residual telescopes

The original well-formed telescope supplies the interpretation of all freshly
bound variables. Erased agreement extends beneath the entire telescope, including
proof-valued binders. This proves exact transport of the semantic fresh-variable
selector wherever that telescope has a typed realization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature

namespace ProofShape
/-- Entering one binder before a telescope equals entering its successor length. -/
theorem Subst.lift_liftN (σ : Subst) : ∀ n, σ.lift.liftN n = σ.liftN (n + 1)
  | 0 => rfl
  | n + 1 => by simp only [Subst.liftN, Subst.lift_liftN σ n]

/-- A term lifted past a telescope substitutes only its original variables. -/
theorem liftN_subst_liftN (e : ProofShape) (σ : Subst) (n : Nat) :
    (e.liftN n).subst (σ.liftN n) = (e.subst σ).liftN n := by
  induction n with
  | zero => simp only [Subst.liftN, liftN_zero]
  | succ n ih =>
    rw [← liftN_add (n := n) (m := 1), Subst.liftN, lift_subst_lift, ih, liftN_add]

/-- Substitute each erased lambda annotation at its own binder depth. -/
theorem wrapLams_subst (domains : List ProofShape) (body : ProofShape) (σ : Subst) :
    (wrapLams domains body).subst σ =
      wrapLams (domains.mapIdx fun i A => A.subst (σ.liftN i))
        (body.subst (σ.liftN domains.length)) := by
  induction domains generalizing σ with
  | nil => rfl
  | cons A ds ih =>
    simpa only [wrapLams, List.foldr_cons, subst, List.mapIdx_cons, Subst.lift_liftN,
      List.length_cons, Subst.liftN] using congrArg (ProofShape.lam (A.subst σ)) (ih σ.lift)
end ProofShape

variable [Params] {domains : List VExpr}

/-- A typed simultaneous substitution extends beneath an entire well-formed
telescope, and retained-variable erasure agreement extends with it. -/
theorem erasedSubst_telescope (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    let ds := domains.mapIdx fun i A => A.subst (σ.liftN i)
    OnCtx (ds.reverse ++ Γ₀) (env.IsType univs) ∧
      Ctx.SubstEq env univs (ds.reverse ++ Γ₀) (σ.liftN domains.length)
        (σ.liftN domains.length) (domains.reverse ++ Γ) ∧
      ErasedSubstAgreement (domains.reverse ++ Γ) (ds.reverse ++ Γ₀)
        (σ.liftN domains.length) (τ.liftN domains.length) := by
  induction domains generalizing Γ Γ₀ σ τ with
  | nil => exact ⟨hΓ₀, W, E⟩
  | cons A ds ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx
    obtain ⟨_, u, hA⟩ := OnCtx.of_append hctx
    have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    simpa only [List.mapIdx_cons, VExpr.Subst.liftN, VExpr.Subst.lift_liftN,
      ProofShape.Subst.lift_liftN, List.length_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append] using
      ih hΓA₀ (W.lift henv.ordered hA) (E.lift hΓ₀ W hA) hctx

/-- Every substituted residual annotation erases by the corresponding lifted
raw substitution, including annotations depending on earlier proof binders. -/
theorem proofEraseDomains_subst (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    proofEraseDomains Γ₀ (domains.mapIdx fun i A => A.subst (σ.liftN i)) =
      (proofEraseDomains Γ domains).mapIdx fun i A => A.subst (τ.liftN i) := by
  induction domains generalizing Γ Γ₀ σ τ with
  | nil => rfl
  | cons A ds ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx
    obtain ⟨_, u, hA⟩ := OnCtx.of_append hctx
    have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    simp only [List.mapIdx_cons, VExpr.Subst.liftN, ProofShape.Subst.liftN,
      proofEraseDomains, proofErase_subst_with hΓ₀ W hA E]
    congr 1
    simpa only [VExpr.Subst.lift_liftN, ProofShape.Subst.lift_liftN,
      VExpr.Subst.liftN, ProofShape.Subst.liftN] using
      ih hΓA₀ (W.lift henv.ordered hA) (E.lift hΓ₀ W hA) hctx

/-- The fresh-variable vector substitutes exactly whenever the residual
telescope is well formed. Proof markers remain markers at the target. -/
theorem proofErase_contextVars_subst (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    let ds := domains.mapIdx fun i A => A.subst (σ.liftN i)
    ProofShape.contextVars (proofEraseCtx (ds.reverse ++ Γ₀)) domains.length 0 =
      (ProofShape.contextVars (proofEraseCtx (domains.reverse ++ Γ)) domains.length 0).map
        (·.subst (τ.liftN domains.length)) := by
  dsimp only
  obtain ⟨hctx₀, Wext, Eext⟩ := erasedSubst_telescope hΓ₀ W E hctx
  rw [← proofErase_contextVars hctx₀, ← proofErase_contextVars hctx, List.map_map]
  apply List.map_congr_left
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  have hlookup := Lookup.ofLt (Γ := domains.reverse ++ Γ)
    (i := 0 + i) (by simp only [List.length_append, List.length_reverse]; omega)
  have hh := proofErase_subst_with hctx₀ Wext (HasType.bvar hlookup.2) Eext
  simpa only [VExpr.subst_bvar, VExpr.Subst.liftN_apply, Nat.zero_add,
    if_pos hi, Function.comp_def] using hh

/-- Raw opening commutes with substitution under a typed residual telescope.
Only this telescope realization is needed; the raw providers may be arbitrary. -/
theorem proofErase_openPrefixArguments_subst (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) (args : List ProofShape) :
    ProofShape.openPrefixArguments (proofEraseCtx Γ₀)
      (proofEraseDomains Γ₀ (domains.mapIdx fun i A => A.subst (σ.liftN i)))
      (args.map (·.subst τ)) =
      (ProofShape.openPrefixArguments (proofEraseCtx Γ) (proofEraseDomains Γ domains) args).map
        (·.subst (τ.liftN domains.length)) := by
  simp only [ProofShape.openPrefixArguments, proofEraseDomains_length, List.length_mapIdx,
    ← proofEraseDomains_context, List.map_append, List.map_map, Function.comp_def,
    ProofShape.liftN_subst_liftN, proofErase_contextVars_subst hΓ₀ W E hctx]

end Lean4Lean.VEnv.Strengthening
