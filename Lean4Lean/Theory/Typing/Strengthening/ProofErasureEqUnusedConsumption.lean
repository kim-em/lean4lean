import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedContext

/-! # Consume an unused ambient binder beneath retained annotations

The actual endpoint context identifies the consumed binder. When completion
comes from below that unused insertion, descend the annotation certificates
and cancel the insertion without assigning the argument in the target.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- Supplying an unused binder at any depth cancels its insertion, independently
of the argument. Newer bound variables retain their original indices. -/
theorem ProofShape.consume_unused_lift (e x : ProofShape) (depth : Nat) :
    (e.liftN 1 depth).subst ((ProofShape.Subst.one x).liftN depth) = e := by
  have H : ∀ i, (ProofShape.Subst.one x).liftN depth (liftVar 1 i depth) = ProofShape.Subst.id i := by
    induction depth with
    | zero => intro i; simp [ProofShape.Subst.liftN, liftVar, ProofShape.Subst.one,
        ProofShape.Subst.cons, ProofShape.Subst.id, Nat.add_comm]
    | succ depth ih =>
      intro i
      cases i with
      | zero => simp [ProofShape.Subst.liftN, liftVar, ProofShape.Subst.lift, ProofShape.Subst.id]
      | succ i =>
        have E : liftVar 1 (i+1) (depth+1) = liftVar 1 i depth + 1 := by
          simp only [liftVar, Nat.succ_lt_succ_iff]
          split <;> omega
        rw [E]
        simp only [ProofShape.Subst.liftN, ProofShape.Subst.lift, ih]
        simp [ProofShape.Subst.id, ProofShape.liftN, liftVar, Nat.add_comm]
  exact (ProofShape.subst_liftN_agree e H).trans (ProofShape.subst_id e)

variable [Params]

/-- Classify the actual endpoint map while retaining descent through its
consumed binder when that binder is an unused insertion. The lower context
changes only by the recorded annotation history; no target image or actual
argument representative is needed for this cancellation. -/
theorem PiInertEndpointContext.unused_ancestry
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertEndpointContext D Ξ Ξ' σ) :
    (σ = ProofShape.Subst.id ∧ PiInertContextHistory D Ξ Ξ') ∨
      ∃ x depth, σ = (ProofShape.Subst.one x).liftN depth ∧
        ∀ {Γ Γ'}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
          Ctx.LiftN 1 depth Γ Γ' → proofEraseCtx Γ' = Ξ →
          PiInertContextHistory D (proofEraseCtx Γ) Ξ' := by
  induction H with
  | base H =>
    cases H with
    | identity => exact .inl ⟨rfl, .refl⟩
    | @inst rawA Ξ rawX W =>
      refine .inr ⟨rawX, 0, rfl, ?_⟩
      intro Γ Γ' hΓ hΓ' WI E
      cases WI with
      | zero As hlen =>
        cases As with
        | nil => simp at hlen
        | cons A As =>
          have EL : As.length = 0 := by simpa only [List.length_cons] using Nat.succ.inj hlen
          have EAs := List.length_eq_zero_iff.mp EL
          subst As
          have EΓ := (List.cons.inj E).2
          change proofEraseCtx Γ = _ at EΓ
          simpa only [EΓ] using (PiInertContextHistory.refl (D := D) (Ξ := proofEraseCtx Γ))
  | @binder n Ξ rawA rawA' Ξ' σ RD H ih =>
    rcases ih with ⟨rfl, Hctx⟩ | ⟨x, depth, rfl, HC⟩
    · exact .inl ⟨ProofShape.Subst.id_lift,
        by simpa only [ProofShape.subst_id] using PiInertContextHistory.step (.head RD) Hctx.tail⟩
    · refine .inr ⟨x, depth+1, rfl, ?_⟩
      intro Γ Γ' hΓ hΓ' WI E
      cases WI with
      | @succ _ Γ₀ Γ₀' A WI =>
        obtain ⟨hΓ₀, u, hA⟩ := hΓ
        obtain ⟨hΓ₀', _, _⟩ := hΓ'
        obtain ⟨EA, EΓ⟩ := List.cons.inj E
        have EA₀ := (proofErase_liftN hΓ₀ hΓ₀' WI hA).symm.trans EA
        obtain ⟨A', HA, RA, EA'⟩ := proofErase_scoped_compute_certificate_descend
          (pi_inert_stage_certificate_descent heq hs n) hΓ₀ hΓ₀' WI hA EΓ (EA₀.symm ▸ RD)
        have HE : rawA'.subst ((ProofShape.Subst.one x).liftN depth) = proofErase Γ₀ A' := by
          rw [← EA']
          exact ProofShape.consume_unused_lift _ _ _
        simpa only [proofEraseCtx, ProofShape.Subst.liftN, HE] using
          PiInertContextHistory.step (.head RA) (HC hΓ₀ hΓ₀' WI EΓ).tail

/-- Replay an annotation history on the fully completed prefix, retaining all
unused ambient insertion witnesses. -/
theorem IteratedAmbientEqCompletion.context_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Δ v w original Ξ source)
    (H : PiInertContextHistory D Ξ Ξ') :
    IteratedAmbientEqCompletion Δ v w original Ξ' source := by
  induction H with
  | refl => exact HP
  | step R _ ih => exact ih (HP.compute_context (pi_inert_stage_certificate_descent heq hs _) hΔ R)

/-- The bounded target prefix comes from below one unused binder at the
specified depth. Extra actual source arguments may use that binder freely;
only the target-relevant prefix must have the lower completion witness. -/
def UnusedTargetPrefixCompletion (Δ : List VExpr) (v w : VLevel) (original : List VExpr)
    (Ξ : List ProofShape) (source : ProofShape) (depth : Nat) : Prop :=
  ∃ ls args, source = ProofShape.mkApps (.const ``Eq.rec ls) args ∧
    ∃ Γ Γ' f F, OnCtx Γ (env.IsType univs) ∧ OnCtx Γ' (env.IsType univs) ∧
      Ctx.LiftN 1 depth Γ Γ' ∧ proofEraseCtx Γ' = Ξ ∧ env.HasType univs Γ f F ∧
      IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ) (proofErase Γ f) ∧
      (proofErase Γ f).liftN 1 depth = ProofShape.mkApps (.const ``Eq.rec ls) (args.take original.length)

/-- Restoring the unused insertion recovers the existing bounded completion. -/
theorem UnusedTargetPrefixCompletion.forget
    (H : UnusedTargetPrefixCompletion Δ v w original Ξ source depth) :
    EqTargetPrefixCompletion Δ v w original Ξ source := by
  obtain ⟨ls, args, E, Γ, Γ', f, F, hΓ, hΓ', W, EΓ, hf, HP, EP⟩ := H
  exact ⟨ls, args, E, by simpa only [EΓ, EP] using
    IteratedAmbientEqCompletion.insert hΓ hΓ' W hf HP⟩

/-- Consume the unused binder using its derived lower context history. The
supplied argument is arbitrary; cancellation of the literal lifted prefix
replaces any target-image compatibility requirement for this case. -/
theorem UnusedTargetPrefixCompletion.consume
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : UnusedTargetPrefixCompletion Δ v w original Ξ source depth)
    (HC : ∀ {Γ Γ'}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
      Ctx.LiftN 1 depth Γ Γ' → proofEraseCtx Γ' = Ξ →
      PiInertContextHistory D (proofEraseCtx Γ) Ξ') (x : ProofShape) :
    EqTargetPrefixCompletion Δ v w original Ξ'
      (source.subst ((ProofShape.Subst.one x).liftN depth)) := by
  obtain ⟨ls, args, rfl, Γ, Γ', f, F, hΓ, hΓ', W, EΓ, hf, HP, EP⟩ := H
  have HP' := HP.context_history heq hs hΔ (HC hΓ hΓ' W EΓ)
  refine ⟨ls, args.map (·.subst ((ProofShape.Subst.one x).liftN depth)),
    by simp only [ProofShape.subst_mkApps, ProofShape.subst], ?_⟩
  have EE := congrArg (fun e => e.subst ((ProofShape.Subst.one x).liftN depth)) EP
  simp only [ProofShape.consume_unused_lift, ProofShape.subst_mkApps, ProofShape.subst,
    List.map_take] at EE
  exact EE ▸ HP'

end Lean4Lean.VEnv.Strengthening
