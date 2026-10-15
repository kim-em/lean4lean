import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredWeakening

/-! # Exact renaming transport for contextual recovery and joint checking

Variable renamings preserve the selected recovered type when their context
oracles agree. Unlike substitution by arbitrary expressions, this invariant
extends under binders without a re-synthesis assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- An interpreted variable renaming that transports every oracle assignment
exactly, including the default entries outside the context. -/
structure ContextRenaming (Δ Δ' : List ProofShape) (τ : Subst) : Prop where
  interpretation : ContextSubstitution Δ Δ' τ
  lookup : ∀ i, ∃ j, τ i = .bvar j ∧ contextOracle Δ' j = (contextOracle Δ i).subst τ

/-- A fresh displayed binder preserves exact variable and oracle transport. -/
theorem ContextRenaming.cons (W : ContextRenaming Δ Δ' τ) :
    ContextRenaming (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  refine ⟨ContextSubstitution.cons W.interpretation, ?_⟩
  intro i
  cases i with
  | zero =>
    refine ⟨0, rfl, ?_⟩
    simp only [contextOracle, TypeOracle.cons, lift_subst_lift]
  | succ i =>
    obtain ⟨j, Ej, ET⟩ := W.lookup i
    refine ⟨j+1, ?_, ?_⟩
    · simp [Subst.lift, Ej, ProofShape.liftN, liftVar, Nat.add_comm]
    · simp only [contextOracle, TypeOracle.cons, lift_subst_lift] at ET ⊢
      exact congrArg (·.liftN 1) ET

omit [Params] in
private theorem subst_bvar_liftN (e : ProofShape) :
    e.subst (fun i => .bvar (liftVar n i k)) = e.liftN n k := by
  have H := liftN_subst e Subst.id (n := n) (k := k)
  rw [subst_id] at H
  exact H.symm

/-- Every actual well-formed binder insertion supplies an exact interpreted
renaming, with no inhabitants needed for the inserted declarations. -/
theorem ContextRenaming.of_liftN
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') :
    ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ') (fun i => .bvar (liftVar n i k)) := by
  refine ⟨ContextSubstitution.of_typed hΓ'
    (substEq_of_thinning hΓ (Ctx.liftN_iff_lift'.1 W)) ?_, ?_⟩
  · intro i A hl hn
    have hx : env.HasType univs Γ (.bvar i) A := .bvar hl
    change proofErase Γ' ((VExpr.bvar i).lift' _) = _
    rw [VExpr.lift'_consN_skipN]
    rw [proofErase_liftN hΓ hΓ' W hx]
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn]
    rfl
  · intro i
    refine ⟨liftVar n i k, rfl, ?_⟩
    rw [proofEraseCtx_oracle, proofEraseCtx_oracle, subst_bvar_liftN]
    exact erasedTypeOracle_renames hΓ hΓ' W i

/-- Contextual finite computation transports under any exact variable-renaming
simulation of its primitives, including below changing binder annotations. -/
theorem ScopedCompute.rename
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (H : ScopedCompute Step Δ a b) (W : ContextRenaming Δ Δ' τ) :
    ScopedCompute Step' Δ' (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | base H => exact .base (hstep H W)
  | beta H => exact .beta H.subst
  | trans _ _ ih1 ih2 => exact (ih1 W).trans (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.cons)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.cons)

/-- Renaming preserves the exact selected recovery output. This requires only
primitive renaming, not completeness, descent, or domain re-synthesis. -/
theorem ScopedTypeRecovery.rename
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (H : ScopedTypeRecovery Step Δ e T) (W : ContextRenaming Δ Δ' τ) :
    ScopedTypeRecovery Step' Δ' (e.subst τ) (T.subst τ) := by
  induction H generalizing Δ' τ with
  | bvar =>
    rename_i Δ i
    obtain ⟨j, Ej, ET⟩ := W.lookup i
    simp only [ProofShape.subst, Ej, ← ET]
    exact .bvar
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih => exact .lam (ih W.cons)
  | app _ ih =>
    rw [subst_inst]
    exact .app (ih W)
  | forallE _ _ ihA ihB => exact .forallE (ihA W) (ihB W.cons)
  | proj hi HT hj hlen HR ih =>
    have HR' := ih W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at HR'
    rw [ProofShape.projectionType_subst HT hj (by omega)]
    exact .proj hi HT hj (by simpa only [List.length_map] using hlen) HR'
  | convert _ RC ih => exact .convert (ih W) (RC.rename hstep W)

/-- Renaming changes only the explicit carrier attached to a checking mode. -/
def JointCheckKind.subst (τ : Subst) : JointCheckKind → JointCheckKind
  | .compare mode => .compare mode
  | .carrier A => .carrier (A.subst τ)

/-- The entire mutually recursive checking grammar transports under exact
context renaming. In the recovered-application case both the selected Pi and
its carrier guard transport together, with no re-synthesis hypothesis. -/
theorem JointCheck.rename
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (H : JointCheck Step Δ kind a b) (W : ContextRenaming Δ Δ' τ) :
    JointCheck Step' Δ' (kind.subst τ) (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | leaf H => exact .leaf H.subst
  | app _ _ ihf ihx => exact .app (ihf W) (ihx W)
  | appCarrier R _ _ ihf ihx => exact .appCarrier (R.rename hstep W) (ihf W) (ihx W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihA ihb => exact .lam (ihA W) (ihb W.cons)
  | forallE _ _ ihA ihB => exact .forallE (ihA W) (ihB W.cons)
  | lamSorted S S' _ _ ihA ihb =>
    exact .lamSorted (ContextSubstitution.sort W.interpretation S) (ContextSubstitution.sort W.interpretation S') (ihA W) (ihb W.cons)
  | forallSorted S S' _ T T' _ ihA ihB =>
    exact .forallSorted (ContextSubstitution.sort W.interpretation S) (ContextSubstitution.sort W.interpretation S') (ihA W)
      (ContextSubstitution.sort (ContextSubstitution.cons W.interpretation) T) (ContextSubstitution.sort (ContextSubstitution.cons W.interpretation) T') (ihB W.cons)
  | lamCommon _ ih => exact .lamCommon (ih W.cons)
  | etaBodyL S _ ih =>
    apply JointCheck.etaBodyL (ContextSubstitution.sort W.interpretation S)
    simpa only [JointCheckKind.subst, ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | etaBodyR S _ ih =>
    apply JointCheck.etaBodyR (ContextSubstitution.sort W.interpretation S)
    simpa only [JointCheckKind.subst, ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | @structFields Δ family info ls ps fields m hi hx hp hf hadm H ih =>
    simp only [JointCheckKind.subst, ProofShape.subst_mkApps, List.map_append, ProofShape.subst]
    apply JointCheck.structFields hi hx (by simpa only [List.length_map] using hp)
      (by simpa only [List.length_map] using hf) hadm
    intro i hj hn
    have hj' : i < fields.length := by simpa only [List.length_map] using hj
    have hn' : fields[i] ≠ .proof := by
      intro E
      apply hn
      simp only [List.getElem_map, E, ProofShape.subst]
    simpa only [JointCheckKind.subst, List.getElem_map, ProofShape.subst] using ih i hj' hn' W
  | etaLams _ H ih => exact .etaLams (ih W) (H.elim (fun H => .inl H.subst) (fun H => .inr H.subst))
  | compute Ra Rb _ ih => exact .compute (Ra.rename hstep W) (Rb.rename hstep W) (ih W)
  | symm _ ih => exact .symm (ih W)
  | carrierIntro hi hx hp hadm _ ih =>
    simp only [JointCheckKind.subst, subst_mkApps, ProofShape.subst]
    apply JointCheck.carrierIntro hi hx (by simpa only [List.length_map] using hp) hadm
    intro i hj hn
    exact ih i hj hn W
  | carrierChecked _ ih => exact .carrierChecked (ih W)
  | carrierSubsingleton H => exact .carrierSubsingleton (H.subst τ)
  | carrierFunction S _ ih =>
    apply JointCheck.carrierFunction (ContextSubstitution.sort W.interpretation S)
    simpa only [JointCheckKind.subst, ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | carrierSymm _ ih => exact .carrierSymm (ih W)
  | carrierCompute R _ ih => exact .carrierCompute (R.rename hstep W) (ih W)
  | carrierReduce Ra Rb _ ih => exact .carrierReduce (Ra.rename hstep W) (Rb.rename hstep W) (ih W)
  | @carrierNested family info ls doms result Δ ps a b hi hx hp hadm HT _ ih =>
    simp only [JointCheckKind.subst, subst_mkApps, ProofShape.subst]
    apply JointCheck.carrierNested hi hx (by simpa only [List.length_map] using hp) hadm HT
    intro i hj hn
    simpa only [JointCheckKind.subst, projectionType_subst (args := ps) HT _ (by omega),
      ProofShape.subst] using ih i hj hn W

end ProofShape
end Lean4Lean.VEnv.Strengthening
