import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointChecking

/-! # Exact renaming of computed joint checking -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- The entire mutually recursive checking grammar transports under exact
context renaming. In the recovered-application case both the selected Pi and
its carrier guard transport together, with no re-synthesis hypothesis. -/
theorem ComputedJointCheck.rename
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (H : ComputedJointCheck Step Δ kind a b) (W : ContextRenaming Δ Δ' τ) :
    ComputedJointCheck Step' Δ' (kind.subst τ) (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | leaf H => exact .leaf H.subst
  | app _ _ ihf ihx => exact .app (ihf W) (ihx W)
  | appCarrier R _ _ ihf ihx => exact .appCarrier (R.rename hstep W) (ihf W) (ihx W)
  | appComputed R _ _ ihf ihx => exact .appComputed (R.rename hstep W) (ihf W) (ihx W)
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
    apply ComputedJointCheck.etaBodyL (ContextSubstitution.sort W.interpretation S)
    simpa only [JointCheckKind.subst, ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | etaBodyR S _ ih =>
    apply ComputedJointCheck.etaBodyR (ContextSubstitution.sort W.interpretation S)
    simpa only [JointCheckKind.subst, ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | @structFields Δ family info ls ps fields m hi hx hp hf hadm H ih =>
    simp only [JointCheckKind.subst, ProofShape.subst_mkApps, List.map_append, ProofShape.subst]
    apply ComputedJointCheck.structFields hi hx (by simpa only [List.length_map] using hp)
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
    apply ComputedJointCheck.carrierIntro hi hx (by simpa only [List.length_map] using hp) hadm
    intro i hj hn
    exact ih i hj hn W
  | carrierChecked _ ih => exact .carrierChecked (ih W)
  | carrierSubsingleton H => exact .carrierSubsingleton (H.subst τ)
  | carrierFunction S _ ih =>
    apply ComputedJointCheck.carrierFunction (ContextSubstitution.sort W.interpretation S)
    simpa only [JointCheckKind.subst, ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | carrierSymm _ ih => exact .carrierSymm (ih W)
  | carrierCompute R _ ih => exact .carrierCompute (R.rename hstep W) (ih W)
  | carrierReduce Ra Rb _ ih => exact .carrierReduce (Ra.rename hstep W) (Rb.rename hstep W) (ih W)
  | @carrierNested family info ls doms result Δ ps a b hi hx hp hadm HT _ ih =>
    simp only [JointCheckKind.subst, subst_mkApps, ProofShape.subst]
    apply ComputedJointCheck.carrierNested hi hx (by simpa only [List.length_map] using hp) hadm HT
    intro i hj hn
    simpa only [JointCheckKind.subst, projectionType_subst (args := ps) HT _ (by omega),
      ProofShape.subst] using ih i hj hn W

end ProofShape
end Lean4Lean.VEnv.Strengthening
