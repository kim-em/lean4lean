import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonSlots

/-! # Computing the capture vector of a typed erased template

Only the old captures need a typed telescope realization. Their raw outputs
can be inserted into the fixed template without a new recovery or typing
premise. Singleton slot selection retains the corresponding capture paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- Pointwise scoped computation extends through an application spine in the
same raw context. No typing or primitive closure assumptions are needed. -/
theorem ProofShape.ScopedCompute.mkApps
    (HF : ScopedCompute Step Δ f f')
    (HA : List.Forall₂ (ScopedCompute Step Δ) args args') :
    ScopedCompute Step Δ (ProofShape.mkApps f args) (ProofShape.mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact HF
  | cons H HT ih => exact ih (.app HF H)

private theorem getD_compute
    (H : List.Forall₂ (ScopedCompute Step Δ) args args') (i : Nat) :
    ScopedCompute Step Δ (args.getD i .proof) (args'.getD i .proof) := by
  induction H generalizing i with
  | nil => exact .refl
  | cons H HT ih =>
    cases i with
    | zero => exact H
    | succ i => exact ih i

/-- Slot selection preserves pointwise scoped computation, including proof
markers and out-of-range defaults. This statement is entirely raw. -/
theorem ProofShape.singletonSlots_compute
    (H : List.Forall₂ (ScopedCompute Step Δ) args args') :
    List.Forall₂ (ScopedCompute Step Δ)
      (singletonSlots slots count args) (singletonSlots slots count args') := by
  unfold singletonSlots
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply Lean4Lean.List.Forall₂.rfl
  intro i hi
  cases slots.getD i none with
  | none => exact .refl
  | some k => exact getD_compute H k

variable [Params]

/-- Pointwise computation of erased captures extends through a closed typed
equation body. Source telescope typing is sufficient; the output vector may
consist of raw reducts without chosen original representatives. Only primitive
renaming is used beneath the template's dependent binders. -/
theorem proofErase_template_compute_captures
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΔ : OnCtx doms.reverse (env.IsType univs))
    (he : env.HasType univs doms.reverse e T) (ha : TelInst env univs Γ doms args)
    (H : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) rawArgs) :
    ScopedCompute Step (proofEraseCtx Γ)
      ((proofErase doms.reverse e).instOuter (args.map (proofErase Γ)))
      ((proofErase doms.reverse e).instOuter rawArgs) := by
  have W := erasedTemplate_substEq hΔ ha
  have E : ErasedSubstAgreement doms.reverse Γ (VExpr.Subst.ofList args)
      (ProofShape.Subst.ofList (args.map (proofErase Γ))) := by
    intro i A hl _
    have hi : i < args.length := by
      have := hl.lt
      have := ha.1
      simp only [List.length_reverse] at *
      omega
    simp only [VExpr.Subst.ofList, ProofShape.Subst.ofList, List.length_map, dif_pos hi,
      List.getElem_map]
  apply proofErase_compute_subst_images_of_renaming hrename hΓ W he E
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := H.length_eq
  by_cases hi : i < (args.map (proofErase Γ)).length
  · simp only [← hlen, dif_pos hi]
    exact H.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .refl

end Lean4Lean.VEnv.Strengthening
