import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaSquares
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeRecovery

/-! # Native telescope histories through structure and function eta

Every original retained argument supplies its literal assigned domain. The
arguments may then compute independently and lose those certificates. Pi
component readout and the body/argument square keep every selected output
reachable from the original declaration residual, including conversions at
intermediate application prefixes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A literal typed telescope with native evidence only for original retained
arguments. Constructing this walk for arbitrary arguments is not asserted;
computed images never need their own native certificates. -/
inductive RetainedNativeWalk (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) : VExpr → List VExpr → VExpr → Prop where
  | nil : RetainedNativeWalk Step Γ T [] T
  | cons : env.HasType univs Γ a A →
      (¬ IsProof Γ a → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ A)) →
      RetainedNativeWalk Step Γ (B.inst a) args result →
      RetainedNativeWalk Step Γ (.forallE A B) (a :: args) result

/-- Forgetting native images leaves the ordinary literal telescope. -/
theorem RetainedNativeWalk.typed (W : RetainedNativeWalk Step Γ T args result) :
    InstForallsC env univs Γ T args result := by
  induction W with
  | nil => exact .nil
  | cons ha _ _ ih => exact .cons ha ih

/-- A computed literal Pi can be supplied with a computed argument. Only the
original retained argument must recover its original assigned domain. -/
theorem static_structure_computed_pi_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.forallE rawA rawB))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (B.inst x)) (rawB.inst image) := by
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at RT
  obtain ⟨_, _, _, _, _, _, _, RB⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hB RT
  exact static_structure_body_argument_square heq hs ⟨hΓ, u, hA⟩ hB hx HR RB RX

/-- Recovery of a computed application retains a path from the original
instantiated codomain whenever every recovery of its function has the stated
Pi origin. The function itself may be arbitrary raw syntax. -/
theorem static_structure_computed_app_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (ha : env.HasType univs Γ a A)
    (HR : ¬ IsProof Γ a → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ A))
    (HN : ∀ {T}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f T →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A B)) T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) argOut)
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app f argOut) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (B.inst a)) out := by
  generalize EΔ : proofEraseCtx Γ = Δ at R
  generalize E : ProofShape.app f argOut = e at R
  induction R with
  | app RF =>
    cases E
    rw [← EΔ] at RF ⊢
    exact static_structure_computed_pi_inst heq hs hΓ hA hB ha HR (HN RF) RA
  | convert _ H ih => exact (ih EΔ E).trans H
  | bvar | sort | const | lam | forallE | proj => cases E

/-- Every recovery of a computed argument spine has the original residual
as an ancestor, even with arbitrary structure/function eta at every prefix.
The original walk carries exact retained recoveries; no confluence is used. -/
theorem static_structure_computed_telescope_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : RetainedNativeWalk (ErasedStaticStructureEtaExpansionUnion D) Γ T args residual)
    (HN : ∀ {U}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f U →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) U)
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps f args') out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ residual) out := by
  induction HW generalizing f u args' with
  | nil => cases HA; exact HN R
  | cons ha HR _ ih =>
    cases HA with | cons RA HA =>
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    exact ih (hB.instN henv Ctx.InstN.zero ha)
      (fun R => static_structure_computed_app_native heq hs hΓ hA hB ha HR HN RA R) HA R

/-- A declared constant supplies the telescope origin without a separate
coverage premise. Only its original retained argument walk remains required. -/
theorem static_structure_computed_const_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = ci.uvars)
    (HW : RetainedNativeWalk (ErasedStaticStructureEtaExpansionUnion D) Γ
      (ci.type.instL ls) args residual)
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) args') out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ residual) out := by
  have hf := HasType.const (Γ := []) hc hw hl
  obtain ⟨u, hT⟩ := hf.isType henv (by trivial)
  apply static_structure_computed_telescope_native heq hs hΓ (hT.weak0 henv.ordered) HW ?_ HA R
  intro U H
  rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ]
  exact H.const_compute hc

end Lean4Lean.VEnv.Strengthening
