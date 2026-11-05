import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualEtaTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualInstantiationFork

/-! # Simultaneous dependent lambda annotation replacement

The assigned Pi telescope supplies a generic eta expansion. Substituting a
lambda telescope with the same length cancels every written annotation by beta,
leaving the original body beneath the assigned domains. No pointwise domain
comparison, native certificate, or lambda-body congruence is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- Generic eta at the assigned domains cancels a supplied lambda prefix of
the same length, regardless of its written dependent annotations. This is
administrative beta only; the residual body is untouched. -/
theorem EtaTelescope.generic_inst_reannotate_beta
    (hlen : written.length = ds.length) (b : VExpr) :
    VExpr.BetaRed
      ((VExpr.wrapLams (liftDomains ds 0) (etaOpen ds.length (.bvar 0))).inst
        (VExpr.wrapLams written b))
      (VExpr.wrapLams ds b) := by
  rw [generic_inst, ← hlen]
  exact beta_wrapLams (etaOpen_wrapLams_beta written b) ds

variable [Params] {D : PureObservation.Definitions}

/-- Typing at an assigned Pi telescope suffices to replace all written lambda
domains simultaneously. The target body needs no separate typing premise under
the new domains; its typing follows from eta followed by administrative beta. -/
theorem telescope_annotations_defeq
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (VExpr.wrapLams written b) (VExpr.wrapForalls ds T))
    (hlen : written.length = ds.length) :
    env.IsDefEq univs Γ (VExpr.wrapLams written b) (VExpr.wrapLams ds b)
      (VExpr.wrapForalls ds T) := by
  have HE := hf.etaOpen_defeq henv hΓ
  have RB : VExpr.BetaRed
      (VExpr.wrapLams ds (etaOpen ds.length (VExpr.wrapLams written b)))
      (VExpr.wrapLams ds b) := by
    rw [← hlen]
    exact EtaTelescope.beta_wrapLams (EtaTelescope.etaOpen_wrapLams_beta written b) ds
  exact HE.trans (beta_eq hΓ HE.hasType.2 RB)

/-- A typed identity beta redex is a common computational ancestor of the
original and simultaneously reannotated lambda telescopes. This fork is proved
without TypeForkJoin, including for proof-valued functions. Its generic variable
supplies every eta guard before the actual abstraction is substituted. -/
theorem static_structure_telescope_annotations_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (VExpr.wrapLams written b) (VExpr.wrapForalls ds T))
    (hlen : written.length = ds.length) :
    let A := VExpr.wrapForalls ds T
    let root := VExpr.app (.lam A (.bvar 0)) (VExpr.wrapLams written b)
    env.HasType univs Γ root A ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ root) (proofErase Γ (VExpr.wrapLams written b)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ root) (proofErase Γ (VExpr.wrapLams ds b)) := by
  dsimp only
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls ds T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hv : env.HasType univs (VExpr.wrapForalls ds T :: Γ) (.bvar 0)
      (VExpr.wrapForalls ds T).lift := .bvar .zero
  have hg := generic_eta_telescope_typing hΓ hT
  obtain ⟨RL, RR⟩ := static_structure_instantiation_compute_peak heq hs hΓ hT hv hf
    (static_structure_generic_eta_telescope heq hs hΓ hT)
  rw [← proofErase_instN hΓT hf Ctx.InstN.zero hg] at RR
  have RC := proofErase_beta_forward hΓ (hg.instN henv.ordered Ctx.InstN.zero hf)
    (EtaTelescope.generic_inst_reannotate_beta hlen b)
  refine ⟨?_, ?_, RR.trans (.beta RC)⟩
  · simpa only [VExpr.inst_lift] using HasType.app (HasType.lam hT hv) hf
  · simpa only [VExpr.inst, VExpr.instVar_zero] using RL

/-- Under TypeForkJoin, every typed observation joins a lambda telescope with
its simultaneous reannotation at the assigned Pi domains. The written and
assigned telescopes may differ at every dependent binder. This removes domain
alignment from that comparison, but does not compare different residual bodies
or establish the still-open type-fork premise. -/
theorem TypeForkJoin.contextual_telescope_annotations
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (VExpr.wrapLams written b) (VExpr.wrapForalls ds T))
    (hlen : written.length = ds.length) :
    TypeContextJoin D Γ (VExpr.wrapForalls ds T)
      (VExpr.wrapLams written b) (VExpr.wrapLams ds b) := by
  intro K z hK
  have HE := telescope_annotations_defeq hΓ hf hlen
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls ds T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  obtain ⟨hroot, RL, RR⟩ := static_structure_telescope_annotations_fork heq hs hΓ hf hlen
  have OL := proofErase_static_structure_compute_inst_argument heq hs hΓT hK hroot RL
  have OR := proofErase_static_structure_compute_inst_argument heq hs hΓT hK hroot RR
  rw [← proofErase_instN hΓT hf Ctx.InstN.zero hK] at OL
  rw [← proofErase_instN hΓT HE.hasType.2 Ctx.InstN.zero hK] at OR
  exact HF hΓ (hK.instN henv.ordered Ctx.InstN.zero hroot) OL OR

/-- Two same-body lambda telescopes at a common assigned type join in every
typed type context, even when all their written dependent annotations differ.
The common intermediate uses the assigned domains. No native recovery, domain
join or independently transported body typing is required. -/
theorem TypeForkJoin.contextual_same_body_telescopes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.HasType univs Γ (VExpr.wrapLams left b) (VExpr.wrapForalls ds T))
    (hr : env.HasType univs Γ (VExpr.wrapLams right b) (VExpr.wrapForalls ds T))
    (hlenL : left.length = ds.length) (hlenR : right.length = ds.length) :
    TypeContextJoin D Γ (VExpr.wrapForalls ds T)
      (VExpr.wrapLams left b) (VExpr.wrapLams right b) := by
  have HR : TypeContextJoin D Γ (VExpr.wrapForalls ds T)
      (VExpr.wrapLams right b) (VExpr.wrapLams ds b) :=
    HF.contextual_telescope_annotations heq hs hΓ hr hlenR
  intro K z hK
  exact TypeContextJoin.trans HF hΓ (telescope_annotations_defeq hΓ hl hlenL).hasType.2
    (HF.contextual_telescope_annotations heq hs hΓ hl hlenL)
    HR.symm hK

end Lean4Lean.VEnv.Strengthening
