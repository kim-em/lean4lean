import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalInstantiation
import Lean4Lean.Theory.Typing.Strengthening.StructureProofFieldExamples

/-! # Recursive instantiation by structures with no retained fields

The image may be an arbitrary term, including a computation, at a convertible
assigned type. Fieldless structures are covered even with indices. A closed
all-proof-fields certificate additionally covers unindexed structures whose
primitive projections exist but disappear under typed erasure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Any typed value at a fieldless registered structure instantiates recursive
checking; no constructor exposure or native recovery of the image is required. -/
theorem proofErase_computed_joint_zero_compare_inst_fieldless
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) args))
    (hi : env.projections c info) (hz : info.numFields = 0)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_terminal hs hΓ hp (.fieldless hdata hi hz) ha hb H

/-- Fieldless images also preserve exact first-layer computation outputs. -/
theorem proofErase_computed_joint_one_compute_inst_fieldless
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) args))
    (hi : env.projections c info) (hz : info.numFields = 0)
    (ht : env.HasType univs (P :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_terminal heq hs hΓ hp (.fieldless hdata hi hz) ht R

/-- Closed proof-field typings suffice for recursive instantiation of any
unindexed structure value, at any of its actual assigned types. -/
theorem proofErase_computed_joint_zero_compare_inst_proofStructure
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) ps))
    (hi : env.projections c info) (hps : ps.length = info.nparams) (hx : info.nindices = 0)
    (HF : StructureReplay.ProofFields env univs info ls)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_terminal hs hΓ hp
    (.proofStructure hdata hi hps hx HF) ha hb H

/-- All-proof-field images retain exact outputs through the first recursive
computation layer, including generated singleton telescopes. -/
theorem proofErase_computed_joint_one_compute_inst_proofStructure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) ps))
    (hi : env.projections c info) (hps : ps.length = info.nparams) (hx : info.nindices = 0)
    (HF : StructureReplay.ProofFields env univs info ls)
    (ht : env.HasType univs (P :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_terminal heq hs hΓ hp
    (.proofStructure hdata hi hps hx HF) ht R

/-- The ordinary two-proposition, two-proof-field constructor telescope gives a
terminal image from declaration syntax alone. The structure's result universe
is unrestricted, so the major itself need not be erased as a proof. -/
theorem TerminalImage.of_conjunction_shape
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) [P, Q]))
    (hi : env.projections c info) (hx : info.nindices = 0)
    (hshape : info.ctorType = wrapForalls [.sort .zero, .sort .zero, .bvar 1, .bvar 1] result)
    (hp : info.nparams = 2) (hf : info.numFields = 2) : TerminalImage Γ p :=
  .proofStructure hdata hi (by simp [hp]) hx
    (StructureReplay.ProofFields.conjunction_shape hshape hp hf)

/-- A concrete proof-only constructor telescope supplies every image premise
for recursive body instantiation, including when the image's selected type
is not syntactically its structure type. -/
theorem proofErase_computed_joint_zero_compare_inst_conjunctionShape
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ p T)
    (hdata : env.HasType univs Γ p (VExpr.mkApps (.const c ls) [P, Q]))
    (hi : env.projections c info) (hx : info.nindices = 0)
    (hshape : info.ctorType = wrapForalls [.sort .zero, .sort .zero, .bvar 1, .bvar 1] result)
    (hp : info.nparams = 2) (hf : info.numFields = 2)
    (ha : env.HasType univs (T :: Γ) a A) (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (T :: Γ)) mode
      (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_terminal hs hΓ ht
    (TerminalImage.of_conjunction_shape hdata hi hx hshape hp hf) ha hb H

end Lean4Lean.VEnv.Strengthening
