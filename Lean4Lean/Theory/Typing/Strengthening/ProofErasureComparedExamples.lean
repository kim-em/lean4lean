import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedK
import Lean4Lean.Theory.Typing.Strengthening.CertifiedKExamples

/-! # Concrete eta-guarded erased Eq computations

The typed source which refuted beta/syntactic-K eta removal computes in the
recursive erased comparison fragment. An enclosing Eq.rec uses that computation
as its endpoint certificate, giving a genuine two-stage example.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open EqRecEtaBoundary
variable [Params] {D : PureObservation.Definitions}

/-- The earlier typed eta obstruction computes at stage one, using its actual
well-formed context and canonical Eq rule rather than an assumed comparison. -/
theorem erased_eta_obstruction_computes (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ProofShape.Compute (ErasedComparedKStage D 1)
      (proofErase context source) (proofErase context carrier) := by
  apply proofErase_compared_K_forward heq hs (context_wf heq) (source_typed henv heq)
  exact proofErase_compared_K_eta (context_wf heq) (function_typed henv)

/-- The type-valued nested example computes at stage two. Its endpoint guard
uses the first stage's checked path and a reflexive terminal comparison. -/
theorem erased_nested_eta_computes (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ProofShape.Compute (ErasedComparedKStage D 2)
      (proofErase context CertifiedKExamples.nestedSource) (proofErase context carrier) := by
  apply proofErase_compared_K_forward heq hs (context_wf heq) (CertifiedKExamples.nested_typed henv heq)
  exact .compute (erased_eta_obstruction_computes heq hs) .refl .refl

/-- The nested certificate survives any insertion and reflects to the original
lower equality by the new comparison theorem. -/
theorem erased_nested_eta_descends (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k context Γ') :
    env.IsDefEq univs context CertifiedKExamples.nestedSource carrier (.sort (.succ .zero)) := by
  have H : ProofShape.Compare (ErasedComparedKStage D 2) true
      (proofErase Γ' (CertifiedKExamples.nestedSource.liftN n k))
      (proofErase Γ' (carrier.liftN n k)) := by
    rw [proofErase_liftN (context_wf heq) hΓ' W (CertifiedKExamples.nested_typed henv heq),
      proofErase_liftN (context_wf heq) hΓ' W (carrier_typed env univs context)]
    exact (ProofShape.Compare.compute (erased_nested_eta_computes heq hs) .refl
      (ProofShape.Compare.refl (mode := true))).liftN (erased_compared_K_stage_liftN 2)
  exact proofErase_compared_K_descend heq hs (context_wf heq) hΓ' W
    (CertifiedKExamples.nested_typed henv heq) (carrier_typed env univs context) H

end Lean4Lean.VEnv.Strengthening
