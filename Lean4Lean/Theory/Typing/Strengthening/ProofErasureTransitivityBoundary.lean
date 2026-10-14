import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedK
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaDomains

/-! # Raw transitivity can discard the common-type requirement

In an environment with an unindexed empty structure, its raw constructor can
serve as an unchecked intermediate between any two common-mode shapes. Placing
that bridge in an application argument produces the same obstruction in either
outer mode. Under canonical Eq the two displayed original endpoints are typed
propositions and are provably unequal. This refutes untyped transitive closure
of the certificate relation, not strengthening of original equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Empty-structure eta supplies a raw two-link bridge with no intermediate
typing. All universe arguments of the chosen bridge are zero. -/
theorem erased_empty_structure_bridge (hi : env.projections family info)
    (hx : info.nindices = 0) (hf : info.numFields = 0) (a b : ProofShape) :
    ∃ mid, ProofShape.Compare Step true a mid ∧ ProofShape.Compare Step true mid b := by
  let ps : List ProofShape := List.replicate info.nparams .proof
  let ls : List VLevel := List.replicate info.uvars .zero
  let mid := ProofShape.mkApps (.const info.ctorName ls) ps
  have HH (m : ProofShape) : ProofShape.StructureEtaHead mid m := by
    have H : ProofShape.StructureEtaHead
        (ProofShape.mkApps (.const info.ctorName ls) (ps ++ [])) m :=
      .intro hi hx (by simp [ps]) (by simp [hf])
        (.inr (StructureReplay.ProofFields.of_no_fields hf)) (by intro i h; simp at h)
    simpa only [List.append_nil] using H
  exact ⟨mid, .structR (HH a), .structL (HH b)⟩

namespace ErasedTransitivityBoundary
/-- An identity wrapper places the intermediate comparison in common argument
mode even when the whole comparison is requested in inferred mode. -/
def wrap (P : VExpr) : VExpr := .app (.lam (.sort .zero) (.bvar 0)) P

/-- The original wrapped endpoint is a proposition and beta-converts to P. -/
theorem wrap_beta (hP : env.HasType univs Γ P (.sort .zero)) :
    env.IsDefEq univs Γ (wrap P) P (.sort .zero) := by
  simpa [wrap, inst, lift, liftN] using (IsDefEq.beta (.bvar .zero) hP)

/-- With canonical Eq and a registered empty structure, both modes have a raw
nontransitivity witness whose outer endpoints are typed below at the same type.
The middle shape carries no common-type witness. -/
theorem typed_nontransitivity (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hx : info.nindices = 0) (hf : info.numFields = 0) (mode : Bool) :
    env.HasType univs Γ (wrap ErasedEtaDomains.sourceDomain) (.sort .zero) ∧
    env.HasType univs Γ (wrap ErasedEtaDomains.targetDomain) (.sort .zero) ∧
    ∃ mid,
      ProofShape.Compare (ErasedComparedKStage D stage) mode
        (proofErase Γ (wrap ErasedEtaDomains.sourceDomain)) mid ∧
      ProofShape.Compare (ErasedComparedKStage D stage) mode
        mid (proofErase Γ (wrap ErasedEtaDomains.targetDomain)) ∧
      ¬ ProofShape.Compare (ErasedComparedKStage D stage) mode
        (proofErase Γ (wrap ErasedEtaDomains.sourceDomain))
        (proofErase Γ (wrap ErasedEtaDomains.targetDomain)) := by
  obtain ⟨hP, hQ, _⟩ := ErasedEtaDomains.canonical_domain_obstruction heq hΓ
  have hne : ¬ env.IsDefEqU univs Γ ErasedEtaDomains.sourceDomain ErasedEtaDomains.targetDomain :=
    IsDefEqU.rigidApp_forallE_inv henv hΓ (heq.rigid henv)
      (ls := [.succ (.succ .zero)])
      (args := [.sort (.succ .zero), .sort .zero, .sort .zero]) hP
  have hβP := wrap_beta hP
  have hβQ := wrap_beta hQ
  have hAP := hβP.hasType.1
  have hAQ := hβQ.hasType.1
  have EAP : proofErase Γ (wrap ErasedEtaDomains.sourceDomain) =
      .app (proofErase Γ (.lam (.sort .zero) (.bvar 0))) (proofErase Γ ErasedEtaDomains.sourceDomain) :=
    if_neg (not_isProof_of_sort hΓ hAP)
  have EAQ : proofErase Γ (wrap ErasedEtaDomains.targetDomain) =
      .app (proofErase Γ (.lam (.sort .zero) (.bvar 0))) (proofErase Γ ErasedEtaDomains.targetDomain) :=
    if_neg (not_isProof_of_sort hΓ hAQ)
  obtain ⟨mid, HP, HQ⟩ := erased_empty_structure_bridge (Step := ErasedComparedKStage D stage)
    hi hx hf (proofErase Γ ErasedEtaDomains.sourceDomain) (proofErase Γ ErasedEtaDomains.targetDomain)
  refine ⟨hAP, hAQ, .app (proofErase Γ (.lam (.sort .zero) (.bvar 0))) mid, ?_, ?_, ?_⟩
  · rw [EAP]
    exact .app .refl HP
  · rw [EAQ]
    exact .app .refl HQ
  · intro HC
    have HE := (proofErase_compare_reflect (erased_compared_K_stage_descent heq hs stage)
      hΓ hAP hAQ HC).1 ⟨_, HasType.sort (by trivial)⟩
    exact hne ⟨_, hβP.symm.trans ((HE.of_l henv hΓ hAP).trans hβQ)⟩

/-- Unrestricted raw transitivity is false even for inferred mode. A future
composition theorem must retain more than its two untyped input certificates. -/
theorem not_transitive (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hx : info.nindices = 0) (hf : info.numFields = 0) (mode : Bool) :
    ¬ (∀ {a b c}, ProofShape.Compare (ErasedComparedKStage D stage) mode a b →
      ProofShape.Compare (ErasedComparedKStage D stage) mode b c →
      ProofShape.Compare (ErasedComparedKStage D stage) mode a c) := by
  intro Htrans
  obtain ⟨_, _, mid, H1, H2, Hne⟩ := typed_nontransitivity (stage := stage) heq hs hΓ hi hx hf mode
  exact Hne (Htrans H1 H2)

end ErasedTransitivityBoundary
end Lean4Lean.VEnv.Strengthening
