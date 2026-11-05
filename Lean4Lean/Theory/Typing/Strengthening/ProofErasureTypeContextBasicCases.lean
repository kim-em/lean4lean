import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextApplication

/-! # Conversion, beta and proof arguments for contextual type observations

Changing an assigned type transports the observer's typing. Beta computation
and proof irrelevance lift through observers directly. In particular dependent
application at proof arguments requires no generic type-valued result template.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Ordinary conversion of the assigned type transports every type observer.
No computational join of the assignments or confluence premise is required. -/
theorem TypeContextJoin.convert
    (HAB : env.IsDefEq univs Γ A B (.sort u)) (H : TypeContextJoin D Γ A a b) :
    TypeContextJoin D Γ B a b := by
  intro C v hC
  exact H (hC.defeqDFC henv (IsDefEqCtx.succ .zero HAB.symm))

/-- Proofs of one proposition have identical contextual observations. This
supplies the proof-irrelevance equality case with no open joining premise. -/
theorem TypeContextJoin.proof_irrel
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (ha : env.HasType univs Γ a P) (hb : env.HasType univs Γ b P) :
    TypeContextJoin D Γ P a b := by
  have E : proofErase Γ a = proofErase Γ b := by
    rw [proofErase_eq_proof.2 ⟨P, ha, hP⟩, proofErase_eq_proof.2 ⟨P, hb, hP⟩]
  intro C v hC
  exact TypeContextJoin.of_erasure_eq ⟨hΓ, _, hP⟩ ha hb E hC

/-- Any typed beta computation is respected by every typed type context.
The source can be data, and no native certificate for its beta arguments is
needed. This includes the ordinary beta equality rule and nested beta paths. -/
theorem TypeContextJoin.of_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (R : VExpr.BetaRed a b) : TypeContextJoin D Γ A a b := by
  obtain ⟨u, hA⟩ := ha.isType henv hΓ
  have hb := (beta_eq hΓ ha R).hasType.2
  intro C v hC
  exact TypeContextJoin.of_compute_join heq hs ⟨hΓ, u, hA⟩ ha hb
    (.beta (proofErase_beta_forward hΓ ha R)) .refl hC

/-- A dependent function preserves contextual equality of any two proofs of
its input proposition. The generic result type may depend on that proof; only
the two actual applications' common typing and proof erasures are used. -/
theorem TypeContextJoin.app_arg_proofs
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hf : env.HasType univs Γ f (.forallE P B))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P) :
    TypeContextJoin D Γ (B.inst x) (.app f x) (.app f y) := by
  have RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) .proof := by rw [proofErase_eq_proof.2 ⟨P, hx, hP⟩]; exact .refl
  have RY : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ y) .proof := by rw [proofErase_eq_proof.2 ⟨P, hy, hP⟩]; exact .refl
  intro C v hC
  exact TypeContextJoin.app_arg_of_compute_join heq hs hΓ hf (.proofIrrel hP hx hy) RX RY hC

/-- The type-argument case also covers converted assignments: the function
need not be written with a literal sort domain. A sort typing of the actual
argument, uniqueness and observer conversion expose that domain. The codomain
remains fully dependent, and no generic result-sort premise is required. -/
theorem TypeContextJoin.app_arg_sort_typed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (Hxy : env.IsDefEq univs Γ x y A) (hx : env.HasType univs Γ x (.sort u))
    (HJ : TypeContextJoin D Γ A x y) :
    TypeContextJoin D Γ (B.inst x) (.app f x) (.app f y) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨w, hA⟩, v, hB⟩ := hPi.forallE_inv henv
  have HA := (Hxy.hasType.1.uniqU henv hΓ hx).of_l henv hΓ hA
  have HPiEq := IsDefEq.forallEDF HA hB
  have hf' := HPiEq.defeq hf
  have Hxy' := IsDefEq.defeqDF HA Hxy
  have HJ' : TypeContextJoin D Γ (.sort u) x y := TypeContextJoin.convert HA HJ
  intro C z hC
  exact TypeContextJoin.app_arg_type heq hs hΓ hf' Hxy' HJ' hC

end Lean4Lean.VEnv.Strengthening
