import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInstantiationBinders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureCommonApplication

/-! # Discharging a certified binder after one arbitrary type instantiation

One joining instantiation may be followed by exact instantiation of a proof
or a natively recovered value. Both sides use the same substituted common
output; no transitivity of joining or second type-fork premise is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- The open type-instantiation premise handles one arbitrary argument below
a dependent binder. Supplying a certified second argument then transports both
sides of that same join exactly. The second argument needs native recovery only
when it is retained; no recovery is required for the first argument. This does
not compose two arbitrary joining substitutions. -/
theorem TypeInstantiationJoin.inst_then_certified
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (P :: A :: Γ) (env.IsType univs))
    (hB : env.HasType univs (P :: A :: Γ) B (.sort v))
    (hx : env.HasType univs Γ x A) (hp : env.HasType univs Γ p (P.inst x))
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ (P.inst x)))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (P :: A :: Γ))
      (proofErase (P :: A :: Γ) B) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ ((B.inst x 1).inst p)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        ((out.inst (proofErase Γ x) 1).inst (proofErase Γ p)) shared := by
  have W : Ctx.InstN Γ x A 1 (P :: A :: Γ) (P.inst x :: Γ) := Ctx.InstN.zero.succ
  obtain ⟨joint, RL, RR⟩ := HJ.instN heq hs hx W hctx hB RB
  have hBI := hB.instN henv.ordered W hx
  have LL := static_structure_union_compute_inst heq hs hΓ hp HR hBI RL
  obtain ⟨B', HB', EB'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hctx hB rfl rfl RB
  have hB'I := HB'.hasType.2.instN henv.ordered W hx
  have EI := proofErase_instN hctx hx W HB'.hasType.2
  rw [EB'] at EI
  rw [← EI] at RR
  have RR' := static_structure_union_compute_inst heq hs hΓ hp HR hB'I RR
  have hctxI := (W.wf henv.ordered hx hctx).2
  have EP := proofErase_instN hctxI hp Ctx.InstN.zero hB'I
  rw [EP, EI] at RR'
  exact ⟨joint.inst (proofErase Γ p), LL, RR'⟩

/-- A dependent propositional witness may be discharged after the single
arbitrary instantiation join, without any second native certificate. This is
the two-binder substitution needed by a type template carrying an auxiliary Eq
proof. It proves substitution joining for the template only; eliminating a cast
used to form that template is a separate computation obligation. -/
theorem TypeInstantiationJoin.inst_then_proof
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (P :: A :: Γ) (env.IsType univs))
    (hP : env.HasType univs (A :: Γ) P (.sort .zero))
    (hB : env.HasType univs (P :: A :: Γ) B (.sort v))
    (hx : env.HasType univs Γ x A) (hp : env.HasType univs Γ p (P.inst x))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (P :: A :: Γ))
      (proofErase (P :: A :: Γ) B) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ ((B.inst x 1).inst p)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        ((out.inst (proofErase Γ x) 1).inst .proof) shared := by
  have hPI := hP.instN henv.ordered Ctx.InstN.zero hx
  have hproof : IsProof Γ p := ⟨P.inst x, hp, hPI⟩
  obtain ⟨shared, RL, RR⟩ := HJ.inst_then_certified heq hs hΓ hctx hB hx hp
    (fun hn => (hn hproof).elim) RB
  exact ⟨shared, RL, by simpa only [proofErase_eq_proof.2 hproof] using RR⟩

end Lean4Lean.VEnv.Strengthening
