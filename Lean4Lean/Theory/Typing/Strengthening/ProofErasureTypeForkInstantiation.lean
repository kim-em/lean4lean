import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeForkBinderJoin

/-! # Substituting type joins under type-only fork joining

The type-instantiation premise joins each substituted computation with the
substitution of its raw output. Realizing that output as a type allows the two
joins to compose using type-only fork joining. Contextual equality of arguments
then permits distinct arguments in distinct but joined type bodies.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A computational join between two types survives arbitrary typed
instantiation, under type-only fork joining. No native premise is imposed on the
argument. The raw common output is realized before invoking the final fork. -/
theorem TypeForkJoin.type_join_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs (A :: Γ) C (.sort w)) (hx : env.HasType univs Γ x A)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) out)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) C) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst x)) shared := by
  obtain ⟨s, LB, LO⟩ := TypeForkJoin.instantiation_join HF hΓ hA hB hx RB
  obtain ⟨t, RC, RO⟩ := TypeForkJoin.instantiation_join HF hΓ hA hC hx RC
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨B₀, HB₀, EB₀⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hB rfl rfl RB
  have hBx := HB₀.hasType.2.instN henv.ordered Ctx.InstN.zero hx
  have E : proofErase Γ (B₀.inst x) = out.inst (proofErase Γ x) := by
    rw [proofErase_instN hΓA hx Ctx.InstN.zero HB₀.hasType.2, EB₀]
  obtain ⟨r, L, R⟩ := HF hΓ hBx (E ▸ LO) (E ▸ RO)
  exact ⟨r, LB.trans L, RC.trans R⟩

/-- Distinct contextually compared arguments can be substituted in distinct
contextually compared type bodies. The bodies are compared under A; the argument
comparison is observed using the second type body. Every fork used to compose
these operations is rooted at a typed type, not at either data argument. -/
theorem TypeForkJoin.contextual_type_inst_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs (A :: Γ) C (.sort v))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HBC : TypeContextJoin D (A :: Γ) (.sort v) B C)
    (Hxy : TypeContextJoin D Γ A x y) :
    TypeContextJoin D Γ (.sort v) (B.inst x) (C.inst y) := by
  obtain ⟨out, RB, RC⟩ := TypeContextJoin.type_join HBC
  obtain ⟨s, LB, LC⟩ := HF.type_join_inst heq hs hΓ hA hB hC hx RB RC
  obtain ⟨t, RC, RY⟩ := Hxy hC
  have hCx := hC.instN henv.ordered Ctx.InstN.zero hx
  obtain ⟨r, L, R⟩ := HF hΓ hCx LC RC
  have hBx := hB.instN henv.ordered Ctx.InstN.zero hx
  have hCy := hC.instN henv.ordered Ctx.InstN.zero hy
  obtain ⟨w, hSort⟩ := hBx.isType henv hΓ
  have hΓSort : OnCtx (.sort v :: Γ) (env.IsType univs) := ⟨hΓ, w, hSort⟩
  intro T z hT
  exact TypeContextJoin.of_compute_join heq hs hΓSort hBx hCy (LB.trans L) (RY.trans R) hT

end Lean4Lean.VEnv.Strengthening
