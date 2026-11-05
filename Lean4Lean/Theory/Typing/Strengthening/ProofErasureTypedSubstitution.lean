import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedBinderTransport

/-! # Simultaneous substitution for typed computation chains

Abstract one source variable, recursively substitute the remaining context,
apply the related head images, and contract beta. Native guards are never
substituted. The two maps may differ at every dependent source declaration.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
/-- A substitution is reconstructed from its head and tail. -/
private theorem subst_tail_head (σ : VExpr.Subst) : σ.tail.cons σ.head = σ := by
  funext i
  cases i <;> rfl

/-- Simultaneous substitution of two pointwise computation-chain-related maps
preserves typed computation equality. Images may be arbitrary dependent data or
proofs, without native certificates or common reducts. Ordinary substitution
typing is explicit, and no fork-joining or equality-completeness premise is used. -/
theorem TypedComputationEq.substDF
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : Ctx.SubstEq env univs Δ σ τ Γ)
    (HC : ∀ i A, Lookup Γ i A → TypedComputationEq D Δ (σ i) (τ i) (A.subst σ))
    (H : TypedComputationEq D Γ a b T) :
    TypedComputationEq D Δ (a.subst σ) (b.subst τ) (T.subst σ) := by
  induction Γ generalizing σ τ a b T with
  | nil =>
    have ha := H.defeq.closedN henv.ordered (by trivial)
    have hb := H.defeq.symm.closedN henv.ordered (by trivial)
    obtain ⟨_, hT⟩ := H.defeq.hasType.1.isType henv (by trivial)
    have hTc := hT.closedN henv.ordered (by trivial)
    have WL : Ctx.LiftN Δ.length 0 [] Δ := by
      simpa only [List.append_nil] using Ctx.LiftN.zero (Γ := []) Δ
    have HW := H.liftN heq hs (by trivial) hΔ WL
    rw [ha.liftN_eq (Nat.zero_le _), hb.liftN_eq (Nat.zero_le _), hTc.liftN_eq (Nat.zero_le _)] at HW
    rw [ha.subst_eq .zero, hb.subst_eq .zero, hTc.subst_eq .zero]
    exact HW
  | cons A Γ ih =>
    cases W with
    | cons W hA _ =>
      have Htail : ∀ i B, Lookup Γ i B →
          TypedComputationEq D Δ (σ.tail i) (τ.tail i) (B.subst σ.tail) := by
        intro i B hl
        simpa only [VExpr.Subst.tail, VExpr.lift_subst] using HC (i+1) B.lift (.succ hl)
      have Hhead : TypedComputationEq D Δ σ.head τ.head (A.subst σ.tail) := by
        simpa only [VExpr.Subst.head, VExpr.lift_subst] using HC 0 A.lift .zero
      have HL := H.lam_body W.wf hA
      have HL' := ih W Htail HL
      have HP := HL'.app hΔ Hhead
      have HB := (TypedComputationEq.of_beta hΔ HP.defeq.hasType.1 VExpr.BetaRed.beta).symm.trans
        (HP.trans (TypedComputationEq.of_beta hΔ HP.defeq.hasType.2 VExpr.BetaRed.beta))
      simpa only [VExpr.inst_lift_cons, subst_tail_head] using HB

/-- Any ordinary well-typed substitution transports a typed computation chain.
Each image supplies its reflexive chain from its ordinary lookup typing. This
requires neither image native recovery nor exact substitution of forward steps. -/
theorem TypedComputationEq.subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : Ctx.SubstEq env univs Δ σ σ Γ)
    (H : TypedComputationEq D Γ a b T) :
    TypedComputationEq D Δ (a.subst σ) (b.subst σ) (T.subst σ) :=
  H.substDF heq hs hΔ W (fun _ _ hl => .refl (W.lookup hl).hasType.1)

/-- Instantiation beneath any dependent prefix preserves computation chains.
The ordinary InstN witness determines the changed context and shifted images;
the general substitution theorem supplies the chain without native image guards. -/
theorem TypedComputationEq.instN
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.InstN Γ₀ x A k Γ' Γ) (hx : env.HasType univs Γ₀ x A)
    (H : TypedComputationEq D Γ' a b T) :
    TypedComputationEq D Γ (a.inst x k) (b.inst x k) (T.inst x k) := by
  simpa only [← VExpr.instN_eq] using H.subst heq hs hΓ (W.substEq hΓ' hx)

/-- A changing body and a changing argument instantiate together at the
left-hand dependent result type. Converted application retags intermediate
assignments, and beta removes the two displayed abstraction wrappers. -/
theorem TypedComputationEq.instDF
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HX : TypedComputationEq D Γ x y A)
    (HB : TypedComputationEq D (A :: Γ) b b' T) :
    TypedComputationEq D Γ (b.inst x) (b'.inst y) (T.inst x) := by
  have HP := (HB.lam_body hΓ hA).app hΓ HX
  exact (TypedComputationEq.of_beta hΓ HP.defeq.hasType.1 VExpr.BetaRed.beta).symm.trans
    (HP.trans (TypedComputationEq.of_beta hΓ HP.defeq.hasType.2 VExpr.BetaRed.beta))

/-- A full-union computation from a typed source has a realized output whose
arbitrary typed instances are related by a computation chain. The output may
initially be raw; replay supplies its typing. This repairs substitution at the
level of chains without asserting an exact forward path to the instantiated
raw output. -/
theorem typed_compute_substitution_replay
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : Ctx.SubstEq env univs Δ σ σ Γ)
    (he : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧ proofErase Γ e' = out ∧
      TypedComputationEq D Δ (e.subst σ) (e'.subst σ) (T.subst σ) := by
  obtain ⟨e', HE, E⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) W.wf he rfl rfl R
  exact ⟨e', HE, E, (TypedComputationEq.step HE (E ▸ R)).subst heq hs hΔ W⟩

end Lean4Lean.VEnv.Strengthening
