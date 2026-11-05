import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInstantiationBinders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureTypeArgumentOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryPrimitiveSquare

/-! # Type instantiation joining for bodies that become types after substitution

A fresh neutral caller makes the generic computation type-valued. Once the
substituted body has a sort assignment, type-argument origins read its history
out of the joined calls. Certificate descent then removes the fresh caller.
The type-instantiation joining premise itself remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A common reduct of two neutral universe-to-universe calls gives a common
reduct of their type arguments. Read one branch, append its beta readout to the
other branch, then read that branch. Only pure beta argument inversion is used;
there is no assumption that arbitrary full-union joins compose. -/
theorem static_structure_neutral_type_argument_join_reflect
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort u))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort u) (.sort v)))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ A)) shared)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ B)) shared) :
    ∃ joint, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) joint ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ B) joint := by
  obtain ⟨A', _, RA, BA⟩ := static_structure_neutral_type_argument_origin heq hs hΓ hA hf RL
  obtain ⟨B', _, RB, BB⟩ := static_structure_neutral_type_argument_origin heq hs hΓ hB hf
    (RR.trans (.beta BA))
  obtain ⟨args, E, Hargs⟩ := BB.bvar_spine (args := [proofErase Γ A'])
  cases Hargs with
  | cons R Hnil =>
    cases Hnil
    have ER := (ProofShape.app.inj E).2
    exact ⟨proofErase Γ B', RA.trans (.beta (ER.symm ▸ R)), RB⟩

/-- The open type-instantiation premise also joins a computation of a body
that has arbitrary generic type but becomes type-valued after substitution.
A fresh neutral caller is inserted before the generic computation, instantiated
with it, and removed by certificate descent after type-argument readout. No
native certificate for the substituted argument or cast-elimination hypothesis
is required. This extends HJ; it does not prove HJ or its sufficiency. -/
theorem TypeInstantiationJoin.instN_of_instantiated_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hx : env.HasType univs Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (hb : env.HasType univs Γ₁ b T)
    (hbi : env.HasType univs Γ (b.inst x k) (.sort v))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₁)
      (proofErase Γ₁ b) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x k)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ₀ x) k) shared := by
  have hΓ := (W.wf henv.ordered hx hΓ₁).2
  obtain ⟨u, hT⟩ := hb.isType henv hΓ₁
  let F := VExpr.forallE T (.sort .zero)
  have hF : env.HasType univs Γ₁ F (.sort (.imax u (.succ .zero))) :=
    HasType.forallE hT (HasType.sort (by trivial))
  have hctx : OnCtx (F :: Γ₁) (env.IsType univs) := ⟨hΓ₁, _, hF⟩
  have hf : env.HasType univs (F :: Γ₁) (.bvar 0) (.forallE T.lift (.sort .zero)) := .bvar .zero
  have hC : ∀ {b}, env.HasType univs Γ₁ b T →
      env.HasType univs (F :: Γ₁) (.app (.bvar 0) b.lift) (.sort .zero) := by
    intro b hb
    exact hf.app (hb.weak henv.ordered)
  have EC : ∀ {b} (hb : env.HasType univs Γ₁ b T),
      proofErase (F :: Γ₁) (.app (.bvar 0) b.lift) =
        .app (.bvar 0) (proofErase (F :: Γ₁) b.lift) := by
    intro b hb
    rw [show proofErase (F :: Γ₁) (.app (.bvar 0) b.lift) = .app _ _ from
      if_neg (not_isProof_of_sort hctx (hC hb))]
    rw [show proofErase (F :: Γ₁) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_function_to_sort hctx hf)]
  obtain ⟨b', HB', EB'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ₁ hb rfl rfl RB
  have RL := static_structure_compute_under_domain heq hs (DomainSort.of_typed hΓ₁ hF) RB
  have EL := proofErase_liftN hΓ₁ hctx Ctx.LiftN.one hb
  have ER := proofErase_liftN hΓ₁ hctx Ctx.LiftN.one HB'.hasType.2
  rw [← EB', ← EL, ← ER] at RL
  have RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (F :: Γ₁))
      (proofErase (F :: Γ₁) (.app (.bvar 0) b.lift))
      (proofErase (F :: Γ₁) (.app (.bvar 0) b'.lift)) := by
    rw [EC hb, EC HB'.hasType.2]
    exact .app .refl RL
  obtain ⟨joint, JL, JR⟩ := HJ.instN heq hs hx W.succ hctx (hC hb) RC
  have EI := proofErase_instN hctx hx W.succ (hC HB'.hasType.2)
  rw [← EI] at JR
  have EX : ∀ b : VExpr, (VExpr.app (.bvar 0) b.lift).inst x (k+1) =
      .app (.bvar 0) (b.inst x k).lift := by
    intro b
    simp only [VExpr.inst, instVar, Nat.zero_lt_succ, ↓reduceIte, ← VExpr.lift_instN_lo]
  simp only [EX] at JL JR
  have hFI := hF.instN henv.ordered W hx
  have hctxI : OnCtx (F.inst x k :: Γ) (env.IsType univs) := ⟨hΓ, _, hFI⟩
  have hTS := ((hb.instN henv.ordered W hx).uniqU henv hΓ hbi).of_l henv hΓ
    (hT.instN henv.ordered W hx)
  have hFP := IsDefEq.forallEDF hTS (HasType.sort (l := .zero) (by trivial))
  have hfI : env.HasType univs (F.inst x k :: Γ) (.bvar 0)
      (.forallE (.sort v) (.sort .zero)) :=
    (hFP.weak henv.ordered).defeq (HasType.bvar .zero)
  have hB'i := (IsDefEq.trans_l henv hΓ hbi (IsDefEq.instN henv.ordered hx W HB')).hasType.2
  have ECI : ∀ {a} (ha : env.HasType univs Γ a (.sort v)),
      proofErase (F.inst x k :: Γ) (.app (.bvar 0) a.lift) =
        .app (.bvar 0) (proofErase (F.inst x k :: Γ) a.lift) := by
    intro a ha
    have ht := hfI.app (ha.weak henv.ordered)
    rw [show proofErase (F.inst x k :: Γ) (.app (.bvar 0) a.lift) = .app _ _ from
      if_neg (not_isProof_of_sort hctxI ht)]
    rw [show proofErase (F.inst x k :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_function_to_sort hctxI hfI)]
  rw [ECI hbi] at JL
  rw [ECI hB'i] at JR
  obtain ⟨shared, SL, SR⟩ := static_structure_neutral_type_argument_join_reflect heq hs hctxI
    (hbi.weak henv.ordered) (hB'i.weak henv.ordered) hfI JL JR
  rw [proofErase_liftN hΓ hctxI Ctx.LiftN.one hbi] at SL
  rw [proofErase_liftN hΓ hctxI Ctx.LiftN.one hB'i] at SR
  have HD : ErasedScopedPrimitiveCertificateDescent
      (ErasedStaticStructureEtaExpansionUnion D) (ErasedStaticStructureEtaExpansionUnion D) :=
    erased_static_structure_eta_expansion_union_certificate_descent heq hs
  obtain ⟨left, HL, LL, EE⟩ := proofErase_scoped_compute_certificate_descend
    HD hΓ hctxI Ctx.LiftN.one hbi rfl SL
  obtain ⟨right, HR, RR, EE'⟩ := proofErase_scoped_compute_certificate_descend
    HD hΓ hctxI Ctx.LiftN.one hB'i rfl SR
  have Ejoin := ProofShape.liftN_inj.1 (EE.trans EE'.symm)
  have Eout := proofErase_instN hΓ₁ hx W HB'.hasType.2
  rw [EB'] at Eout
  exact ⟨proofErase Γ left, LL, by simpa only [Eout, Ejoin] using RR⟩

/-- The generic body of a type-valued beta redex need not itself be a type.
HJ nevertheless joins direct beta contraction with any generic body history
followed by contraction. This handles the post-instantiation typing case;
arbitrary argument histories and composition of separate joins remain outside
this statement. -/
theorem TypeInstantiationJoin.type_valued_beta_body_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b T) (hx : env.HasType univs Γ x A)
    (ht : env.HasType univs Γ (.app (.lam A b) x) (.sort v))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ x)) shared := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  exact HJ.instN_of_instantiated_type heq hs hx Ctx.InstN.zero ⟨hΓ, u, hA⟩ hb
    (IsDefEq.trans_l henv hΓ ht (IsDefEq.beta hb hx)).hasType.2 RB

end Lean4Lean.VEnv.Strengthening
