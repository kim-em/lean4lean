import Lean4Lean.Theory.Typing.Strengthening.ProofErasureInstantiationProofDischarge
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryPrimitiveSquare

/-! # Type-valued cast templates for bodies with an arbitrary generic type

An auxiliary equality proof makes a body into a type-valued template before
instantiation. The open type-instantiation premise then joins the instantiated
casts. Removing these casts is a separate obligation, not supplied here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A computation of the payload extends through a fixed canonical cast whose
target is a sort. The payload itself need not be a type in the generic context.
No native certificate for the payload is assumed. -/
theorem proofErase_typeCast_payload_compute
    (heq : env.HasCanonicalEq) (hv : v.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ v)))
    (he : env.HasType univs Γ e (eqApp (.succ (.succ v)) (.sort (.succ v)) T (.sort v)))
    (hb : env.HasType univs Γ b T) (hb' : env.HasType univs Γ b' T)
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (proofErase Γ b')) :
    ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (typeCast (.succ v) T (.sort v) e b))
      (proofErase Γ (typeCast (.succ v) T (.sort v) e b')) := by
  have HC := HasType.typeCast (u := .succ v) henv.ordered heq hv hT (HasType.sort hv) he hb
  have HC' := HasType.typeCast (u := .succ v) henv.ordered heq hv hT (HasType.sort hv) he hb'
  have E := proofErase_mkApps hΓ
    (args := [.sort (.succ v), T, castMotive (.succ v) T, b, .sort v, e])
    HC (not_isProof_of_sort hΓ HC)
  have E' := proofErase_mkApps hΓ
    (args := [.sort (.succ v), T, castMotive (.succ v) T, b', .sort v, e])
    HC' (not_isProof_of_sort hΓ HC')
  change proofErase Γ (typeCast (.succ v) T (.sort v) e b) = _ at E
  change proofErase Γ (typeCast (.succ v) T (.sort v) e b') = _ at E'
  rw [E, E']
  exact ScopedCompute.mkApps .refl
    (.cons .refl (.cons .refl (.cons .refl (.cons R (.cons .refl (.cons .refl .nil))))))

omit [Params] in
private theorem cast_inst (u : VLevel) (T e b x : VExpr) (k : Nat) :
    (typeCast u T (.sort v) e b).inst x k =
      typeCast u (T.inst x k) (.sort v) (e.inst x k) (b.inst x k) := by
  simp only [typeCast, eqRecApp, castMotive, eqApp, VExpr.inst,
    ← VExpr.lift_instN_lo]
  rfl

/-- One arbitrary instantiation join and exact discharge of an auxiliary Eq
proof join casts of a generic body and any of its computational outputs. The
body need not be type-valued before substitution. The conclusion deliberately
retains both casts: neither their removal nor joining of the uncast payloads
follows from this theorem. `TypeInstantiationJoin` remains an open premise. -/
theorem TypeInstantiationJoin.cast_template
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hT : env.HasType univs (A :: Γ) T (.sort (.succ v)))
    (hb : env.HasType univs (A :: Γ) b T) (hx : env.HasType univs Γ x A)
    (hp : env.HasType univs Γ p
      (eqApp (.succ (.succ v)) (.sort (.succ v)) (T.inst x) (.sort v)))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ∃ b', env.IsDefEq univs (A :: Γ) b b' T ∧ proofErase (A :: Γ) b' = out ∧
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (typeCast (.succ v) (T.inst x) (.sort v) p (b.inst x))) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (typeCast (.succ v) (T.inst x) (.sort v) p (b'.inst x))) shared := by
  let P := eqApp (.succ (.succ v)) (.sort (.succ v)) T (.sort v)
  have hP : env.HasType univs (A :: Γ) P (.sort .zero) :=
    HasType.eqApp heq hv (HasType.sort hv) hT (HasType.sort hv)
  have hctx : OnCtx (P :: A :: Γ) (env.IsType univs) := ⟨hΓA, .zero, hP⟩
  have he : env.HasType univs (P :: A :: Γ) (.bvar 0)
      (eqApp (.succ (.succ v)) (.sort (.succ v)) T.lift (.sort v)) := by
    simpa only [P, eqApp, VExpr.lift, VExpr.liftN] using
      (HasType.bvar (U := univs) (Γ := P :: A :: Γ) .zero)
  let C (b : VExpr) := typeCast (.succ v) T.lift (.sort v) (.bvar 0) b.lift
  have hC : ∀ {b}, env.HasType univs (A :: Γ) b T →
      env.HasType univs (P :: A :: Γ) (C b) (.sort v) := by
    intro b hb
    exact HasType.typeCast (u := .succ v) henv.ordered heq hv (hT.weak henv.ordered)
      (HasType.sort hv) he (hb.weak henv.ordered)
  obtain ⟨b', HB', EB'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb rfl rfl RB
  have RL := static_structure_compute_under_domain heq hs (DomainSort.of_typed hΓA hP) RB
  have EL := proofErase_liftN hΓA hctx Ctx.LiftN.one hb
  have ER := proofErase_liftN hΓA hctx Ctx.LiftN.one HB'.hasType.2
  rw [← EB', ← EL, ← ER] at RL
  have RC := proofErase_typeCast_payload_compute heq hv hctx (hT.weak henv.ordered)
    he (hb.weak henv.ordered) (HB'.hasType.2.weak henv.ordered) RL
  have hp' : env.HasType univs Γ p (P.inst x) := by
    simpa only [P, eqApp, VExpr.inst] using hp
  obtain ⟨shared, JL, JR⟩ := HJ.inst_then_proof heq hs hΓ hctx hP (hC hb) hx hp' RC
  have W : Ctx.InstN Γ x A 1 (P :: A :: Γ) (P.inst x :: Γ) := Ctx.InstN.zero.succ
  have EI := proofErase_instN hctx hx W (hC HB'.hasType.2)
  have EP := proofErase_instN ((W.wf henv.ordered hx hctx).2) hp' Ctx.InstN.zero
    ((hC HB'.hasType.2).instN henv.ordered W hx)
  have hpProof : IsProof Γ p := ⟨P.inst x, hp', hP.instN henv.ordered Ctx.InstN.zero hx⟩
  rw [EI, proofErase_eq_proof.2 hpProof] at EP
  rw [← EP] at JR
  have EC : ∀ b, ((C b).inst x 1).inst p =
      typeCast (.succ v) (T.inst x) (.sort v) p (b.inst x) := by
    intro b
    simp only [C, cast_inst, ← VExpr.lift_instN_lo, VExpr.inst_lift,
      VExpr.inst, instVar, Nat.zero_lt_succ, Nat.not_lt_zero, ↓reduceIte, VExpr.liftN_zero]
  exact ⟨b', HB', EB', shared, by simpa only [EC] using JL, by simpa only [EC] using JR⟩

/-- If the substituted body is a type, uniqueness supplies the auxiliary Eq
proof as a reflexivity term with a converted endpoint. Thus cast-template
joining needs no independent equality witness. Both casts remain in the
conclusion; ordinary endpoint conversion is not computational cast removal. -/
theorem TypeInstantiationJoin.cast_template_of_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HJ : TypeInstantiationJoin D)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hT : env.HasType univs (A :: Γ) T (.sort (.succ v)))
    (hb : env.HasType univs (A :: Γ) b T) (hx : env.HasType univs Γ x A)
    (hbi : env.HasType univs Γ (b.inst x) (.sort v))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ∃ b', env.IsDefEq univs (A :: Γ) b b' T ∧ proofErase (A :: Γ) b' = out ∧
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (typeCast (.succ v) (T.inst x) (.sort v)
            (eqReflApp (.succ (.succ v)) (.sort (.succ v)) (T.inst x)) (b.inst x))) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (typeCast (.succ v) (T.inst x) (.sort v)
            (eqReflApp (.succ (.succ v)) (.sort (.succ v)) (T.inst x)) (b'.inst x))) shared := by
  have hTI := hT.instN henv.ordered Ctx.InstN.zero hx
  have hBI := hb.instN henv.ordered Ctx.InstN.zero hx
  have hTS := (hBI.uniqU henv hΓ hbi).of_l henv hΓ hTI
  have hrefl := HasType.eqReflApp (w := .succ (.succ v)) heq hv (HasType.sort hv) hTI
  have hEP := IsDefEq.eqApp_r (w := .succ (.succ v)) heq hv (HasType.sort hv) hTI hTS
  exact HJ.cast_template heq hs hv hΓ hΓA hT hb hx (hEP.defeq hrefl) RB

end Lean4Lean.VEnv.Strengthening
