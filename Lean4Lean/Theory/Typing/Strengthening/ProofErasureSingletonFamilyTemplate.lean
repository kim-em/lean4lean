import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonSlots

/-! # Closed erased templates for the two singleton family guards

The cast-bearing transported family is typed at generic occurrence arguments.
Its erasure therefore specializes from a fixed template; the major contributes
only a proof marker. No alignment of bare fields or checked prefix is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- The generic occurrence telescope used by both family templates. -/
def singletonOccurrenceDomains (S : SingletonLayout) (params : List VExpr) (E : PropElim) : List VExpr :=
  params ++ S.indices ++ [majorTy S params E]

/-- Fixed erased transported-family template, retaining its necessary casts. -/
noncomputable def erasedTransportedFamilyTemplate (S : SingletonLayout) (params : List VExpr)
    (E : PropElim) : ProofShape :=
  proofErase (singletonOccurrenceDomains S params E).reverse
    (transportedFamily S params E (genericPa S params) (genericIa S) (.bvar 0))

/-- Fixed erased requested-family template at the same occurrence telescope. -/
noncomputable def erasedRequestedFamilyTemplate (S : SingletonLayout) (params : List VExpr)
    (E : PropElim) : ProofShape :=
  proofErase (singletonOccurrenceDomains S params E).reverse
    (mkApps E.family (genericPa S params ++ genericIa S))

/-- The original generic transported family specializes exactly to an arbitrary
typed occurrence, before any definitional family conversion is assumed. -/
theorem transportedFamily_generic_inst (heq : env.HasCanonicalEq)
    (W : E.WF S params env univs) (hps : ps.length = params.length)
    (hidx : idx.length = S.indices.length) :
    (transportedFamily S params E (genericPa S params) (genericIa S) (.bvar 0)).instOuter
      (ps ++ idx ++ [m]) = transportedFamily S params E ps idx m := by
  simp only [instOuter_eq_subst]
  rw [transportedFamily_subst henv heq W W.genericCtx (by simp [genericPa])
    (W.genericArgs henv)]
  simp only [← instOuter_eq_subst, (generic_at hps hidx).1, (generic_at hps hidx).2]
  congr 1
  simp [instOuter_eq_subst, Subst.ofList]

/-- The requested family has the same exact generic specialization. -/
theorem requestedFamily_generic_inst (W : E.WF S params env univs)
    (hps : ps.length = params.length) (hidx : idx.length = S.indices.length) :
    (mkApps E.family (genericPa S params ++ genericIa S)).instOuter (ps ++ idx ++ [m]) =
      mkApps E.family (ps ++ idx) := by
  have hhead : E.family.instOuter (ps ++ idx ++ [m]) = E.family := by
    rw [instOuter_eq_subst]
    exact W.family_closed.subst_eq .zero
  rw [instOuter_mkApps, hhead, List.map_append,
    (generic_at hps hidx).1, (generic_at hps hidx).2]

/-- The transported-family erasure depends on erased parameters and indices;
the actual major proof is replaced by one proof marker in the substitution. -/
theorem proofErase_transportedFamily_template (heq : env.HasCanonicalEq)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (singletonOccurrenceDomains S params E) (ps ++ idx ++ [m])) :
    proofErase Γ (transportedFamily S params E ps idx m) =
      (erasedTransportedFamilyTemplate S params E).instOuter
        (ps.map (proofErase Γ) ++ idx.map (proofErase Γ) ++ [.proof]) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1
    simp only [singletonOccurrenceDomains, List.length_append, List.length_singleton] at this
    omega
  have hgeneric := (transportedFamily_typings henv heq W W.genericCtx
    (by simp [genericPa]) (W.genericArgs henv)).1
  have hm : proofErase Γ m = .proof :=
    proofErase_eq_proof.2 ⟨_, W.major_typed hps hargs, W.family_prop henv hps hargs⟩
  rw [← transportedFamily_generic_inst heq W hps hidx,
    proofErase_instOuter hΓ W.genericCtx hgeneric hargs]
  simp only [List.map_append, List.map_cons, List.map_nil, hm,
    erasedTransportedFamilyTemplate, singletonOccurrenceDomains]

/-- The requested-family erasure uses precisely the same erased provider list. -/
theorem proofErase_requestedFamily_template (W : E.WF S params env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (singletonOccurrenceDomains S params E) (ps ++ idx ++ [m])) :
    proofErase Γ (mkApps E.family (ps ++ idx)) =
      (erasedRequestedFamilyTemplate S params E).instOuter
        (ps.map (proofErase Γ) ++ idx.map (proofErase Γ) ++ [.proof]) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1
    simp only [singletonOccurrenceDomains, List.length_append, List.length_singleton] at this
    omega
  have hgeneric := W.family_prop henv (by simp [genericPa]) (W.genericArgs henv)
  have hm : proofErase Γ m = .proof :=
    proofErase_eq_proof.2 ⟨_, W.major_typed hps hargs, W.family_prop henv hps hargs⟩
  rw [← requestedFamily_generic_inst (m := m) W hps hidx,
    proofErase_instOuter hΓ W.genericCtx hgeneric hargs]
  simp only [List.map_append, List.map_cons, List.map_nil, hm,
    erasedRequestedFamilyTemplate, singletonOccurrenceDomains]

/-- Equal erased providers determine both guard endpoints across arbitrary
well-formed occurrence contexts. The two major proofs need not be related. -/
theorem proofErase_singleton_family_providers_congr (heq : env.HasCanonicalEq)
    (W : E.WF S params env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (hps : ps.length = params.length) (hps' : ps'.length = params.length)
    (hargs : TelInst env univs Γ (singletonOccurrenceDomains S params E) (ps ++ idx ++ [m]))
    (hargs' : TelInst env univs Γ' (singletonOccurrenceDomains S params E) (ps' ++ idx' ++ [m']))
    (HP : ps.map (proofErase Γ) = ps'.map (proofErase Γ'))
    (HI : idx.map (proofErase Γ) = idx'.map (proofErase Γ')) :
    proofErase Γ (transportedFamily S params E ps idx m) =
        proofErase Γ' (transportedFamily S params E ps' idx' m') ∧
      proofErase Γ (mkApps E.family (ps ++ idx)) =
        proofErase Γ' (mkApps E.family (ps' ++ idx')) := by
  rw [proofErase_transportedFamily_template heq W hΓ hps hargs,
    proofErase_transportedFamily_template heq W hΓ' hps' hargs',
    proofErase_requestedFamily_template W hΓ hps hargs,
    proofErase_requestedFamily_template W hΓ' hps' hargs', HP, HI]
  exact ⟨rfl, rfl⟩

end Lean4Lean.VEnv.Strengthening
