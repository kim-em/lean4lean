import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.ProjTyping

/-! # Projection field types under substitution

Two companions of `VEnv.proj_typed` for a projection-registered structure:
* the field type `fieldType` commutes with an arbitrary substitution
  (`VEnv.ProjTele.fieldType_subst`);
* at a typed major `w`, the substitutions instantiating the constructor telescope at the
  parameters and the projections of `w`, resp. of a definitionally equal `w'`, are
  definitionally equal along the telescope (`VEnv.ProjTele.substEq_projs`). -/

namespace Lean4Lean
open VExpr

/-- Two substitutions agreeing below the closure bound act identically (a local copy of
`VExpr.subst_congr_closedN`, which lives outside this file's import scope). -/
private theorem subst_congr_closedN' {e : VExpr} (he : e.ClosedN k) {σ σ' : VExpr.Subst}
    (h : ∀ i < k, σ i = σ' i) : e.subst σ = e.subst σ' := by
  induction e generalizing k σ σ' with (simp [VExpr.ClosedN] at he; simp only [VExpr.subst])
  | bvar i => exact h _ he
  | app _ _ ih1 ih2 => rw [ih1 he.1 h, ih2 he.2 h]
  | proj _ _ _ ihe => rw [ihe he h]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    rw [ih1 he.1 h, ih2 he.2 (σ' := σ'.lift)]
    intro i hi
    cases i with
    | zero => rfl
    | succ i => simp only [VExpr.Subst.lift]; rw [h i (by omega)]

theorem VExpr.argSubst_comp_lt (as : List VExpr) (σ : VExpr.Subst) {m : Nat}
    (h : m < as.length) :
    (argSubst as m).subst σ = argSubst (as.map (·.subst σ)) m := by
  rw [argSubst_lt _ h, argSubst_lt _ (by simpa using h)]
  simp

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem projsOf_subst (S : Name) (w : VExpr) (j : Nat) (σ : VExpr.Subst) :
    (projsOf S w j).map (·.subst σ) = projsOf S (w.subst σ) j := by
  simp [projsOf, VExpr.subst]


/-- The domains of a projection telescope are closed at their depth. -/
theorem ProjTele.closedN_dom (henv : env.Ordered) {S : Name} {info : VProjectionInfo}
    {ls : List VLevel} {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    (k : Nat) (hk : k < D.length) : (D[k]).ClosedN k := by
  obtain ⟨u, hu⟩ := T.doms k hk
  have := hu.closedN henv (CtxWF.closed henv (T.ctx k (by omega)))
  simpa [Nat.min_eq_left (Nat.le_of_lt hk)] using this

/-- The instantiated field domain commutes with substitution. -/
theorem ProjTele.dom_subst (henv : env.Ordered) {S : Name} {info : VProjectionInfo}
    {ls : List VLevel} {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    {ps : List VExpr} (hpl : ps.length = info.nparams) (w : VExpr) {j : Nat}
    (hj : info.nparams + j < D.length) (σ : VExpr.Subst) :
    ((D[info.nparams + j]).subst (VExpr.argSubst (ps ++ projsOf S w j))).subst σ =
      (D[info.nparams + j]).subst
        (VExpr.argSubst (ps.map (·.subst σ) ++ projsOf S (w.subst σ) j)) := by
  rw [VExpr.subst_subst, ← projsOf_subst, ← List.map_append]
  apply subst_congr_closedN' (T.closedN_dom henv _ hj)
  intro i hi
  exact VExpr.argSubst_comp_lt _ σ (by simp [projsOf, hpl]; omega)

/-- **`fieldType` commutes with substitution.** -/
theorem ProjTele.fieldType_subst (henv : env.Ordered) {S : Name} {info : VProjectionInfo}
    {ls : List VLevel} {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    (hlen : ls.length = info.uvars) {ps : List VExpr} (hpl : ps.length = info.nparams)
    {w : VExpr} {j : Nat} (hj : info.nparams + j < D.length) (σ : VExpr.Subst) {F : VExpr}
    (hF : info.fieldType S ls ps j w = some F) :
    info.fieldType S ls (ps.map (·.subst σ)) j (w.subst σ) = some (F.subst σ) := by
  rw [T.fieldType hlen hpl w hj, Option.some.injEq] at hF
  subst hF
  rw [T.fieldType hlen (by simpa using hpl) _ hj, T.dom_subst henv hpl w hj σ]

/-- **The projection telescope at definitionally equal majors.** Under the hypotheses of
`proj_typed`, the substitutions instantiating the first `info.nparams + j` binders of the
constructor telescope at the parameters and the first `j` projections of `w`, resp. of `w'`,
are definitionally equal along that prefix. -/
theorem ProjTele.substEq_projs (henv : env.Ordered) {Δ : List VExpr}
    (hΔ : OnCtx Δ (env.IsType U))
    {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hcl : info.ctorType.Closed) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = info.uvars) (hnz : (info.resultLevel.inst ls).IsNeverZero)
    {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    {ps : List VExpr} {Tail : VExpr} (hps : ArgsTyped env U Δ (info.ctorType.instL ls) ps Tail)
    (hpl : ps.length = info.nparams) {w : VExpr} {idx' : List VExpr}
    (hidx : idx'.length = info.nindices)
    (hw : env.HasType U Δ w (VExpr.mkApps (.const S ls) (ps ++ idx')))
    {w' : VExpr} (hww' : env.IsDefEq U Δ w w' (VExpr.mkApps (.const S ls) (ps ++ idx'))) :
    ∀ j, j ≤ info.numFields →
      Ctx.SubstEq env U Δ (VExpr.argSubst (ps ++ projsOf S w j))
        (VExpr.argSubst (ps ++ projsOf S w' j)) (D.take (info.nparams + j)).reverse := by
  obtain ⟨c, lsR, args, hR0⟩ := T.head
  have hR0' : ∀ (σ : VExpr.Subst) A B, R0.subst σ ≠ .forallE A B := by
    rw [hR0]; exact subst_mkApps_const_ne_forallE c lsR args
  have hT : info.ctorType.instL ls = (VExpr.wrapForalls (D.drop ([] : List VExpr).length) R0).subst
      (VExpr.argSubst []) := by
    rw [T.shape]; exact VExpr.subst_id.symm
  have hps' := hps
  rw [hT] at hps'
  obtain ⟨hle, W0, -⟩ := ArgsTyped.substEq T.doms hR0' ps [] .nil (by simp) hps'
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hle W0
  have L2 := proj_typed henv hΔ hp hcl hls hlen hnz T hps hpl hidx hw
  rw [T.numFields] at L2 ⊢
  intro j
  induction j with
  | zero => intro _; simpa [projsOf, ← hpl] using W0
  | succ j ih =>
    intro hj
    have W := ih (by omega)
    have hk : info.nparams + j < D.length := by omega
    obtain ⟨u, hu⟩ := T.doms _ hk
    obtain ⟨F, hft, -, -, hcong⟩ := L2 j (by omega)
    rw [T.fieldType hlen hpl w hk, Option.some.injEq] at hft
    subst hft
    rw [projsOf_succ, projsOf_succ, ← List.append_assoc, ← List.append_assoc,
      show info.nparams + (j + 1) = (info.nparams + j) + 1 by omega,
      List.take_succ_eq_append_getElem hk, List.reverse_append, List.reverse_singleton,
      List.singleton_append, VExpr.argSubst_append_one, VExpr.argSubst_append_one]
    exact .cons (by rw [VExpr.Subst.cons_tail, VExpr.Subst.cons_tail]; exact W) hu
      (by rw [VExpr.Subst.cons_head, VExpr.Subst.cons_head, VExpr.Subst.cons_tail]
          exact hcong w' hww')

end VEnv
end Lean4Lean
