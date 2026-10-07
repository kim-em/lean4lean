import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineTele

/-! # Field observations of constructor spines of projection-registered families (stage C)

The construction of the field observations of a constructor spine `mk ps fs` (needed by
`projIota`, and by the eta binding mode of rules on projection-registered families) works in the
constructor's telescope: typed keys along the telescope (`TeleKeys`) wind up to a typed
observation of the constant (`tele_wind`), with the value class of the codomain the element
class of the constructor applied to the anchors. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The anchors of a chain of typed keys. -/
theorem TeleKeys.anchors (h : TeleKeys env U Δ σ S ds keys σ' S') :
    ∃ ys : List VExpr, σ' = ys.foldl VExpr.Subst.cons σ ∧ ys.length = ds.length ∧
      List.Forall₂ (fun (k : Key) y => k.2.1 y) keys ys := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, .nil⟩
  | @cons c y K σ S A ds keys σ' S' hc hy _ _ _ ih =>
    obtain ⟨ys, e, hl, hk⟩ := ih
    exact ⟨y :: ys, e, by simp [hl], .cons hy hk⟩

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The class of applications of the members of a function's class to the members of an
argument's class. -/
theorem appCls_eq (hf : env.HasType U Δ f (.forallE A B)) (ha : env.HasType U Δ a A) :
    appCls env U Δ (ElCls env U Δ (TyCls env U Δ (.forallE A B)) f)
        (ElCls env U Δ (TyCls env U Δ A) a) (TyCls env U Δ (B.inst a)) =
      ElCls env U Δ (TyCls env U Δ (B.inst a)) (.app f a) := by
  funext z; apply propext; constructor
  · rintro ⟨w, y, hw, hy, hz⟩
    have hfw := ElCls.collapse henv hΔ hf TyCls.self hw
    have hay := ElCls.collapse henv hΔ ha TyCls.self hy
    have happ : env.IsDefEq U Δ (.app f a) (.app w y) (B.inst a) := IsDefEq.appDF hfw hay
    rw [ElCls.eq_of_defeq TyCls.self happ]; exact hz
  · intro hz; exact ⟨_, _, ElCls.self, ElCls.self, hz⟩

/-- **Winding up a chain of typed keys**: an observation typed, at the class of the function
applied to the anchors, at codomain observations of the chain, wrapped in the keys, is typed at
observations of the telescope, at the class of the function. -/
theorem tele_wind (h : TeleKeys env U Δ σ S ds keys σ' S') :
    ∀ (f : VExpr), env.HasType U Δ f ((VExpr.wrapForalls ds R).subst σ) →
    ∃ ys : List VExpr, σ' = ys.foldl VExpr.Subst.cons σ ∧ ys.length = ds.length ∧
      List.Forall₂ (fun (k : Key) y => k.2.1 y) keys ys ∧
      env.HasType U Δ (VExpr.mkApps f ys) (R.subst σ') ∧
      ∀ o τc, (∀ τ ∈ τc, Obs' σ' S' R τ) →
        TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (R.subst σ')) (VExpr.mkApps f ys)) o τc →
        ∃ τ₀, (∀ τ ∈ τ₀, Obs' σ S (VExpr.wrapForalls ds R) τ) ∧
          TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ ((VExpr.wrapForalls ds R).subst σ)) f)
            (wrap keys o) τ₀ := by
  induction h with
  | nil =>
    intro f hf
    exact ⟨[], rfl, rfl, .nil, hf, fun o τc hτc ho => ⟨τc, hτc, ho⟩⟩
  | @cons c y K σ S A ds keys σ' S' hc hy hK hb _ ih =>
    intro f hf
    have hf' : env.HasType U Δ f (.forallE (A.subst σ) ((VExpr.wrapForalls ds R).subst σ.lift)) :=
      hf
    have hyA := hc.hasType henv hΔ hy
    have happ : env.HasType U Δ (.app f y) ((VExpr.wrapForalls ds R).subst (σ.cons y)) := by
      have := IsDefEq.appDF hf' hyA
      rwa [VExpr.subst_lift_inst] at this
    obtain ⟨ys, e, hl, hk, hg, hwind⟩ := ih (.app f y) happ
    refine ⟨y :: ys, e, by simp [hl], .cons hy hk, hg, fun o τc hτc ho => ?_⟩
    obtain ⟨τ₀, h1, h2⟩ := hwind o τc hτc ho
    obtain ⟨τk, hτk, hkk⟩ := TypedAt.merge hK
    obtain ⟨τs, h3, h4⟩ := pi_list hc hy hτk hkk hb h1
    refine ⟨τs, h3, h4 _ _ ?_⟩
    obtain ⟨_, _, _, ec⟩ := hc.mem henv hΔ hy
    rw [ec, ← VExpr.subst_lift_inst, show (VExpr.wrapForalls (A :: ds) R).subst σ =
      .forallE (A.subst σ) ((VExpr.wrapForalls ds R).subst σ.lift) from rfl,
      appCls_eq henv hΔ hf' hyA, VExpr.subst_lift_inst]
    exact h2

/-- **The field classes of a constructor spine** (by L3): the projections onto field `i` of
the class of a constructor spine of a never-zero projection-registered structure form the
class of the field. -/
theorem ctor_projCls {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hcl : info.ctorType.Closed) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = info.uvars) (hnz : (info.resultLevel.inst ls).IsNeverZero)
    {doms idx : List VExpr}
    (hshape : info.ctorType = VExpr.wrapForalls doms
      (VExpr.mkApps (.const S (VLevel.params info.uvars))
        ((List.range info.nparams).reverse.map
            (fun i => VExpr.bvar (doms.length - info.nparams + i)) ++ idx)))
    (hidx : idx.length = info.nindices) (hwf : env.IsType info.uvars [] info.ctorType)
    (hctor : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩)
    {ps fs : List VExpr} {R : VExpr}
    (hargs : ArgsTyped env U Δ (info.ctorType.instL ls) (ps ++ fs) R)
    (hpl : ps.length = info.nparams) (hfl : fs.length = info.numFields)
    {i : Nat} (hi : i < fs.length) :
    env.HasType U Δ (VExpr.mkApps (.const info.ctorName ls) (ps ++ fs))
      (VExpr.mkApps (.const S ls)
        (ps ++ idx.map fun e => (e.instL ls).subst (VExpr.argSubst (ps ++ fs)))) ∧
    ∃ F, info.fieldType S ls ps i (VExpr.mkApps (.const info.ctorName ls) (ps ++ fs)) = some F ∧
      env.IsDefEq U Δ (.proj S i (VExpr.mkApps (.const info.ctorName ls) (ps ++ fs))) fs[i] F ∧
      projCls env U Δ S i
        (ElCls env U Δ (TyCls env U Δ (VExpr.mkApps (.const S ls)
          (ps ++ idx.map fun e => (e.instL ls).subst (VExpr.argSubst (ps ++ fs)))))
          (VExpr.mkApps (.const info.ctorName ls) (ps ++ fs))) (TyCls env U Δ F) =
        ElCls env U Δ (TyCls env U Δ F) fs[i] := by
  obtain ⟨hmk, hall⟩ := proj_spine henv hΔ hp hcl hls hlen hnz hshape hidx hwf hctor hargs hpl hfl
  obtain ⟨F, hF, hpty, hdef⟩ := hall i hi
  refine ⟨hmk, F, hF, hdef, ?_⟩
  obtain ⟨fl, hFs⟩ := hpty.isType henv hΔ
  have hidx' : (idx.map fun e => (e.instL ls).subst (VExpr.argSubst (ps ++ fs))).length =
      info.nindices := by simp [hidx]
  funext z; apply propext; constructor
  · rintro ⟨w, hw, hz⟩
    have hmw := ElCls.collapse henv hΔ hmk TyCls.self hw
    have hpw : env.IsDefEq U Δ (.proj S i (VExpr.mkApps (.const info.ctorName ls) (ps ++ fs)))
        (.proj S i w) F := .projDF hp hls hlen hpl hidx' hF hFs hmk hmw hcl (.inl hnz)
    rw [ElCls.eq_of_defeq TyCls.self hdef.symm, ElCls.eq_of_defeq TyCls.self hpw]
    exact hz
  · intro hz
    exact ⟨_, ElCls.self, by rw [ElCls.eq_of_defeq TyCls.self hdef]; exact hz⟩

end

end Model
end VEnv
end Lean4Lean
