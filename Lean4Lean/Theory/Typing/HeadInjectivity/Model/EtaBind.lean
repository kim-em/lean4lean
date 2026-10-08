import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjCtor
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjValid

/-! # The eta binding of rule clauses on majors of projection-registered families (D16)

Constructor spines of projection-registered families have only field observations (clause
`projCtor`), so the rule clauses identify the rule of such a major from the head type
(`EtaHead`) and bind its fields from the field observations of the major key (the eta
alternative of `RuleBind`). This file collects the facts used by the soundness of pattern rules
(`RuleSound.lean`, `ElimRuleSound.lean`) in that case:

* `MajorFam`: the static facts about the family of a rule's major that select the binding modes;
* `projctor_spine_inv`: field observations of a constructor spine come from the `projCtor`
  clause, with the field observation covered by an observation of the field argument;
* `eta_anchor_defeq`: an eta-bound anchor is definitionally equal to the field of the actual
  major (by `projIota`), which is the left-to-right direction of the binding. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The family `I` of the major of a pattern rule, with the major constructor `ctor`, the major
arguments `ms ++ fs.map .bvar` at the constructor levels `lsC`, in the rule instance at the
levels `ls`: either `I` is not projection-registered and `ctor` is not a projection
constructor (the constructor binding modes), or `I` is projection-registered with the
constructor `ctor`, the major is a full constructor application whose variable fields not bound
by the leading arguments are proper fields, and either the entry is never zero at the major's
levels (the eta binding) or every such field is a proof (the proof binding). -/
def MajorFam (env : VEnv) (U : Nat) (Δ Γ : List VExpr) (I ctor : Name)
    (doms lead ms : List VExpr) (fs : List Nat) (ls lsC : List VLevel) : Prop :=
  ((∀ info, ¬ env.projections I info) ∧ ¬ IsProjCtor env ctor) ∨
  ∃ info, env.projections I info ∧ ProjValid env I info ∧ info.ctorName = ctor ∧
    ms.length + fs.length = info.nparams + info.numFields ∧
    (∀ x j, fs[j]? = some x → (∀ i : Nat, lead[i]? ≠ some (.bvar x)) →
      info.nparams ≤ ms.length + j) ∧
    ((info.resultLevel.inst (lsC.map (·.inst ls))).IsNeverZero ∨
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs env U Δ v vS (binderTy doms ls x) τ →
          ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])

theorem wrapForalls_inj_len' : ∀ {ds ds' : List VExpr} {b b' : VExpr},
    ds.length = ds'.length → VExpr.wrapForalls ds b = VExpr.wrapForalls ds' b' → ds = ds' ∧ b = b'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | d :: ds, d' :: ds', _, _, hl, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.forallE.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, rfl⟩ := wrapForalls_inj_len' (Nat.succ.inj hl) h2
    exact ⟨by rw [h1], rfl⟩

/-- The head-type premise of a rule clause names the family of the head type's major domain. -/
theorem EtaHead.fam {T : VExpr} (h : EtaHead env I' ctor' T k)
    (eH : T = .wrapForalls dsH RH) (hlenH : dsH.length = k + 1)
    (hkH : dsH[k]? = some (.mkApps (.const I lsI) iargs)) :
    I' = I ∧ ∃ info : VProjectionInfo, env.projections I info ∧ info.ctorName = ctor' := by
  obtain ⟨info, dsH', RH', lsI', iargs', hp, hcn, eH', hlen', hk'⟩ := h
  obtain ⟨rfl, -⟩ := wrapForalls_inj_len' (by rw [hlenH, hlen']) (eH.symm.trans eH')
  rw [hkH] at hk'
  obtain ⟨rfl, -, -⟩ := mkApps_const_inj (Option.some.inj hk')
  exact ⟨rfl, info, hp, hcn⟩

/-- Field observations of a spine of a rigid constructor come from the `projCtor` clause: the
constructor is the constructor of the family, and the field observation is covered by an
observation of the field argument. -/
theorem projctor_spine_inv {σ : VExpr.Subst} {S : ObSets} (hrig : env.Rigid c)
    (h : Obs' σ S (.mkApps (.const c lsc) margs) (.fieldOb I i L k)) :
    ∃ info : VProjectionInfo, env.projections I info ∧ info.ctorName = c ∧
      ∃ a, margs[info.nparams + i]? = some a ∧ ∃ k', Obs' σ S a k' ∧ k' ≼ k := by
  obtain ⟨keys, hk, hw⟩ := wrap_of_obs_mkApps' h
  rcases Obs.const_iff.1 hw with ⟨_, _, keys', r', e, _, _, _, _, hr'⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r', e, _, _, _, _, _, hr', _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨fam, info, _, _, keys', r', e, hp, hcn, _, _, _, _, hend, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · obtain ⟨-, rfl⟩ := wrap_inj e trivial hr'.notApp
    rcases hr' with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; rfl) (hrig df hdf _)
  · have hrn : r'.NotApp := by
      rcases hr' with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨-, rfl⟩ := wrap_inj e trivial hrn
    rcases hr' with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig df hdf lsP)
  · obtain ⟨j, L', k₀, rfl, -, -, -, kj, hkj, hk₀⟩ := hend
    obtain ⟨rfl, e2⟩ := wrap_inj e trivial trivial
    cases e2
    have hil : info.nparams + i < keys.length := (List.getElem?_eq_some_iff.1 hkj).1
    obtain ⟨hil', _, hcov⟩ := forall₂_getElem hk _ hil
    have hkj' : keys[info.nparams + i] = kj := (List.getElem?_eq_some_iff.1 hkj).2
    rw [hkj'] at hcov
    obtain ⟨k', hk', l⟩ := hcov k hk₀
    exact ⟨info, hp, hcn, _, List.getElem?_eq_getElem hil', k', hk', l⟩
  · obtain ⟨-, h⟩ := wrap_inj e trivial trivial; cases h
  · obtain ⟨-, h⟩ := wrap_inj e trivial trivial; cases h

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **The eta anchor** (left to right): a member `z` of the class of the projections onto field
`i` of the major key's class `cm`, a typed class at `B`, is definitionally equal at `B` to the
field `a` of a constructor spine of the family in `cm`, when `a` has type `B` (by `projIota`). -/
theorem eta_anchor_defeq {I : Name} {info : VProjectionInfo} (hp : env.projections I info)
    {lsc : List VLevel} {margs : List VExpr} {B : VExpr} {cm : VExpr → Prop} {i : Nat}
    {z a : VExpr}
    (hTE : TypedElCls env U Δ (TyCls env U Δ B) (projCls env U Δ I i cm (TyCls env U Δ B)))
    (hz : projCls env U Δ I i cm (TyCls env U Δ B) z)
    (hM : cm (.mkApps (.const info.ctorName lsc) margs))
    (ha : margs[info.nparams + i]? = some a) (haT : env.HasType U Δ a B) :
    env.IsDefEq U Δ z a B := by
  have hpM : projCls env U Δ I i cm (TyCls env U Δ B)
      (.proj I i (.mkApps (.const info.ctorName lsc) margs)) := ⟨_, hM, ElCls.self⟩
  have h1 := hTE.defeq henv hΔ hz hpM
  have h2 := hTE.hasType henv hΔ hpM
  exact h1.trans (.projIota hp h2 ha haT)

end

end Model
end VEnv
end Lean4Lean
