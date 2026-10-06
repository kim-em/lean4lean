import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleSound

/-! # The quotient rule as a pattern rule (stage A2)

The syntactic facts of `quotDefEq` needed by `sound_pat`: its pattern
(`Quot.lift α r β f c (Quot.mk α r a) ≡ f a`, lead `α r β f c`, major `Quot.mk α r a` with
field `a`), the family `Quot` of the major domain of `Quot.lift`'s type, and, at levels at
which `Quot` is a proposition (mode C), the propositional typing of the field `a`. They
hold whenever the quotient constants are the ones installed by `addQuot`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The leading lambdas of a term. -/
def lamDoms : VExpr → List VExpr
  | .lam d b => d :: lamDoms b
  | _ => []

def quotDoms : List VExpr := lamDoms quotDefEq.lhs

def quotLead : List VExpr := [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]

theorem quotDefEq_lhs : quotDefEq.lhs = .wrapLams quotDoms (.mkApps
    (.const `Quot.lift [.param 0, .param 1])
    (quotLead ++ [.mkApps (.const `Quot.mk [.param 0]) ([.bvar 5, .bvar 4] ++ [0].map .bvar)])) :=
  rfl

theorem quotDefEq_rhs : quotDefEq.rhs = .wrapLams quotDoms (.app (.bvar 2) (.bvar 0)) := rfl

theorem quotDefEq_ctorMajor : quotDefEq.HasConstructorMajor ``Quot.mk :=
  ⟨.mkApps (.const `Quot.lift [.param 0, .param 1]) quotLead, [.param 0],
    [.bvar 5, .bvar 4, .bvar 0], rfl⟩

theorem quotDoms_length : quotDoms.length = 6 := rfl

theorem quot_cov : ∀ x < quotDoms.length, VExpr.bvar x ∈ quotLead ∨ x ∈ [0] := by
  intro x hx; rw [quotDoms_length] at hx
  match x, hx with
  | 0, _ => exact .inr (by simp)
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => exact .inl (by simp [quotLead])

/-- The quotient constants as installed by `addQuot`. -/
def QuotConsts (env : VEnv) : Prop :=
  env.constants ``Quot = some quotConst ∧ env.constants ``Quot.mk = some quotMkConst ∧
    env.constants ``Quot.lift = some quotLiftConst

def quotLiftDoms : List VExpr := [.sort (.param 0),
  .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort (.param 1),
  .forallE (.bvar 2) (.bvar 1),
  .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
    (.app (.app (.app (.const `Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
      (.app (.bvar 3) (.bvar 1))))),
  .mkApps (.const `Quot [.param 0]) [.bvar 4, .bvar 3]]

theorem quotLiftConst_type : quotLiftConst.type = .wrapForalls quotLiftDoms (.bvar 3) := rfl

theorem quotConst_type : quotConst.type =
    .wrapForalls [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))]
      (.sort (.param 0)) := rfl

theorem quot_headFam (hq : QuotConsts env) (hrig : env.Rigid ``Quot) :
    HeadFam env ``Quot.lift quotLead.length ``Quot.mk :=
  ⟨_, _, _, _, _, _, _, _, _, hq.2.2, quotLiftConst_type, rfl, rfl, hq.1, quotConst_type, rfl,
    hrig, _, _, hq.2.1, rfl⟩

theorem wrapForalls_inj_len : ∀ {ds ds' : List VExpr} {b b' : VExpr}, ds.length = ds'.length →
    VExpr.wrapForalls ds b = VExpr.wrapForalls ds' b' → ds = ds' ∧ b = b'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | d :: ds, d' :: ds', _, _, hl, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons] at h
    injection h with h1 h2
    obtain ⟨rfl, rfl⟩ := wrapForalls_inj_len (Nat.succ.inj hl) h2
    exact ⟨by rw [h1], rfl⟩

theorem MajorSort.unique (h1 : MajorSort env n k ls ℓ₁) (h2 : MajorSort env n k ls ℓ₂) :
    ℓ₁ = ℓ₂ := by
  obtain ⟨ci, dsH, RH, I, lsI, iargs, cI, dsI, w, hci, eH, hl, hk, hI, hIty, hIl, rfl⟩ := h1
  obtain ⟨ci', dsH', RH', I', lsI', iargs', cI', dsI', w', hci', eH', hl', hk', hI', hIty', hIl',
    rfl⟩ := h2
  cases hci.symm.trans hci'
  obtain ⟨rfl, -⟩ := wrapForalls_inj_len (hl.trans hl'.symm) (eH.symm.trans eH')
  rw [hk] at hk'; injection hk' with hk'
  obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj hk'
  cases hI.symm.trans hI'
  obtain ⟨-, e⟩ := wrapForalls_inj_len (hIl.trans hIl'.symm) (hIty.symm.trans hIty')
  injection e with e; subst e; rfl

theorem quot_majorSort (hq : QuotConsts env) :
    MajorSort env ``Quot.lift quotLead.length ls ((VLevel.param 0).inst ls).eval :=
  ⟨_, _, _, _, _, _, _, _, _, hq.2.2, quotLiftConst_type, rfl, rfl, hq.1, quotConst_type, rfl,
    by simp [VLevel.inst]⟩

theorem quot_lead_x (hx : x < quotDoms.length)
    (hnb : ∀ i : Nat, quotLead[i]? ≠ some (VExpr.bvar x)) : x = 0 := by
  rw [quotDoms_length] at hx
  match x, hx with
  | 0, _ => rfl
  | 1, _ => exact absurd rfl (hnb 4)
  | 2, _ => exact absurd rfl (hnb 3)
  | 3, _ => exact absurd rfl (hnb 2)
  | 4, _ => exact absurd rfl (hnb 1)
  | 5, _ => exact absurd rfl (hnb 0)

theorem quot_binderTy0 : binderTy quotDoms ls 0 = .bvar 5 := rfl

theorem quot_binderTy5 : binderTy quotDoms ls 5 = .sort ((VLevel.param 0).inst ls) := rfl

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- In mode C (the quotient is a proposition at `ls`), the field `a` is a proof. -/
theorem quot_pf (hq : QuotConsts env) (hlsw : ∀ l ∈ ls, l.WF U) :
    RuleMode env ``Quot.lift quotLead.length ls true → ∀ x < quotDoms.length,
      (∀ i : Nat, quotLead[i]? ≠ some (VExpr.bvar x)) →
      ∀ v vS, Ctx.SubstEq env U Δ v v ((quotDoms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((quotDoms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy quotDoms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy quotDoms ls x) τ → TypedOb env U Δ τ [.sort fun _ => 0] := by
  intro hmode x hx hnb v vS Wv tvv
  obtain rfl := quot_lead_x hx hnb
  obtain ⟨ℓ, hms, hℓ⟩ := hmode
  have e0 : ((VLevel.param 0).inst ls).eval = fun _ => 0 := by
    rw [hms.unique (quot_majorSort hq)] at hℓ; exact hℓ.1 rfl
  have hL := lookup_binderTy (Γ := Γ) (ls := ls) (doms := quotDoms) (x := 5) (by decide)
  rw [quot_binderTy5] at hL
  have hv5 := (Wv.lookup hL).hasType.1
  have hw : ((VLevel.param 0).inst ls).WF U := .inst hlsw
  have hsz : env.IsDefEq U Δ (.sort ((VLevel.param 0).inst ls)) (.sort .zero)
      (.sort (.succ ((VLevel.param 0).inst ls))) := .sortDF hw trivial e0
  rw [quot_binderTy0]
  refine ⟨⟨v 5, .self, hsz.defeqDF hv5⟩, fun τ hτ => ?_⟩
  have := tvv 5 _ hL τ (Obs.bvar_iff.1 hτ)
  have := typedAt_sort_iff.1 this
  rw [e0] at this
  exact this

end

/-- Uniqueness of the quotient rule for its head, in an environment whose rules are
delta rules or the quotient rule. -/
theorem quot_uniq (hrules : ∀ df, env.defeqs df → (∃ n ls, df.lhs = .const n ls) ∨ df = quotDefEq) :
    ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      env.defeqs df' →
      df'.lhs = .wrapLams doms' (.mkApps (.const ``Quot.lift lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = quotLead.length ∧
        ((ctor' = ``Quot.mk ∨ RuleMode env ``Quot.lift quotLead.length ls true) →
          df' = quotDefEq) := by
  intro df' doms' lsP' lead' ctor' lsC' ms' fs' body' hdf hl _
  rcases hrules df' hdf with ⟨_, _, h⟩ | rfl
  · exact absurd (hl.symm.trans h) VExpr.wrapLams_mkApps_snoc_ne_const
  · obtain ⟨-, -, -, h, -⟩ := wrapLams_pat_inj (hl.symm.trans quotDefEq_lhs)
    exact ⟨by rw [h], fun _ => rfl⟩

end Model
end VEnv
end Lean4Lean
