import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.ChainLemmas
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.MinimalEnv
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Extra
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.EqRecVal

/-! # Soundness: the ι rule of `Eq.rec`

`pat_core`: a redex `Eq.rec α a M m b (Eq.refl α' a')` that has the semantic judgment and the
head invariant at a type `A` denotes the same as its reduct. If `A` denotes a proposition,
both denote `•`. Otherwise the chain of the redex is tracked through all six arguments of
the declared type of `Eq.rec`; it gives the arguments' memberships and that the value of the
major premise, which reduces to `r`, realizes `eqCand α a b`, so the endpoints are identical
and `recBody` returns the minor premise.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

variable {env : VEnv}

/-- `Eq.rec` is an element of its declared type, with a realizing value. -/
theorem UniverseTower.constOK_EqRec {𝕋 : UniverseTower} (ls : List VLevel) :
    𝕋.ConstOK ``Eq.rec ls (canonicalEqRecType.instL ls) := by
  intro ρ
  have hc : 𝕋.constDen ``Eq.rec ls = 𝕋.recDen (ls.getD 0 .zero) (ls.getD 1 .zero) := by
    simp [UniverseTower.constDen]
  have hv : constVal ``Eq.rec = recVal := by simp [constVal]
  rw [UniverseTower.recTy_eq, hc, hv]
  exact ⟨UniverseTower.recDen_mem ρ, UniverseTower.recVal_realizes _ _ ρ⟩

/-- Every constant of the environment is an element of its declared type, with a realizing
value. -/
theorem KlopInventory.constOK (𝕋 : UniverseTower) (heq : env.HasCanonicalEq)
    (K : KlopInventory env) {c : Name} {ci : VConstant} (h : env.constants c = some ci)
    (ls : List VLevel) : 𝕋.ConstOK c ls (ci.type.instL ls) := by
  rcases K.constants_only c ci h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases Option.some.inj (heq.1.symm.trans h); exact UniverseTower.constOK_Eq ls
  · cases Option.some.inj (heq.2.1.symm.trans h); exact UniverseTower.constOK_EqRefl ls
  · cases Option.some.inj (heq.2.2.1.symm.trans h); exact UniverseTower.constOK_EqRec ls
  · cases Option.some.inj (K.T.symm.trans h); exact UniverseTower.constOK_T ls
  · cases Option.some.inj (K.E.symm.trans h); exact UniverseTower.constOK_E ls
  · cases Option.some.inj (K.P.symm.trans h); exact UniverseTower.constOK_P ls
  · cases Option.some.inj (K.H.symm.trans h)
    have := UniverseTower.constOK_H (𝕋 := 𝕋) ls
    simpa [VExpr.instL, VExpr.eqApp, VLevel.inst] using this
  · cases Option.some.inj (K.C.symm.trans h); exact UniverseTower.constOK_C ls
  · cases Option.some.inj (K.Fix.symm.trans h); exact UniverseTower.constOK_Fix ls

/-- The reduct template of the ι rule at levels `v`, `u`. -/
def recRhs (v u : VLevel) : VExpr :=
  .lam (rA1 u) (.lam rA2 (.lam (rA3 v u) (.lam (rA4 u) (.bvar 0))))

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- A value reducing to `r` realizes an equation only at identical endpoints. -/
theorem eq_of_eqCand_toR {α a b : 𝕋.S} {x : PVal} (h : (𝕋.eqCand α a b).mem x)
    (hr : PVal.ToR x) : a = b := by
  unfold eqCand at h
  by_cases h1 : a ∈ₛ 𝕋.El α ∧ a = b
  · exact h1.2
  · rw [if_neg h1] at h
    by_cases h2 : a ∈ₛ 𝕋.El α ∧ 𝕋.Rel α a b
    · rw [if_pos h2] at h; exact (PVal.not_toR_toBot hr h).elim
    · rw [if_neg h2] at h; exact h.elim

/-- Two terms with the semantic judgment at the same type and equal denotations at every
valuation of the context are semantically equal. -/
theorem Sem.of_den_eq' {Γ : List VExpr} {a b A : VExpr}
    (Ha : 𝕋.Sem Γ a a A) (Hb : 𝕋.Sem Γ b b A)
    (h : ∀ ρ w, 𝕋.ValOK Γ ρ w → 𝕋.den ρ a = 𝕋.den ρ b) : 𝕋.Sem Γ a b A := by
  intro ρ w hρ
  obtain ⟨hty, -, hm, hv, hr⟩ := Ha ρ w hρ
  obtain ⟨-, -, -, hv', -⟩ := Hb ρ w hρ
  exact ⟨hty, h ρ w hρ, hm, fun hc => ⟨(hv hc).1, (hv' hc).1⟩, hr⟩

/-- **The ι rule, semantically.** -/
theorem pat_core (heq : env.HasCanonicalEq) (K : KlopInventory env)
    {Γ : List VExpr} {ls lsC : List VLevel} {αt at' Mt mt bt α' a' A : VExpr}
    {ρ : Nat → 𝕋.S} {w : Nat → PVal} (hρ : 𝕋.ValOK Γ ρ w)
    (He : 𝕋.Sem Γ
      (.app (.app (.app (.app (.app (.app (.const ``Eq.rec ls) αt) at') Mt) mt) bt)
        (.app (.app (.const ``Eq.refl lsC) α') a'))
      (.app (.app (.app (.app (.app (.app (.const ``Eq.rec ls) αt) at') Mt) mt) bt)
        (.app (.app (.const ``Eq.refl lsC) α') a')) A)
    (Hs : 𝕋.SpineOK env ρ w
      (.app (.app (.app (.app (.app (.app (.const ``Eq.rec ls) αt) at') Mt) mt) bt)
        (.app (.app (.const ``Eq.refl lsC) α') a')) A)
    (Hr : 𝕋.Sem Γ
      (.app (.app (.app (.app (recRhs (ls.getD 0 .zero) (ls.getD 1 .zero)) αt) at') Mt) mt)
      (.app (.app (.app (.app (recRhs (ls.getD 0 .zero) (ls.getD 1 .zero)) αt) at') Mt) mt) A) :
    𝕋.den ρ (.app (.app (.app (.app (.app (.app (.const ``Eq.rec ls) αt) at') Mt) mt) bt)
        (.app (.app (.const ``Eq.refl lsC) α') a')) =
      𝕋.den ρ (.app (.app (.app (.app (recRhs (ls.getD 0 .zero) (ls.getD 1 .zero)) αt) at')
        Mt) mt) := by
  obtain ⟨⟨n, hty⟩, -, hem, -, -⟩ := He ρ w hρ
  obtain ⟨-, -, hrm, -, -⟩ := Hr ρ w hρ
  by_cases hc : 𝕋.IsCand (𝕋.den ρ A)
  · rw [isCand_eq hc] at hem hrm
    rw [(𝕋.mem_El_cand.1 hem).1, (𝕋.mem_El_cand.1 hrm).1]
  have hconst : ∀ c ci ls, env.constants c = some ci → 𝕋.ConstOK c ls (ci.type.instL ls) :=
    fun c ci ls h => K.constOK 𝕋 heq h ls
  obtain ⟨o, hch, hcl⟩ := Hs trivial
  cases o with
  | none =>
    have := hch.none_star hconst rfl
    rw [this] at hem
    exact (hty.star_not_mem hc hem).elim
  | some R6 =>
    have hR6 := hcl R6 rfl
    generalize hv : ls.getD 0 .zero = v at Hr hrm ⊢
    generalize hu : ls.getD 1 .zero = u at Hr hrm ⊢
    obtain ⟨P5, c5, f5⟩ := chain_step hch
    obtain ⟨P4, c4, f4⟩ := chain_step c5
    obtain ⟨P3, c3, f3⟩ := chain_step c4
    obtain ⟨P2, c2, f2⟩ := chain_step c3
    obtain ⟨P1, c1, f1⟩ := chain_step c2
    obtain ⟨P0, c0, f0⟩ := chain_step c1
    obtain ⟨ci, hci, hP0⟩ := chain_const_inv c0
    cases Option.some.inj (heq.2.2.1.symm.trans hci)
    have hP0' : P0 = 𝕋.den ρ (recTy v u) := by
      rw [Option.some.inj hP0, recTy_eq, hv, hu]
    -- the six arguments
    obtain ⟨hα, hP1, -⟩ := f0 (𝕋.den ρ (rA1 u)) (fun x1 => 𝕋.den (𝕋.cons x1 ρ)
      (.forallE rA2 (.forallE (rA3 v u) (.forallE (rA4 u) (.forallE rA5
        (.forallE (rA6 u) rR)))))) hP0'
    obtain ⟨ha, hP2, -⟩ := f1 _ (fun x2 => 𝕋.den (𝕋.cons x2 (𝕋.cons (𝕋.den ρ αt) ρ))
      (.forallE (rA3 v u) (.forallE (rA4 u) (.forallE rA5 (.forallE (rA6 u) rR))))) hP1
    obtain ⟨hM, hP3, -⟩ := f2 _ (fun x3 => 𝕋.den
      (𝕋.cons x3 (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ)))
      (.forallE (rA4 u) (.forallE rA5 (.forallE (rA6 u) rR)))) hP2
    obtain ⟨hm, hP4, -⟩ := f3 _ (fun x4 => 𝕋.den
      (𝕋.cons x4 (𝕋.cons (𝕋.den ρ Mt) (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ))))
      (.forallE rA5 (.forallE (rA6 u) rR))) hP3
    obtain ⟨hb, hP5, -⟩ := f4 _ (fun x5 => 𝕋.den
      (𝕋.cons x5 (𝕋.cons (𝕋.den ρ mt) (𝕋.cons (𝕋.den ρ Mt) (𝕋.cons (𝕋.den ρ at')
        (𝕋.cons (𝕋.den ρ αt) ρ)))))
      (.forallE (rA6 u) rR)) hP4
    obtain ⟨ht, hR, hval⟩ := f5 _ (fun x6 => 𝕋.den
      (𝕋.cons x6 (𝕋.cons (𝕋.den ρ bt) (𝕋.cons (𝕋.den ρ mt) (𝕋.cons (𝕋.den ρ Mt)
        (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ))))))
      rR) hP5
    -- the right-hand side is the minor premise
    have hrhs : 𝕋.den ρ (.app (.app (.app (.app (recRhs v u) αt) at') Mt) mt) = 𝕋.den ρ mt := by
      have e1 : 𝕋.mkApp (𝕋.den ρ (recRhs v u)) (𝕋.den ρ αt) = 𝕋.den (𝕋.cons (𝕋.den ρ αt) ρ)
          (.lam rA2 (.lam (rA3 v u) (.lam (rA4 u) (.bvar 0)))) := 𝕋.mkApp_mkLam hα
      have e2 : 𝕋.mkApp (𝕋.den (𝕋.cons (𝕋.den ρ αt) ρ)
          (.lam rA2 (.lam (rA3 v u) (.lam (rA4 u) (.bvar 0))))) (𝕋.den ρ at') =
          𝕋.den (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ))
            (.lam (rA3 v u) (.lam (rA4 u) (.bvar 0))) := 𝕋.mkApp_mkLam ha
      have e3 : 𝕋.mkApp (𝕋.den (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ))
          (.lam (rA3 v u) (.lam (rA4 u) (.bvar 0)))) (𝕋.den ρ Mt) =
          𝕋.den (𝕋.cons (𝕋.den ρ Mt) (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ)))
            (.lam (rA4 u) (.bvar 0)) := 𝕋.mkApp_mkLam hM
      have e4 : 𝕋.mkApp (𝕋.den (𝕋.cons (𝕋.den ρ Mt) (𝕋.cons (𝕋.den ρ at')
          (𝕋.cons (𝕋.den ρ αt) ρ))) (.lam (rA4 u) (.bvar 0))) (𝕋.den ρ mt) = 𝕋.den ρ mt :=
        𝕋.mkApp_mkLam hm
      show 𝕋.mkApp (𝕋.mkApp (𝕋.mkApp (𝕋.mkApp (𝕋.den ρ (recRhs v u)) _) _) _) _ = _
      rw [e1, e2, e3, e4]
    -- the binder types, semantically
    have hα' : 𝕋.den ρ αt ∈ₛ 𝕋.El (𝕋.sortDen u) := hα
    have ha' : 𝕋.den ρ at' ∈ₛ 𝕋.El (𝕋.den ρ αt) := ha
    have hM' : 𝕋.den ρ Mt ∈ₛ 𝕋.El (𝕋.motiveTy v (𝕋.den ρ αt) (𝕋.den ρ at')) := by
      have := den_motiveOf (𝕋 := 𝕋) (v := v) (u := u) (α := .bvar 1) (a := .bvar 0)
        (ρ := 𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ)) hα' ha'
      rw [rA3, this] at hM
      exact hM
    have hm' : 𝕋.den ρ mt ∈ₛ 𝕋.El (𝕋.mkApp (𝕋.mkApp (𝕋.den ρ Mt) (𝕋.den ρ at')) 𝕋.star) := by
      have h4 : 𝕋.den (𝕋.cons (𝕋.den ρ Mt) (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ)))
          (rA4 u) = 𝕋.mkApp (𝕋.mkApp (𝕋.den ρ Mt) (𝕋.den ρ at')) 𝕋.star := by
        show 𝕋.mkApp (𝕋.mkApp _ _) (𝕋.den _ (reflS u _ _)) = _
        rw [den_reflS]; rfl
      rw [h4] at hm
      exact hm
    have hb' : 𝕋.den ρ bt ∈ₛ 𝕋.El (𝕋.den ρ αt) := hb
    have h6 : 𝕋.den (𝕋.cons (𝕋.den ρ bt) (𝕋.cons (𝕋.den ρ mt) (𝕋.cons (𝕋.den ρ Mt)
        (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ))))) (rA6 u) =
        𝕋.cand (𝕋.eqCand (𝕋.den ρ αt) (𝕋.den ρ at') (𝕋.den ρ bt)) :=
      den_eqApp (𝕋 := 𝕋) (l := u) (A := .bvar 4) (x := .bvar 3) (y := .bvar 0)
        (ρ := 𝕋.cons (𝕋.den ρ bt) (𝕋.cons (𝕋.den ρ mt) (𝕋.cons (𝕋.den ρ Mt)
          (𝕋.cons (𝕋.den ρ at') (𝕋.cons (𝕋.den ρ αt) ρ))))) hα' ha' hb'
    rw [h6] at ht hval
    have hval' := hval ⟨_, rfl⟩
    rw [𝕋.candOf_cand] at hval'
    have htoR : PVal.ToR ((pval (.app (.app (.const ``Eq.refl lsC) α') a')).subst w) := by
      show PVal.ToR (.app (.app ((constVal ``Eq.refl).subst w) _) _)
      rw [constVal_subst]
      have : constVal ``Eq.refl = reflVal := by simp [constVal]
      rw [this]
      exact .head (.appL .beta) (.head .beta .rfl)
    have hab : 𝕋.den ρ at' = 𝕋.den ρ bt := eq_of_eqCand_toR hval' htoR
    have htS := (𝕋.mem_El_cand.1 ht).1
    -- the fibre is not a proposition
    have hfib : ¬𝕋.IsCand (𝕋.mkApp (𝕋.mkApp (𝕋.den ρ Mt) (𝕋.den ρ bt)) 𝕋.star) := by
      have : 𝕋.den ρ A = 𝕋.mkApp (𝕋.mkApp (𝕋.den ρ Mt) (𝕋.den ρ bt))
          (𝕋.den ρ (.app (.app (.const ``Eq.refl lsC) α') a')) := hR6.symm.trans hR
      rw [htS] at this
      rw [← this]; exact hc
    rw [hrhs]
    have hc' : 𝕋.den ρ (.const ``Eq.rec ls) = 𝕋.recDen v u := by
      have : 𝕋.den ρ (.const ``Eq.rec ls) =
          𝕋.recDen (ls.getD 0 .zero) (ls.getD 1 .zero) := by simp [den, constDen]
      rw [this, hv, hu]
    show 𝕋.mkApp (𝕋.mkApp (𝕋.mkApp (𝕋.mkApp (𝕋.mkApp (𝕋.mkApp
      (𝕋.den ρ (.const ``Eq.rec ls)) _) _) _) _) _) _ = _
    rw [hc', recDen_app hα' ha' hM' hm' hb' ht, recBody, if_neg hfib, if_neg]
    exact fun h => h.2.2 hab

end UniverseTower

/-- The registered reduct template of `Eq.rec`, level-instantiated. -/
theorem eqRecRule_rhs_instL (ls : List VLevel) :
    eqRecRule.rhs.instL ls = recRhs (ls.getD 0 .zero) (ls.getD 1 .zero) := by
  show canonicalEqRecRule.rhs.instL ls = _
  simp [canonicalEqRecRule, canonicalEqRecMotive, canonicalEqRecMinor, VExpr.instL, recRhs,
    rA1, rA2, rA3, rA4, motiveOf, eqS, reflS, VExpr.lift, VExpr.liftN, liftVar, VLevel.inst]

/-- **The ι rule of `Eq.rec` is sound**: a matched redex with the semantic judgment and the
head invariant is semantically equal to its registered reduct. -/
theorem KlopInventory.sem_pat_core (𝕋 : UniverseTower) (heq : env.HasCanonicalEq)
    (K : KlopInventory env)
    {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check} {e A : VExpr} {m1 m2}
    (hp : env.pats p r) (hm : p.Matches e m1 m2)
    (He : 𝕋.Sem Γ e e A) (Hs : ∀ ρ w, 𝕋.ValOK Γ ρ w → 𝕋.SpineOK env ρ w e A)
    (Hr : 𝕋.Sem Γ (r.1.apply m1 m2) (r.1.apply m1 m2) A) :
    𝕋.Sem Γ e (r.1.apply m1 m2) A := by
  obtain ⟨rfl, hr⟩ := K.pats_only p r hp
  subst hr
  refine UniverseTower.Sem.of_den_eq' He Hr fun ρ w hρ => ?_
  obtain ⟨recArgs, ctorArgs, lsC, h1, h2, rfl, hred⟩ :=
    SimplePattern.iotaRHS_apply_of_matches (k := 4) (nind := 1) (cnp := 2) (nf := 0)
      (rhs := eqRecRule.rhs) (hc := eqRecRule_closed) hm
  have hred' : eqPatRHS.1.apply m1 m2 =
      (eqRecRule.rhs.instL m1).mkApps (recArgs.take 4 ++ ctorArgs.drop 2) := hred
  rw [hred'] at Hr ⊢
  match recArgs, h1, ctorArgs, h2 with
  | [αt, at', Mt, mt, bt], _, [α', a'], _ =>
    rw [eqRecRule_rhs_instL] at Hr ⊢
    exact UniverseTower.pat_core heq K hρ He (Hs ρ w hρ) Hr

end VEnv.Strengthening
end Lean4Lean
