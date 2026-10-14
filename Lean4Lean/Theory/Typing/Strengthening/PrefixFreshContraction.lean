import Lean4Lean.Theory.Typing.Strengthening.PrefixFreshReflection
import Lean4Lean.Theory.Typing.PrefixUnfolding.Substitution

/-! # Contracting a duplicated first residual binder

The ambient fresh binder can be identified with the first residual binder of a
prefix check when their domains agree. Ordinary typed substitution then reflects
all fully opened checking premises. This is a restricted reflection theorem,
not strengthening through an arbitrary unused binder.
-/
namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr

/-- Renaming past a duplicated binder and substituting its other copy cancel
through every domain of a dependent telescope. -/
theorem instDomains_rename_fresh (ds : List VExpr) (k : Nat) :
    instDomains (renameDomains ((Lift.refl.skipN 1).consN (k + 1)) ds) (.bvar 0) k = ds := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    simp only [renameDomains, instDomains, lift'_consN_skipN, inst_liftN_bvar]
    exact congrArg (List.cons d) (ih (k + 1))

/-- The first residual binder can be instantiated by the equal ambient binder.
The resulting opened context is the original lower telescope. -/
theorem opened_fresh_contraction (A : VExpr) (ds Γ : List VExpr) :
    Ctx.InstN (A :: Γ) (.bvar 0) A.lift ds.length
      ((renameDomains (.skip .refl) (A :: ds)).reverse ++ A :: Γ)
      ((A :: ds).reverse ++ Γ) := by
  have H := Ctx.InstN.reverse (renameDomains ((Lift.refl.skipN 1).consN 1) ds)
    (Ctx.InstN.zero (Γ₀ := A :: Γ) (e₀ := .bvar 0) (A₀ := A.lift))
  rw [instDomains_rename_fresh ds 0] at H
  simpa only [renameDomains_length, Nat.add_zero,
    renameDomains, ← lift_eq_lift', List.reverse_cons, List.append_assoc,
    List.singleton_append, Lift.consN, Lift.skipN_one] using H

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

private theorem etaOpen_lift_fresh (n : Nat) (e : VExpr) :
    etaOpen n e.lift = (etaOpen n e).liftN 1 n := by
  have h := etaOpen_lift' n e (Lift.refl.skipN 1)
  rw [lift'_consN_skipN] at h
  simpa only [Lift.skipN_one, ← lift_eq_lift'] using h

private theorem lift'_fresh_consN (e : VExpr) (n : Nat) :
    e.lift' ((Lift.skip Lift.refl).consN n) = e.liftN 1 n := by
  simpa only [Lift.skipN_one] using (lift'_consN_skipN (e := e) (n := 1) (k := n))

/-- A checked prefix under an extra copy of its first residual domain reflects
by contracting the two copies. Source typing is supplied below; every other
checking premise follows from ordinary substitution, without strengthening. -/
theorem unfoldingCheck_contract_fresh (henv : env.WF)
    (ht : env.HasType U Γ source program.type) (hd : program.domains = A :: ds)
    (H : UnfoldingCheck env U (A :: Γ) source.lift (program.rename (.skip .refl))) :
    UnfoldingCheck env U Γ source program := by
  have W := opened_fresh_contraction A ds Γ
  have harg : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hscope := H.templateScope henv
  have hlen : program.domains.length = ds.length + 1 := by simp [hd]
  have hρ : (Lift.skip Lift.refl).consN program.domains.length =
      (Lift.refl.skipN 1).consN (ds.length + 1) := by rw [hlen]; rfl
  have hctx : (program.rename (.skip .refl)).domains.reverse ++ A :: Γ =
      (renameDomains (.skip .refl) (A :: ds)).reverse ++ A :: Γ := by
    simp only [PrefixUnfolding.rename, hd]
  have lower {e T : VExpr}
      (he : env.HasType U ((program.rename (.skip .refl)).domains.reverse ++ A :: Γ)
        (e.liftN 1 (ds.length + 1)) T) :
      env.HasType U (program.domains.reverse ++ Γ) e (T.inst (.bvar 0) ds.length) := by
    rw [hctx] at he
    simpa only [inst_liftN_bvar, ← hd] using he.instN henv.ordered W harg
  refine { source_typed := ht
           remaining_nonempty := by simp [hd]
           equation_present := H.equation_present
           equation_body := H.equation_body
           levels_wf := H.levels_wf
           levels_length := H.levels_length
           captures_length := by simpa only [PrefixUnfolding.rename, List.length_map] using H.captures_length
           captures_typed := ?_
           major_prop := ?_
           recursor_lhs := ?_ }
  · intro j hj hdom
    have hc := H.captures_typed j (by simpa only [PrefixUnfolding.rename, List.length_map] using hj) hdom
    simp only [PrefixUnfolding.rename, List.getElem_map, hρ, lift'_consN_skipN] at hc
    have hclosed : (program.equationBody.domains[j].instL program.levels).ClosedN
        (program.captures.take j).length := by
      simpa only [PrefixUnfolding.rename, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using
        (hscope.2.2 j hdom).instL (ls := program.levels)
    have he : ((program.equationBody.domains[j].instL program.levels).instOuter
        (program.captures.take j)).liftN 1 (ds.length + 1) =
        (program.equationBody.domains[j].instL program.levels).instOuter
          ((program.captures.map (·.liftN 1 (ds.length + 1))).take j) := by
      rw [← instantiateParams_eq_instOuter, ← lift'_consN_skipN,
        instantiateParams_lift' hclosed]
      simp only [instantiateParams_eq_instOuter, List.map_take, lift'_consN_skipN]
    rw [← he] at hc
    simpa only [inst_liftN_bvar] using lower hc
  · obtain ⟨T, hp, hm, hc⟩ := H.major_prop
    rw [hctx] at hp
    have hp' := hp.instN henv.ordered W harg
    rw [← hd] at hp'
    have hm' := lower (e := .bvar 0) (by
      simpa only [liftN, liftVar_zero] using hm)
    have hc' := lower (e := program.constructor) (by
      simpa only [PrefixUnfolding.rename, hρ, lift'_consN_skipN] using hc)
    exact ⟨_, hp', hm', hc'⟩
  · have hr := H.recursor_lhs
    have hleft : (VExpr.app (etaOpen (program.domains.length - 1) source).lift program.constructor).liftN
        1 (ds.length + 1) =
        VExpr.app (etaOpen ((program.rename (.skip .refl)).domains.length - 1) source.lift).lift
          (program.rename (.skip .refl)).constructor := by
      simp only [PrefixUnfolding.rename, renameDomains_length,
        hlen, Nat.add_sub_cancel, etaOpen_lift_fresh, lift_liftN', liftN, lift'_fresh_consN]
    have hclosed : (program.equationBody.lhs.instL program.levels).ClosedN program.captures.length := by
      simpa only [PrefixUnfolding.rename, List.length_map] using hscope.1.instL (ls := program.levels)
    have hright : ((program.equationBody.lhs.instL program.levels).instOuter program.captures).liftN
        1 (ds.length + 1) =
        ((program.rename (.skip .refl)).equationBody.lhs.instL
          (program.rename (.skip .refl)).levels).instOuter (program.rename (.skip .refl)).captures := by
      simp only [PrefixUnfolding.rename, hρ]
      rw [← instantiateParams_eq_instOuter, ← lift'_consN_skipN, instantiateParams_lift' hclosed, instantiateParams_eq_instOuter]
    rw [← hleft, ← hright, hctx] at hr
    simpa only [inst_liftN_bvar, ← hd] using hr.instN henv W harg

/-- A check is invariant under insertion of another copy of its first domain.
The forward direction is weakening and the reverse direction is contraction;
no source-context well-formedness or general strengthening premise is needed. -/
theorem unfoldingCheck_fresh_domain_iff (henv : env.WF)
    (ht : env.HasType U Γ source program.type) (hd : program.domains = A :: ds) :
    UnfoldingCheck env U (A :: Γ) source.lift (program.rename (.skip .refl)) ↔
      UnfoldingCheck env U Γ source program := by
  refine ⟨unfoldingCheck_contract_fresh henv ht hd, fun H => ?_⟩
  simpa only [← lift_eq_lift'] using H.weak' henv (Ctx.Lift'.skip (A := A) .refl)

end Lean4Lean.VEnv.Strengthening
