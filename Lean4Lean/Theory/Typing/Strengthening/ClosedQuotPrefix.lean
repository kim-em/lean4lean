import Lean4Lean.Theory.Typing.Strengthening.ClosedQuotUnfolding
import Lean4Lean.Theory.Typing.Strengthening.QuotPrefixFreshAbstraction
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLiftRenaming

/-! # The closed quotient equation is an actual checked prefix

Reabstracting the five fresh arguments of the checked quotient rule yields its
zero-argument rule. Generation fixes the output literally to the closed value;
no eta comparison remains in this operational statement.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedQuot
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

private theorem reabstract (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (ht : HasType env U Γ (mkApps (.const ``Quot.lift levels) args)
      (wrapForalls ds residual))
    (he : etaOpen ds.length (mkApps (.const ``Quot.lift levels) args) =
      mkApps (.const ``Quot.lift levels) openedArgs)
    (H : QuotPrefixUnfold env U (ds.reverse ++ Γ) levels openedArgs out) :
    ∃ rhs, QuotPrefixUnfold env U Γ levels args rhs := by
  induction ds generalizing Γ args with
  | nil =>
    obtain ⟨_, _, rfl⟩ := mkApps_const_inj he
    exact ⟨_, H⟩
  | cons A ds ih =>
    obtain ⟨u, hA⟩ := (IsType.forallE_inv henv.ordered (ht.isType henv.ordered hΓ)).1
    have ht' := IsDefEq.appDF (ht.weak henv.ordered (B := A))
      (IsDefEq.bvar (Lookup.zero (Γ := Γ) (ty := A)))
    simp only [lift, VExpr.inst_liftN_bvar] at ht'
    have es : (.app (mkApps (.const ``Quot.lift levels) args).lift (.bvar 0)) =
        mkApps (.const ``Quot.lift levels) (args.map VExpr.lift ++ [.bvar 0]) := by
      simp [mkApps_append, mkApps_cons, mkApps_nil, lift, liftN_mkApps, liftN]
    rw [es] at ht'
    have he' : etaOpen ds.length
        (mkApps (.const ``Quot.lift levels) (args.map VExpr.lift ++ [.bvar 0])) =
        mkApps (.const ``Quot.lift levels) openedArgs := by
      simpa only [List.length_cons, etaOpen, es] using he
    have H' : QuotPrefixUnfold env U (ds.reverse ++ A :: Γ) levels openedArgs out := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H
    obtain ⟨rhs, HR⟩ := ih (Γ := A :: Γ) ⟨hΓ, u, hA⟩ ht' he' H'
    obtain ⟨domain, _, HR⟩ := quotPrefixUnfold_fresh_argument henv hΓ ht HR
    exact ⟨_, HR⟩

/-- The added closed quotient equation is exactly an actual checked
zero-argument prefix, in any well-formed context. -/
private theorem zero_prefix_wf (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero) :
    QuotPrefixUnfold env U Γ [u,v] [] (value u v) := by
  have ht : HasType env U Γ (.const ``Quot.lift [u,v])
      (wrapForalls (domains u v) (result u v)) := by
    rw [← type_shape]
    exact .const hr.lift (by simpa using And.intro hu hv) rfl
  obtain ⟨hctx, hopen⟩ := ht.etaOpen_wf henv.ordered hΓ
  have hp := QuotPrefixUnfold.atFive henv hctx hr hu hv hz ⟨_, opened ▸ hopen⟩
  obtain ⟨rhs, H⟩ := reabstract (args := []) henv hΓ ht opened hp
  cases H with
  | intro hr hw hz hg hc =>
    rw [← generated_zero_rhs hg]
    exact .intro hr hw hz hg hc

/-- The closed quotient equation is a checked prefix even in an arbitrary
ambient context: its empty-context checks weaken without context typing. -/
theorem zero_prefix (henv : env.WF) (hr : QuotRegistered env)
    (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero) :
    QuotPrefixUnfold env U Γ [u,v] [] (value u v) := by
  have H := zero_prefix_wf (Γ := []) henv (by trivial) hr hu hv hz
  have W : Ctx.LiftN Γ.length 0 [] Γ := by
    simpa only [List.append_nil] using (Ctx.LiftN.zero (Γ := []) Γ)
  have HR := H.weakN henv W
  simpa only [List.map_nil, (value_closed henv hr hu hv hz).liftN_eq (Nat.zero_le _)] using HR

end Lean4Lean.VEnv.Strengthening.ClosedQuot
