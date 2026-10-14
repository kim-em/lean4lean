import Lean4Lean.Theory.Typing.Strengthening.PrefixProgramCongruence
import Lean4Lean.Theory.Typing.Strengthening.EtaPrefixExchange
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLiftRenaming

/-! # Exact exchange of argument changes with checked prefixes

Full prefix computation is a weakening-stable congruence relation. Changing
supplied arguments therefore computes the entire generated program, including
its dependent lambda domains. The same argument gives exact eta exchange:
the earlier NormalEq remainder is unnecessary at these prefix roots.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Compatible prefix computation weakens without source typing. Occurrence
checks weaken using their stored typing derivations. -/
theorem PrefixCompute.weakN (R : PrefixCompute D Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    PrefixCompute D Γ' (a.liftN n k) (b.liftN n k) := by
  induction R generalizing n k Γ' with
  | base R =>
    simp only [← lift'_consN_skipN, InductiveSignature.RecursorData.lift'_eq_subst]
    exact .base R.subst
  | singleton H =>
    simpa only [liftN_mkApps, VExpr.liftN] using PrefixCompute.singleton (H.weakN henv W)
  | quotient H =>
    simpa only [liftN_mkApps, VExpr.liftN] using PrefixCompute.quotient (H.weakN henv W)
  | trans _ _ ih1 ih2 => exact (ih1 W).trans (ih2 W)
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | proj _ ih => exact .proj (ih W)

/-- Finite prefix computation satisfies the raw congruence interface. -/
theorem prefixCompute_congrRel : CongrRel (PrefixCompute D) where
  rfl := .refl
  app := .app
  proj := .proj
  lam := .lam
  forallE := .forallE
  weakN W R := R.weakN W

/-- Sound definitions supply the typed replay interface for argument paths. -/
theorem prefixCompute_argRel (hs : D.Sound env univs) : ArgRel (PrefixCompute D) :=
  prefixCompute_congrRel.argRel (fun hΓ R ht => R.simAt hs hΓ _ ht)

/-- A checked singleton prefix commutes with arbitrary finite computation of
its supplied arguments, retaining a direct computation of the entire output. -/
theorem singleton_prefix_compute (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (HA : List.Forall₂ (PrefixCompute D Γ) args args') :
    ∃ rhs', PrefixUnfold env univs recursorData Γ name levels args' rhs' ∧
      PrefixCompute D Γ rhs rhs' :=
  singleton_prefix_congr prefixCompute_congrRel (prefixCompute_argRel hs) hΓ H HA

/-- Quotient prefixes commute with computation of their supplied arguments. -/
theorem quotient_prefix_compute (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (HA : List.Forall₂ (PrefixCompute D Γ) args args') :
    ∃ rhs', QuotPrefixUnfold env univs Γ levels args' rhs' ∧ PrefixCompute D Γ rhs rhs' :=
  quotient_prefix_congr prefixCompute_congrRel (prefixCompute_argRel hs) hΓ H HA

/-- Argument eta expansion propagates directly through the full singleton
program; no normal comparison of residual lambda domains is needed. -/
theorem singleton_prefix_eta (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixUnfold env univs recursorData Γ name levels args rhs)
    (HA : List.Forall₂ (TypedEtaExpansion Γ) args args') :
    ∃ rhs', PrefixUnfold env univs recursorData Γ name levels args' rhs' ∧
      TypedEtaExpansion Γ rhs rhs' :=
  singleton_prefix_congr typedEtaExpansion_congrRel typedEtaExpansion_argRel hΓ H HA

/-- Quotient programs also preserve argument eta expansion exactly. -/
theorem quotient_prefix_eta (hΓ : OnCtx Γ (env.IsType univs))
    (H : QuotPrefixUnfold env univs Γ levels args rhs)
    (HA : List.Forall₂ (TypedEtaExpansion Γ) args args') :
    ∃ rhs', QuotPrefixUnfold env univs Γ levels args' rhs' ∧ TypedEtaExpansion Γ rhs rhs' :=
  quotient_prefix_congr typedEtaExpansion_congrRel typedEtaExpansion_argRel hΓ H HA

/-- Move a singleton contraction before argument eta expansions with an exact
eta path between the resulting programs. -/
theorem singleton_prefix_eta_exchange_exact (hΓ : OnCtx Γ (env.IsType univs))
    (HA : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T)
    (H : PrefixUnfold env univs recursorData Γ name levels args' rhs') :
    ∃ rhs, PrefixUnfold env univs recursorData Γ name levels args rhs ∧
      TypedEtaExpansion Γ rhs rhs' := by
  have HE := TypedEtaExpansion.spine_defeq hΓ HA ht
  obtain ⟨rhs, H'⟩ := H.congr_defeq hΓ (HE.flip.imp (fun _ _ (h : env.IsDefEqU univs Γ _ _) => h.symm))
  exact ⟨rhs, H', singleton_program_congr typedEtaExpansion_congrRel H' H HA⟩

/-- Move a quotient contraction before argument eta expansions exactly. -/
theorem quotient_prefix_eta_exchange_exact (hΓ : OnCtx Γ (env.IsType univs))
    (HA : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (ht : env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) T)
    (H : QuotPrefixUnfold env univs Γ levels args' rhs') :
    ∃ rhs, QuotPrefixUnfold env univs Γ levels args rhs ∧ TypedEtaExpansion Γ rhs rhs' := by
  have HE := TypedEtaExpansion.spine_defeq hΓ HA ht
  obtain ⟨rhs, H'⟩ := H.congr_defeq hΓ (HE.flip.imp (fun _ _ (h : env.IsDefEqU univs Γ _ _) => h.symm))
  exact ⟨rhs, H', quotient_program_congr typedEtaExpansion_congrRel H' H HA⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
