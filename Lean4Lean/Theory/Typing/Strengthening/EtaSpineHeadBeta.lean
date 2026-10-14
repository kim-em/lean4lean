import Lean4Lean.Theory.Typing.Strengthening.EtaHeadBeta
import Lean4Lean.Theory.Typing.Confluence.EtaSpine

/-! # Rigid eta spines normalize by head beta alone

The normalization proof for EtaSpine contracts only applications on the function
spine. Recording that bound permits a symmetric eta join to expose a family
head without importing arbitrary full computation into its computational phase.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Lift a finite head-beta path through one unchanged argument. -/
theorem HeadBetaRed.appL (R : HeadBetaRed f f') (a : VExpr) :
    HeadBetaRed (.app f a) (.app f' a) := by
  induction R with
  | rfl => exact .rfl
  | tail _ R ih => exact ih.tail (.appL R)

variable [Params]

/-- Head-beta normalization leaves either the original rigid spine or a lambda
with strictly fewer eta wrappers. Original argument paths remain full paths;
the normalization path itself contains only head beta contractions. -/
def EtaSpineHeadNF (c : Name) (ls : List VLevel) (Γ : List VExpr) (e : VExpr)
    (args : List VExpr) (n : Nat) : Prop :=
  (∃ bs, HeadBetaRed e (mkApps (.const c ls) bs) ∧ List.Forall₂ (FullReduction Γ) args bs) ∨
  (∃ A body m, m < n ∧ HeadBetaRed e (.lam A body) ∧
    EtaSpine c ls (A :: Γ) body (args.map VExpr.lift ++ [.bvar 0]) m)

private theorem headBeta_type (hΓ : OnCtx Γ (env.IsType univs))
    (R : HeadBetaRed a b) (ht : env.HasType univs Γ a T) : env.HasType univs Γ b T :=
  (R.toBeta.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht).hasType.2

private theorem etaSpine_headBeta_aux (hΓ : OnCtx Γ (env.IsType univs))
    (outer : ∀ m e args T, m < N → EtaSpine c ls Γ e args m → TypedArgs Γ args →
      env.HasType univs Γ e T → EtaSpineHeadNF c ls Γ e args m)
    (H : EtaSpine c ls Γ e args n) (hn : n ≤ N) (ht : TypedArgs Γ args)
    (he : env.HasType univs Γ e T) : EtaSpineHeadNF c ls Γ e args n := by
  induction H generalizing T with
  | spine h => exact .inl ⟨_, .rfl, h⟩
  | eta _ _ Hb => exact .inr ⟨_, _, _, Nat.lt_succ_self _, .rfl, Hb⟩
  | @app Γ f as₀ n a b Hf hr ih =>
    have hta := TypedArgs.append.1 ht
    obtain ⟨X, Y, hf, hb⟩ := he.app_inv henv hΓ
    rcases ih hΓ outer hn hta.1 hf with ⟨bs, r, hbs⟩ | ⟨A, body, m, hm, r, Hbody⟩
    · refine .inl ⟨bs ++ [b], ?_, hbs.append' (.cons hr .nil)⟩
      rw [mkApps_snoc]
      exact r.appL b
    · have r1 := r.appL b
      have hβ := headBeta_type hΓ r1 he
      obtain ⟨X', Y', hl, hb'⟩ := hβ.app_inv henv hΓ
      obtain ⟨Y'', hY, _⟩ := hl.lam_inv_forallE henv hΓ
      have ⟨⟨_, hAX⟩, _⟩ := hY.forallE_inv henv hΓ
      have hbA : env.HasType univs Γ b A := hb'.defeqU_r henv hΓ ⟨_, hAX.symm⟩
      have H' := Hbody.instN .zero hbA
      simp only [List.map_append, List.map_map, Function.comp_def, VExpr.inst_lift,
        List.map_id', List.map_cons, List.map_nil, VExpr.inst, instVar, Nat.lt_irrefl, if_false,
        VExpr.liftN_zero] at H'
      have H'' := H'.pre hΓ ((FullReduction.forall₂_rfl _).append' (.cons hr .nil)) ht
      have r2 : HeadBetaRed (.app f b) (body.inst b) := r1.tail .beta
      rcases outer m _ _ _ (by omega) H'' ht (headBeta_type hΓ r2 he) with
        ⟨bs, r', hbs⟩ | ⟨A', body', m', hm', r', Hb'⟩
      · exact .inl ⟨bs, r2.trans r', hbs⟩
      · exact .inr ⟨A', body', m', by omega, r2.trans r', Hb'⟩

/-- The original finite eta-spine normalization needs only head beta. -/
theorem etaSpine_headBeta_normalize (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n {e args T}, EtaSpine c ls Γ e args n → TypedArgs Γ args →
      env.HasType univs Γ e T → EtaSpineHeadNF c ls Γ e args n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro e args T H ht he
    exact etaSpine_headBeta_aux hΓ (fun m _ _ _ hm H ht he => ih m hm H ht he)
      H (Nat.le_refl _) ht he

/-- Sort typing excludes the residual lambda alternative. Head beta therefore
exposes the original constant at reducts of its original arguments. -/
theorem etaSpine_sort_headBeta (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaSpine c ls Γ e args n) (ht : TypedArgs Γ args)
    (he : env.HasType univs Γ e (.sort u)) :
    ∃ bs, HeadBetaRed e (mkApps (.const c ls) bs) ∧
      List.Forall₂ (FullReduction Γ) args bs := by
  rcases etaSpine_headBeta_normalize hΓ n H ht he with h | ⟨A, body, m, hm, R, HB⟩
  · exact h
  · exact (HasType.sort_not_lam hΓ (headBeta_type hΓ R he)).elim

end Lean4Lean.VEnv.Strengthening.PureObservation
