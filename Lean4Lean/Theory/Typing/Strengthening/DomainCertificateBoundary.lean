import Lean4Lean.Theory.Typing.Strengthening.DomainSuperdevelopment
import Lean4Lean.Theory.Typing.Strengthening.HybridSubstitution

/-! # A boundary of beta-only domain-certificate repair

Even an eta-free `NormalEqF false` can hide eta in its declarative lambda-domain
premise. The example below has beta-normal endpoints, so no beta development can
turn that comparison into a recursively domain-certified comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

omit [Params] in
/-- A beta-normal expression has no nontrivial finite beta reduct. -/
theorem beta_eq_of_not_hasBeta (R : BetaRed e e') (hn : ¬ HasBeta e) : e' = e := by
  induction R with
  | refl => rfl
  | trans _ _ ih1 ih2 =>
    have h1 := ih1 hn
    subst h1
    exact ih2 hn
  | app _ _ ih1 ih2 =>
    rw [ih1 (fun h => hn (.inr (.inl h))), ih2 (fun h => hn (.inr (.inr h)))]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    rw [ih1 (fun h => hn (.inl h)), ih2 (fun h => hn (.inr h))]
  | proj _ ih => rw [ih hn]
  | beta => exact (hn (.inl ⟨_, _, rfl⟩)).elim

private theorem not_proof_at_nonzero_sort (hΓ : OnCtx Γ (Params.env.IsType univs))
    (he : Γ ⊢ e : A) (hA : Γ ⊢ A : .sort u) (hu : ¬ u ≈ .zero) : ¬ IsProof Γ e := by
  rintro ⟨P, heP, hP⟩
  have hAP := he.uniqU henv hΓ heP
  have hA0 := hP.defeqU_l henv hΓ hAP.symm
  exact hu ((hA.uniqU henv hΓ hA0).sort_inv henv hΓ)

namespace DomainBoundary
/-- A function from propositions to propositions. -/
def FTy : VExpr := tower 1
/-- A variable predicate on such functions. -/
def PTy : VExpr := .forallE FTy (.sort .zero)
def ctx : List VExpr := [PTy, FTy]
def fn : VExpr := .bvar 1
def etaFn : VExpr := .lam (.sort .zero) (.app (.bvar 2) (.bvar 0))
def domainL : VExpr := .app (.bvar 0) fn
def domainR : VExpr := .app (.bvar 0) etaFn
def left : VExpr := .lam domainL (.sort .zero)
def right : VExpr := .lam domainR (.sort .zero)

private theorem fty_typed (Γ : List VExpr) : Γ ⊢ FTy : .sort (.succ .zero) :=
  tower_typed Params.env univs Γ 1

private theorem pty_typed (Γ : List VExpr) : Γ ⊢ PTy : .sort (.succ .zero) := by
  have h := HasType.forallE (fty_typed Γ) (HasType.sort (l := .zero) (by trivial))
  exact (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero)) (by trivial)
    (by trivial) VLevel.imax_self).defeq h

private theorem ctx_wf : OnCtx ctx (Params.env.IsType univs) :=
  ⟨⟨trivial, _, fty_typed []⟩, _, pty_typed [FTy]⟩

private theorem fn_typed : ctx ⊢ fn : FTy := by
  have h : ctx ⊢ fn : FTy.lift.lift := .bvar (.succ .zero)
  simpa only [FTy, lift, tower_liftN] using h

private theorem pred_typed : ctx ⊢ .bvar 0 : PTy := by
  have h : ctx ⊢ .bvar 0 : PTy.lift := .bvar .zero
  simpa only [PTy, FTy, lift, liftN, tower_liftN] using h

private theorem fn_not_proof : ¬ IsProof ctx fn := by
  apply not_proof_at_nonzero_sort ctx_wf fn_typed (fty_typed ctx)
  intro h
  have := congrFun h []
  simp [VLevel.eval] at this

private theorem fn_eta : IsDefEq Params.env univs ctx fn etaFn FTy :=
  (IsDefEq.eta fn_typed).symm

private theorem domain_typed : ctx ⊢ domainL : .sort .zero :=
  pred_typed.app fn_typed

private theorem domain_eq : IsDefEq Params.env univs ctx domainL domainR (.sort .zero) :=
  .appDF pred_typed fn_eta

private theorem left_typed : ctx ⊢ left : .forallE domainL (.sort (.succ .zero)) :=
  .lam domain_typed (.sort (by trivial))

private theorem left_not_proof : ¬ IsProof ctx left := by
  have ht := HasType.forallE domain_typed
    (HasType.sort (l := .succ .zero) (by trivial))
  apply not_proof_at_nonzero_sort ctx_wf left_typed ht
  intro h
  have := congrFun h []
  simp [VLevel.eval, Lean.Nat.imax] at this

/-- A beta-normal eta-free normal comparison with an opaque eta domain premise. -/
theorem normal : NormalEqF false ctx left right :=
  .lamDF domain_typed domain_eq (.refl (.sort (by trivial)))

/-- The domain premise cannot be replaced by a recursive comparison. -/
theorem no_certificate : ¬ DomainNormal n ctx left right := by
  intro H
  cases H with
  | lamDF _ HD _ =>
    cases HD with
    | appDF _ _ _ _ _ HF =>
      cases HF with
      | proofIrrel hp hl _ => exact fn_not_proof ⟨_, hl, hp⟩
    | proofIrrel hp hl _ => exact not_isProof_of_sort ctx_wf domain_typed ⟨_, hl, hp⟩
  | proofIrrel hp hl _ => exact left_not_proof ⟨_, hl, hp⟩

omit [Params] in
private theorem left_normal : ¬ HasBeta left := by
  simp [left, domainL, fn, HasBeta]

omit [Params] in
private theorem right_normal : ¬ HasBeta right := by
  simp [right, domainR, etaFn, HasBeta]

/-- Beta-only repair of arbitrary eta-free normal comparisons is false, even for
well-typed beta-normal endpoints. Eta is hidden in the old lambda-domain premise.
This refutes that repair claim, not strengthening or a repair allowing eta. -/
theorem no_beta_certificate_join :
    ¬ ∃ l r n, BetaRed left l ∧ BetaRed right r ∧ DomainNormal n ctx l r := by
  rintro ⟨l, r, n, hl, hr, H⟩
  rw [beta_eq_of_not_hasBeta hl left_normal, beta_eq_of_not_hasBeta hr right_normal] at H
  exact no_certificate H

/-- The selective eta-aware relation handles this boundary example directly,
without globally certifying its opaque lambda-domain equality. -/
theorem hybrid : HybridNormal 1 ctx left right :=
  .lamDF domain_typed domain_eq (.refl (.sort (by trivial)))

/-! ## Heterogeneous substitution requires reduction repair -/

/-- Extend by an argument of the left domain; domain conversion also types it on
 the right. -/
def appCtx : List VExpr := domainL :: ctx
def appLeft : VExpr := .app left.lift (.bvar 0)
def appRight : VExpr := .app right.lift (.bvar 0)
def functionType : VExpr := .forallE domainL.lift (.sort (.succ .zero))
def sourceBody : VExpr := .app (.bvar 0) (.bvar 1)

private theorem appCtx_wf : OnCtx appCtx (Params.env.IsType univs) :=
  ⟨ctx_wf, _, domain_typed⟩

private theorem left_lift_typed : appCtx ⊢ left.lift : functionType :=
  left_typed.weak henv

private theorem right_lift_typed : appCtx ⊢ right.lift : functionType :=
  (((normal.defeq ctx_wf).of_l henv ctx_wf left_typed).hasType.2).weak henv

private theorem appLeft_typed : appCtx ⊢ appLeft : .sort (.succ .zero) :=
  left_lift_typed.app (.bvar .zero)

private theorem no_lift_certificate : ¬ DomainNormal n appCtx left.lift right.lift := by
  intro H
  have ht := ((normal.defeq ctx_wf).of_l henv ctx_wf left_typed).hasType.2
  rw [lift_eq_lift', lift_eq_lift'] at H
  obtain ⟨_, H'⟩ := (DomainNormal.reflect n (Ctx.Lift'.skip (A := domainL) .refl)
    ctx_wf appCtx_wf left_typed ht H).2 left_not_proof
  exact no_certificate H'

/-- Direct selective comparison fails after these related lambdas are substituted
into function position. The application result is a sort, ruling out both proof
irrelevance and eta-both as escape cases. -/
theorem no_hybrid_application : ¬ HybridNormal n appCtx appLeft appRight := by
  intro H
  cases H with
  | appDF hs _ _ _ _ _ _ =>
    rcases hs with ⟨hl, _⟩ | ⟨_, Hcert⟩
    · exact hl trivial
    · exact no_lift_certificate Hcert
  | etaBoth hl _ _ =>
    exact (appLeft_typed.uniqU henv appCtx_wf hl).sort_forallE_inv henv appCtx_wf
  | proofIrrel hp hl _ =>
    exact not_isProof_of_sort appCtx_wf appLeft_typed ⟨_, hl, hp⟩

private theorem source_typed : functionType :: appCtx ⊢ sourceBody : .sort (.succ .zero) := by
  have hf : functionType :: appCtx ⊢ .bvar 0 :
      .forallE domainL.lift.lift (.sort (.succ .zero)) := .bvar .zero
  exact hf.app (.bvar (.succ .zero))

/-- A concrete failure of unrestricted heterogeneous substitution for the hybrid
relation itself. Both arguments and the source body have selective comparisons;
their two instances do not. This does not refute closure up to reduction. -/
theorem unrestricted_substitution_fails :
    HybridNormal 1 appCtx left.lift right.lift ∧
    HybridNormal 0 (functionType :: appCtx) sourceBody sourceBody ∧
    ¬ ∃ n, HybridNormal n appCtx (sourceBody.inst left.lift) (sourceBody.inst right.lift) := by
  refine ⟨hybrid.weakN .one, .refl source_typed, ?_⟩
  rintro ⟨n, H⟩
  have H' : HybridNormal n appCtx appLeft appRight := by
    simpa only [sourceBody, appLeft, appRight, inst, instVar, Nat.lt_irrefl,
      Nat.zero_lt_one, Nat.not_lt_zero, Nat.one_ne_zero, ↓reduceIte, liftN_zero] using H
  exact no_hybrid_application H'

/-- One matched beta contraction repairs this substitution boundary. -/
theorem application_repaired :
    BetaRed appLeft (.sort .zero) ∧ BetaRed appRight (.sort .zero) ∧
      HybridNormal 0 appCtx (.sort .zero) (.sort .zero) :=
  ⟨.beta, .beta, .refl (.sort (by trivial))⟩

end DomainBoundary
end Lean4Lean.VEnv.Strengthening
