import Lean4Lean.Theory.Typing.CaseResult
import Lean4Lean.Theory.Typing.LevelEquiv

/-! Syntax congruence for generated case programs. Elimination universes are
compared at complete case applications, where their motives determine them. -/

namespace Lean4Lean.VExpr
open InductiveSignature InductiveSignature.CaseSchema

inductive CaseLevelEquiv (env : VEnv) (U : Nat) : VExpr → VExpr → Prop
  | levels : LEquiv U e e' → CaseLevelEquiv env U e e'
  | app : CaseLevelEquiv env U fn fn' → CaseLevelEquiv env U arg arg' →
      CaseLevelEquiv env U (.app fn arg) (.app fn' arg')
  | lam : CaseLevelEquiv env U domain domain' → CaseLevelEquiv env U body body' →
      CaseLevelEquiv env U (.lam domain body) (.lam domain' body')
  | forallE : CaseLevelEquiv env U domain domain' → CaseLevelEquiv env U body body' →
      CaseLevelEquiv env U (.forallE domain body) (.forallE domain' body')
  | proj : CaseLevelEquiv env U major major' →
      CaseLevelEquiv env U (.proj name field major) (.proj name field major')
  | caseApp {schema : CaseSchema} {owner : Fin schema.signature.families.size} :
      env.eliminators block schema → List.Forall₂ (· ≈ ·) levels levels' →
      args.length = VEnv.caseMajorArity schema owner + 1 →
      List.Forall₂ (CaseLevelEquiv env U) args args' →
      CaseLevelEquiv env U
        (mkApps (.elim block owner.val (target :: levels)) args)
        (mkApps (.elim block owner.val (target' :: levels')) args')

namespace CaseLevelEquiv
variable {σ σ' : VExpr.Subst}

protected theorem refl (e : VExpr) : CaseLevelEquiv env U e e := .levels .refl

theorem liftN (H : CaseLevelEquiv env U e e') :
    CaseLevelEquiv env U (e.liftN n k) (e'.liftN n k) := by
  exact CaseLevelEquiv.rec
    (motive_1 := fun e e' _ => ∀ k, CaseLevelEquiv env U (e.liftN n k) (e'.liftN n k))
    (motive_2 := fun es es' _ => ∀ k, List.Forall₂ (CaseLevelEquiv env U)
      (es.map (·.liftN n k)) (es'.map (·.liftN n k)))
    (fun h k => .levels h.liftN)
    (fun _ _ ihf iha k => .app (ihf k) (iha k))
    (fun _ _ ihd ihb k => .lam (ihd k) (ihb (k + 1)))
    (fun _ _ ihd ihb k => .forallE (ihd k) (ihb (k + 1)))
    (fun _ ih k => .proj (ih k))
    (fun hl hu ha hs ih k => by
      simp only [liftN_mkApps, VExpr.liftN]
      exact caseApp hl hu (by simpa using ha) (ih k))
    (fun _ => .nil)
    (fun _ _ ih ihs k => .cons (ih k) (ihs k)) H k

private theorem subst_lift (h : ∀ i, CaseLevelEquiv env U (σ i) (σ' i)) :
    ∀ i, CaseLevelEquiv env U (σ.lift i) (σ'.lift i) := by
  intro i
  cases i with
  | zero => exact .refl _
  | succ i => exact (h i).liftN

private theorem subst_refl (e : VExpr)
    (h : ∀ i, CaseLevelEquiv env U (σ i) (σ' i)) :
    CaseLevelEquiv env U (e.subst σ) (e.subst σ') := by
  induction e generalizing σ σ' with
  | bvar i => exact h i
  | sort | const | elim => exact .refl _
  | app _ _ ihf iha => exact .app (ihf h) (iha h)
  | lam _ _ ihd ihb => exact .lam (ihd h) (ihb (subst_lift h))
  | forallE _ _ ihd ihb => exact .forallE (ihd h) (ihb (subst_lift h))
  | proj _ _ _ ih => exact .proj (ih h)

private theorem subst_levels (H : LEquiv U e e')
    (h : ∀ i, CaseLevelEquiv env U (σ i) (σ' i)) :
    CaseLevelEquiv env U (e.subst σ) (e'.subst σ') := by
  induction H generalizing σ σ' with
  | refl => exact subst_refl _ h
  | sort he hw => exact .levels (.sort he hw)
  | const he hw => exact .levels (.const he hw)
  | elim he hw => exact .levels (.elim he hw)
  | app _ _ ihf iha => exact .app (ihf h) (iha h)
  | lam _ _ ihd ihb => exact .lam (ihd h) (ihb (subst_lift h))
  | forallE _ _ ihd ihb => exact .forallE (ihd h) (ihb (subst_lift h))
  | proj _ ih => exact .proj (ih h)

/-- Generated case congruence is preserved by related simultaneous term
substitutions, including the previous-field substitutions of projections. -/
theorem subst (H : CaseLevelEquiv env U e e')
    (h : ∀ i, CaseLevelEquiv env U (σ i) (σ' i)) :
    CaseLevelEquiv env U (e.subst σ) (e'.subst σ') := by
  exact CaseLevelEquiv.rec
    (motive_1 := fun e e' _ => ∀ (σ σ' : VExpr.Subst),
      (∀ i, CaseLevelEquiv env U (σ i) (σ' i)) →
      CaseLevelEquiv env U (e.subst σ) (e'.subst σ'))
    (motive_2 := fun es es' _ => ∀ (σ σ' : VExpr.Subst),
      (∀ i, CaseLevelEquiv env U (σ i) (σ' i)) →
      List.Forall₂ (CaseLevelEquiv env U) (es.map (fun e => VExpr.subst e σ)) (es'.map (fun e => VExpr.subst e σ')))
    (fun hl _ _ h => subst_levels hl h)
    (fun _ _ ihf iha _ _ h => .app (ihf _ _ h) (iha _ _ h))
    (fun _ _ ihd ihb _ _ h => .lam (ihd _ _ h) (ihb _ _ (subst_lift h)))
    (fun _ _ ihd ihb _ _ h => .forallE (ihd _ _ h) (ihb _ _ (subst_lift h)))
    (fun _ ih _ _ h => .proj (ih _ _ h))
    (fun hl hu ha hs ih _ _ h => by
      simp only [subst_mkApps, VExpr.subst]
      exact caseApp hl hu (by simpa using ha) (ih _ _ h))
    (fun _ _ _ => .nil)
    (fun _ _ ih ihs _ _ h => .cons (ih _ _ h) (ihs _ _ h)) H σ σ' h

/-- Congruence along ordinary application spines. -/
theorem mkApps (H : CaseLevelEquiv env U fn fn')
    (ha : List.Forall₂ (CaseLevelEquiv env U) args args') :
    CaseLevelEquiv env U (VExpr.mkApps fn args) (VExpr.mkApps fn' args') := by
  induction ha generalizing fn fn' with
  | nil => exact H
  | cons h _ ih => exact ih (.app H h)

/-- Congruence of complete lambda telescopes. -/
theorem wrapLams (H : List.Forall₂ (CaseLevelEquiv env U) domains domains')
    (hb : CaseLevelEquiv env U body body') :
    CaseLevelEquiv env U (VExpr.wrapLams domains body) (VExpr.wrapLams domains' body') := by
  induction H with
  | nil => exact hb
  | cons h _ ih => exact .lam h ih

/-- Simultaneous substitution in declaration order preserves the generated
case congruence; it introduces no comparison of unused field universes. -/
theorem instantiateParams (H : CaseLevelEquiv env U e e')
    (ha : List.Forall₂ (CaseLevelEquiv env U) args args') :
    CaseLevelEquiv env U
      (InductiveSignature.instantiateParams e args)
      (InductiveSignature.instantiateParams e' args') := by
  unfold InductiveSignature.instantiateParams
  apply H.subst
  intro i
  have hlen := List.Forall₂.length_eq ha
  by_cases hi : i < args.length
  · simp only [dif_pos hi, dif_pos (show i < args'.length by omega)]
    have hj : args.length - 1 - i < args.length := by omega
    simpa only [hlen] using VEnv.case_forall₂_get ha hj (by omega)
  · simp only [dif_neg hi, dif_neg (show ¬ i < args'.length by omega), hlen]
    exact .refl _

end CaseLevelEquiv
end Lean4Lean.VExpr
