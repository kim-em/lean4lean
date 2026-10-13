import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainEnvironment
import Lean4Lean.Theory.Typing.Strengthening.DomainCertificateBoundary
import Lean4Lean.Theory.Typing.Confluence.Params
import Lean4Lean.Theory.Typing.Strengthening.LambdaReannotation

/-! # A typed obstruction to beta-only selective repair

The recursive family admits self-application. Eta-equivalent family parameters
produce opaque domain equalities which survive every finite beta reduction of the
self-application loop. This concerns a repair strategy, not strengthening itself.
-/
namespace Lean4Lean.VEnv.Strengthening.RecursiveDomain
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments

def loopCtx : List VExpr := [argType]
def fn : VExpr := .bvar 0
def etaFn : VExpr := .lam (.sort .zero) (.app (.bvar 1) (.bvar 0))
def domainL (c : Name) : VExpr := .app (.const c []) fn
def domainR (c : Name) : VExpr := .app (.const c []) etaFn
def selfBody : VExpr := .app (.bvar 0) (.bvar 0)
def diagonal (D : VExpr) : VExpr := .lam D selfBody
def omegaTerm (D : VExpr) : VExpr := .app (diagonal D) (diagonal D)

/-- The only root beta contraction of the diagonal self-application returns
exactly the same term. Its domain is allowed to be any beta-normal expression. -/
theorem omega_beta_eq (hn : ¬ HasBeta D) (R : BetaRed (omegaTerm D) out) : out = omegaTerm D := by
  have hd : ¬ HasBeta (diagonal D) := by simpa [diagonal, selfBody, HasBeta] using hn
  suffices aux : ∀ {e out}, BetaRed e out → e = omegaTerm D → out = omegaTerm D from aux R rfl
  intro e out R
  induction R with
  | refl => exact id
  | trans _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | app Rf Ra _ _ =>
    intro h
    simp only [omegaTerm] at h
    cases h
    rw [beta_eq_of_not_hasBeta Rf hd, beta_eq_of_not_hasBeta Ra hd]
    rfl
  | beta =>
    intro h
    simp only [omegaTerm, diagonal, VExpr.app.injEq, VExpr.lam.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [selfBody, inst, instVar, omegaTerm, diagonal]
  | lam | forallE | proj => intro h; cases h

section
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

private theorem ctx_wf : OnCtx loopCtx (Params.env.IsType univs) :=
  ⟨trivial, _, argType_typed Params.env univs []⟩

private theorem fn_typed : loopCtx ⊢ fn : argType := by
  have h : loopCtx ⊢ fn : argType.lift := .bvar .zero
  simpa only [argType, lift, tower_liftN] using h

private theorem fn_not_proof : ¬ IsProof loopCtx fn := by
  rintro ⟨P, hfP, hP⟩
  have hA0 := hP.defeqU_l henv ctx_wf (fn_typed.uniqU henv ctx_wf hfP).symm
  have hu := ((argType_typed Params.env univs loopCtx).uniqU henv ctx_wf hA0).sort_inv henv ctx_wf
  have := congrFun hu []
  simp [VLevel.eval] at this

private theorem fn_eta : loopCtx ⊢ fn ≡ etaFn : argType := (IsDefEq.eta fn_typed).symm

private theorem domain_typed (hc : Params.env.constants c = some (declaration c).toVConstant) : loopCtx ⊢ domainL c : .sort (.succ .zero) :=
  (family_typed hc univs loopCtx).app fn_typed

private theorem domain_eq (hc : Params.env.constants c = some (declaration c).toVConstant) : loopCtx ⊢ domainL c ≡ domainR c : .sort (.succ .zero) :=
  .appDF (family_typed hc univs loopCtx) fn_eta

/-- The installed recursive equation is available at the chosen parameter. -/
theorem domain_recursive (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : loopCtx ⊢ domainL c ≡ .forallE (domainL c) (.sort .zero) :
    .sort (.succ .zero) := by
  have he := IsDefEq.appDF (hδ loopCtx) fn_typed
  have hb := BetaRed.simAt (env := Params.env) henv.orderedStrong henv.betaSubjectReduction
    (BetaRed.beta (A := argType) (b := .forallE (.app (.const c []) (.bvar 0)) (.sort .zero))
      (a := fn)) ctx_wf _ he.hasType.2
  simpa [familyValue, domainL, inst, instVar] using he.trans hb

private theorem body_typed (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : domainL c :: loopCtx ⊢ selfBody : .sort .zero := by
  have hv : domainL c :: loopCtx ⊢ .bvar 0 : (domainL c).lift := .bvar .zero
  have hf := ((domain_recursive hδ).weakN henv Ctx.LiftN.one).defeq hv
  exact hf.app hv

private theorem diagonal_typed (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : loopCtx ⊢ diagonal (domainL c) : .forallE (domainL c) (.sort .zero) :=
  .lam (domain_typed hc) (body_typed hδ)

private theorem diagonal_at_domain (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : loopCtx ⊢ diagonal (domainL c) : domainL c :=
  (domain_recursive hδ).symm.defeq (diagonal_typed hc hδ)

/-- The looping application is a proposition, hence is not itself a proof. -/
theorem omega_typed (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : loopCtx ⊢ omegaTerm (domainL c) : .sort .zero :=
  (diagonal_typed hc hδ).app (diagonal_at_domain hc hδ)

private theorem diagonal_not_proof (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : ¬ IsProof loopCtx (diagonal (domainL c)) := by
  intro hp
  exact not_isProof_of_sort ctx_wf (omega_typed hc hδ)
    (IsProof.app_fn ctx_wf (diagonal_typed hc hδ) (diagonal_at_domain hc hδ) hp)

/-- The two diagonal functions have a selective comparison at a common type. -/
theorem diagonal_hybrid (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : HybridNormal 1 loopCtx (diagonal (domainL c)) (diagonal (domainR c)) :=
  .lamDF (domain_typed hc) (domain_eq hc) (.refl (body_typed hδ))

/-- Their common type and the recursive equation also type both arguments of the
right self-application. The old eta-free normal relation compares the loops. -/
theorem omega_normal (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : NormalEqF false loopCtx (omegaTerm (domainL c)) (omegaTerm (domainR c)) := by
  have H : NormalEqF false loopCtx (diagonal (domainL c)) (diagonal (domainR c)) :=
    .lamDF (domain_typed hc) (domain_eq hc) (.refl (body_typed hδ))
  have hl := diagonal_typed hc hδ
  have hr := ((H.defeq ctx_wf).of_l henv ctx_wf hl).hasType.2
  have har := (domain_recursive hδ).symm.defeq hr
  exact .appDF hl hr (diagonal_at_domain hc hδ) har H H

private theorem no_domain_certificate (hc : Params.env.constants c = some (declaration c).toVConstant) : ¬ DomainNormal n loopCtx (domainL c) (domainR c) := by
  intro H
  cases H with
  | appDF _ _ _ _ _ HF =>
    cases HF with
    | proofIrrel hp hl _ => exact fn_not_proof ⟨_, hl, hp⟩
  | proofIrrel hp hl _ => exact not_isProof_of_sort ctx_wf (domain_typed hc) ⟨_, hl, hp⟩

private theorem no_diagonal_certificate (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) :
    ¬ DomainNormal n loopCtx (diagonal (domainL c)) (diagonal (domainR c)) := by
  intro H
  cases H with
  | lamDF _ HD _ => exact no_domain_certificate hc HD
  | proofIrrel hp hl _ => exact diagonal_not_proof hc hδ ⟨_, hl, hp⟩

/-- The selective relation cannot directly compare the looping applications. -/
theorem no_omega_hybrid (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) : ¬ HybridNormal n loopCtx (omegaTerm (domainL c)) (omegaTerm (domainR c)) := by
  intro H
  cases H with
  | appDF hs _ _ _ _ _ _ =>
    rcases hs with ⟨hl, _⟩ | ⟨_, Hcert⟩
    · exact hl trivial
    · exact no_diagonal_certificate hc hδ Hcert
  | etaBoth hl _ _ => exact ((omega_typed hc hδ).uniqU henv ctx_wf hl).sort_forallE_inv henv ctx_wf
  | proofIrrel hp hl _ => exact not_isProof_of_sort ctx_wf (omega_typed hc hδ) ⟨_, hl, hp⟩

/-- No finite beta reductions repair these normally equal, typed loops into a
selective comparison. This refutes arbitrary-round beta-only repair, not repair
using eta or the full reduction system, and not canonical-Eq strengthening. -/
theorem no_beta_hybrid_join (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) :
    ¬ ∃ l r n, BetaRed (omegaTerm (domainL c)) l ∧ BetaRed (omegaTerm (domainR c)) r ∧
      HybridNormal n loopCtx l r := by
  rintro ⟨l, r, n, hl, hr, H⟩
  have hnL : ¬ HasBeta (domainL c) := by simp [domainL, fn, HasBeta]
  have hnR : ¬ HasBeta (domainR c) := by simp [domainR, etaFn, HasBeta]
  rw [omega_beta_eq hnL hl, omega_beta_eq hnR hr] at H
  exact no_omega_hybrid hc hδ H

/-- Eta expansion at the already available common function type reannotates the
right diagonal to the left one. The full reduction system repairs this beta-only
obstruction without normalizing the self-application loop. -/
theorem full_repair (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ .const c [] ≡ familyValue c : familyType) :
    FullReduction loopCtx (omegaTerm (domainR c)) (omegaTerm (domainL c)) ∧
    HybridNormal 0 loopCtx (omegaTerm (domainL c)) (omegaTerm (domainL c)) := by
  have H := diagonal_hybrid hc hδ
  have hr := ((H.defeq ctx_wf).of_l henv ctx_wf (diagonal_typed hc hδ)).hasType.2
  have R : FullReduction loopCtx (diagonal (domainR c)) (diagonal (domainL c)) :=
    lambda_reannotation hr
  exact ⟨R.app R, .refl (omega_typed hc hδ)⟩

end
/-- The beta-only repair obstruction is realized in an actual well-formed extension
of any canonical-Eq environment at a fresh name. Both loops are typed propositions
and have an eta-free normal comparison; no finite beta join has a hybrid comparison.
This is a counterexample to the repair strategy, not to definitional strengthening. -/
theorem canonical_beta_only_failure (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    (extended base c).HasCanonicalEq ∧
    letI := (extended_wf hbase hfresh).params 0
    (extended base c).HasType 0 loopCtx (omegaTerm (domainL c)) (.sort .zero) ∧
    (extended base c).HasType 0 loopCtx (omegaTerm (domainR c)) (.sort .zero) ∧
    NormalEqF false loopCtx (omegaTerm (domainL c)) (omegaTerm (domainR c)) ∧
    ¬ ∃ l r n, BetaRed (omegaTerm (domainL c)) l ∧ BetaRed (omegaTerm (domainR c)) r ∧
      HybridNormal n loopCtx l r := by
  refine ⟨extended_canonicalEq heq hfresh, ?_⟩
  letI := (extended_wf hbase hfresh).params 0
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (.const c []) (familyValue c) familyType :=
    fun Γ => equation 0 Γ
  have ht := omega_typed hc hδ
  have H := omega_normal hc hδ
  exact ⟨ht, ((H.defeq ctx_wf).of_l henv ctx_wf ht).hasType.2, H, no_beta_hybrid_join hc hδ⟩

end Lean4Lean.VEnv.Strengthening.RecursiveDomain
