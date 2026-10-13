import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaLoop

/-! # The guarded-loop obstruction already occurs for propositions

Applying each function-valued loop to a proposition variable produces two normally
equal propositions. No finite beta-only bidirectional join exists. The obstruction
is realized in a canonical-Eq-preserving environment and has a finite full repair.
It rules out a join strategy for PropFront, not PropFront itself.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments

def propCtx : List VExpr := [prop]
def propLeft (c : Name) : VExpr := .app (omegaTerm c) (.bvar 0)
def propRight (c : Name) : VExpr := .app (etaOmega c) (.bvar 0)

/-- Applying the beta-fixed ordinary loop to a variable remains beta-fixed. -/
theorem propLeft_beta_eq (R : BetaRed (propLeft c) out) : out = propLeft c := by
  suffices aux : ∀ {e out}, BetaRed e out → e = propLeft c → out = propLeft c from aux R rfl
  intro e out R
  induction R with
  | refl => exact id
  | trans _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | app Rf Ra _ _ =>
    intro h
    cases h
    rw [omega_beta_eq Rf, beta_eq_of_not_hasBeta Ra (by simp [HasBeta])]
    rfl
  | beta => intro h; cases h
  | lam | forallE | proj => intro h; cases h

section
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

private theorem propCtx_wf : OnCtx propCtx (Params.env.IsType univs) :=
  ⟨trivial, _, HasType.sort (by trivial)⟩

private theorem propVar_typed : propCtx ⊢ .bvar 0 : prop := .bvar .zero

/-- The ordinary loop application is a proposition, hence not a proof. -/
theorem propLeft_typed
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    propCtx ⊢ propLeft c : prop := HasType.app (omega_typed hc hδ) propVar_typed

/-- The proposition pair has an ordinary normal comparison at a common sort. -/
theorem propositions_normal
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    NormalEqF true propCtx (propLeft c) (propRight c) := by
  have H := omega_normal hc hδ propCtx_wf
  have hl := omega_typed (Γ := propCtx) hc hδ
  have hr := ((H.defeq propCtx_wf).of_l henv propCtx_wf hl).hasType.2
  exact .appDF hl hr propVar_typed propVar_typed H (.refl propVar_typed)

/-- Even proposition endpoints do not suffice for beta-only bidirectional joins. -/
theorem propositions_no_beta_join
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    ¬ BiBetaJoin true propCtx (propLeft c) (propRight c) := by
  rintro ⟨l, r, n, Rl, Rr, H⟩
  rw [propLeft_beta_eq Rl] at H
  exact no_common hδ propCtx_wf H (.app (.app .diagonal)) (by simp [propLeft, IsLam])
    (Guarded.beta Rr (.app etaOmega_guarded .var))
    (not_isProof_of_sort propCtx_wf (propLeft_typed hc hδ))

/-- Full repair reaches the right proposition without any recursive beta unfolding. -/
theorem propositions_full_repair
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    FullReduction propCtx (propLeft c) (propRight c) :=
  (full_repair hc hδ propCtx_wf).1.app .rfl

end

/-- A canonical-Eq instance of the beta-only failure at exactly the proposition
sort. The terms are already equal in the smaller context and have full repair. -/
theorem canonical_proposition_failure (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    (extended base c).HasCanonicalEq ∧
    letI := (extended_wf hbase hfresh).params 0
    (extended base c).HasType 0 propCtx (propLeft c) prop ∧
    (extended base c).HasType 0 propCtx (propRight c) prop ∧
    NormalEqF true propCtx (propLeft c) (propRight c) ∧
    ¬ BiBetaJoin true propCtx (propLeft c) (propRight c) ∧
    FullReduction propCtx (propLeft c) (propRight c) := by
  refine ⟨extended_canonicalEq heq hfresh, ?_⟩
  letI := (extended_wf hbase hfresh).params 0
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Γ => equation 0 Γ
  have ht := propLeft_typed hc hδ
  have H := propositions_normal hc hδ
  exact ⟨ht, ((H.defeq propCtx_wf).of_l henv propCtx_wf ht).hasType.2, H,
    propositions_no_beta_join hc hδ, propositions_full_repair hc hδ⟩

end Lean4Lean.VEnv.Strengthening.GuardedEta
