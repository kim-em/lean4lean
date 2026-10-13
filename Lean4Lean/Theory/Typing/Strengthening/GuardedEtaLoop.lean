import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaComparison

/-! # Canonical-Eq failure of beta-only bidirectional joins

The recursive type `D = D → (Prop → Prop)` types two eta-equal diagonals. Their
self-applications admit an ordinary normal comparison. Every beta reduct of the
eta-expanded loop retains its guarded syntax, preventing a bidirectional join in
either mode. A finite full eta repair is exhibited separately.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
section
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

private theorem body_typed
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    domain c :: Γ ⊢ selfBody : resultType := by
  have hv : domain c :: Γ ⊢ .bvar 0 : domain c := .bvar .zero
  exact HasType.app ((hδ _).defeq hv) hv

private theorem diagonal_typed
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    Γ ⊢ diagonal c : domainValue c := .lam (domain_typed hc univs Γ) (body_typed hδ)

/-- The recursive equation types the unexpanded self-application at a function
returning propositions; it is not a proof. -/
theorem omega_typed
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    Γ ⊢ omegaTerm c : resultType :=
  HasType.app (diagonal_typed hc hδ) ((hδ Γ).symm.defeq (diagonal_typed hc hδ))

/-- Eta of the diagonal's body is permitted by ordinary common-type comparison. -/
theorem diagonal_normal
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    NormalEqF true Γ (diagonal c) (etaDiagonal c) := by
  have hb : domain c :: Γ ⊢ selfBody : resultType := body_typed hδ
  have he : prop :: domain c :: Γ ⊢ .app selfBody.lift (.bvar 0) : prop :=
    HasType.app (hb.weak henv) (.bvar .zero)
  exact .lamDF (domain_typed hc univs Γ) (domain_typed hc univs Γ) (.etaR hb (.refl he))

/-- Ordinary normal equality compares the two loops before any reduction. -/
theorem omega_normal
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    NormalEqF true Γ (omegaTerm c) (etaOmega c) := by
  have H := diagonal_normal (Γ := Γ) hc hδ
  have hl := diagonal_typed (Γ := Γ) hc hδ
  have hr := ((H.defeq hΓ).of_l henv hΓ hl).hasType.2
  exact .appDF hl hr ((hδ Γ).symm.defeq hl) ((hδ Γ).symm.defeq hr) H H

/-- Neither comparison mode admits any finite beta-only join of these normally
equal loops. This includes common-type mode and hence refutes beta-only completeness. -/
theorem no_beta_join
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ¬ BiBetaJoin mode Γ (omegaTerm c) (etaOmega c) := by
  rintro ⟨l, r, n, Rl, Rr, H⟩
  rw [omega_beta_eq Rl] at H
  have hn : ¬ IsProof Γ (omegaTerm c) :=
    not_isProof_function_to_sort hΓ (omega_typed hc hδ)
  have hg := Guarded.beta Rr (etaOmega_guarded (c := c))
  cases mode with
  | false => exact no_independent hδ hΓ H (.app .diagonal) hg hn
  | true => exact no_common hδ hΓ H (.app .diagonal) (by simp [omegaTerm, IsLam]) hg hn

/-- Full eta expansion of each diagonal body repairs the loop pair in two finite
congruence steps; no recursive root redex has to be normalized. -/
theorem full_repair
    (hc : Params.env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    FullReduction Γ (omegaTerm c) (etaOmega c) ∧ BiNormal false 0 Γ (etaOmega c) (etaOmega c) := by
  have R : FullReduction Γ (diagonal c) (etaDiagonal c) :=
    .lam .rfl (.tail .rfl (.funEta (body_typed hδ)))
  have ht := ((omega_normal hc hδ hΓ).defeq hΓ).of_l henv hΓ (omega_typed hc hδ)
  exact ⟨R.app R, .refl ht.hasType.2⟩

end

/-- The failure of beta-only bidirectional completeness occurs in an actual
well-formed extension preserving canonical Eq. It is a counterexample to the join
strategy, not to strengthening: the full eta repair above remains available. -/
theorem canonical_beta_only_failure (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    (extended base c).HasCanonicalEq ∧
    letI := (extended_wf hbase hfresh).params 0
    (extended base c).HasType 0 [] (omegaTerm c) resultType ∧
    (extended base c).HasType 0 [] (etaOmega c) resultType ∧
    NormalEqF true [] (omegaTerm c) (etaOmega c) ∧
    ¬ BiBetaJoin true [] (omegaTerm c) (etaOmega c) := by
  refine ⟨extended_canonicalEq heq hfresh, ?_⟩
  letI := (extended_wf hbase hfresh).params 0
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Γ => equation 0 Γ
  have ht := omega_typed (Γ := []) hc hδ
  have hΓ : OnCtx [] (Params.env.IsType univs) := trivial
  have H := omega_normal hc hδ hΓ
  exact ⟨ht, ((H.defeq hΓ).of_l henv hΓ ht).hasType.2, H, no_beta_join hc hδ hΓ⟩

end Lean4Lean.VEnv.Strengthening.GuardedEta
