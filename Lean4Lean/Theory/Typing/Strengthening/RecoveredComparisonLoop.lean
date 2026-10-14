import Lean4Lean.Theory.Typing.Strengthening.RecoveredComparison
import Lean4Lean.Theory.Typing.Strengthening.RecoveredEtaLoop
import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaPropositions

/-! # Direct comparison of the guarded eta loop using recovered types

The old mode-indexed comparison has no finite beta join for this pair. Recovering
the two diagonal types allows their common-mode comparison in function position,
so the new certificate compares the loops directly, without reducing either one.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

/-- The unexpanded diagonal has its displayed Pi type by body reconstruction. -/
theorem diagonal_type_recovery (hd : D.unfolds c [] (domainValue c)) :
    TypeRecovery D depth Γ (diagonal c) (domainValue c) :=
  .lam (selfBody_type_recovery hd)

/-- The expanded diagonal independently recovers exactly that same Pi type. -/
theorem etaDiagonal_type_recovery (hd : D.unfolds c [] (domainValue c)) :
    TypeRecovery D depth Γ (etaDiagonal c) (domainValue c) := by
  have R := (selfBody_type_recovery (Γ := Γ) (depth := depth) hd).weakN
    (Ctx.LiftN.one (A := prop))
  have R' := TypeRecovery.app (a := .bvar 0) R
  exact .lam (.lam R')

private theorem body_typing
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    domain c :: Γ ⊢ selfBody : resultType := by
  have hv : domain c :: Γ ⊢ .bvar 0 : domain c := .bvar .zero
  exact HasType.app ((hδ _).defeq hv) hv

/-- The ordinary common-mode body-eta certificate is already available; it was
its use independently in function position that previously failed. -/
theorem diagonal_common_comparison
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero)) :
    BiNormal true 3 Γ (diagonal c) (etaDiagonal c) := by
  have hb : domain c :: Γ ⊢ selfBody : resultType := body_typing hδ
  have he : prop :: domain c :: Γ ⊢ .app selfBody.lift (.bvar 0) : prop :=
    HasType.app (hb.weak henv) (.bvar .zero)
  exact .lamCommon (domain_typed hc univs Γ) (domain_typed hc univs Γ)
    (.etaR hb (.refl he))

/-- Recovered types turn that exact common-mode certificate into an independent
one, retaining both original diagonal terms. -/
theorem diagonal_recovered_comparison
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hd : D.unfolds c [] (domainValue c)) :
    RecoveredComparison D depth false Γ (diagonal c) (etaDiagonal c) :=
  .sameType (diagonal_type_recovery hd) (etaDiagonal_type_recovery hd)
    (.base (diagonal_common_comparison hc hδ))

/-- The guarded recursive loops compare directly in either mode. No root beta
contraction or body eta expansion is required by the certificate. -/
theorem omega_recovered_comparison
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hd : D.unfolds c [] (domainValue c)) (hΓ : OnCtx Γ (env.IsType univs)) :
    RecoveredComparison D depth mode Γ (omegaTerm c) (etaOmega c) := by
  have H := diagonal_common_comparison (Γ := Γ) hc hδ
  have hl : Γ ⊢ diagonal c : domainValue c := .lam (domain_typed hc univs Γ) (body_typing hδ)
  have hr := ((H.defeq hΓ).of_l henv hΓ hl).hasType.2
  exact .app hl hr ((hδ Γ).symm.defeq hl) ((hδ Γ).symm.defeq hr)
    (diagonal_recovered_comparison hc hδ hd) (.base H)

/-- Applying the loop to a proposition variable retains the new independent
function certificate, so the old obstruction at proposition endpoints is covered. -/
theorem propositions_recovered_comparison
    (hc : env.constants c = some (declaration c).toVConstant)
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hd : D.unfolds c [] (domainValue c)) :
    RecoveredComparison D depth true propCtx (propLeft c) (propRight c) := by
  have hΓ : OnCtx propCtx (env.IsType univs) := ⟨trivial, _, HasType.sort (by trivial)⟩
  have H := omega_recovered_comparison (depth := depth) (mode := false) hc hδ hd hΓ
  have hl := omega_typed (Γ := propCtx) hc hδ
  have hr := ((H.defeq hΓ).of_l henv hΓ hl).hasType.2
  have hv : propCtx ⊢ .bvar 0 : prop := .bvar .zero
  exact .app hl hr hv hv H (.base (.refl hv))

omit [Params] in
/-- An actual canonical-Eq-preserving extension exhibits the strict improvement:
the new proposition comparison exists while the old one has no finite beta join. -/
theorem canonical_recovered_comparison (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    let henv := extended_wf hbase hfresh
    letI := henv.params 0
    let D := Definitions.ofEnv (extended base c) 0 henv
    (extended base c).HasCanonicalEq ∧
    RecoveredComparison D 0 true propCtx (propLeft c) (propRight c) ∧
    ¬ BiBetaJoin true propCtx (propLeft c) (propRight c) := by
  let henv := extended_wf hbase hfresh
  letI := henv.params 0
  let D := Definitions.ofEnv (extended base c) 0 henv
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Γ => equation 0 Γ
  exact ⟨extended_canonicalEq heq hfresh,
    propositions_recovered_comparison hc hδ (PureObservation.guarded_definition henv 0),
    propositions_no_beta_join hc hδ⟩

end Lean4Lean.VEnv.Strengthening.GuardedEta
