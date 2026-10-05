import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaFactor
import Lean4Lean.Theory.Typing.AnchoredFunctionDomain

/-! The eta key program first changes the actual old row's domain at its
old input, then enlarges the input at the actual source domain. It never
requests a larger capability at the old frozen domain. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem EtaFactor.adapter
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    {lambdaKey : Key n} {output : Atom n} {domainSupport : Profile n}
    (factor : EtaFactor env U registry Γ locals σ f lambdaKey output outside)
    {support : Profile (factor.rank + 1)}
    (guard : LambdaGuard env U registry Γ σ A lambdaKey domainSupport)
    (related : Related env U registry Γ left right (.forallE (A.subst σ) bodyType)
      (Profile.fn factor.key factor.rawOutput) support) :
    Nonempty (NormalProfileAdapter env U registry Γ (Profile.fn factor.key factor.rawOutput)
      (raiseProfile (factor.rank + 1) (Nat.succ_le_succ factor.bound)
        (Profile.fn lambdaKey output))) := by
  classical
  obtain ⟨oldSupport, oldTyped, oldFormed, oldPath, oldBridge⟩ :=
    related.fn_domain_alignment henv hscoped hΓ
  let highKey := raiseKey factor.rank factor.bound lambdaKey
  have highGuard := guard.raise henv factor.bound
  let anchored := reanchorKey factor.key lambdaKey.anchor
  let actual := domainKey anchored (A.subst σ)
  let widened := domainKey highKey (A.subst σ)
  have reanchor : NormalAtomAdapter (n := factor.rank + 1) env U registry Γ
      (.fn factor.key factor.rawOutput) (.fn anchored factor.rawOutput) :=
    (AtomView.reanchor (output := factor.rawOutput) factor.admitted).toAdapter henv hscoped hΓ
  have domain : NormalAtomAdapter (n := factor.rank + 1) env U registry Γ
      (.fn anchored factor.rawOutput) (.fn actual factor.rawOutput) :=
    (AtomView.domainRekey (key := anchored) (output := factor.rawOutput)
      oldPath oldTyped oldFormed oldBridge).toAdapter henv hscoped hΓ
  have seed := Admitted.rekey henv highGuard.path highGuard.inputTyped highGuard.formed
    highGuard.domains highGuard.anchor
  have normalSeed := AdapterNormal.normalizeAdmission henv hscoped hΓ seed
  have input : NormalAtomAdapter (n := factor.rank + 1) env U registry Γ
      (.fn actual factor.rawOutput) (.fn widened factor.rawOutput) := by
    exact .fn (.input (.supplied normalSeed) factor.arguments) (.refl _)
  have restore : NormalAtomAdapter (n := factor.rank + 1) env U registry Γ
      (.fn widened factor.rawOutput) (.fn highKey factor.rawOutput) :=
    (AtomView.domainRekey (key := widened) (output := factor.rawOutput)
      highGuard.path.symm highGuard.inputTyped highGuard.formed
      (highGuard.domains.symm henv highGuard.inputTyped.wf_type)).toAdapter henv hscoped hΓ
  have result : NormalAtomAdapter (n := factor.rank + 1) env U registry Γ
      (.fn highKey factor.rawOutput) (.fn highKey (raiseAtom factor.rank factor.bound output)) :=
    .fn (.refl _) factor.result
  have lower := ((functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := Γ) factor.bound lambdaKey output).inverse henv).toAdapter henv hscoped hΓ
  have adapter := reanchor.comp (domain.comp (input.comp (restore.comp (result.comp lower))))
  simp only [Profile.fn, raiseProfile_singleton]
  exact ⟨.cons (List.mem_singleton_self _) adapter (.nil _)⟩

end Lean4Lean.AnchoredSource.Adapted
