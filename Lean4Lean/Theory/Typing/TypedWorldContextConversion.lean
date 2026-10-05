import Lean4Lean.Theory.Typing.TypedWorld

/-! Generated worlds over convertible base contexts. Variable positions and
the insertion map are unchanged. New domains keep their literal syntax;
retained domains follow the corresponding binder of the converted base.
-/

namespace Lean4Lean.VEnv
open VExpr

def convertedContext : Lift → List VExpr → List VExpr → List VExpr
  | .refl, source, _ => source
  | .skip ρ, source, A :: target => A :: convertedContext ρ source target
  | .cons ρ, A :: source, _ :: target => A.lift' ρ :: convertedContext ρ source target
  | _, _, _ => []

theorem convertedContext_skipN (added source old : List VExpr) :
    convertedContext (.skipN .refl added.length) source (added ++ old) = added ++ source := by
  induction added with
  | nil => rfl
  | cons A added ih => exact congrArg (List.cons A) ih

theorem convertedContext_comp {Γ Γ' Δ Ω : List VExpr} {ρ τ : Lift}
    (first : Ctx.Lift' ρ Γ Δ) (second : Ctx.Lift' τ Δ Ω)
    (length : Γ'.length = Γ.length) :
    convertedContext (ρ.comp τ) Γ' Ω =
      convertedContext τ (convertedContext ρ Γ' Δ) Ω := by
  induction second generalizing Γ Γ' ρ with
  | refl => rfl
  | skip previous ih => exact congrArg (List.cons _) (ih first length)
  | cons previous ih =>
    cases first with
    | refl => simp only [Lift.refl_comp, convertedContext]
    | skip first =>
      exact congrArg (List.cons _) (ih first length)
    | cons first =>
      cases Γ' with
      | nil => simp at length
      | cons A Γ' =>
        have tailLength := Nat.succ.inj length
        simp only [Lift.comp, convertedContext, lift'_comp, ih first tailLength]

theorem FutureInsertion.convertBase_exact {env : VEnv} {U : Nat}
    (henv : env.Ordered) {Γ Γ' Δ : List VExpr} {ρ : Lift}
    (conversion : IsDefEqCtx env U [] Γ Γ')
    (insertion : FutureInsertion env U Γ Δ ρ) :
    FutureInsertion env U Γ' (convertedContext ρ Γ' Δ) ρ ∧
      IsDefEqCtx env U [] Δ (convertedContext ρ Γ' Δ) := by
  induction insertion generalizing Γ' with
  | refl hΓ => exact ⟨.refl (conversion.symm henv).isType, conversion⟩
  | skip previous formed ih =>
    obtain ⟨next, changed⟩ := ih conversion
    exact ⟨.skip next (formed.defeqDFC henv changed), .succ changed formed⟩
  | cons previous formed ih =>
    cases conversion with
    | succ base domains =>
      obtain ⟨next, changed⟩ := ih base
      exact ⟨.cons next (domains.hasType.2.defeqDFC henv base),
        .succ changed (domains.weak' henv previous.weakening)⟩

theorem FutureInsertion.convertBase {env : VEnv} {U : Nat}
    (henv : env.Ordered) {Γ Γ' Δ : List VExpr} {ρ : Lift}
    (conversion : IsDefEqCtx env U [] Γ Γ')
    (insertion : FutureInsertion env U Γ Δ ρ) :
    ∃ Δ', FutureInsertion env U Γ' Δ' ρ ∧ IsDefEqCtx env U [] Δ Δ' :=
  ⟨_, insertion.convertBase_exact henv conversion⟩

theorem ProofInsertion.convertBase_exact {env : VEnv} {U : Nat}
    (henv : env.Ordered) {Γ Γ' Δ : List VExpr} {ρ : Lift}
    (conversion : IsDefEqCtx env U [] Γ Γ')
    (insertion : ProofInsertion env U Γ Δ ρ) :
    ProofInsertion env U Γ' (convertedContext ρ Γ' Δ) ρ ∧
      IsDefEqCtx env U [] Δ (convertedContext ρ Γ' Δ) := by
  induction insertion generalizing Γ' with
  | refl hΓ => exact ⟨.refl (conversion.symm henv).isType, conversion⟩
  | skip previous formed witness ih =>
    obtain ⟨next, changed⟩ := ih conversion
    exact ⟨.skip next (formed.defeqDFC henv changed)
      (witness.defeqDFC henv changed), .succ changed formed⟩
  | cons previous formed ih =>
    cases conversion with
    | succ base domains =>
      obtain ⟨next, changed⟩ := ih base
      exact ⟨.cons next (domains.hasType.2.defeqDFC henv base),
        .succ changed (domains.weak' henv previous.weakening)⟩

theorem ProofInsertion.convertBase {env : VEnv} {U : Nat}
    (henv : env.Ordered) {Γ Γ' Δ : List VExpr} {ρ : Lift}
    (conversion : IsDefEqCtx env U [] Γ Γ')
    (insertion : ProofInsertion env U Γ Δ ρ) :
    ∃ Δ', ProofInsertion env U Γ' Δ' ρ ∧ IsDefEqCtx env U [] Δ Δ' :=
  ⟨_, insertion.convertBase_exact henv conversion⟩

end Lean4Lean.VEnv
