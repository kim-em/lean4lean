import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes

/-! # Source constants from the source-constructor validation pass

The source branch's `validateSourceConstructorTypes.sourceConst_of_run`/`sourceConsts_of_run`
(`Nested/Restoration/Validation/Checks.lean`) as consequences of Restoration-A's
`validateSourceConstructorTypes.run.WF`: every source constructor type translates to a
well-formed abstract constant of the checker's model. The cache-mode premise of the source
branch is gone; the checker environment is a `CheckerEnv`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem validateSourceConstructorTypes.sourceConst_of_run
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (C : CheckerEnv safety env venv) {lparams : List Name} {fuel : FuelConfig}
    {types : List InductiveType}
    (hclosed : ∀ type ∈ types, ∀ ctor ∈ type.ctors, ctor.type.FVarsIn fun _ => False)
    (hrun : Lean4Lean.validateSourceConstructorTypes.run env lparams safety fuel types = .ok ())
    {indType : InductiveType} (htype : indType ∈ types) {ctor : Constructor}
    (hctor : ctor ∈ indType.ctors) :
    ∃ constructor : VConstVal, TrSourceConst venv lparams ctor.name ctor.type constructor := by
  obtain ⟨T, hT, hty⟩ :=
    validateSourceConstructorTypes.run.WF C lparams fuel types hclosed hrun indType htype ctor hctor
  exact ⟨{ name := ctor.name, uvars := lparams.length, type := T }, rfl, rfl, hT, hty⟩

theorem validateSourceConstructorTypes.sourceConsts_of_run
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (C : CheckerEnv safety env venv) {lparams : List Name} {fuel : FuelConfig}
    {types : List InductiveType}
    (hclosed : ∀ type ∈ types, ∀ ctor ∈ type.ctors, ctor.type.FVarsIn fun _ => False)
    (hrun : Lean4Lean.validateSourceConstructorTypes.run env lparams safety fuel types = .ok ())
    {indType : InductiveType} (htype : indType ∈ types) :
    ∃ constructors : List VConstVal,
      List.Forall₂ (fun source constructor =>
        TrSourceConst venv lparams source.name source.type constructor)
        indType.ctors constructors := by
  have h : ∀ ctors : List Constructor, (∀ ctor ∈ ctors, ctor ∈ indType.ctors) →
      ∃ constructors : List VConstVal, List.Forall₂ (fun source constructor =>
        TrSourceConst venv lparams source.name source.type constructor) ctors constructors := by
    intro ctors hsub
    induction ctors with
    | nil => exact ⟨[], .nil⟩
    | cons ctor ctors ih =>
      obtain ⟨v, hv⟩ := sourceConst_of_run C hclosed hrun htype (hsub ctor (by simp))
      obtain ⟨vs, hvs⟩ := ih fun c hc => hsub c (by simp [hc])
      exact ⟨v :: vs, .cons hv hvs⟩
  exact h indType.ctors fun _ h => h

end VerifyInductive
end Lean4Lean
