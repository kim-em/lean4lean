import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData

/-! # The generator of the lowered view is the lowered run's

`LoweredView.signature`/`generatedInstance` read the generator off the recursor installation;
`RestoredBlock.compiled` is stated against `RecursorCheck.signature`/`generation`.
They agree (`RecursorCheck.installation_signature`, `installation_generation`), and
`CompilationData.castGenerator` transports a compilation along that agreement. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

theorem LoweredRun.view_signature {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {loweredEnv : Environment}
    (L : LoweredRun Hc nparams indTypes loweredEnv) :
    L.view.signature = L.recursors.signature :=
  L.recursors.installation_signature

theorem LoweredRun.view_generation {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {loweredEnv : Environment}
    (L : LoweredRun Hc nparams indTypes loweredEnv) :
    HEq L.view.generatedInstance L.recursors.generation :=
  L.recursors.installation_generation

theorem CompilationData.castGenerator {env : VEnv} {source expanded : VInductDecl}
    {s s' : InductiveSignature} {g : Instance s} {g' : Instance s'}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (hs : s = s') (hg : HEq g g')
    (H : CompilationData env source expanded s g auxiliaries block) :
    CompilationData env source expanded s' g' auxiliaries block := by
  subst hs; cases eq_of_heq hg; exact H

/-- Transport of a field of a lowered view along a heterogeneous equality of views. -/
theorem LoweredView.heq_field {α : Sort _} {env₁ env₂ : Environment}
    {V₁ : LoweredView env₁} {V₂ : LoweredView env₂} (henv : env₁ = env₂) (h : HEq V₁ V₂)
    (f : ∀ {env}, LoweredView env → α) : f V₁ = f V₂ := by
  subst henv; cases eq_of_heq h; rfl

end VerifyInductive
end Lean4Lean
