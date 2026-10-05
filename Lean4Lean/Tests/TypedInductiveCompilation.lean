import Lean4Lean.Tests.InductiveTheory

namespace Lean4Lean.Tests.TypedInductiveCompilation
open InductiveTheory

/-- The finite compilation judgment is inhabited by a typed source and its
canonically generated output, without any unproved correctness theorem. -/
theorem enumFiniteCompilation : CompiledInductive .empty enumDecl enumBlock :=
  .ordinary enumDecl_wf.1 enumFormation enumCanonicalCompilation
    enumBlockWellFormed rfl rfl rfl enumOrdinaryCompilation.names

/-- The active installation-facing certificate retains the finite judgment. -/
example : CompiledInductive .empty enumDecl enumBlock := enumCompiles.compiled

/-- A completed finite derivation can be reused as a prior-container leaf,
and the leaf points to the actual installed environment. -/
theorem enumCertifiedContainer : ∃ installed,
    VInductBlock.install .empty enumBlock = some installed ∧
    CertifiedSpecializations installed [{
      container := enumDecl
      family := ⟨0, by decide⟩
      auxiliary := `AuxEnum0
      levels := []
      arguments := [] }] := by
  obtain ⟨installed, hinstalled⟩ := enumBlockWellFormed.exists_install
  exact ⟨installed, hinstalled,
    .cons enumFiniteCompilation enumBlockWellFormed hinstalled .rfl .nil⟩

end Lean4Lean.Tests.TypedInductiveCompilation
