import Lean4Lean.Theory.Typing.AnchoredNativeTemplateFactor
import Lean4Lean.Theory.Typing.AnchoredNativeConstantTree

/-! Native templates only inspect their finite registered prefix. Changing
an unused substitution tail preserves the exact observer and all footprints. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Finite factoring yields the precise realized registered template, not
merely a term with an equal target substitution. Every removed source
operand is retained in the concrete factor ledger. -/
theorem CodeCert.factorNativeTemplate
    (certificate : CodeCert env U registry Γ locals σ
      (template.instOuter arguments) demand footprint)
    (scope : template.ClosedN arguments.length) (newLocals : List Nat) :
    ∃ required,
      Nonempty (CodeCert env U registry Γ newLocals
        (nativeCaptureSubst (arguments.map (·.subst σ))) template demand required) ∧
      Nonempty (ParamsFootprint env U registry Γ locals σ arguments footprint required) := by
  obtain ⟨required, ⟨factored⟩, ledger⟩ := certificate.factorParams newLocals
  refine ⟨required, ⟨factored.realizePrefix scope _ ?_⟩, ledger⟩
  intro i hi
  simp only [Subst.comp, Subst.ofList, nativeCaptureSubst, List.length_map]
  rw [dif_pos hi, dif_pos hi]
  simp only [List.getElem_map]

end Lean4Lean.AnchoredSource.Adapted
