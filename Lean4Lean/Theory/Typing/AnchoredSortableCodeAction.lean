import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionCertificate
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults

/-! Interpret finite code actions on actual source certificates and answers. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Leaf interpretation acts on a finite answer already obtained at an
actual source occurrence. It changes neither that expression nor its assigned type. -/
theorem SortableCodeAction.applyResult
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (result : SortableTermTransferResult env U registry target locals σ τ available
      left right assigned relevant profile) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      left right assigned next nextProfile) := by
  induction action with
  | id => exact ⟨result⟩
  | comp first second firstIH secondIH =>
    obtain ⟨middle⟩ := firstIH result
    exact secondIH middle
  | union first second firstIH secondIH =>
    obtain ⟨a⟩ := firstIH result
    obtain ⟨b⟩ := secondIH result
    exact ⟨a.union henv b⟩
  | retag formed => exact ⟨result.retag formed⟩
  | pad => exact ⟨result.pad henv⟩
  | down => exact ⟨result.down henv⟩
  | unpad => exact ⟨result.unpad henv⟩
  | sortPad => exact result.sortPad henv
  | familyPad => exact result.familyPad henv
  | map view => exact result.map henv hscoped view
  | support action => exact ⟨result.supportAction henv hscoped action⟩
  | select member => exact ⟨result.select henv member⟩
  | focusMinimal minimal bound => exact ⟨result.focusMinimal henv minimal bound⟩

end Lean4Lean.AnchoredSource.Adapted
