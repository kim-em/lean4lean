import Lean4Lean.Theory.Typing.AnchoredRecordRequestRetag
import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode
import Lean4Lean.Theory.Typing.AnchoredSortableCodeIntroduction

/-! A sortable projected output is code in its own right. Its frozen request
domain is not identified with the caller field type. Reattaching the code uses
the actual caller field capability, so no cross-domain conversion is assumed. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
open AnchoredSource.Adapted.OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The full finite path is executed as a code action, including grade changes.
Both frozen-anchor and endpoint code relations are obtained from the old
admission, without any new anchor seed or domain-alignment premise. -/
theorem RequestAdmission.sortableOutputCode
    {request : DataRequest (Profile n)} {atom : Atom n} {output : Atom m}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (admitted : RequestAdmission env U (relations env U registry n) Γ request left right)
    (selected : atom ∈ request.input.atoms)
    (path : GeneralOutputPath env U registry Γ atom output)
    (sortable : (Profile.singleton output).HasType (.sort relevant)) :
    TypeRelated env U registry Γ request.anchor left (.singleton output) ∧
    TypeRelated env U registry Γ left right (.singleton output) := by
  obtain ⟨flag, inputSortable, ⟨action⟩⟩ := Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource.GeneralOutputPath.codeAtOutput henv path sortable
  obtain ⟨_, _, _, _, _, first, second⟩ := admitted.singleton selected
  exact ⟨action.codeMap henv hscoped (Related.code_of_sortable henv hscoped formed inputSortable first),
    action.codeMap henv hscoped (Related.code_of_sortable henv hscoped formed inputSortable second)⟩

/-- Caller field code supplies the assigned-type capability. The old request's
raw domain and anchor are preserved and need not equal the caller's domain. -/
theorem RequestAdmission.sortableOutputRelated
    {request : DataRequest (Profile n)} {atom : Atom n} {output : Atom m}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (admitted : RequestAdmission env U (relations env U registry n) Γ request left right)
    (selected : atom ∈ request.input.atoms)
    (path : GeneralOutputPath env U registry Γ atom output)
    (sortable : (Profile.singleton output).HasType (.sort relevant))
    (typed : (Profile.singleton output).HasType support)
    (callerCode : TypeRelated env U registry Γ callerType callerType support) :
    Related env U registry Γ request.anchor left callerType (.singleton output) support ∧
    Related env U registry Γ left right callerType (.singleton output) support := by
  obtain ⟨first, second⟩ := admitted.sortableOutputCode henv hscoped formed selected path sortable
  exact ⟨Related.of_sortable_code henv sortable typed first callerCode,
    Related.of_sortable_code henv sortable typed second callerCode⟩

end Lean4Lean.AnchoredSemantics.RankedData
