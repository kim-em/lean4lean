import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSortRule
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

mutual
theorem SortableObs.sortHereditary
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {left right : VLevel} {demand : Profile n} {footprint : Footprint}
    (leftWF : left.WF U) (rightWF : right.WF U) (equal : left ≈ right)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (observation : SortableObs env U registry target locals σ (.sort left) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.sort left) (.sort right) (.sort (.succ left)) demand) := by
  match observation with
  | .legacy source =>
    obtain ⟨answer⟩ := GradedTransfer.sortDF (assigned := .succ left) (σ := σ) (τ := τ) henv hscoped leftWF rightWF leftWF equal
      (Relevant.succ left) hTarget source resources
    exact ⟨.ofLegacy henv hscoped hTarget answer⟩
  | .code relevant certificate =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget certificate resources
    exact ⟨answer.computational henv⟩
  | .union left right =>
    obtain ⟨a⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    obtain ⟨a⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    obtain ⟨a⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableCert.sortHereditary
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {left right : VLevel} {demand : Profile n} {footprint : Footprint}
    (leftWF : left.WF U) (rightWF : right.WF U) (equal : left ≈ right)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (certificate : SortableCert env U registry target locals σ (.sort left) relevant demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.sort left) (.sort right) (.sort (.succ left)) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    obtain ⟨answer⟩ := source.transfer_graded henv hscoped hTarget closed
      (GradedTransfer.sortDF (assigned := .succ left) henv hscoped leftWF rightWF leftWF equal (Relevant.succ left) hTarget) resources
    exact ⟨SortableTermTransferResult.fromCode henv (.ofCode answer.certificate formed)
      answer.available answer.related
      (.seed (.sort (Relevant.succ left)) (Profile.HasType.sort true))
      (fun _ _ member => nomatch member) source.formed
      (TypeRelated.literalSort (left := .succ left) (right := .succ left) henv leftWF leftWF rfl (Relevant.succ left))⟩
  | .seed observation formed =>
    obtain ⟨answer⟩ := GradedTransfer.sortDF (assigned := .succ left) (σ := σ) (τ := τ) henv hscoped leftWF rightWF leftWF equal
      (Relevant.succ left) hTarget observation resources
    exact (SortableComputationalTransferResult.ofLegacy henv hscoped hTarget answer).sortableResult
      henv hscoped hTarget closed formed
  | .observe observation formed =>
    obtain ⟨answer⟩ := SortableObs.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget observation resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget first
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget second
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨answer.pad henv⟩
  | .down source =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨answer.down henv⟩
  | .unpad source =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨answer.unpad henv⟩
  | .support action source =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨answer.supportAction henv hscoped action⟩
  | .map view source =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact answer.map henv hscoped view
  | .familyPad source =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact answer.familyPad henv
  | .select source member =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
  | .sortPad source =>
    obtain ⟨answer⟩ := SortableCert.sortHereditary (τ := τ) henv hscoped leftWF rightWF equal closed hTarget source resources
    exact answer.sortPad henv
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end
end Lean4Lean.AnchoredSource.Adapted
