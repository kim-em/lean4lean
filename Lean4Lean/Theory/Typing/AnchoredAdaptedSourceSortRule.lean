import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedSort
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty
import Lean4Lean.Theory.Typing.AnchoredCodeIntroduction
import Lean4Lean.Theory.Typing.AnchoredLiteralPi

/-! The original sort equality rule uses literal universe observations.
All finite views and grade changes are handled by the source closure laws. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Relevant.congr (equal : left ≈ right) (flag : Relevant left relevant) :
    Relevant right relevant := by
  cases relevant with
  | false => exact equal.symm.trans flag
  | true => exact fun zero => flag (equal.trans zero)

theorem Relevant.succ (level : VLevel) : Relevant (.succ level) true := by
  simp [Relevant, VLevel.equiv_def, VLevel.eval]

theorem TypeRelated.literalSort
    (henv : env.Ordered) (leftWF : left.WF U) (rightWF : right.WF U)
    (equal : left ≈ right) (flag : Relevant left relevant) :
    TypeRelated env U registry Γ (.sort left) (.sort right) (Profile.sort (n := n) relevant) := by
  cases n <;> intro Δ ρ future atom member
  all_goals
    have he := List.mem_singleton.mp member
    subst atom
    exact ⟨Δ, .refl, left, right,
      ⟨Exposure.literal (future.targetWF henv) ⟨_, .sortDF leftWF leftWF rfl⟩⟩,
      ⟨Exposure.literal (future.targetWF henv) ⟨_, .sortDF rightWF rightWF rfl⟩⟩,
      equal, flag⟩

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem sort_observer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right assigned : VLevel} {demand : Profile n} {footprint : Footprint}
    (leftWF : left.WF U) (rightWF : right.WF U) (assignedWF : assigned.WF U)
    (equal : left ≈ right) (dataType : Relevant assigned true)
    (hTarget : OnCtx target (env.IsType U))
    (observation : Obs env U registry target locals σ (.sort left) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.sort left) (.sort right) (.sort assigned) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | @Obs.sort _ _ _ _ _ flag _ _ _ relevant =>
    have valueCode := TypeRelated.literalSort (registry := registry) (Γ := target) (n := n)
      henv leftWF rightWF equal relevant
    have rightCode := TypeRelated.literalSort (registry := registry) (Γ := target) (n := n)
      henv rightWF rightWF rfl (relevant.congr equal)
    have typeCode := TypeRelated.literalSort (registry := registry) (Γ := target) (n := n)
      henv assignedWF assignedWF rfl dataType
    refine ⟨{
      rank := n
      bound := Nat.le_refl _
      rawDemand := .sort flag
      resultFootprint := []
      observation := .sort (relevant.congr equal)
      adapter := by rw [raiseProfile_self]; exact .refl _
      resultAvailable := fun _ _ h => nomatch h
      support := .sort true
      typeFootprint := []
      certificate := .seed (.sort dataType) (Profile.HasType.sort true)
      typeAvailable := fun _ _ h => nomatch h
      typed := by rw [raiseProfile_self]; exact Profile.HasType.sort flag
      rawTyped := Profile.HasType.sort flag
      typeCode := typeCode
      related := ?_
      rawRelated := Related.of_code henv (Profile.HasType.sort flag)
        (Profile.HasType.sort flag) rightCode typeCode }⟩
    simpa only [raiseProfile_self, subst_sort] using
      Related.of_code henv (Profile.HasType.sort flag) (Profile.HasType.sort flag) valueCode typeCode
  | .union left right =>
    obtain ⟨a⟩ := sort_observer (τ := τ) henv hscoped leftWF rightWF assignedWF equal dataType hTarget
      left (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := sort_observer (τ := τ) henv hscoped leftWF rightWF assignedWF equal dataType hTarget
      right (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := sort_observer (τ := τ) henv hscoped leftWF rightWF assignedWF equal dataType hTarget source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := sort_observer (τ := τ) henv hscoped leftWF rightWF assignedWF equal dataType hTarget source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := sort_observer (τ := τ) henv hscoped leftWF rightWF assignedWF equal dataType hTarget source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := sort_observer (τ := τ) henv hscoped leftWF rightWF assignedWF equal dataType hTarget source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem GradedTransfer.sortDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right assigned : VLevel}
    (leftWF : left.WF U) (rightWF : right.WF U) (assignedWF : assigned.WF U)
    (equal : left ≈ right) (dataType : Relevant assigned true)
    (hTarget : OnCtx target (env.IsType U)) :
    GradedTransfer env U registry target locals σ τ available
      (.sort left) (.sort right) (.sort assigned) :=
  sort_observer (τ := τ) henv hscoped leftWF rightWF assignedWF equal dataType hTarget

theorem GradedJoint.sortDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right : VLevel}
    (leftWF : left.WF U) (rightWF : right.WF U) (equal : left ≈ right) :
    GradedJoint env U registry source (.sort left) (.sort right) (.sort (.succ left)) := by
  apply GradedJoint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  exact ⟨GradedTransfer.sortDF (assigned := .succ left) henv hscoped leftWF rightWF leftWF equal (Relevant.succ _) hTarget,
    GradedTransfer.sortDF (assigned := .succ left) henv hscoped rightWF leftWF leftWF equal.symm (Relevant.succ _) hTarget⟩

end Lean4Lean.AnchoredSource.Adapted
