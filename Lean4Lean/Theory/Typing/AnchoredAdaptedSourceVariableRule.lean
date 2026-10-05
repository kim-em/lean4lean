import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedSort

/-! The original variable rule interprets its actual valuation certificate
through the original lookup-type formation child. All observation closures
retain the same available source demands. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Obs.graded_bvar
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {index : Nat} {A : VExpr} {demand : Profile n} {footprint : Footprint}
    (lookup : Lookup source index A)
    (originalType : GradedJoint env U registry source A A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  match observation with
  | .var _ _ _ demand =>
    obtain ⟨entry⟩ := fits.forward.entry index ⟨n, demand⟩
      (resources index _ List.mem_cons_self) A lookup
    have producer : GradedTransfer env U registry target locals σ σ available A A (.sort level) :=
      (originalType target locals σ σ available closed hTarget
      substitutions.left fits.left).1
    obtain ⟨type⟩ := entry.certificate.transfer_graded henv hscoped hTarget closed
      producer entry.available
    exact ⟨{
      rank := n
      bound := Nat.le_refl n
      rawDemand := demand
      resultFootprint := [(index, ⟨n, demand⟩)]
      observation := .var locals τ index demand
      adapter := by rw [raiseProfile_self]; exact .refl _
      resultAvailable := resources
      support := entry.support
      typeFootprint := entry.footprint
      certificate := entry.certificate
      typeAvailable := entry.available
      typed := by simpa only [raiseProfile_self] using entry.typed
      rawTyped := entry.typed
      typeCode := type.related
      related := by simpa only [raiseProfile_self, subst_bvar] using entry.related
      rawRelated := (entry.related.symm henv).left_diagonal }⟩
  | .empty => exact ⟨.empty⟩
  | .union left right =>
    obtain ⟨a⟩ := left.graded_bvar henv hscoped lookup originalType closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := right.graded_bvar henv hscoped lookup originalType closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view child change =>
    obtain ⟨a⟩ := child.graded_bvar henv hscoped lookup originalType closed hTarget substitutions fits resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad child =>
    obtain ⟨a⟩ := child.graded_bvar henv hscoped lookup originalType closed hTarget substitutions fits resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨a⟩ := child.graded_bvar henv hscoped lookup originalType closed hTarget substitutions fits resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    obtain ⟨a⟩ := child.graded_bvar henv hscoped lookup originalType closed hTarget substitutions fits resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem GradedJoint.bvar
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {index : Nat} {A : VExpr}
    (lookup : Lookup source index A)
    (originalType : GradedJoint env U registry source A A (.sort level)) :
    GradedJoint env U registry source (.bvar index) (.bvar index) A := by
  apply GradedJoint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have transfer : GradedTransfer env U registry target locals σ τ available
      (.bvar index) (.bvar index) A := by
    intro n demand footprint observation resources
    exact observation.graded_bvar henv hscoped lookup originalType closed hTarget
      substitutions fits resources
  exact ⟨transfer, transfer⟩

end Lean4Lean.AnchoredSource.Adapted
