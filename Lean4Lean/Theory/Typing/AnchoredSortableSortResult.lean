import Lean4Lean.Theory.Typing.AnchoredSortableTransferClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSortRule
import Lean4Lean.Theory.Typing.AnchoredSortableLive

/-! Exact formation transfer at an actual source sort. The requested
formation flag and the source sort's relevance are kept distinct. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure SortableSortResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (left right : VExpr) (requestedFlag actualFlag : Bool) (profile : Profile n)
    extends SortableTransferResult env U registry target locals σ τ available
      left right requestedFlag profile where
  sorted : profile.HasType (.sort actualFlag)

theorem SortableComputationalTransferResult.atSort
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (result : SortableComputationalTransferResult env U registry target locals σ τ available
      left right (.sort level) profile)
    (requested : profile.HasType (.sort requestedFlag))
    (actual : Relevant level actualFlag) :
    Nonempty (SortableSortResult env U registry target locals σ τ available
      left right requestedFlag actualFlag profile) := by
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ :=
    result.toSortableGradedResult.code henv closed requested
  exact ⟨{
    footprint := footprint, certificate := certificate, available := resources
    related := (result.requestedRelated henv hTarget).code_of_sortable henv hscoped hTarget requested
    sorted := TypeRelated.sort_typed hTarget actual
      (result.typeCode.lower henv result.bound) result.requestedTyped }⟩

noncomputable def SortableSortResult.computational
    {profile : Profile n}
    (henv : env.Ordered)
    (result : SortableSortResult env U registry target locals σ τ available
      left right requestedFlag actualFlag profile)
    (levelWF : level.WF U) (actual : Relevant level actualFlag) :
    SortableComputationalTransferResult env U registry target locals σ τ available
      left right (.sort level) profile := by
  have typeCode := TypeRelated.literalSort (registry := registry) (Γ := target)
    (n := n) henv levelWF levelWF rfl actual
  have related := Related.of_sortable_code henv result.certificate.formed result.sorted
    result.related typeCode
  exact {
    rank := n, bound := Nat.le_refl _, raw := profile
    footprint := result.footprint, observation := .code requestedFlag result.certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := result.available, live := result.certificate.live
    support := .sort actualFlag, typeFootprint := []
    typeCertificate := .seed (.sort actual) (Profile.HasType.sort actualFlag)
    typeAvailable := fun _ _ h => nomatch h
    typed := by simpa only [raiseProfile_self] using result.sorted
    rawTyped := result.sorted, typeCode := typeCode
    related := by simpa only [raiseProfile_self, subst_sort] using related
    rawRelated := (Related.symm henv related).left_diagonal }

end Lean4Lean.AnchoredSource.Adapted
