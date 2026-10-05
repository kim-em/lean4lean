import Lean4Lean.Theory.Typing.AnchoredSortableStageBudgets
import Lean4Lean.Theory.Typing.AnchoredSortableDepthRetraction
import Lean4Lean.Theory.Typing.AnchoredSortableDepthSupport
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction

/-! Actual hereditary result constructions preserve simultaneous declaration
budgets. Code actions reconstruct the assigned-type support from its stored
finite universe covers, retaining the same bound at arbitrary result grade. -/
namespace Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure CodeResult (budgets : Budgets) (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation) (left right assigned : VExpr)
    (relevant : Bool) (profile : Profile n)
    extends SortableTermTransferResult env U registry target locals σ τ available
      left right assigned relevant profile where
  valueBound : Within budgets certificate.nativeDepth
  typeBound : Within budgets typeCertificate.nativeDepth

def CodeResult.computational (henv : env.Ordered)
    (result : CodeResult budgets env U registry Γ locals σ τ available left right assigned relevant profile) :
    Result budgets env U registry Γ locals σ τ available left right assigned profile where
  toSortableComputationalTransferResult := result.toSortableTermTransferResult.computational henv
  observationBound := by
    intro current fuel member
    simpa only [SortableTermTransferResult.computational, SortableObs.nativeDepth] using
      result.valueBound current fuel member
  certificateBound := result.typeBound

theorem CodeResult.action (henv : env.Ordered) (hscoped : registry.Scoped)
    (action : SortableCodeAction env U registry Γ relevant profile next nextProfile)
    (result : CodeResult budgets env U registry Γ locals σ τ available left right assigned relevant profile) :
    Nonempty (CodeResult budgets env U registry Γ locals σ τ available left right assigned next nextProfile) := by
  obtain ⟨typeFootprint, typeCertificate, typeAvailable, typeDepth⟩ :=
    result.typeCertificate.flatSortsAt_allDepth result.typeAvailable
  refine ⟨{
    toSortableTermTransferResult := SortableTermTransferResult.fromCode henv
      (action.applyCertificate result.certificate) (action.available result.available)
      (action.codeMap henv hscoped result.related) typeCertificate typeAvailable
      (action.typedAtSorts (result.certificate.formed.flatSorts result.typed))
      (result.typeCode.flatSortsAt henv)
    valueBound := ?_
    typeBound := ?_ }⟩
  · intro current fuel member
    simpa only [SortableTermTransferResult.fromCode,
      SortableCodeAction.nativeDepth_applyCertificate] using result.valueBound current fuel member
  · intro current fuel member
    exact Nat.le_trans (typeDepth current) (result.typeBound current fuel member)

def CodeResult.union (henv : env.Ordered)
    (first : CodeResult budgets env U registry Γ locals σ τ available left right assigned relevant p)
    (second : CodeResult budgets env U registry Γ locals σ τ available left right assigned relevant q) :
    CodeResult budgets env U registry Γ locals σ τ available left right assigned relevant (p.union q) where
  toSortableTermTransferResult := first.toSortableTermTransferResult.union henv second.toSortableTermTransferResult
  valueBound := by
    intro current fuel member
    simpa only [SortableTermTransferResult.union, SortableTermTransferResult.fromCode, SortableCert.nativeDepth] using
      Nat.max_le.mpr ⟨first.valueBound current fuel member, second.valueBound current fuel member⟩
  typeBound := by
    intro current fuel member
    simpa only [SortableTermTransferResult.union, SortableTermTransferResult.fromCode, SortableCert.nativeDepth] using
      Nat.max_le.mpr ⟨first.typeBound current fuel member, second.typeBound current fuel member⟩

theorem Result.sortable (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (closed : available.AtomClosed)
    (result : Result budgets env U registry Γ locals σ τ available left right assigned profile)
    (formed : profile.HasType (.sort relevant)) :
    Nonempty (CodeResult budgets env U registry Γ locals σ τ available left right assigned relevant profile) := by
  obtain ⟨footprint, certificate, resources, depth⟩ := result.toSortableGradedResult.code_allDepth henv closed formed
  refine ⟨{
    toSortableTermTransferResult := SortableTermTransferResult.fromCode henv certificate resources
      ((result.requestedRelated henv hΓ).code_of_sortable henv hscoped hΓ formed)
      result.requestedCertificate result.typeAvailable result.requestedTyped
      (result.typeCode.lower henv result.bound)
    valueBound := fun current fuel member => Nat.le_trans (depth current) (result.observationBound current fuel member)
    typeBound := ?_ }⟩
  intro current fuel member
  simpa only [SortableTermTransferResult.fromCode, SortableComputationalTransferResult.requestedCertificate,
    SortableCert.nativeDepth_lower] using result.certificateBound current fuel member

def Result.unpad
    (result : Result budgets env U registry Γ locals σ τ available left right assigned profile.pad) :
    Result budgets env U registry Γ locals σ τ available left right assigned profile where
  toSortableComputationalTransferResult := result.toSortableComputationalTransferResult.unpad
  observationBound := result.observationBound
  certificateBound := result.certificateBound

noncomputable def Result.pad (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (result : Result budgets env U registry Γ locals σ τ available left right assigned profile) :
    Result budgets env U registry Γ locals σ τ available left right assigned profile.pad where
  toSortableComputationalTransferResult := result.toSortableComputationalTransferResult.pad henv hscoped hΓ
  observationBound := by
    intro current fuel member
    simpa only [SortableComputationalTransferResult.pad, SortableObs.nativeDepth] using result.observationBound current fuel member
  certificateBound := by
    intro current fuel member
    simpa only [SortableComputationalTransferResult.pad, SortableCert.nativeDepth] using result.certificateBound current fuel member

noncomputable def Result.view (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (view : AtomView env U registry Γ a b)
    (result : Result budgets env U registry Γ locals σ τ available left right assigned (.singleton a)) :
    Result budgets env U registry Γ locals σ τ available left right assigned (.singleton b) where
  toSortableComputationalTransferResult := result.toSortableComputationalTransferResult.view henv hscoped hΓ view
  observationBound := result.observationBound
  certificateBound := by
    intro current fuel member
    simpa only [SortableComputationalTransferResult.view, SortableCert.nativeDepth,
      SortableCert.nativeDepth_raise, SortableComputationalTransferResult.requestedCertificate,
      SortableCert.nativeDepth_lower, Nat.max_self] using result.certificateBound current fuel member

noncomputable def Result.union (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (first : Result budgets env U registry Γ locals σ τ available left right assigned p)
    (second : Result budgets env U registry Γ locals σ τ available left right assigned q) :
    Result budgets env U registry Γ locals σ τ available left right assigned (p.union q) where
  toSortableComputationalTransferResult := first.toSortableComputationalTransferResult.union henv hscoped hΓ second.toSortableComputationalTransferResult
  observationBound := by
    intro current fuel member
    simp only [SortableComputationalTransferResult.union, SortableObs.nativeDepth,
      SortableComputationalTransferResult.raiseTo, SortableObs.nativeDepth_raise]
    exact Nat.max_le.mpr ⟨first.observationBound current fuel member, second.observationBound current fuel member⟩
  certificateBound := by
    intro current fuel member
    simp only [SortableComputationalTransferResult.union, SortableCert.nativeDepth,
      SortableComputationalTransferResult.raiseTo, SortableCert.nativeDepth_raise]
    exact Nat.max_le.mpr ⟨first.certificateBound current fuel member, second.certificateBound current fuel member⟩

def Result.empty : Result budgets env U registry Γ locals σ τ available left right assigned (.empty (n := n)) where
  toSortableComputationalTransferResult := .empty
  observationBound := by
    intro current fuel member
    simp only [SortableComputationalTransferResult.empty, SortableObs.nativeDepth, Obs.nativeDepth]
    exact Nat.zero_le _
  certificateBound := by
    intro current fuel member
    simp only [SortableComputationalTransferResult.empty, SortableCert.nativeDepth, Obs.nativeDepth]
    exact Nat.zero_le _

open private code_union from Lean4Lean.Theory.Typing.AnchoredSortableTransferAction

theorem Result.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (_closed : available.AtomClosed)
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (result : Result budgets env U registry Γ locals σ τ available
      left right assigned (.singleton a)) :
    Nonempty (Result budgets env U registry Γ locals σ τ available
      left right assigned (.singleton b)) := by
  let requestedSupport := action.support.apply (lowerProfile n result.bound result.support)
  have requestTyped := action.typed result.requestedTyped
  have requestCode := action.support.codeMap henv hscoped
    (result.typeCode.lower henv result.bound)
  have requestRelated := action.termMap henv hscoped hΓ result.requestedTyped
    (result.requestedRelated henv hΓ)
  have highTyped := Profile.HasType.raise result.bound requestTyped
  have highCode := requestCode.raise henv result.bound
  have highRelated := requestRelated.raise henv result.bound
  have wf := result.rawTyped.wf_type.union highTyped.wf_type
  have typed := highTyped.enlarge (Profile.le_union_right _ _) wf
  have rawTyped := result.rawTyped.enlarge (Profile.le_union_left _ _) wf
  have code := code_union result.typeCode highCode
  have step : GeneralNormalProfileAdapter env U registry Γ (.singleton a) (.singleton b) :=
    .cons (List.mem_singleton_self _) (action.toGeneralAdapter henv hscoped hΓ) (.nil _)
  exact ⟨{
    rank := result.rank
    bound := result.bound
    raw := result.raw
    footprint := result.footprint
    observation := result.observation
    adapter := result.adapter.comp (GeneralNormalProfileAdapter.raise henv hscoped hΓ result.bound step)
    resources := result.resources
    live := result.live
    support := result.support.union (raiseProfile result.rank result.bound requestedSupport)
    typeFootprint := result.typeFootprint ++ result.typeFootprint
    typeCertificate := .union result.typeCertificate
      ((SortableCert.support action.support result.requestedCertificate).raise result.bound)
    typeAvailable := fun i need member => (List.mem_append.mp member).elim
      (result.typeAvailable i need) (result.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code highRelated
    rawRelated := Related.retag henv rawTyped code result.rawRelated
    observationBound := result.observationBound
    certificateBound := by
      intro current fuel member
      simpa only [SortableCert.nativeDepth, SortableCert.nativeDepth_raise,
        SortableComputationalTransferResult.requestedCertificate, SortableCert.nativeDepth_lower,
        Nat.max_self] using result.certificateBound current fuel member }⟩

end Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
