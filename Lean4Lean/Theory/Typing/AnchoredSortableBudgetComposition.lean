import Lean4Lean.Theory.Typing.AnchoredSortableBudgetResults

/-! Composition and formation queries preserve the actual hereditary caller
budgets; source witnesses stay those computed by the original rule calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalTail
open private code_union from Lean4Lean.Theory.Typing.AnchoredSortableTransferComposition
set_option backward.isDefEq.respectTransparency false

theorem Transfer.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left middle right sourceType : VExpr}
    (first : Transfer budgets env U registry target locals σ σ
      available left middle sourceType)
    (second : Transfer budgets env U registry target locals σ τ
      available middle right sourceType) :
    Transfer budgets env U registry target locals σ τ
      available left right sourceType := by
  intro n demand footprint observation bounded resources
  obtain ⟨a⟩ := first observation bounded resources
  obtain ⟨b⟩ := second a.observation a.observationBound a.resources
  have firstTyped := Profile.HasType.raise b.bound a.typed
  have firstRelated := Related.raise henv b.bound a.related
  have firstCode := TypeRelated.raise henv b.bound a.typeCode
  have firstAdapter := GeneralNormalProfileAdapter.raise henv hscoped hTarget b.bound a.adapter
  simp only [raiseProfile_trans] at firstTyped firstRelated firstAdapter
  have wf := firstTyped.wf_type.union b.typed.wf_type
  have typed := firstTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := b.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have code := code_union firstCode b.typeCode
  have cross := GeneralNormalProfileAdapter.termMap firstAdapter henv hscoped hTarget typed code b.related
  exact ⟨{
    rank := b.rank
    bound := Nat.le_trans a.bound b.bound
    raw := b.raw
    footprint := b.footprint
    observation := b.observation
    adapter := GeneralNormalProfileAdapter.comp b.adapter firstAdapter
    resources := b.resources
    support := (raiseProfile b.rank b.bound a.support).union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    typeCertificate := .union (a.typeCertificate.raise b.bound) b.typeCertificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.typeAvailable i need) (b.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.trans henv hscoped firstRelated cross
    rawRelated := Related.retag henv rawTyped code b.rawRelated
    live := b.live
    observationBound := b.observationBound
    certificateBound := by
      intro current fuel member
      simp only [SortableCert.nativeDepth, SortableCert.nativeDepth_raise]
      exact Nat.max_le.mpr ⟨a.certificateBound current fuel member, b.certificateBound current fuel member⟩ }⟩

theorem Transfer.sortable
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (transfer : Transfer budgets env U registry target locals σ τ available left right assigned)
    (certificate : SortableCert env U registry target locals σ left relevant profile footprint)
    (bounded : Within budgets certificate.nativeDepth) (resources : footprint.Available available) :
    Nonempty (CodeResult budgets env U registry target locals σ τ available left right assigned relevant profile) := by
  obtain ⟨result⟩ := transfer (.code relevant certificate) (by
    intro current fuel member
    simpa only [SortableObs.nativeDepth] using bounded current fuel member) resources
  exact result.sortable henv hscoped hTarget closed certificate.formed

theorem frame_left
    {frame : SortableTailPairedFits env registry target context locals σ τ available}
    (bounded : Within budgets frame.nativeDepth) : Within budgets frame.left.nativeDepth := by
  intro current fuel member
  simp only [SortableTailPairedFits.nativeDepth, SortableTailPairedFits.left,
    SortableTailFits.nativeDepth_left, Nat.max_self]
  exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member)

theorem frame_right
    {frame : SortableTailPairedFits env registry target context locals σ τ available}
    (bounded : Within budgets frame.nativeDepth) : Within budgets frame.right.nativeDepth := by
  intro current fuel member
  simp only [SortableTailPairedFits.nativeDepth, SortableTailPairedFits.right,
    SortableTailPairedFits.left, SortableTailPairedFits.symm,
    SortableTailFits.nativeDepth_left, Nat.max_self]
  exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member)

end Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
