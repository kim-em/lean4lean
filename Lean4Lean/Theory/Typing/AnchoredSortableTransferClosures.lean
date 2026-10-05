import Lean4Lean.Theory.Typing.AnchoredSortableTransferComposition

/-! Source observation closures preserve the finite graded transfer contract.
In particular unpadding changes only the requested grade; it never asserts
that the returned raw observation can itself be lowered. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left right sourceType : VExpr}

def SortableComputationalTransferResult.unpad {demand : Profile n}
    (result : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand.pad) :
    SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand where
  rank := result.rank
  bound := Nat.le_trans (Nat.le_succ _) result.bound
  raw := result.raw
  footprint := result.footprint
  observation := result.observation
  adapter := by simpa only [raiseProfile_pad] using result.adapter
  resources := result.resources
  support := result.support
  typeFootprint := result.typeFootprint
  typeCertificate := result.typeCertificate
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_pad] using result.typed
  rawTyped := result.rawTyped
  typeCode := result.typeCode
  related := by simpa only [raiseProfile_pad] using result.related
  rawRelated := result.rawRelated
  live := result.live

noncomputable def SortableComputationalTransferResult.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile n}
    (result : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand.pad where
  rank := result.rank + 1
  bound := Nat.succ_le_succ result.bound
  raw := result.raw.pad
  footprint := result.footprint
  observation := result.observation.pad
  adapter := by
    simpa only [raiseProfile_pad, raiseProfile_step result.bound] using
      GeneralNormalProfileAdapter.pad henv hscoped hTarget result.adapter
  resources := result.resources
  support := result.support.pad
  typeFootprint := result.typeFootprint
  typeCertificate := result.typeCertificate.pad
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_pad, raiseProfile_step result.bound] using result.typed.pad
  rawTyped := result.rawTyped.pad
  typeCode := result.typeCode.pad henv
  related := by simpa only [raiseProfile_pad, raiseProfile_step result.bound] using result.related.pad henv
  rawRelated := result.rawRelated.pad henv
  live := Profile.Live.pad_iff.mpr result.live

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

noncomputable def SortableComputationalTransferResult.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {a b : Atom n} (view : AtomView env U registry target a b)
    (result : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType (.singleton a)) :
    SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType (.singleton b) := by
  let mapped := view.mapType (lowerProfile n result.bound result.support)
  have mappedTyped := view.mapType_typed result.requestedTyped
  have mappedCode := view.codeMap henv hscoped
    (TypeRelated.lower henv result.bound result.typeCode)
  have mappedRelated := view.termMap henv hscoped hTarget (result.requestedRelated henv hTarget)
  have highTyped := Profile.HasType.raise result.bound mappedTyped
  have highCode := TypeRelated.raise henv result.bound mappedCode
  have highRelated := Related.raise henv result.bound mappedRelated
  have wf := result.rawTyped.wf_type.union highTyped.wf_type
  have typed := highTyped.enlarge (Profile.le_union_right _ _) wf
  have rawTyped := result.rawTyped.enlarge (Profile.le_union_left _ _) wf
  have code := code_union result.typeCode highCode
  let step : GeneralNormalProfileAdapter env U registry target (.singleton a) (.singleton b) :=
    (ProfileView.cons view .nil).toGeneralAdapter henv hscoped hTarget
  exact {
    rank := result.rank
    bound := result.bound
    raw := result.raw
    footprint := result.footprint
    observation := result.observation
    adapter := GeneralNormalProfileAdapter.comp result.adapter
      (GeneralNormalProfileAdapter.raise henv hscoped hTarget result.bound step)
    resources := result.resources
    support := result.support.union (raiseProfile result.rank result.bound mapped)
    typeFootprint := result.typeFootprint ++ result.typeFootprint
    typeCertificate := .union result.typeCertificate
      ((SortableCert.map view result.requestedCertificate).raise result.bound)
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (result.typeAvailable i need) (result.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code highRelated
    rawRelated := Related.retag henv rawTyped code result.rawRelated
    live := result.live }

noncomputable def SortableComputationalTransferResult.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile n}
    (result : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand)
    (N : Nat) (bound : result.rank ≤ N) :
    SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand where
  rank := N
  bound := Nat.le_trans result.bound bound
  raw := raiseProfile N bound result.raw
  footprint := result.footprint
  observation := result.observation.raise bound
  adapter := by simpa only [raiseProfile_trans] using
    GeneralNormalProfileAdapter.raise henv hscoped hTarget bound result.adapter
  resources := result.resources
  support := raiseProfile N bound result.support
  typeFootprint := result.typeFootprint
  typeCertificate := result.typeCertificate.raise bound
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_trans] using Profile.HasType.raise bound result.typed
  rawTyped := Profile.HasType.raise bound result.rawTyped
  typeCode := TypeRelated.raise henv bound result.typeCode
  related := by simpa only [raiseProfile_trans] using Related.raise henv bound result.related
  rawRelated := Related.raise henv bound result.rawRelated
  live := (raiseProfile_live_iff bound result.raw).mpr result.live

noncomputable def SortableComputationalTransferResult.union
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {p q : Profile n}
    (first : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType p)
    (second : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType q) :
    SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType (p.union q) := by
  let N := max first.rank second.rank
  let a := first.raiseTo henv hscoped hTarget N (Nat.le_max_left ..)
  let b := second.raiseTo henv hscoped hTarget N (Nat.le_max_right ..)
  have wf := a.typed.wf_type.union b.typed.wf_type
  have aTyped := a.typed.enlarge (Profile.le_union_left _ _) wf
  have bt := b.typed.enlarge (Profile.le_union_right _ _) wf
  have ar := a.rawTyped.enlarge (Profile.le_union_left _ _) wf
  have br := b.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have code := code_union a.typeCode b.typeCode
  exact {
    rank := N
    bound := a.bound
    raw := a.raw.union b.raw
    footprint := a.footprint ++ b.footprint
    observation := .union a.observation b.observation
    adapter := by
      rw [raiseProfile_union]
      exact GeneralNormalProfileAdapter.union a.adapter b.adapter
    resources := fun i need hm => (List.mem_append.mp hm).elim
      (a.resources i need) (b.resources i need)
    support := a.support.union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    typeCertificate := .union a.typeCertificate b.typeCertificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.typeAvailable i need) (b.typeAvailable i need)
    typed := by
      rw [raiseProfile_union]
      exact aTyped.union bt
    rawTyped := ar.union br
    typeCode := code
    related := by
      rw [raiseProfile_union]
      exact (Related.retag henv aTyped code a.related).union (Related.retag henv bt code b.related)
    rawRelated := (Related.retag henv ar code a.rawRelated).union
      (Related.retag henv br code b.rawRelated)
    live := Profile.Live.union_iff.mpr ⟨a.live, b.live⟩ }

def SortableComputationalTransferResult.empty :
    SortableComputationalTransferResult env U registry target locals σ τ available
      left right sourceType (Profile.empty (n := n)) where
  rank := n
  bound := Nat.le_refl _
  raw := .empty
  footprint := []
  observation := .legacy .empty
  adapter := by rw [raiseProfile_self]; exact .nil _
  resources := fun _ _ h => nomatch h
  support := .empty
  typeFootprint := []
  typeCertificate := .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value)
  typeAvailable := fun _ _ h => nomatch h
  typed := by rw [raiseProfile_self]; exact Profile.HasType.empty Profile.WF.empty
  rawTyped := Profile.HasType.empty Profile.WF.empty
  typeCode := by
    cases n <;> exact fun Δ ρ insertion atom hm => nomatch hm
  related := by
    rw [raiseProfile_self]
    cases n <;> exact fun _ h => nomatch h
  rawRelated := by cases n <;> exact fun _ h => nomatch h
  live := Profile.Live.empty

end Lean4Lean.AnchoredSource.Adapted
