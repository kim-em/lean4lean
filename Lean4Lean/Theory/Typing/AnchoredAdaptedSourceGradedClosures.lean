import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

/-! Source observation closures preserve the finite graded transfer contract.
In particular unpadding changes only the requested grade; it never asserts
that the returned raw observation can itself be lowered. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left right sourceType : VExpr}

def GradedTransferResult.unpad {demand : Profile n}
    (result : GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand.pad) :
    GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand where
  rank := result.rank
  bound := Nat.le_trans (Nat.le_succ _) result.bound
  rawDemand := result.rawDemand
  resultFootprint := result.resultFootprint
  observation := result.observation
  adapter := by simpa only [raiseProfile_pad] using result.adapter
  resultAvailable := result.resultAvailable
  support := result.support
  typeFootprint := result.typeFootprint
  certificate := result.certificate
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_pad] using result.typed
  rawTyped := result.rawTyped
  typeCode := result.typeCode
  related := by simpa only [raiseProfile_pad] using result.related
  rawRelated := result.rawRelated

noncomputable def GradedTransferResult.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile n}
    (result : GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand.pad where
  rank := result.rank + 1
  bound := Nat.succ_le_succ result.bound
  rawDemand := result.rawDemand.pad
  resultFootprint := result.resultFootprint
  observation := result.observation.pad
  adapter := by
    simpa only [raiseProfile_pad, raiseProfile_step result.bound] using
      NormalProfileAdapter.pad henv hscoped hTarget result.adapter
  resultAvailable := result.resultAvailable
  support := result.support.pad
  typeFootprint := result.typeFootprint
  certificate := result.certificate.pad
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_pad, raiseProfile_step result.bound] using result.typed.pad
  rawTyped := result.rawTyped.pad
  typeCode := result.typeCode.pad henv
  related := by simpa only [raiseProfile_pad, raiseProfile_step result.bound] using result.related.pad henv
  rawRelated := result.rawRelated.pad henv

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

noncomputable def GradedTransferResult.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {a b : Atom n} (view : AtomView env U registry target a b)
    (result : GradedTransferResult env U registry target locals σ τ
      available left right sourceType (.singleton a)) :
    GradedTransferResult env U registry target locals σ τ
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
  let step : NormalProfileAdapter env U registry target (.singleton a) (.singleton b) :=
    (ProfileView.cons view .nil).toAdapter henv hscoped hTarget
  exact {
    rank := result.rank
    bound := result.bound
    rawDemand := result.rawDemand
    resultFootprint := result.resultFootprint
    observation := result.observation
    adapter := NormalProfileAdapter.comp result.adapter
      (NormalProfileAdapter.raise henv hscoped hTarget result.bound step)
    resultAvailable := result.resultAvailable
    support := result.support.union (raiseProfile result.rank result.bound mapped)
    typeFootprint := result.typeFootprint ++ result.typeFootprint
    certificate := .union result.certificate
      ((CodeCert.map view result.requestedCertificate).raise result.bound)
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (result.typeAvailable i need) (result.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code highRelated
    rawRelated := Related.retag henv rawTyped code result.rawRelated }

noncomputable def GradedTransferResult.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {demand : Profile n}
    (result : GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand)
    (N : Nat) (bound : result.rank ≤ N) :
    GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand where
  rank := N
  bound := Nat.le_trans result.bound bound
  rawDemand := raiseProfile N bound result.rawDemand
  resultFootprint := result.resultFootprint
  observation := result.observation.raise bound
  adapter := by simpa only [raiseProfile_trans] using
    NormalProfileAdapter.raise henv hscoped hTarget bound result.adapter
  resultAvailable := result.resultAvailable
  support := raiseProfile N bound result.support
  typeFootprint := result.typeFootprint
  certificate := result.certificate.raise bound
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_trans] using Profile.HasType.raise bound result.typed
  rawTyped := Profile.HasType.raise bound result.rawTyped
  typeCode := TypeRelated.raise henv bound result.typeCode
  related := by simpa only [raiseProfile_trans] using Related.raise henv bound result.related
  rawRelated := Related.raise henv bound result.rawRelated

noncomputable def GradedTransferResult.union
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {p q : Profile n}
    (first : GradedTransferResult env U registry target locals σ τ
      available left right sourceType p)
    (second : GradedTransferResult env U registry target locals σ τ
      available left right sourceType q) :
    GradedTransferResult env U registry target locals σ τ
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
    rawDemand := a.rawDemand.union b.rawDemand
    resultFootprint := a.resultFootprint ++ b.resultFootprint
    observation := .union a.observation b.observation
    adapter := by
      rw [raiseProfile_union]
      exact NormalProfileAdapter.union a.adapter b.adapter
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.resultAvailable i need) (b.resultAvailable i need)
    support := a.support.union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    certificate := .union a.certificate b.certificate
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
      (Related.retag henv br code b.rawRelated) }

end Lean4Lean.AnchoredSource.Adapted
