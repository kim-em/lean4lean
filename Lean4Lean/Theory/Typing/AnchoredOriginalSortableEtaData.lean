import Lean4Lean.Theory.Typing.AnchoredOriginalSortableLambdaRule
import Lean4Lean.Theory.Typing.AnchoredSortablePiShape
import Lean4Lean.Theory.Typing.AnchoredOriginalTailEta
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiShape
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
structure SortableEtaExpansionResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (A B f : VExpr) (demand : Profile n) where
  rawDemand : Profile n
  footprint : Footprint
  observation : SortableObs env U registry target locals τ (.lam A (.app f.lift (.bvar 0))) rawDemand footprint
  resultAvailable : footprint.Available available
  adapter : GeneralNormalProfileAdapter env U registry target rawDemand demand
  support : Profile n
  typeFootprint : Footprint
  certificate : SortableCert env U registry target locals σ (.forallE A B) true support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : demand.HasType support
  rawTyped : rawDemand.HasType support
  code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ) ((VExpr.forallE A B).subst σ) support
  related : Related env U registry target (f.subst τ)
    ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
    ((VExpr.forallE A B).subst σ) demand support
  rawRelated : Related env U registry target
    ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
    ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
    ((VExpr.forallE A B).subst σ) rawDemand support

private theorem eta_subst (A f : VExpr) (τ : Subst) :
    (VExpr.lam A (.app f.lift (.bvar 0))).subst τ =
      .lam (A.subst τ) (.app (f.subst τ).lift (.bvar 0)) := by
  show VExpr.lam (A.subst τ) (.app (f.lift.subst τ.lift) ((VExpr.bvar 0).subst τ.lift)) = _
  rw [lift_subst_lift]
  rfl

private theorem etaPack (input : Profile n) (outside : Footprint) :
    BinderPack n input (outside.sourceLift (.skip .refl) ++ [(0, ⟨n, input⟩)]) outside := by
  induction outside with
  | nil =>
    have h := BinderPack.local (n := n) ⟨n, input⟩ (Nat.le_refl n) BinderPack.nil
    simpa [Need.atGrade, Profile.union, Profile.empty, Profile.atoms, Profile.mk, Footprint.sourceLift] using h
  | cons entry rest ih =>
    obtain ⟨i, need⟩ := entry
    exact .external i need ih

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim (fun h => first.singleton h) (fun h => second.singleton h)

def SortableEtaExpansionResult.empty :
    SortableEtaExpansionResult env U registry target locals σ τ available A B f (Profile.empty (n := n)) where
  rawDemand := .empty
  footprint := []
  observation := .legacy .empty
  resultAvailable := fun _ _ h => nomatch h
  adapter := .nil _
  support := .empty
  typeFootprint := []
  certificate := .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value)
  typeAvailable := fun _ _ h => nomatch h
  typed := Profile.HasType.empty Profile.WF.empty
  rawTyped := Profile.HasType.empty Profile.WF.empty
  code := by cases n <;> exact fun Δ ρ insertion atom hm => nomatch hm
  related := by cases n <;> exact fun _ h => nomatch h
  rawRelated := by cases n <;> exact fun _ h => nomatch h

noncomputable def SortableEtaExpansionResult.union
    (henv : env.Ordered)
    (a : SortableEtaExpansionResult env U registry target locals σ τ available A B f (p : Profile n))
    (b : SortableEtaExpansionResult env U registry target locals σ τ available A B f (q : Profile n)) :
    SortableEtaExpansionResult env U registry target locals σ τ available A B f (p.union q) := by
  have wf := a.typed.wf_type.union b.typed.wf_type
  have aTyped := a.typed.enlarge (Profile.le_union_left _ _) wf
  have bt := b.typed.enlarge (Profile.le_union_right _ _) wf
  have ar := a.rawTyped.enlarge (Profile.le_union_left _ _) wf
  have br := b.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have code := code_union a.code b.code
  exact {
    rawDemand := a.rawDemand.union b.rawDemand
    footprint := a.footprint ++ b.footprint
    observation := .union a.observation b.observation
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.resultAvailable i need) (b.resultAvailable i need)
    adapter := GeneralNormalProfileAdapter.union a.adapter b.adapter
    support := a.support.union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    certificate := .union a.certificate b.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.typeAvailable i need) (b.typeAvailable i need)
    typed := aTyped.union bt
    rawTyped := ar.union br
    code := code
    related := (Related.retag henv aTyped code a.related).union (Related.retag henv bt code b.related)
    rawRelated := (Related.retag henv ar code a.rawRelated).union (Related.retag henv br code b.rawRelated) }

end Lean4Lean.AnchoredSource.Adapted
