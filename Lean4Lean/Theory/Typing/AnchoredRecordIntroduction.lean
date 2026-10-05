import Lean4Lean.Theory.Typing.AnchoredConstructorIntroduction
import Batteries.Tactic.OpenPrivate

/-! An empty record demand observes only the assigned family. It needs the
actual record registration and endpoint typings, but no projection child.
This is the resource-free record seed required by zero-field structure eta. -/
namespace Lean4Lean.AnchoredProfiles
open private AtomTyped AtomWF RecordWF checks from Lean4Lean.Theory.Typing.AnchoredProfiles

theorem Profile.HasType.emptyRecord
    {family : FamilyData (Profile n)} (relevant : family.relevant = true)
    (formed : (Profile.singleton (n := n + 1) (.family family)).WF) :
    (Profile.singleton (n := n + 1) (.record ⟨family, relevant, []⟩)).HasType
      (.singleton (.family family)) := by
  refine ⟨?_, formed, ?_⟩
  · intro atom member
    cases List.mem_singleton.mp member
    exact ⟨formed _ (List.mem_singleton_self _), fun _ member => nomatch member⟩
  · intro atom member
    cases List.mem_singleton.mp member
    exact ⟨.family family, List.mem_singleton_self _, rfl⟩

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem RankedData.emptyRecord
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {Γ : List VExpr}
    {family : FamilyData (Profile n)} (relevant : family.relevant = true)
    {info : VProjectionInfo} (lookup : registry.projections family.name = some info)
    (inert : CanonicalDataHead.HeadInert registry info.ctorName)
    {left right type : VExpr}
    (leftTyped : env.HasType U Γ left type) (rightTyped : env.HasType U Γ right type)
    (code : RankedData.FamilyRelation env U registry (relations env U registry n)
      Γ type type family) :
    RankedData.RecordRelation env U registry (relations env U registry n)
      Γ left right type ⟨family, relevant, []⟩ := by
  intro Δ ρ future
  refine ⟨{
    baseWF := future.targetWF henv
    context := Δ
    map := .refl
    insertion := .proof (.refl (future.targetWF henv))
    info := info
    lookup := lookup
    ctorDefinition := inert.definition
    ctorNative := inert.native
    ctorQuotient := inert.quotient
    bounded := fun _ member => nomatch member
    typeCode := ?_
    leftType := ?_
    rightType := ?_
    leftOrigins := fun _ member => nomatch member
    rightOrigins := fun _ member => nomatch member
    fields := .nil }⟩
  · have same (data : FamilyData (Profile n)) : data.rename .refl = data := by
      unfold FamilyData.rename
      rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
        show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
        FamilyData.map_id]
    change RankedData.FamilyRelation env U registry (relations env U registry n) Δ
      ((type.lift' ρ).lift' .refl) ((type.lift' ρ).lift' .refl)
      ((family.rename ρ).rename .refl)
    rw [same, lift'_refl]
    exact code.future henv future
  · simpa only [lift'_refl] using leftTyped.weak' henv future.weakening
  · simpa only [lift'_refl] using rightTyped.weak' henv future.weakening

theorem Related.record
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right type : VExpr}
    {demand : RecordData (Profile n)} {support : Profile (n + 1)}
    (typed : (Profile.singleton (n := n + 1) (.record demand)).HasType support)
    (code : TypeRelated env U registry Γ type type support)
    (value : RankedData.RecordRelation env U registry (relations env U registry n)
      Γ left right type demand) :
    Related env U registry Γ left right type (Profile.singleton (n := n + 1) (.record demand)) support := by
  apply CoreRelated.related henv hscoped
  refine ⟨typed, code, ?_⟩
  intro atom member
  cases List.mem_singleton.mp member
  exact value

end Lean4Lean.AnchoredSemantics
