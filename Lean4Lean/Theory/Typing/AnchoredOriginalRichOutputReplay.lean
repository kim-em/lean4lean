import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication
import Lean4Lean.Theory.Typing.AnchoredSortableVariableNormalization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationOrigins

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
open private GeneralProfileAdapter.union append_available from
  Lean4Lean.Theory.Typing.AnchoredSortableGradedResult

def RichGradedResult.empty : RichGradedResult sourceEnv env U registry target node locals σ available (.empty : Profile n) where
  rank := n
  bound := Nat.le_refl _
  raw := .empty
  footprint := []
  observation := .legacy (.legacy .empty)
  adapter := by rw [raiseProfile_self]; exact .nil _
  resources := fun _ _ h => nomatch h
  live := fun _ h => nomatch h

def RichGradedResult.unpad {requested : Profile n}
    (result : RichGradedResult sourceEnv env U registry target node locals σ available requested.pad) :
    RichGradedResult sourceEnv env U registry target node locals σ available requested where
  rank := result.rank
  bound := Nat.le_trans (Nat.le_succ _) result.bound
  raw := result.raw
  footprint := result.footprint
  observation := result.observation
  adapter := by simpa only [raiseProfile_pad] using result.adapter
  resources := result.resources
  live := result.live

noncomputable def RichGradedResult.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested : Profile n}
    (result : RichGradedResult sourceEnv env U registry target node locals σ available requested) :
    RichGradedResult sourceEnv env U registry target node locals σ available requested.pad := by
  let N := max result.rank (n + 1)
  let lifted := result.raiseTo henv hscoped formed N (Nat.le_max_left ..)
  refine ⟨N, Nat.le_max_right .., lifted.raw, lifted.footprint, lifted.observation,
    ?_, lifted.resources, lifted.live⟩
  rw [raiseProfile_pad]
  exact lifted.adapter

noncomputable def RichGradedResult.union
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : RichGradedResult sourceEnv env U registry target node locals σ available p)
    (right : RichGradedResult sourceEnv env U registry target node locals σ available q) :
    RichGradedResult sourceEnv env U registry target node locals σ available (p.union q) := by
  let N := max left.rank right.rank
  let a := left.raiseTo henv hscoped formed N (Nat.le_max_left ..)
  let b := right.raiseTo henv hscoped formed N (Nat.le_max_right ..)
  refine ⟨N, a.bound, a.raw.union b.raw, a.footprint ++ b.footprint,
    .union a.observation b.observation, ?_, append_available a.resources b.resources,
    Profile.Live.union_iff.mpr ⟨a.live, b.live⟩⟩
  rw [raiseProfile_union]
  have ha : GeneralNormalProfileAdapter env U registry target (a.raw : Profile N) (raiseProfile N a.bound p) := a.adapter
  have hb : GeneralNormalProfileAdapter env U registry target (b.raw : Profile N) (raiseProfile N b.bound q) := b.adapter
  simpa only [GeneralNormalProfileAdapter, AdapterNormal.profile, Profile.union, Profile.atoms,
    Profile.mk, List.map_append] using GeneralProfileAdapter.union ha hb

/-- Cross-grade code actions modify only the finite directional adapter;
the retained raw source query and its actual liveness remain unchanged. -/
noncomputable def RichGradedResult.codeAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {profile : Profile n} {output : Profile m}
    (result : RichGradedResult sourceEnv env U registry target node locals σ available profile)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (sorted : profile.HasType (.sort relevant)) :
    RichGradedResult sourceEnv env U registry target node locals σ available output := by
  let N := max result.rank m
  let lifted := result.raiseTo henv hscoped formed N (Nat.le_max_left ..)
  have outBound : m ≤ N := Nat.le_max_right ..
  have inputSorted := Profile.HasType.raise_sort lifted.bound sorted
  let adapter := (action.atGrade lifted.bound outBound).toGeneralAdapter inputSorted
  exact ⟨N, outBound, lifted.raw, lifted.footprint, lifted.observation,
    lifted.adapter.comp adapter, lifted.resources, lifted.live⟩

theorem RichGradedResult.outputPath
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (path : GeneralOutputPath env U registry target a b)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available (.singleton a)) :
    Nonempty (RichGradedResult sourceEnv env U registry target node locals σ available (.singleton b)) := by
  induction path with
  | refl => exact ⟨result⟩
  | action path action ih =>
    obtain ⟨result⟩ := ih
    exact result.action henv hscoped formed action
  | code path action sorted ih =>
    obtain ⟨result⟩ := ih
    exact ⟨result.codeAdapter henv hscoped formed action sorted⟩
  | pad path ih =>
    obtain ⟨result⟩ := ih
    exact ⟨result.pad henv hscoped formed⟩
  | unpad path ih =>
    obtain ⟨result⟩ := ih
    exact ⟨result.unpad⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
