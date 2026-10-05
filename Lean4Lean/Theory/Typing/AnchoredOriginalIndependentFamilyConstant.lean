import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyFamilyConstantOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalFamilyConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode

/-! A function-valued family constant may retain its plan in an independent
canonical source. Selection keeps that actual source and original root; it
never casts the seed to the caller's environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure IndependentFamilySeed (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (name : Name) (levels : List VLevel) where
  sourceEnv : VEnv
  source : List VExpr
  rootExpression : VExpr
  rootType : VExpr
  root : EndpointRef sourceEnv U source rootExpression rootType
  ordered : sourceEnv.Ordered
  below : sourceEnv ≤ env
  retained : RetainedRichFamilySeed root env registry target name levels

noncomputable def IndependentFamilySeed.ofRetained
    {sourceEnv : VEnv} {source : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (seed : RetainedRichFamilySeed root env registry target name levels) :
    IndependentFamilySeed env U registry target name levels :=
  ⟨sourceEnv, source, rootExpression, rootType, root, ordered, below, seed⟩

theorem RichObs.independentFamilyValueAux
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {demand : Profile n} {atom : Atom n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (fuel : Nat) (bounded : sizeOf query < fuel)
    (location : Located root node) (member : atom ∈ demand.atoms)
    (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag)) :
    ∃ seed : IndependentFamilySeed env U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.retained.atom atom) := by
  cases hquery : query with
  | family origin lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree typed
    let seed := RetainedRichFamilySeed.ofNative location origin lookup noDefinition noNative noQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree
    exact ⟨.ofRetained ordered below seed, ⟨.refl⟩⟩
  | constructor _ _ _ _ _ _ _ _ _ _ _ _ _ tree =>
    exact (RichConstructorPlan.not_familyEnd henv hscoped formed tree member ends).elim
  | canonicalDelta lookup _ _ _ _ _ _ _ _ _ _ _ => rw [notDefinition] at lookup; contradiction
  | canonicalConst origin realization child resources =>
    exact child.independentFamilyValueAux henv hscoped formed origin.owner.selected.origin.ordered
      origin.owner.selected.origin.sourceBelow notDefinition notNative (fuel - 1)
      (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) .here member ends nonsortable
  | legacy child =>
    obtain ⟨seed, path⟩ := child.familyConstantOrigin henv hscoped formed ordered below
      notDefinition notNative location member ends
    exact ⟨.ofRetained ordered below seed, path⟩
  | code child => exact (nonsortable _ (child.formed.singleton_of_mem member)).elim
  | route path child =>
    exact child.independentFamilyValueAux henv hscoped formed ordered below notDefinition notNative
      (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega)
      (path.locate location) member ends nonsortable
  | union left right =>
    rcases List.mem_append.mp member with member | member
    · exact left.independentFamilyValueAux henv hscoped formed ordered below notDefinition notNative
        (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega)
        location member ends nonsortable
    · exact right.independentFamilyValueAux henv hscoped formed ordered below notDefinition notNative
        (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega)
        location member ends nonsortable
  | view child change =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩⟩ := child.independentFamilyValueAux henv hscoped formed ordered below
      notDefinition notNative (fuel - 1)
      (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) location (List.mem_singleton_self _)
      (ends.viewBack henv hscoped formed change)
      (fun flag sorted => nonsortable flag ((AtomAction.view change).sortable sorted))
    exact ⟨seed, ⟨.action path (.view change)⟩⟩
  | action child change =>
    cases List.mem_singleton.mp member
    obtain ⟨seed, ⟨path⟩⟩ := child.independentFamilyValueAux henv hscoped formed ordered below
      notDefinition notNative (fuel - 1)
      (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) location (List.mem_singleton_self _)
      (ends.normalAdapterBack (change.toGeneralAdapter henv hscoped formed))
      (fun flag sorted => nonsortable flag (change.sortable sorted))
    exact ⟨seed, ⟨.action path change⟩⟩
  | select child selected =>
    cases List.mem_singleton.mp member
    exact child.independentFamilyValueAux henv hscoped formed ordered below notDefinition notNative
      (fuel - 1) (by have hb := bounded; rw [hquery] at hb; simp at hb; omega)
      location selected ends nonsortable
  | pad child =>
    obtain ⟨old, selected, equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨seed, ⟨path⟩⟩ := child.independentFamilyValueAux henv hscoped formed ordered below
      notDefinition notNative (fuel - 1)
      (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) location selected ends
      (fun flag sorted => nonsortable flag sorted.pad_sort)
    exact ⟨seed, ⟨.pad path⟩⟩
  | unpad child =>
    obtain ⟨seed, ⟨path⟩⟩ := child.independentFamilyValueAux henv hscoped formed ordered below
      notDefinition notNative (fuel - 1)
      (by have hb := bounded; rw [hquery] at hb; simp at hb; omega) location (List.mem_map_of_mem member) ends
      (fun flag sorted => nonsortable flag (by
        have high : (Profile.singleton atom).pad.HasType (.sort flag) := by
          simpa only [Profile.pad_singleton] using sorted
        simpa only [Profile.down_sort] using high.pad_inv))
    exact ⟨seed, ⟨.unpad path⟩⟩
termination_by fuel
decreasing_by all_goals omega

/-- The public selector computes its traversal bound from the actual query.
Its output keeps the independent original root of every canonical wrapper. -/
theorem RichObs.independentFamilyValue
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {demand : Profile n} {atom : Atom n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node) (member : atom ∈ demand.atoms)
    (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag)) :
    ∃ seed : IndependentFamilySeed env U registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.retained.atom atom) :=
  query.independentFamilyValueAux henv hscoped formed ordered below notDefinition notNative
    (sizeOf query + 1) (Nat.lt_succ_self _) location member ends nonsortable

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
