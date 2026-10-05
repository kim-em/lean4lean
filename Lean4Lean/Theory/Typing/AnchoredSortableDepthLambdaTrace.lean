import Lean4Lean.Theory.Typing.AnchoredSortableLambdaTrace
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth

/-! The actual selected lambda row retains every caller's declaration fuel,
even when actions and unused rich union branches surround that row. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
theorem Obs.lambda_factor_allDepth {demand : Profile n}
    (observation : Obs env U registry Γ locals σ (.lam A body) demand footprint)
    (output : Atom n) (single : demand = .singleton output) :
    ∃ origin : LamOrigin env U registry Γ locals σ A body,
      Nonempty (AppOutputPath env U registry Γ (r := origin.rank + 1) (AtomData.fn origin.key origin.output) output) ∧
      footprint = origin.node.domainFootprint ++ origin.node.outside ∧
      ∀ current, max (origin.node.domain.nativeDepth current) (origin.node.bodyObservation.nativeDepth current) ≤
        observation.nativeDepth current := by
  match n, demand, footprint, observation with
  | _, _, _, .empty => cases single
  | _, _, _, .lam domain guard body pack covered =>
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, ⟨_, _, domain, guard, _, body, _, _, pack, covered⟩⟩, ⟨.refl⟩, rfl, by intro current; simp only [Obs.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, @Obs.union _ _ _ _ _ _ _ _ leftDemand _ rightDemand _ left right =>
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · have hf := left.lam_empty_footprint hs.1
      obtain ⟨origin, path, footprint, bound⟩ := right.lambda_factor_allDepth output hs.2
      exact ⟨origin, path, by rw [hf, List.nil_append, footprint], fun current =>
        Nat.le_trans (bound current) (by simp only [Obs.nativeDepth]; exact Nat.le_max_right _ _)⟩
    · obtain ⟨origin, path, footprint, bound⟩ := left.lambda_factor_allDepth output hs.1
      have hf := right.lam_empty_footprint hs.2
      exact ⟨origin, path, by rw [hf, List.append_nil, footprint], fun current =>
        Nat.le_trans (bound current) (by simp only [Obs.nativeDepth]; exact Nat.le_max_left _ _)⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bound⟩ := source.lambda_factor_allDepth _ rfl
    exact ⟨origin, ⟨.view path change⟩, footprint, by intro current; simpa only [Obs.nativeDepth] using bound current⟩
  | _, _, _, @Obs.pad _ _ _ _ _ _ _ _ demand _ source =>
    obtain ⟨first, he, hout⟩ := List.map_eq_singleton_iff.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bound⟩ := source.lambda_factor_allDepth first he
    exact ⟨origin, hout ▸ Nonempty.intro (AppOutputPath.pad path), footprint, by intro current; simpa only [Obs.nativeDepth] using bound current⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, footprint, bound⟩ := source.lambda_factor_allDepth (.pad output)
      (by rw [single, Profile.pad_singleton])
    exact ⟨origin, ⟨.unpad path⟩, footprint, by intro current; simpa only [Obs.nativeDepth] using bound current⟩
  | _, _, _, .rowShift source =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bound⟩ := source.lambda_factor_allDepth _ rfl
    exact ⟨origin, ⟨.rowShift path⟩, footprint, by intro current; simpa only [Obs.nativeDepth] using bound current⟩
termination_by sizeOf observation

theorem SortableObs.lambda_factorFunction_allDepth {demand : Profile n}
    (observation : SortableObs env U registry Γ locals σ (.lam A body) demand footprint)
    (output : Atom n) (single : demand = .singleton output) (shape : FunctionShape output) :
    ∃ origin : SortableLamOrigin env U registry Γ locals σ A body,
      Nonempty (SortableOutputPath env U registry Γ (r := origin.rank + 1)
        (AtomData.fn origin.key origin.output) output) ∧
      List.Subset (origin.node.domainFootprint ++ origin.node.outside) footprint ∧
      ∀ current, max (origin.node.domain.nativeDepth current) (origin.node.bodyObservation.nativeDepth current) ≤
        observation.nativeDepth current := by
  match n, demand, footprint, observation with
  | _, _, _, .legacy source =>
    obtain ⟨origin, ⟨path⟩, equal, bound⟩ := source.lambda_factor_allDepth output single
    exact ⟨⟨origin.rank, origin.key, origin.output, origin.node.toSortable⟩, ⟨.legacy path⟩,
      (fun _ member => equal ▸ member), by
        intro current
        simpa only [CoveredLambda.toSortable, SortableCert.nativeDepth, SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .code _ certificate =>
    exact False.elim (shape.not_sortable (single ▸ certificate.formed))
  | _, _, _, .lam domain guard body pack covered =>
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, ⟨_, _, domain, guard, _, body, _, _, pack, covered⟩⟩,
      ⟨.refl⟩, (fun _ member => member), by intro current; simp only [SortableObs.nativeDepth]; exact Nat.le_refl _⟩
  | _, _, _, .union left right =>
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · obtain ⟨origin, path, included, bound⟩ := right.lambda_factorFunction_allDepth output hs.2 shape
      exact ⟨origin, path, (fun _ member => List.mem_append_right _ (included member)), fun current =>
        Nat.le_trans (bound current) (by simp only [SortableObs.nativeDepth]; exact Nat.le_max_right _ _)⟩
    · obtain ⟨origin, path, included, bound⟩ := left.lambda_factorFunction_allDepth output hs.1 shape
      exact ⟨origin, path, (fun _ member => List.mem_append_left _ (included member)), fun current =>
        Nat.le_trans (bound current) (by simp only [SortableObs.nativeDepth]; exact Nat.le_max_left _ _)⟩
  | _, _, _, .action source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, included, bound⟩ :=
      source.lambda_factorFunction_allDepth _ rfl ((AtomAction.functionShape_iff change).mpr shape)
    exact ⟨origin, ⟨.action path change⟩, included, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, included, bound⟩ :=
      source.lambda_factorFunction_allDepth _ rfl ((AtomView.functionShape_iff change).mpr shape)
    exact ⟨origin, ⟨.action path (.view change)⟩, included, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .pad source =>
    obtain ⟨first, equal, outputEq⟩ := List.map_eq_singleton_iff.mp single
    have firstShape : FunctionShape first := by simpa only [← outputEq, FunctionShape] using shape
    obtain ⟨origin, ⟨path⟩, included, bound⟩ := source.lambda_factorFunction_allDepth first equal firstShape
    exact ⟨origin, outputEq ▸ Nonempty.intro (SortableOutputPath.pad path), included, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, included, bound⟩ := source.lambda_factorFunction_allDepth (.pad output)
      (by rw [single, Profile.pad_singleton]) shape
    exact ⟨origin, ⟨.unpad path⟩, included, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
  | _, _, _, .rowShift source =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, included, bound⟩ := source.lambda_factorFunction_allDepth _ rfl True.intro
    exact ⟨origin, ⟨.rowShift path⟩, included, by intro current; simpa only [SortableObs.nativeDepth] using bound current⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

end Lean4Lean.AnchoredSource.Adapted
