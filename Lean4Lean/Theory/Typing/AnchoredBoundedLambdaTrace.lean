import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaTrace
import Lean4Lean.Theory.Typing.AnchoredNativeDepth

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

theorem Obs.lambda_factor_bounded {demand : Profile n}
    (observation : Obs env U registry Γ locals σ (.lam A body) demand footprint)
    (bound : observation.nativeDepth current ≤ fuel)
    (output : Atom n) (single : demand = .singleton output) :
    ∃ origin : LamOrigin env U registry Γ locals σ A body,
      Nonempty (AppOutputPath env U registry Γ (r := origin.rank + 1) (AtomData.fn origin.key origin.output) output) ∧
      footprint = origin.node.domainFootprint ++ origin.node.outside ∧
      origin.node.domain.nativeDepth current ≤ fuel ∧
      origin.node.bodyObservation.nativeDepth current ≤ fuel := by
  match n, demand, footprint, observation with
  | _, _, _, .empty => cases single
  | _, _, _, .lam domain guard body pack covered =>
    simp only [Obs.nativeDepth] at bound
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, ⟨_, _, domain, guard, _, body, _, _, pack, covered⟩⟩, ⟨.refl⟩, rfl, Nat.max_le.mp bound⟩
  | _, _, _, @Obs.union _ _ _ _ _ _ _ _ leftDemand _ rightDemand _ left right =>
    simp only [Obs.nativeDepth] at bound
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · have hf := left.lam_empty_footprint hs.1
      obtain ⟨origin, path, footprint, bounds⟩ := Obs.lambda_factor_bounded right (Nat.max_le.mp bound).2 output hs.2
      exact ⟨origin, path, by rw [hf, List.nil_append, footprint], bounds⟩
    · obtain ⟨origin, path, footprint, bounds⟩ := Obs.lambda_factor_bounded left (Nat.max_le.mp bound).1 output hs.1
      have hf := right.lam_empty_footprint hs.2
      exact ⟨origin, path, by rw [hf, List.append_nil, footprint], bounds⟩
  | _, _, _, .view source change =>
    simp only [Obs.nativeDepth] at bound
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bounds⟩ := Obs.lambda_factor_bounded source bound _ rfl
    exact ⟨origin, ⟨.view path change⟩, footprint, bounds⟩
  | _, _, _, @Obs.pad _ _ _ _ _ _ _ _ demand _ source =>
    simp only [Obs.nativeDepth] at bound
    obtain ⟨first, he, hout⟩ := List.map_eq_singleton_iff.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bounds⟩ := Obs.lambda_factor_bounded source bound first he
    exact ⟨origin, hout ▸ Nonempty.intro (AppOutputPath.pad path), footprint, bounds⟩
  | _, _, _, .unpad source =>
    simp only [Obs.nativeDepth] at bound
    obtain ⟨origin, ⟨path⟩, footprint, bounds⟩ := Obs.lambda_factor_bounded source bound (.pad output)
      (by rw [single, Profile.pad_singleton])
    exact ⟨origin, ⟨.unpad path⟩, footprint, bounds⟩
  | _, _, _, .rowShift source =>
    simp only [Obs.nativeDepth] at bound
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bounds⟩ := Obs.lambda_factor_bounded source bound _ rfl
    exact ⟨origin, ⟨.rowShift path⟩, footprint, bounds⟩
termination_by sizeOf observation


end Lean4Lean.AnchoredSource.Adapted
