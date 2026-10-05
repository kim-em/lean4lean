import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambda
import Lean4Lean.Theory.Typing.AnchoredApplicationTrace

/-! A singleton lambda observation retains one actual lambda constructor.
Its finite outer path records every output view and change of grade. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Obs.lam_empty_footprint
    (observation : Obs env U registry Γ locals σ (.lam A body) demand footprint)
    (empty : demand = .empty) : footprint = [] := by
  match observation with
  | .empty => rfl
  | .lam .. => cases empty
  | .union left right =>
    have parts := List.append_eq_nil_iff.mp empty
    rw [left.lam_empty_footprint parts.1, right.lam_empty_footprint parts.2]
    rfl
  | .view .. => cases empty
  | .pad source => exact source.lam_empty_footprint (List.map_eq_nil_iff.mp empty)
  | .unpad source => exact source.lam_empty_footprint (by rw [empty]; rfl)
  | .rowShift .. => cases empty
termination_by sizeOf observation

structure LamOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (A body : VExpr) where
  rank : Nat
  key : Key rank
  output : Atom rank
  node : CoveredLambda env U registry Γ locals σ A body key output

theorem Obs.lambda_factor {demand : Profile n}
    (observation : Obs env U registry Γ locals σ (.lam A body) demand footprint)
    (output : Atom n) (single : demand = .singleton output) :
    ∃ origin : LamOrigin env U registry Γ locals σ A body,
      Nonempty (AppOutputPath env U registry Γ (r := origin.rank + 1) (AtomData.fn origin.key origin.output) output) ∧
      footprint = origin.node.domainFootprint ++ origin.node.outside := by
  match n, demand, footprint, observation with
  | _, _, _, .empty => cases single
  | _, _, _, .lam domain guard body pack covered =>
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, ⟨_, _, domain, guard, _, body, _, _, pack, covered⟩⟩, ⟨.refl⟩, rfl⟩
  | _, _, _, @Obs.union _ _ _ _ _ _ _ _ leftDemand _ rightDemand _ left right =>
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · have hf := left.lam_empty_footprint hs.1
      obtain ⟨origin, path, footprint⟩ := right.lambda_factor output hs.2
      exact ⟨origin, path, by rw [hf, List.nil_append, footprint]⟩
    · obtain ⟨origin, path, footprint⟩ := left.lambda_factor output hs.1
      have hf := right.lam_empty_footprint hs.2
      exact ⟨origin, path, by rw [hf, List.append_nil, footprint]⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.lambda_factor _ rfl
    exact ⟨origin, ⟨.view path change⟩, footprint⟩
  | _, _, _, @Obs.pad _ _ _ _ _ _ _ _ demand _ source =>
    obtain ⟨first, he, hout⟩ := List.map_eq_singleton_iff.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.lambda_factor first he
    exact ⟨origin, hout ▸ Nonempty.intro (AppOutputPath.pad path), footprint⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.lambda_factor (.pad output)
      (by rw [single, Profile.pad_singleton])
    exact ⟨origin, ⟨.unpad path⟩, footprint⟩
  | _, _, _, .rowShift source =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.lambda_factor _ rfl
    exact ⟨origin, ⟨.rowShift path⟩, footprint⟩
termination_by sizeOf observation

end Lean4Lean.AnchoredSource.Adapted
