import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceReflection
import Lean4Lean.Theory.Typing.AnchoredEtaFootprint
import Lean4Lean.Theory.Typing.AnchoredApplicationTrace

/-! Actual adapted eta spines retain the raw argument profile and its
stored directional adapter. Variable traces still have only finite views. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def Obs.variableTrace
    (observation : Obs env U registry Γ locals σ (.bvar i) demand footprint) :
    VariableTrace env U registry Γ i demand footprint :=
  match observation with
  | .var _ _ _ demand => .leaf demand
  | .empty => .empty
  | .union left right => .union left.variableTrace right.variableTrace
  | .view source change => .view source.variableTrace change
  | .pad source => .pad source.variableTrace
  | .unpad source => .unpad source.variableTrace
  | .rowShift source => .rowShift source.variableTrace

theorem Obs.app_empty_footprint
    (observation : Obs env U registry Γ locals σ (.app f a) demand footprint)
    (empty : demand = .empty) : footprint = [] := by
  match observation with
  | .empty => rfl
  | .app .. => cases empty
  | .union left right =>
    have parts := List.append_eq_nil_iff.mp empty
    rw [left.app_empty_footprint parts.1, right.app_empty_footprint parts.2]
    rfl
  | .view .. => cases empty
  | .pad source => exact source.app_empty_footprint (List.map_eq_nil_iff.mp empty)
  | .unpad source =>
    exact source.app_empty_footprint (by rw [empty]; rfl)
  | .rowShift .. => cases empty
termination_by sizeOf observation

structure AppOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr) where
  rank : Nat
  key : Key rank
  output : Atom rank
  functionFootprint : Footprint
  argumentFootprint : Footprint
  function : Obs env U registry Γ locals σ f (Profile.fn key output) functionFootprint
  rawInput : Profile rank
  argument : Obs env U registry Γ locals σ a rawInput argumentFootprint
  arguments : NormalProfileAdapter env U registry Γ rawInput key.input
  admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)

theorem Obs.application_factor {demand : Profile n}
    (observation : Obs env U registry Γ locals σ (.app f a) demand footprint)
    (output : Atom n) (single : demand = .singleton output) :
    ∃ origin : AppOrigin env U registry Γ locals σ f a,
      Nonempty (AppOutputPath env U registry Γ origin.output output) ∧
      footprint = origin.functionFootprint ++ origin.argumentFootprint := by
  match n, demand, footprint, observation with
  | _, _, _, .empty => cases single
  | _, _, _, .app fn arg arguments admitted =>
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, _, _, fn, _, arg, arguments, admitted⟩, ⟨.refl⟩, rfl⟩
  | _, _, _, @Obs.union _ _ _ _ _ _ _ _ leftDemand _ rightDemand _ left right =>
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · have hf := left.app_empty_footprint hs.1
      obtain ⟨origin, path, footprint⟩ := right.application_factor output hs.2
      exact ⟨origin, path, by rw [hf, List.nil_append, footprint]⟩
    · obtain ⟨origin, path, footprint⟩ := left.application_factor output hs.1
      have hf := right.app_empty_footprint hs.2
      exact ⟨origin, path, by rw [hf, List.append_nil, footprint]⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor _ rfl
    exact ⟨origin, ⟨.view path change⟩, footprint⟩
  | _, _, _, @Obs.pad _ _ _ _ _ _ _ _ demand _ source =>
    obtain ⟨first, he, hout⟩ := List.map_eq_singleton_iff.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor first he
    exact ⟨origin, hout ▸ Nonempty.intro (AppOutputPath.pad path), footprint⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor (.pad output)
      (by rw [single, Profile.pad_singleton])
    exact ⟨origin, ⟨.unpad path⟩, footprint⟩
  | _, _, _, .rowShift source =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint⟩ := source.application_factor _ rfl
    exact ⟨origin, ⟨.rowShift path⟩, footprint⟩
termination_by sizeOf observation

end Lean4Lean.AnchoredSource.Adapted
