import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaFactor
import Lean4Lean.Theory.Typing.AnchoredBoundedReflection

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private normalSelect from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaFactor
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

theorem Obs.application_factorBounded {demand : Profile n}
    (observation : Obs env U registry Γ locals σ (.app f a) demand footprint)
    (output : Atom n) (single : demand = .singleton output)
    (bound : observation.nativeDepth current ≤ fuel) :
    ∃ origin : AppOrigin env U registry Γ locals σ f a,
      Nonempty (AppOutputPath env U registry Γ origin.output output) ∧
      footprint = origin.functionFootprint ++ origin.argumentFootprint ∧
      origin.function.nativeDepth current ≤ fuel := by
  match n, demand, footprint, observation with
  | _, _, _, .empty => cases single
  | _, _, _, .app fn arg arguments admitted =>
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, _, _, fn, _, arg, arguments, admitted⟩, ⟨.refl⟩, rfl, (Nat.max_le.mp (by simpa only [Obs.nativeDepth] using bound)).1⟩
  | _, _, _, @Obs.union _ _ _ _ _ _ _ _ leftDemand _ rightDemand _ left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using bound)
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · have hf := left.app_empty_footprint hs.1
      obtain ⟨origin, path, footprint, bounded⟩ := right.application_factorBounded output hs.2 bounds.2
      exact ⟨origin, path, by rw [hf, List.nil_append, footprint], bounded⟩
    · obtain ⟨origin, path, footprint, bounded⟩ := left.application_factorBounded output hs.1 bounds.1
      have hf := right.app_empty_footprint hs.2
      exact ⟨origin, path, by rw [hf, List.append_nil, footprint], bounded⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bounded⟩ := source.application_factorBounded _ rfl (by simpa only [Obs.nativeDepth] using bound)
    exact ⟨origin, ⟨.view path change⟩, footprint, bounded⟩
  | _, _, _, @Obs.pad _ _ _ _ _ _ _ _ demand _ source =>
    obtain ⟨first, he, hout⟩ := List.map_eq_singleton_iff.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bounded⟩ := source.application_factorBounded first he (by simpa only [Obs.nativeDepth] using bound)
    exact ⟨origin, hout ▸ Nonempty.intro (AppOutputPath.pad path), footprint, bounded⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, footprint, bounded⟩ := source.application_factorBounded (.pad output)
      (by rw [single, Profile.pad_singleton]) (by simpa only [Obs.nativeDepth] using bound)
    exact ⟨origin, ⟨.unpad path⟩, footprint, bounded⟩
  | _, _, _, .rowShift source =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, footprint, bounded⟩ := source.application_factorBounded _ rfl (by simpa only [Obs.nativeDepth] using bound)
    exact ⟨origin, ⟨.rowShift path⟩, footprint, bounded⟩
termination_by sizeOf observation

theorem Obs.eta_factorBounded
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    {lambdaKey : Key n} {output : Atom n} {packed : Profile n}
    (body : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ lambdaKey.input.atoms) :
    ∃ factor : EtaFactor env U registry Γ locals σ f lambdaKey output outside,
      factor.function.nativeDepth current ≤ fuel := by
  obtain ⟨origin, ⟨path⟩, hbody, functionBound⟩ := body.application_factorBounded output rfl bodyBound
  obtain ⟨required, reflected, hrequired, reflectedBound⟩ :=
    origin.function.reflectSourceBounded (.skip .refl) lift_eq_lift' locals functionBound
  change Obs env U registry Γ locals σ f (Profile.fn origin.key origin.output) required at reflected
  rw [hbody, hrequired] at pack
  let argument := origin.argument.variableTrace
  obtain ⟨hinput, hbounds, houtside⟩ := pack.etaFootprint argument
  subst outside
  let N := max path.height argument.height
  have hp : path.height ≤ N := Nat.le_max_left _ _
  have ha : argument.height ≤ N := Nat.le_max_right _ _
  have hn : n ≤ N := Nat.le_trans path.bounds.2 hp
  have hr : origin.rank ≤ N := Nat.le_trans path.bounds.1 hp
  have liftedPair : ∃ lifted : Obs env U registry Γ locals σ f
      (raiseProfile (N + 1) (Nat.succ_le_succ hr) (Profile.fn origin.key origin.output)) required,
      lifted.nativeDepth current ≤ fuel :=
    ⟨reflected.raise (Nat.succ_le_succ hr), by simpa only [Obs.nativeDepth_raise] using reflectedBound⟩
  rw [show raiseProfile (N + 1) (Nat.succ_le_succ hr) (Profile.fn origin.key origin.output) =
    Profile.singleton (raiseAtom (N + 1) (Nat.succ_le_succ hr) (.fn origin.key origin.output)) from
    raiseProfile_singleton (Nat.succ_le_succ hr) _] at liftedPair
  obtain ⟨lifted, liftedBound⟩ := liftedPair
  let exposed := Obs.view lifted (functionGradeView hr origin.key origin.output)
  have variableAdapter := (argument.normalize N ha).toAdapter henv hscoped hΓ
  have selected : NormalProfileAdapter env U registry Γ
      (raiseProfile N hn lambdaKey.input) (origin.argumentFootprint.atGrade N) := by
    rw [Footprint.atGrade_raise hn hbounds, ← hinput]
    exact normalSelect (raiseProfile_subset hn covered)
  have argumentAdapter := NormalProfileAdapter.raise henv hscoped hΓ hr origin.arguments
  have arguments := NormalProfileAdapter.comp selected
    (NormalProfileAdapter.comp variableAdapter argumentAdapter)
  refine ⟨{
    rank := N
    bound := hn
    key := raiseKey N hr origin.key
    rawOutput := raiseAtom N hr origin.output
    function := exposed
    admitted := Admitted.raise henv hr origin.admitted
    arguments := arguments
    resultView := path.normalize N hp
    result := (path.normalize N hp).toAdapter henv hscoped hΓ }, ?_⟩
  simpa only [exposed, Obs.nativeDepth] using liftedBound

end Lean4Lean.AnchoredSource.Adapted
