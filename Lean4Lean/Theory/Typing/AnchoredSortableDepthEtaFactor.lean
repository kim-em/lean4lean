import Lean4Lean.Theory.Typing.AnchoredSortableEtaFactor
import Lean4Lean.Theory.Typing.AnchoredSortableDepthAppOrigin
import Lean4Lean.Theory.Typing.AnchoredSortableDepthReflection
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthGrades
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
private noncomputable def selectGeneral_allDepth {p q : Profile n}
    (included : List.Subset q.atoms p.atoms) :
    GeneralNormalProfileAdapter env U registry Γ p q :=
  GeneralProfileAdapter.select (fun _ h => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨a, included ha, rfl⟩)

theorem SortableObs.eta_factor_allDepth
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    {lambdaKey : Key n} {output : Atom n} {packed : Profile n}
    (body : SortableObs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ lambdaKey.input.atoms) :
    ∃ factor : SortableEtaFactor env U registry Γ locals σ f lambdaKey output outside,
      ∀ current, factor.function.nativeDepth current ≤ body.nativeDepth current := by
  obtain ⟨origin, ⟨path⟩, included, originDepth⟩ := body.applicationOrigin_allDepth (List.mem_singleton_self _)
  obtain ⟨required, reflected, hrequired, reflectedDepth⟩ :=
    origin.function.reflectSource_allDepth (.skip .refl) lift_eq_lift' locals
  change SortableObs env U registry Γ locals σ f (Profile.fn origin.key origin.output) required at reflected
  let argument := origin.argument.variableTrace
  have harg : List.Subset origin.argumentFootprint bodyFootprint :=
    fun _ h => included (List.mem_append_right _ h)
  obtain ⟨hbounds, hinput⟩ := BinderPack.variable_subset pack argument harg
  have houtside : List.Subset required outside := by
    intro entry member
    rcases entry with ⟨i, need⟩
    apply BinderPack.external_member pack
    apply included
    apply List.mem_append_left
    rw [hrequired]
    exact List.mem_map.mpr ⟨(i, need), member, rfl⟩
  let N := max path.height argument.height
  have hp : path.height ≤ N := Nat.le_max_left _ _
  have ha : argument.height ≤ N := Nat.le_max_right _ _
  have hn : n ≤ N := Nat.le_trans path.bounds.2 hp
  have hr : origin.rank ≤ N := Nat.le_trans path.bounds.1 hp
  let lifted : SortableObs env U registry Γ locals σ f
      (.singleton (raiseAtom (N + 1) (Nat.succ_le_succ hr) (.fn origin.key origin.output))) required :=
    cast (congrArg (fun p => SortableObs env U registry Γ locals σ f p required)
      (raiseProfile_singleton (Nat.succ_le_succ hr) (.fn origin.key origin.output)))
      (reflected.raise (Nat.succ_le_succ hr))
  let exposed := SortableObs.view lifted (functionGradeView hr origin.key origin.output)
  have exposedDepth (current : Name → Bool) : exposed.nativeDepth current = origin.function.nativeDepth current := by
    simp only [exposed, SortableObs.nativeDepth]
    rw [show lifted.nativeDepth current = reflected.nativeDepth current from
      (SortableObs.nativeDepth_cast current (raiseProfile_singleton (Nat.succ_le_succ hr) (.fn origin.key origin.output)) _ _).trans
        (reflected.nativeDepth_raise current (Nat.succ_le_succ hr))]
    exact reflectedDepth current
  have variableAdapter := argument.normalize henv hscoped hΓ N ha
  have selected : GeneralNormalProfileAdapter env U registry Γ
      (raiseProfile N hn lambdaKey.input) (origin.argumentFootprint.atGrade N) := by
    rw [Footprint.atGrade_raise hn hbounds]
    exact selectGeneral_allDepth (raiseProfile_subset hn (fun a h => covered a (hinput h)))
  have argumentAdapter := GeneralNormalProfileAdapter.raise henv hscoped hΓ hr origin.arguments
  have arguments := selected.comp (variableAdapter.comp argumentAdapter)
  have outputAction := path.normalize N hp
  exact ⟨{
    rank := N
    bound := hn
    key := raiseKey N hr origin.key
    rawOutput := raiseAtom N hr origin.output
    functionFootprint := required
    function := exposed
    included := houtside
    admitted := Admitted.raise henv hr origin.admitted
    arguments := arguments
    resultAction := outputAction
    result := outputAction.toGeneralAdapter henv hscoped hΓ }, by
      intro current
      change exposed.nativeDepth current ≤ _
      rw [exposedDepth]
      exact Nat.le_trans (Nat.le_max_left _ _) (originDepth current)⟩

end Lean4Lean.AnchoredSource.Adapted
