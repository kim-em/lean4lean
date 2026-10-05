import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaFactor
import Lean4Lean.Theory.Typing.AnchoredSortableVariableNormalization
import Lean4Lean.Theory.Typing.AnchoredSortableReflection
import Lean4Lean.Theory.Typing.AnchoredSortableAppOrigin
import Lean4Lean.Theory.Typing.AnchoredSortableEtaPack
import Lean4Lean.Theory.Typing.AnchoredSortableGrades

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics

/-- The retained function has its actual input key. The requested lambda
input is connected contravariantly by an explicit finite general adapter.
Unused query branches may retain extra outside resources. -/
structure SortableEtaFactor (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (f : VExpr)
    (lambdaKey : Key n) (output : Atom n) (outside : Footprint) where
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  rawOutput : Atom rank
  functionFootprint : Footprint
  function : SortableObs env U registry Γ locals σ f (Profile.fn key rawOutput) functionFootprint
  included : List.Subset functionFootprint outside
  admitted : Admitted env U registry Γ key lambdaKey.anchor lambdaKey.anchor
  arguments : GeneralNormalProfileAdapter env U registry Γ
    (raiseProfile rank bound lambdaKey.input) key.input
  resultAction : AtomAction env U registry Γ rawOutput (raiseAtom rank bound output)
  result : GeneralNormalAtomAdapter env U registry Γ rawOutput (raiseAtom rank bound output)

set_option backward.isDefEq.respectTransparency false

private noncomputable def selectGeneral {p q : Profile n}
    (included : List.Subset q.atoms p.atoms) :
    GeneralNormalProfileAdapter env U registry Γ p q :=
  GeneralProfileAdapter.select (fun _ h => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨a, included ha, rfl⟩)

theorem SortableObs.eta_factor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    {lambdaKey : Key n} {output : Atom n} {packed : Profile n}
    (body : SortableObs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ lambdaKey.input.atoms) :
    Nonempty (SortableEtaFactor env U registry Γ locals σ f lambdaKey output outside) := by
  obtain ⟨origin, ⟨path⟩, included⟩ := body.applicationOrigin (List.mem_singleton_self _)
  obtain ⟨required, ⟨reflected⟩, hrequired⟩ :=
    origin.function.reflectSource (.skip .refl) lift_eq_lift' locals
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
  have lifted := reflected.raise (Nat.succ_le_succ hr)
  simp only [Profile.fn, raiseProfile_singleton] at lifted
  have exposed := SortableObs.view lifted (functionGradeView hr origin.key origin.output)
  have variableAdapter := argument.normalize henv hscoped hΓ N ha
  have selected : GeneralNormalProfileAdapter env U registry Γ
      (raiseProfile N hn lambdaKey.input) (origin.argumentFootprint.atGrade N) := by
    rw [Footprint.atGrade_raise hn hbounds]
    exact selectGeneral (raiseProfile_subset hn (fun a h => covered a (hinput h)))
  have argumentAdapter := GeneralNormalProfileAdapter.raise henv hscoped hΓ hr origin.arguments
  have arguments := selected.comp (variableAdapter.comp argumentAdapter)
  have outputAction := path.normalize N hp
  exact ⟨{
    rank := N
    bound := hn
    key := raiseKey N hr origin.key
    rawOutput := raiseAtom N hr origin.output
    functionFootprint := required
    function := by simpa only [Profile.fn, raiseProfile_singleton] using exposed
    included := houtside
    admitted := Admitted.raise henv hr origin.admitted
    arguments := arguments
    resultAction := outputAction
    result := outputAction.toGeneralAdapter henv hscoped hΓ }⟩

end Lean4Lean.AnchoredSource.Adapted
