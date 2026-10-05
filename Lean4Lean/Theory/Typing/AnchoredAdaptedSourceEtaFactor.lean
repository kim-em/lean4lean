import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaTrace
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaGrades
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGrades

/-! The concrete adapted eta spine. The declared lambda input only needs to
cover consumed leaves; its argument action is directional throughout. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private noncomputable def selectAdapter {p q : Profile n}
    (included : ∀ atom ∈ q.atoms, atom ∈ p.atoms) :
    ProfileAdapter env U registry Γ p q := by
  induction q with
  | nil => exact .nil _
  | cons a q ih =>
    exact .cons (included a List.mem_cons_self) (.refl a)
      (ih (fun a hm => included a (List.mem_cons_of_mem _ hm)))

private noncomputable def normalSelect {p q : Profile n}
    (included : ∀ atom ∈ q.atoms, atom ∈ p.atoms) :
    NormalProfileAdapter env U registry Γ p q :=
  selectAdapter (fun atom hm => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨a, included a ha, rfl⟩)

structure EtaFactor (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (f : VExpr)
    (lambdaKey : Key n) (output : Atom n) (outside : Footprint) where
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  rawOutput : Atom rank
  function : Obs env U registry Γ locals σ f (Profile.fn key rawOutput) outside
  admitted : Admitted env U registry Γ key lambdaKey.anchor lambdaKey.anchor
  arguments : NormalProfileAdapter env U registry Γ
    (raiseProfile rank bound lambdaKey.input) key.input
  resultView : AtomView env U registry Γ rawOutput (raiseAtom rank bound output)
  result : NormalAtomAdapter env U registry Γ rawOutput (raiseAtom rank bound output)

theorem Obs.eta_factor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    {lambdaKey : Key n} {output : Atom n} {packed : Profile n}
    (body : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ lambdaKey.input.atoms) :
    Nonempty (EtaFactor env U registry Γ locals σ f lambdaKey output outside) := by
  obtain ⟨origin, ⟨path⟩, hbody⟩ := body.application_factor output rfl
  obtain ⟨required, ⟨reflected⟩, hrequired⟩ :=
    origin.function.reflectSource (.skip .refl) lift_eq_lift' locals
  change Obs env U registry Γ locals σ f (Profile.fn origin.key origin.output) required at reflected
  rw [hbody, hrequired] at pack
  let argument := origin.argument.variableTrace
  obtain ⟨hinput, hbounds, houtside⟩ := pack.etaFootprint argument
  let N := max path.height argument.height
  have hp : path.height ≤ N := Nat.le_max_left _ _
  have ha : argument.height ≤ N := Nat.le_max_right _ _
  have hn : n ≤ N := Nat.le_trans path.bounds.2 hp
  have hr : origin.rank ≤ N := Nat.le_trans path.bounds.1 hp
  have lifted := reflected.raise (Nat.succ_le_succ hr)
  simp only [Profile.fn, raiseProfile_singleton] at lifted
  have exposed := Obs.view lifted (functionGradeView hr origin.key origin.output)
  have variableAdapter := (argument.normalize N ha).toAdapter henv hscoped hΓ
  have selected : NormalProfileAdapter env U registry Γ
      (raiseProfile N hn lambdaKey.input) (origin.argumentFootprint.atGrade N) := by
    rw [Footprint.atGrade_raise hn hbounds, ← hinput]
    exact normalSelect (raiseProfile_subset hn covered)
  have argumentAdapter := NormalProfileAdapter.raise henv hscoped hΓ hr origin.arguments
  have arguments := NormalProfileAdapter.comp selected
    (NormalProfileAdapter.comp variableAdapter argumentAdapter)
  exact ⟨{
    rank := N
    bound := hn
    key := raiseKey N hr origin.key
    rawOutput := raiseAtom N hr origin.output
    function := by simpa only [Profile.fn, raiseProfile_singleton, houtside] using exposed
    admitted := Admitted.raise henv hr origin.admitted
    arguments := arguments
    resultView := path.normalize N hp
    result := (path.normalize N hp).toAdapter henv hscoped hΓ }⟩

end Lean4Lean.AnchoredSource.Adapted
