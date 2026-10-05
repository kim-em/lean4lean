import Lean4Lean.Theory.Typing.AnchoredTraceCode
import Lean4Lean.Theory.Typing.AnchoredExposureAbsorption
import Batteries.Tactic.OpenPrivate

/-! Expand one endpoint through its actual native proof frame. The other
endpoint is lifted from the base and its exposure absorbs that frame. Paired
applications may therefore allocate different proof telescopes. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false
open private frontMap path_future from Lean4Lean.Theory.Typing.AnchoredTraceCode

theorem SortRelated.prependLeftTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ front : List VExpr} {left right leftResult : VExpr} {relevant : Bool}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (related : SortRelated env U registry (front ++ Γ) leftResult
      (right.lift' (.skipN .refl front.length)) relevant) :
    SortRelated env U registry Γ left right relevant := by
  obtain ⟨Δ, ρ, u, v, ⟨leftExposure⟩, ⟨rightExposure⟩, levels, flag⟩ := related
  exact ⟨Δ, (Lift.skipN .refl front.length).comp ρ, u, v,
    ⟨leftExposure.prependTrace henv leftTrace generated leftPath⟩,
    rightExposure.absorb henv hscoped generated, levels, flag⟩

noncomputable def PiWitness.prependLeftTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ front : List VExpr}
    {left right leftResult A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (display : PiWitness env U registry lower (front ++ Γ) leftResult (right.lift' (.skipN .refl front.length))
      (A.lift' (.skipN .refl front.length)) (B.lift' (Lift.skipN .refl front.length).cons)
      (domain.rename (.skipN .refl front.length)) (Rows.rename (.skipN .refl front.length) rows)) :
    PiWitness env U registry lower Γ left right A B domain rows where
  context := display.context
  map := (Lift.skipN .refl front.length).comp display.map
  leftDomain := display.leftDomain
  leftBody := display.leftBody
  rightDomain := display.rightDomain
  rightBody := display.rightBody
  leftExposure := display.leftExposure.prependTrace henv leftTrace generated leftPath
  rightExposure := Classical.choice (display.rightExposure.absorb henv hscoped generated)
  leftDomainType := display.leftDomainType
  rightDomainType := display.rightDomainType
  leftBodyType := display.leftBodyType
  rightBodyType := display.rightBodyType
  domains := display.domains
  bodies := display.bodies
  prototypeDomainPath := by simpa only [lift'_comp] using display.prototypeDomainPath
  prototypeBodyPath := by
    simpa only [show ((Lift.skipN .refl front.length).comp display.map).cons =
      (Lift.skipN .refl front.length).cons.comp display.map.cons from rfl,
      lift'_comp] using display.prototypeBodyPath
  domainRelated := by simpa only [Profile.rename_comp] using display.domainRelated
  rowDomains := by
    intro key output member
    have result := display.rowDomains (key.rename (.skipN .refl front.length))
      (output.rename (.skipN .refl front.length))
      (List.mem_map.mpr ⟨(key, output), member, rfl⟩)
    simpa only [Key.rename_comp, Profile.rename_comp, Key.rename, ← lift'_comp] using result
  rowBodies := by
    intro key output member Δ ρ future x y admitted
    have result := display.rowBodies (key.rename (.skipN .refl front.length))
      (output.rename (.skipN .refl front.length))
      (List.mem_map.mpr ⟨(key, output), member, rfl⟩) Δ ρ future x y
    have admitted' : Admission env U lower Δ
        ((key.rename (.skipN .refl front.length)).rename (display.map.comp ρ)) x y := by
      simpa only [Key.rename_comp, Lift.comp_assoc] using admitted
    simpa only [Profile.rename_comp, Lift.comp_assoc] using result admitted'

noncomputable def RankedData.FamilyWitness.prependLeftTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ front : List VExpr}
    {left right leftResult : VExpr} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (display : RankedData.FamilyWitness env U registry lower (front ++ Γ)
      leftResult (right.lift' (.skipN .refl front.length)) (demand.rename (.skipN .refl front.length))) :
    RankedData.FamilyWitness env U registry lower Γ left right demand where
  registryScoped := display.registryScoped
  headInert := display.headInert
  context := display.context
  map := (Lift.skipN .refl front.length).comp display.map
  leftLevel := display.leftLevel
  rightLevel := display.rightLevel
  leftRelevance := display.leftRelevance
  rightRelevance := display.rightRelevance
  path := by
    have before := (display.leftExposure.insertion henv).path henv leftPath
    simpa only [lift'_comp] using before.trans display.path
  leftLevels := display.leftLevels
  rightLevels := display.rightLevels
  leftArguments := display.leftArguments
  rightArguments := display.rightArguments
  leftType := display.leftType
  rightType := display.rightType
  leftExposure := display.leftExposure.prependTrace henv leftTrace generated leftPath
  rightExposure := Classical.choice (display.rightExposure.absorb henv hscoped generated)
  leftTerminal := display.leftTerminal
  rightTerminal := display.rightTerminal
  leftUniverses := display.leftUniverses
  rightUniverses := display.rightUniverses
  arguments := by
    have arguments := display.arguments
    change RankedData.Arguments env U lower display.context
      ((demand.arguments.map (DataRequest.rename (.skipN .refl front.length))).map (DataRequest.rename display.map))
      display.leftArguments display.rightArguments at arguments
    simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp] using arguments

theorem TypeRelated.prependLeftTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ front : List VExpr} {left right leftResult : VExpr}
    {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (related : TypeRelated env U registry (front ++ Γ) leftResult (right.lift' (.skipN .refl front.length))
      (profile.rename (.skipN .refl front.length))) :
    TypeRelated env U registry Γ left right profile := by
  induction n generalizing Γ front left right leftResult with
  | zero =>
    intro Δ ρ future atom member
    obtain ⟨newGenerated, extended⟩ := generated.renameFront front future henv
    have leftPath' := path_future henv leftPath extended
    have result := related _ _ extended
    rw [← Profile.rename_comp, frontMap, Profile.rename_comp, ← lift'_comp, frontMap, lift'_comp] at result
    have member' : atom ∈ ((profile.rename ρ).rename
        (.skipN .refl (renameAdded ρ front).length)).atoms := by
      simpa [Profile.rename, Profile.atoms, Atom.rename] using member
    exact SortRelated.prependLeftTrace henv hscoped (leftTrace.rename hscoped ρ)
      (by simpa only [renameAdded_length] using newGenerated)
      leftPath' (result atom member')
  | succ n ih =>
    intro Δ ρ future atom member
    obtain ⟨newGenerated, extended⟩ := generated.renameFront front future henv
    have leftPath' := path_future henv leftPath extended
    have result := related _ _ extended
    rw [← Profile.rename_comp, frontMap, Profile.rename_comp, ← lift'_comp, frontMap, lift'_comp] at result
    have member' : atom.rename (.skipN .refl (renameAdded ρ front).length) ∈
        ((profile.rename ρ).rename (.skipN .refl (renameAdded ρ front).length)).atoms :=
      List.mem_map.mpr ⟨atom, member, rfl⟩
    have value := result _ member'
    have generated' : ProofInsertion env U Δ (renameAdded ρ front ++ Δ)
        (.skipN .refl (renameAdded ρ front).length) := by
      simpa only [renameAdded_length] using newGenerated
    cases atom with
    | sort flag =>
      exact SortRelated.prependLeftTrace henv hscoped (leftTrace.rename hscoped ρ)
        generated' leftPath' value
    | fn | ctor | record => exact value.elim
    | family demand =>
      obtain ⟨display⟩ := value
      exact ⟨display.prependLeftTrace henv hscoped (leftTrace.rename hscoped ρ)
        generated' leftPath'⟩
    | pi A B domain rows =>
      obtain ⟨display⟩ := value
      exact ⟨display.prependLeftTrace henv hscoped (leftTrace.rename hscoped ρ)
        generated' leftPath'⟩
    | pad atom =>
      change TypeRelated env U registry (renameAdded ρ front ++ Δ)
        (leftResult.lift' (ρ.consN front.length)) ((right.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
        (.singleton (atom.rename (.skipN .refl (renameAdded ρ front).length))) at value
      rw [← Profile.rename_singleton] at value
      exact ih (leftTrace.rename hscoped ρ)
        generated' leftPath' value

end Lean4Lean.AnchoredSemantics
