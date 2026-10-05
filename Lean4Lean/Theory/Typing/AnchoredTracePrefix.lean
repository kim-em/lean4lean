import Lean4Lean.Theory.Typing.AnchoredSemantics

/-! Prepend an actual native trace and its inhabited proof frame to an
existing type exposure. The frame is reused literally; this operation never
reruns the native allocator inside the already extended context. -/

namespace Lean4Lean.CanonicalDataHead

theorem Trace.trans
    (first : Trace registry expression front middle)
    (second : Trace registry middle suffix result) :
    Trace registry expression (suffix ++ front) result := by
  induction first with
  | refl => simpa only [List.append_nil] using second
  | next step tail ih =>
    simpa only [List.append_assoc] using Trace.next step (ih second)

end Lean4Lean.CanonicalDataHead

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def Exposure.prependTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ front : List VExpr} {expression middle head : VExpr} {ρ : Lift}
    (henv : env.Ordered)
    (trace : CanonicalDataHead.Trace registry expression front middle)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (path : TypeConversion env U (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) middle)
    (exposure : Exposure env U registry (front ++ Γ) middle Δ ρ head) :
    Exposure env U registry Γ expression Δ
      ((Lift.skipN .refl front.length).comp ρ) head where
  added := exposure.added ++ front
  result := exposure.result
  postMap := exposure.postMap
  trace := trace.trans exposure.trace
  generated := by
    simpa only [List.append_assoc, List.length_append, Lift.comp_skipN,
      Lift.comp, Lift.skipN_skipN, Nat.add_comm] using
      generated.comp exposure.generated henv
  postContext := exposure.postContext
  post := by simpa only [List.append_assoc] using exposure.post
  terminal := exposure.terminal
  map_eq := by
    simpa only [← Lift.comp_assoc, List.length_append, Lift.comp_skipN,
      Lift.comp, Lift.skipN_skipN, Nat.add_comm] using
      congrArg ((Lift.skipN .refl front.length).comp ·) exposure.map_eq
  result_eq := exposure.result_eq
  sound := by
    simpa only [lift'_comp] using
      ((exposure.insertion henv).path henv path).trans exposure.sound
  headType := exposure.headType

theorem SortRelated.prependTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ front : List VExpr} {left right leftResult rightResult : VExpr} {relevant : Bool}
    (henv : env.Ordered)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (rightTrace : CanonicalDataHead.Trace registry right front rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (rightPath : TypeConversion env U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult)
    (related : SortRelated env U registry (front ++ Γ) leftResult rightResult relevant) :
    SortRelated env U registry Γ left right relevant := by
  obtain ⟨Δ, ρ, u, v, ⟨leftExposure⟩, ⟨rightExposure⟩, levels, flag⟩ := related
  exact ⟨Δ, (Lift.skipN .refl front.length).comp ρ, u, v,
    ⟨leftExposure.prependTrace henv leftTrace generated leftPath⟩,
    ⟨rightExposure.prependTrace henv rightTrace generated rightPath⟩, levels, flag⟩

/-- Keep the chosen Pi display and all future row obligations unchanged.
Only the source traces and their composite map acquire the native prefix. -/
def PiWitness.prependTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ front : List VExpr}
    {left right leftResult rightResult A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (rightTrace : CanonicalDataHead.Trace registry right front rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (rightPath : TypeConversion env U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult)
    (display : PiWitness env U registry lower (front ++ Γ) leftResult rightResult
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
  rightExposure := display.rightExposure.prependTrace henv rightTrace generated rightPath
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

/-- Prefixing a family CODE display retains its exposed universe witnesses.
The incoming raw chains are concatenated at the private display context. -/
def RankedData.FamilyWitness.prependTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {lower : Relations n} {Γ front : List VExpr}
    {left right leftResult rightResult : VExpr} {demand : FamilyData (Profile n)}
    (henv : env.Ordered)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (rightTrace : CanonicalDataHead.Trace registry right front rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (rightPath : TypeConversion env U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult)
    (display : RankedData.FamilyWitness env U registry lower (front ++ Γ)
      leftResult rightResult (demand.rename (.skipN .refl front.length))) :
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
    have after := (display.rightExposure.insertion henv).path henv rightPath
    simpa only [lift'_comp] using (before.trans display.path).trans after.symm
  leftLevels := display.leftLevels
  rightLevels := display.rightLevels
  leftArguments := display.leftArguments
  rightArguments := display.rightArguments
  leftType := display.leftType
  rightType := display.rightType
  leftExposure := display.leftExposure.prependTrace henv leftTrace generated leftPath
  rightExposure := display.rightExposure.prependTrace henv rightTrace generated rightPath
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

end Lean4Lean.AnchoredSemantics
