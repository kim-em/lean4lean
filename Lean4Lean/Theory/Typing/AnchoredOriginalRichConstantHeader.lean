import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay

/-! The primitive constant's assigned formation and its retained earlier
header have the same closed source expression. Their reindex call is charged
to the actual constant rule, before any declaration-domain query is selected.
This is a fixed original expression-R edge, not assigned-type uniqueness. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The earlier original header has an actual weakening display into the
current source context. Closedness follows from the installed declaration. -/
noncomputable def selectedHeaderDisplay
    {sourceEnv : VEnv} {name : Name} {info : VConstant} {levels : List VLevel} {U : Nat}
    (ordered : sourceEnv.Ordered) (lookup : sourceEnv.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (source : List VExpr) :
    EndpointDisplay (selectOriginalHeader ordered lookup levelsWF).source U source
      (info.type.instL levels) (.sort (selectOriginalHeader ordered lookup levelsWF).level) where
  source := []
  sourceExpression := info.type.instL levels
  sourceType := .sort (selectOriginalHeader ordered lookup levelsWF).level
  context := .nil
  node := .ref (.left (selectOriginalHeader ordered lookup levelsWF).original)
  provenance := .ofLocation .here .nil
  map := .skipN .refl source.length
  insertion := by simpa only [List.append_nil, Lift.consN] using Ctx.liftN_iff_lift'.mp (Ctx.LiftN.zero (Γ := []) source)
  expression_eq := ((ordered.closedC lookup).instL.lift'_eq .zero).symm
  type_eq := rfl

 theorem constantHeader_pair_lt
    (ordered : sourceEnv.Ordered)
    (lookup : sourceEnv.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (otherWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation sourceEnv U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (environment : List Closure) :
    (Closure.close (ambient.dependencyOrigin ordered) environment).cost +
      (Closure.close ((selectOriginalHeader ordered lookup levelsWF).original.dependencyOrigin
        (selectOriginalHeader ordered lookup levelsWF).ordered) []).cost <
    (Closure.close ((Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
      environment).cost := by
  let h := (selectOriginalHeader ordered lookup levelsWF).original.dependencyOrigin
    (selectOriginalHeader ordered lookup levelsWF).ordered
  have small : (ambient.dependencyOrigin ordered).weight + h.weight <
      ((Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient).dependencyOrigin
        ordered).weight := by
    rw [Derivation.dependencyOrigin.eq_def ordered
      (Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient)]
    simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    dsimp only [h]
    omega
  have pair := Nat.mul_lt_mul_of_pos_right small
    (show 0 < 1 + environmentCost environment by omega)
  have headerBound := Nat.mul_le_mul_left h.weight
    (show 1 ≤ 1 + environmentCost environment by omega)
  simp only [Nat.mul_one] at headerBound
  simp only [Nat.add_mul] at pair
  change (ambient.dependencyOrigin ordered).weight * (1 + environmentCost environment) +
    h.weight * (1 + environmentCost []) < _
  simpa only [environmentCost, Nat.add_zero, Nat.mul_one, Closure.cost, Derivation.dependencyOrigin, h] using
    Nat.lt_of_le_of_lt (Nat.add_le_add_left headerBound
      ((ambient.dependencyOrigin ordered).weight * (1 + environmentCost environment))) pair

/-- At the primitive constant boundary the rich query is sent to one fixed
original earlier header. The source expression equality is literal (including
its universe instance); the destination has no source capture slots. -/
theorem replayConstantHeader
    (ordered : sourceEnv.Ordered)
    (lookup : sourceEnv.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (otherWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation sourceEnv U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (environment : List Closure)
    (certificate : RichCert sourceEnv env U registry target (.ref (.left ambient)) locals σ relevant profile footprint)
    (resources : footprint.Available available)
    (reindex : richSchedule .expressionReindex
      ((Closure.close (ambient.dependencyOrigin ordered) environment).cost +
       (Closure.close ((selectOriginalHeader ordered lookup levelsWF).original.dependencyOrigin
         (selectOriginalHeader ordered lookup levelsWF).ordered) []).cost) <
      richSchedule .fundamental
        (Closure.close ((Derivation.constDF lookup levelsWF otherWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
          environment).cost →
      RichCodeTransfer env U registry target (.ref (.left ambient))
        (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
        locals [] σ headerRealization available (fun _ => [])) :
    Nonempty (RichCodeTransferResult env U registry target (.ref (.left ambient))
      (.ref (.left (selectOriginalHeader ordered lookup levelsWF).original))
      [] σ headerRealization (fun _ => []) relevant profile) := by
  exact reindex (richSchedule_strict
    (constantHeader_pair_lt ordered lookup levelsWF otherWF count equivalent levelWF closed ambient environment) _ _)
    certificate resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
