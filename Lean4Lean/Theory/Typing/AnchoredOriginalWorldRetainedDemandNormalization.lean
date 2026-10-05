import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandHead

/-! An exact syntactic derivation of demand-head normalization. Unlike operand
readback alone, it retains every selected key, continuation and output path. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private levelsTrans levelsRightSelf levelsUnliftSelf
  RetainedApplicationDemandHead.output RetainedApplicationDemandHead.rename
  RetainedApplicationDemandHead.output_readback RetainedApplicationDemandHead.rename_readback
  from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandHead
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedDemandHeadNormalization (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (goalFunction goalArgument : VExpr) {goalRank : Nat} (goalOutput : Atom goalRank) :
    {expression : VExpr} → {n : Nat} → {atom : Atom n} →
    RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom →
    RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom → Type where
  | application (functionSelf : EqUpToLevels U goalFunction goalFunction)
      (argumentSelf : EqUpToLevels U goalArgument goalArgument) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        .application (.application .refl (by simpa using functionSelf) (by simpa using argumentSelf) .refl)
  | output (path : GeneralOutputPath env U registry target old next)
      (prior : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput demand head) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (.output path demand) (RetainedApplicationDemandHead.output path head)
  | domain {support : Profile n} {rows : List (Key n × Profile n)}
      (member : atom ∈ support.atoms)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (.domain (B := B) (rows := rows) (prototypeDomain := prototypeDomain) (prototypeBody := prototypeBody) member continuation)
        (.domain .refl member continuation)
  | body {support result : Profile n} {rows : List (Key n × Profile n)}
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (.body (A := A) (support := support) (prototypeDomain := prototypeDomain) (prototypeBody := prototypeBody)
          selected member anchor admitted continuation)
        (.body .refl selected member anchor admitted continuation)
  | levelsApplication (functionEq : EqUpToLevels U sourceFunction function)
      (argumentEq : EqUpToLevels U sourceArgument argument)
      (functionLevels : EqUpToLevels U function (goalFunction.lift' ρ))
      (argumentLevels : EqUpToLevels U argument (goalArgument.lift' ρ))
      (path : GeneralOutputPath env U registry target atom goalOutput)
      (prior : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        demand (.application ρ functionLevels argumentLevels path)) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (.levels (.app functionEq argumentEq) demand)
        (.application ρ (levelsTrans functionEq functionLevels) (levelsTrans argumentEq argumentLevels) path)
  | levelsDomain {support : Profile n} {rows : List (Key n × Profile n)}
      (domainEq : EqUpToLevels U sourceDomain A) (bodyEq : EqUpToLevels U sourceBody B)
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (member : atom ∈ support.atoms)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom)
      (prior : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        demand (.domain (B := B) path member continuation)) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (.levels (.forallE domainEq bodyEq) demand) (.domain path member (.levels domainEq continuation))
  | levelsBody {support result : Profile n} {rows : List (Key n × Profile n)}
      (domainEq : EqUpToLevels U sourceDomain A) (bodyEq : EqUpToLevels U sourceBody B)
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
      (prior : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        demand (.body (A := A) path selected member anchor admitted continuation)) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (.levels (.forallE domainEq bodyEq) demand)
        (.body path selected member anchor admitted (.levels bodyEq continuation))
  | rename (ρ : Lift)
      (prior : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput demand head) :
      RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (.rename ρ demand) (RetainedApplicationDemandHead.rename ρ head)

theorem RetainedApplicationDemand.headNormalized
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (self : EqUpToLevels U expression expression) :
    ∃ head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom,
      Nonempty (RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput demand head) ∧
      ∀ τ, head.readback τ = demand.readback τ := by
  induction demand with
  | application =>
    cases self with
    | app function argument => exact ⟨_, ⟨.application function argument⟩, fun _ => rfl⟩
  | output path continuation ih =>
    obtain ⟨head, ⟨prior⟩, same⟩ := ih self
    exact ⟨RetainedApplicationDemandHead.output path head, ⟨.output path prior⟩, fun τ => (RetainedApplicationDemandHead.output_readback path head τ).trans (same τ)⟩
  | domain member continuation ih => exact ⟨_, ⟨.domain member continuation⟩, fun _ => rfl⟩
  | body selected member anchor admitted continuation ih =>
    exact ⟨_, ⟨.body selected member anchor admitted continuation⟩, fun _ => rfl⟩
  | levels equal continuation ih =>
    obtain ⟨head, ⟨prior⟩, same⟩ := ih (levelsRightSelf equal)
    cases head with
    | application ρ functionLevels argumentLevels path =>
      cases equal with
      | app f a => exact ⟨_, ⟨.levelsApplication f a functionLevels argumentLevels path prior⟩, same⟩
    | domain path member nextContinuation =>
      cases equal with
      | forallE domain body => exact ⟨_, ⟨.levelsDomain domain body path member nextContinuation prior⟩, same⟩
    | body path selected member anchor admitted nextContinuation =>
      cases equal with
      | forallE domain body => exact ⟨_, ⟨.levelsBody domain body path selected member anchor admitted nextContinuation prior⟩, same⟩
  | rename ρ continuation ih =>
    obtain ⟨head, ⟨prior⟩, same⟩ := ih (levelsUnliftSelf self)
    exact ⟨RetainedApplicationDemandHead.rename ρ head, ⟨.rename ρ prior⟩, fun τ => (RetainedApplicationDemandHead.rename_readback ρ head τ).trans (same _)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
