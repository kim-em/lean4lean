import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandHead

/-! One head-normalization algorithm for literal application and projection
term goals. The terminal retains its exact renaming, universe correspondence
and selected output path; domain/body continuations retain actual keys. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private levelsTrans levelsRightSelf levelsUnliftSelf from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandHead
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedTermDemandHead (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (goal : VExpr) {goalRank : Nat} (goalOutput : Atom goalRank) : VExpr → {n : Nat} → Atom n → Type where
  | terminal (ρ : Lift)
      (levels : EqUpToLevels U expression (goal.lift' ρ))
      (path : GeneralOutputPath env U registry target atom goalOutput) :
      RetainedTermDemandHead env U registry target goal goalOutput expression atom
  | domain {support : Profile n} {rows : List (Key n × Profile n)}
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (member : atom ∈ support.atoms)
      (continuation : RetainedTermDemand env U registry target goal goalOutput A atom) :
      RetainedTermDemandHead env U registry target goal goalOutput (.forallE A B) input
  | body {support result : Profile n} {rows : List (Key n × Profile n)}
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedTermDemand env U registry target goal goalOutput B atom) :
      RetainedTermDemandHead env U registry target goal goalOutput (.forallE A B) input

noncomputable def RetainedTermDemandHead.readback
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression atom)
    (τ : Subst) : VExpr := by
  cases head with
  | terminal ρ _ _ => exact goal.subst (Subst.lift_l ρ τ)
  | domain _ _ continuation => exact continuation.readback τ
  | body _ _ _ anchor _ continuation => exact continuation.readback (τ.cons anchor)

private noncomputable def appendPath
    (first : GeneralOutputPath env U registry target a b)
    (second : GeneralOutputPath env U registry target b c) :
    GeneralOutputPath env U registry target a c := by
  induction second with
  | refl => exact first
  | action path change ih => exact .action ih change
  | code path change formed ih => exact .code ih change formed
  | pad path ih => exact .pad ih
  | unpad path ih => exact .unpad ih

private noncomputable def RetainedTermDemandHead.output
    (path : GeneralOutputPath env U registry target old next)
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression next) :
    RetainedTermDemandHead env U registry target goal goalOutput expression old := by
  cases head with
  | terminal ρ levels tail =>
    exact .terminal ρ levels (appendPath path tail)
  | domain tail member continuation => exact .domain (appendPath path tail) member continuation
  | body tail selected member anchor admitted continuation =>
    exact .body (appendPath path tail) selected member anchor admitted continuation

private theorem RetainedTermDemandHead.levels
    (equal : EqUpToLevels U sourceExpression expression)
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression atom) :
    Nonempty (RetainedTermDemandHead env U registry target goal goalOutput sourceExpression atom) := by
  cases head with
  | terminal ρ levels path =>
    exact ⟨.terminal ρ (levelsTrans equal levels) path⟩
  | domain path member continuation =>
    cases equal with
    | forallE domain body => exact ⟨.domain path member (.levels domain continuation)⟩
  | body path selected member anchor admitted continuation =>
    cases equal with
    | forallE domain body => exact ⟨.body path selected member anchor admitted (.levels body continuation)⟩

private noncomputable def RetainedTermDemandHead.rename
    (ρ : Lift)
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression atom) :
    RetainedTermDemandHead env U registry target goal goalOutput (expression.lift' ρ) atom := by
  cases head with
  | terminal previous levels path =>
    exact .terminal (previous.comp ρ)
      (by simpa only [lift'_comp] using levels.lift' ρ) path
  | domain path member continuation => exact .domain path member (.rename ρ continuation)
  | body path selected member anchor admitted continuation =>
    exact .body path selected member anchor admitted (.rename ρ.cons continuation)

private theorem RetainedTermDemandHead.output_readback
    (path : GeneralOutputPath env U registry target old next)
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression next)
    (τ : Subst) : (head.output path).readback τ = head.readback τ := by
  cases head <;> rfl

private theorem RetainedTermDemandHead.rename_readback
    (ρ : Lift)
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression atom)
    (τ : Subst) : (head.rename ρ).readback τ = head.readback (Subst.lift_l ρ τ) := by
  cases head with
  | terminal previous levels path =>
    have pull : Subst.lift_l (previous.comp ρ) τ = Subst.lift_l previous (Subst.lift_l ρ τ) := by
      funext i
      simp only [Subst.lift_l, Lift.liftVar_comp]
    change goal.subst _ = goal.subst _
    rw [pull]
  | domain path member continuation => rfl
  | body path selected member anchor admitted continuation =>
    have pull : Subst.lift_l ρ.cons (τ.cons anchor) = (Subst.lift_l ρ τ).cons anchor := by
      funext i
      cases i <;> rfl
    change continuation.readback _ = continuation.readback _
    rw [pull]

private theorem RetainedTermDemandHead.levelsReadback
    (equal : EqUpToLevels U sourceExpression expression)
    (head : RetainedTermDemandHead env U registry target goal goalOutput expression atom) :
    ∃ next : RetainedTermDemandHead env U registry target goal goalOutput sourceExpression atom,
      ∀ τ, next.readback τ = head.readback τ := by
  cases head with
  | terminal ρ levels path =>
    exact ⟨.terminal ρ (levelsTrans equal levels) path, fun _ => rfl⟩
  | domain path member continuation =>
    cases equal with
    | forallE domain body => exact ⟨.domain path member (.levels domain continuation), fun _ => rfl⟩
  | body path selected member anchor admitted continuation =>
    cases equal with
    | forallE domain body => exact ⟨.body path selected member anchor admitted (.levels body continuation), fun _ => rfl⟩

/-- Head normalization preserves the exact final operands for every current
resource substitution. Its terminal renaming can therefore be read back in
the caller after composing the actual program transitions. -/
theorem RetainedTermDemand.headReadback
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (self : EqUpToLevels U expression expression) :
    ∃ head : RetainedTermDemandHead env U registry target goal goalOutput expression atom,
      ∀ τ, head.readback τ = demand.readback τ := by
  induction demand with
  | terminal =>
    exact ⟨.terminal .refl (by simpa using self) .refl, fun _ => rfl⟩
  | output path continuation ih =>
    obtain ⟨head, same⟩ := ih self
    exact ⟨head.output path, fun τ => (head.output_readback path τ).trans (same τ)⟩
  | domain member continuation ih => exact ⟨.domain .refl member continuation, fun _ => rfl⟩
  | body selected member anchor admitted continuation ih =>
    exact ⟨.body .refl selected member anchor admitted continuation, fun _ => rfl⟩
  | levels equal continuation ih =>
    obtain ⟨head, same⟩ := ih (levelsRightSelf equal)
    obtain ⟨next, changed⟩ := head.levelsReadback equal
    exact ⟨next, fun τ => (changed τ).trans (same τ)⟩
  | rename ρ continuation ih =>
    obtain ⟨head, same⟩ := ih (levelsUnliftSelf self)
    exact ⟨head.rename ρ, fun τ => (head.rename_readback ρ τ).trans (same _)⟩

/-- The next instruction is derived from concrete syntax. The self-equality
premise is available from the actual original typing; bare demand syntax does
not assert that arbitrary universe levels are well formed. -/
theorem RetainedTermDemand.head
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (self : EqUpToLevels U expression expression) :
    Nonempty (RetainedTermDemandHead env U registry target goal goalOutput expression atom) := by
  induction demand with
  | terminal => exact ⟨.terminal .refl (by simpa using self) .refl⟩
  | output path continuation ih =>
    obtain ⟨head⟩ := ih self
    exact ⟨head.output path⟩
  | domain member continuation ih => exact ⟨.domain .refl member continuation⟩
  | body selected member anchor admitted continuation ih => exact ⟨.body .refl selected member anchor admitted continuation⟩
  | levels equal continuation ih =>
    obtain ⟨head⟩ := ih (levelsRightSelf equal)
    exact head.levels equal
  | rename ρ continuation ih =>
    obtain ⟨head⟩ := ih (levelsUnliftSelf self)
    exact ⟨head.rename ρ⟩


inductive RetainedTermHeadNormalization (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (goal : VExpr) {goalRank : Nat} (goalOutput : Atom goalRank) :
    {expression : VExpr} → {n : Nat} → {atom : Atom n} →
    RetainedTermDemand env U registry target goal goalOutput expression atom →
    RetainedTermDemandHead env U registry target goal goalOutput expression atom → Type where
  | terminal (self : EqUpToLevels U goal goal) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        .terminal (.terminal .refl (by simpa using self) .refl)
  | output (path : GeneralOutputPath env U registry target old next)
      (prior : RetainedTermHeadNormalization env U registry target goal goalOutput demand head) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        (.output path demand) (RetainedTermDemandHead.output path head)
  | domain {support : Profile n} {rows : List (Key n × Profile n)}
      (member : atom ∈ support.atoms)
      (continuation : RetainedTermDemand env U registry target goal goalOutput A atom) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        (.domain (B := B) (rows := rows) (prototypeDomain := prototypeDomain) (prototypeBody := prototypeBody) member continuation)
        (.domain .refl member continuation)
  | body {support result : Profile n} {rows : List (Key n × Profile n)}
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedTermDemand env U registry target goal goalOutput B atom) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        (.body (A := A) (support := support) (prototypeDomain := prototypeDomain) (prototypeBody := prototypeBody)
          selected member anchor admitted continuation)
        (.body .refl selected member anchor admitted continuation)
  | levelsTerminal (equal : EqUpToLevels U sourceExpression expression)
      (terminalLevels : EqUpToLevels U expression (goal.lift' ρ))
      (path : GeneralOutputPath env U registry target atom goalOutput)
      (prior : RetainedTermHeadNormalization env U registry target goal goalOutput
        demand (.terminal ρ terminalLevels path)) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        (.levels equal demand)
        (.terminal ρ (levelsTrans equal terminalLevels) path)
  | levelsDomain {support : Profile n} {rows : List (Key n × Profile n)}
      (domainEq : EqUpToLevels U sourceDomain A) (bodyEq : EqUpToLevels U sourceBody B)
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (member : atom ∈ support.atoms)
      (continuation : RetainedTermDemand env U registry target goal goalOutput A atom)
      (prior : RetainedTermHeadNormalization env U registry target goal goalOutput
        demand (.domain (B := B) path member continuation)) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        (.levels (.forallE domainEq bodyEq) demand) (.domain path member (.levels domainEq continuation))
  | levelsBody {support result : Profile n} {rows : List (Key n × Profile n)}
      (domainEq : EqUpToLevels U sourceDomain A) (bodyEq : EqUpToLevels U sourceBody B)
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedTermDemand env U registry target goal goalOutput B atom)
      (prior : RetainedTermHeadNormalization env U registry target goal goalOutput
        demand (.body (A := A) path selected member anchor admitted continuation)) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        (.levels (.forallE domainEq bodyEq) demand)
        (.body path selected member anchor admitted (.levels bodyEq continuation))
  | rename (ρ : Lift)
      (prior : RetainedTermHeadNormalization env U registry target goal goalOutput demand head) :
      RetainedTermHeadNormalization env U registry target goal goalOutput
        (.rename ρ demand) (RetainedTermDemandHead.rename ρ head)

theorem RetainedTermDemand.headNormalized
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (self : EqUpToLevels U expression expression) :
    ∃ head : RetainedTermDemandHead env U registry target goal goalOutput expression atom,
      Nonempty (RetainedTermHeadNormalization env U registry target goal goalOutput demand head) ∧
      ∀ τ, head.readback τ = demand.readback τ := by
  induction demand with
  | terminal => exact ⟨_, ⟨.terminal self⟩, fun _ => rfl⟩
  | output path continuation ih =>
    obtain ⟨head, ⟨prior⟩, same⟩ := ih self
    exact ⟨RetainedTermDemandHead.output path head, ⟨.output path prior⟩, fun τ => (RetainedTermDemandHead.output_readback path head τ).trans (same τ)⟩
  | domain member continuation ih => exact ⟨_, ⟨.domain member continuation⟩, fun _ => rfl⟩
  | body selected member anchor admitted continuation ih =>
    exact ⟨_, ⟨.body selected member anchor admitted continuation⟩, fun _ => rfl⟩
  | levels equal continuation ih =>
    obtain ⟨head, ⟨prior⟩, same⟩ := ih (levelsRightSelf equal)
    cases head with
    | terminal ρ terminalLevels path =>
      exact ⟨_, ⟨.levelsTerminal equal terminalLevels path prior⟩, same⟩
    | domain path member nextContinuation =>
      cases equal with
      | forallE domain body => exact ⟨_, ⟨.levelsDomain domain body path member nextContinuation prior⟩, same⟩
    | body path selected member anchor admitted nextContinuation =>
      cases equal with
      | forallE domain body => exact ⟨_, ⟨.levelsBody domain body path selected member anchor admitted nextContinuation prior⟩, same⟩
  | rename ρ continuation ih =>
    obtain ⟨head, ⟨prior⟩, same⟩ := ih (levelsUnliftSelf self)
    exact ⟨RetainedTermDemandHead.rename ρ head, ⟨.rename ρ prior⟩, fun τ => (RetainedTermDemandHead.rename_readback ρ head τ).trans (same _)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
