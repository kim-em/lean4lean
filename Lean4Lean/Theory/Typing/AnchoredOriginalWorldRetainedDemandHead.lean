import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback
import Lean4Lean.Theory.Typing.AnchoredExposureLevels

/-! Normalize the next finite demand instruction by raw syntax. Universe
changes and binder renamings are pushed to the actual domain/body continuation.
Application leaves retain one concrete renaming and both operand level proofs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem listLevelsTrans
    {left middle right : List VLevel}
    (first : List.Forall₂ (· ≈ ·) left middle)
    (second : List.Forall₂ (· ≈ ·) middle right) :
    List.Forall₂ (· ≈ ·) left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons next rest => exact .cons (head.trans next) (ih rest)

private theorem levelsTrans (first : EqUpToLevels U a b) (second : EqUpToLevels U b c) :
    EqUpToLevels U a c := by
  induction first generalizing c with
  | bvar => cases second; exact .bvar
  | const left _ levels =>
    cases second with
    | const _ right next => exact .const left right (listLevelsTrans levels next)
  | elim left _ levels =>
    cases second with
    | elim _ right next => exact .elim left right (listLevelsTrans levels next)
  | sort left _ levels =>
    cases second with
    | sort _ right next => exact .sort left right (levels.trans next)
  | app _ _ function argument =>
    cases second with
    | app nextFunction nextArgument => exact .app (function nextFunction) (argument nextArgument)
  | proj _ major =>
    cases second with
    | proj next => exact .proj (major next)
  | lam _ _ domain body =>
    cases second with
    | lam nextDomain nextBody => exact .lam (domain nextDomain) (body nextBody)
  | forallE _ _ domain body =>
    cases second with
    | forallE nextDomain nextBody => exact .forallE (domain nextDomain) (body nextBody)

private theorem levelsRightSelf (equal : EqUpToLevels U a b) : EqUpToLevels U b b := by
  induction equal with
  | bvar => exact .bvar
  | const _ right _ => exact .const right right (Lean4Lean.List.Forall₂.rfl fun _ _ => rfl)
  | elim _ right _ => exact .elim right right (Lean4Lean.List.Forall₂.rfl fun _ _ => rfl)
  | sort _ right _ => exact .sort right right rfl
  | app _ _ function argument => exact .app function argument
  | proj _ major => exact .proj major
  | lam _ _ domain body => exact .lam domain body
  | forallE _ _ domain body => exact .forallE domain body

private theorem levelsUnliftSelf {e : VExpr}
    (self : EqUpToLevels U (e.lift' ρ) (e.lift' ρ)) : EqUpToLevels U e e := by
  induction e generalizing ρ with
  | bvar => exact .bvar
  | sort => cases self with | sort a b equal => exact .sort a b equal
  | const => cases self with | const a b equal => exact .const a b equal
  | elim => cases self with | elim a b equal => exact .elim a b equal
  | app _ _ function argument =>
    cases self with
    | app f a => exact .app (function f) (argument a)
  | proj _ _ _ major =>
    cases self with
    | proj value => exact .proj (major value)
  | lam _ _ domain body =>
    cases self with
    | lam a b => exact .lam (domain a) (body b)
  | forallE _ _ domain body =>
    cases self with
    | forallE a b => exact .forallE (domain a) (body b)

inductive RetainedApplicationDemandHead (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (goalFunction goalArgument : VExpr) {goalRank : Nat} (goalOutput : Atom goalRank) : VExpr → {n : Nat} → Atom n → Type where
  | application (ρ : Lift)
      (functionLevels : EqUpToLevels U function (goalFunction.lift' ρ))
      (argumentLevels : EqUpToLevels U argument (goalArgument.lift' ρ))
      (path : GeneralOutputPath env U registry target atom goalOutput) :
      RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput (.app function argument) atom
  | domain {support : Profile n} {rows : List (Key n × Profile n)}
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (member : atom ∈ support.atoms)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom) :
      RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput (.forallE A B) input
  | body {support result : Profile n} {rows : List (Key n × Profile n)}
      (path : GeneralOutputPath env U registry target input
        (show Atom (n+1) from .pi prototypeDomain prototypeBody support rows))
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom) :
      RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput (.forallE A B) input

noncomputable def RetainedApplicationDemandHead.readback
    (head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom)
    (τ : Subst) : VExpr × VExpr := by
  cases head with
  | application ρ _ _ _ => exact (goalFunction.subst (Subst.lift_l ρ τ), goalArgument.subst (Subst.lift_l ρ τ))
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

private noncomputable def RetainedApplicationDemandHead.output
    (path : GeneralOutputPath env U registry target old next)
    (head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression next) :
    RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression old := by
  cases head with
  | application ρ functionLevels argumentLevels tail =>
    exact .application ρ functionLevels argumentLevels (appendPath path tail)
  | domain tail member continuation => exact .domain (appendPath path tail) member continuation
  | body tail selected member anchor admitted continuation =>
    exact .body (appendPath path tail) selected member anchor admitted continuation

private theorem RetainedApplicationDemandHead.levels
    (equal : EqUpToLevels U sourceExpression expression)
    (head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom) :
    Nonempty (RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput sourceExpression atom) := by
  cases head with
  | application ρ functionLevels argumentLevels path =>
    cases equal with
    | app f a => exact ⟨.application ρ (levelsTrans f functionLevels) (levelsTrans a argumentLevels) path⟩
  | domain path member continuation =>
    cases equal with
    | forallE domain body => exact ⟨.domain path member (.levels domain continuation)⟩
  | body path selected member anchor admitted continuation =>
    cases equal with
    | forallE domain body => exact ⟨.body path selected member anchor admitted (.levels body continuation)⟩

private noncomputable def RetainedApplicationDemandHead.rename
    (ρ : Lift)
    (head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom) :
    RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput (expression.lift' ρ) atom := by
  cases head with
  | application previous functionLevels argumentLevels path =>
    exact .application (previous.comp ρ)
      (by simpa only [lift'_comp] using functionLevels.lift' ρ)
      (by simpa only [lift'_comp] using argumentLevels.lift' ρ) path
  | domain path member continuation => exact .domain path member (.rename ρ continuation)
  | body path selected member anchor admitted continuation =>
    exact .body path selected member anchor admitted (.rename ρ.cons continuation)

private theorem RetainedApplicationDemandHead.output_readback
    (path : GeneralOutputPath env U registry target old next)
    (head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression next)
    (τ : Subst) : (head.output path).readback τ = head.readback τ := by
  cases head <;> rfl

private theorem RetainedApplicationDemandHead.rename_readback
    (ρ : Lift)
    (head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom)
    (τ : Subst) : (head.rename ρ).readback τ = head.readback (Subst.lift_l ρ τ) := by
  cases head with
  | application previous functionLevels argumentLevels path =>
    have pull : Subst.lift_l (previous.comp ρ) τ = Subst.lift_l previous (Subst.lift_l ρ τ) := by
      funext i
      simp only [Subst.lift_l, Lift.liftVar_comp]
    change (goalFunction.subst _, goalArgument.subst _) = (goalFunction.subst _, goalArgument.subst _)
    rw [pull]
  | domain path member continuation => rfl
  | body path selected member anchor admitted continuation =>
    have pull : Subst.lift_l ρ.cons (τ.cons anchor) = (Subst.lift_l ρ τ).cons anchor := by
      funext i
      cases i <;> rfl
    change continuation.readback _ = continuation.readback _
    rw [pull]

private theorem RetainedApplicationDemandHead.levelsReadback
    (equal : EqUpToLevels U sourceExpression expression)
    (head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom) :
    ∃ next : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput sourceExpression atom,
      ∀ τ, next.readback τ = head.readback τ := by
  cases head with
  | application ρ functionLevels argumentLevels path =>
    cases equal with
    | app f a => exact ⟨.application ρ (levelsTrans f functionLevels) (levelsTrans a argumentLevels) path, fun _ => rfl⟩
  | domain path member continuation =>
    cases equal with
    | forallE domain body => exact ⟨.domain path member (.levels domain continuation), fun _ => rfl⟩
  | body path selected member anchor admitted continuation =>
    cases equal with
    | forallE domain body => exact ⟨.body path selected member anchor admitted (.levels body continuation), fun _ => rfl⟩

/-- Head normalization preserves the exact final operands for every current
resource substitution. Its terminal renaming can therefore be read back in
the caller after composing the actual program transitions. -/
theorem RetainedApplicationDemand.headReadback
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (self : EqUpToLevels U expression expression) :
    ∃ head : RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom,
      ∀ τ, head.readback τ = demand.readback τ := by
  induction demand with
  | application =>
    cases self with
    | app function argument =>
      exact ⟨.application .refl (by simpa using function) (by simpa using argument) .refl, fun _ => rfl⟩
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
theorem RetainedApplicationDemand.head
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (self : EqUpToLevels U expression expression) :
    Nonempty (RetainedApplicationDemandHead env U registry target goalFunction goalArgument goalOutput expression atom) := by
  induction demand with
  | application =>
    cases self with
    | app function argument => exact ⟨.application .refl (by simpa using function) (by simpa using argument) .refl⟩
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

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
