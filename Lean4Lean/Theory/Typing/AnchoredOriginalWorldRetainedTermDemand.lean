import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-! Shared retained demands for arbitrary literal terminal expressions.
Applications and projections use the same exact output, domain, body,
universe and binder operations. A demand is executable syntax, not a
supplied interpreter or a promise of caller-side reconstruction. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private levelsSubstitutionKernel from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedTermDemand (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (goal : VExpr) (goalOutput : Atom goalRank) : VExpr → {n : Nat} → Atom n → Type where
  | terminal : RetainedTermDemand env U registry target goal goalOutput
      goal goalOutput
  | output (path : GeneralOutputPath env U registry target old next)
      (continuation : RetainedTermDemand env U registry target goal goalOutput expression next) :
      RetainedTermDemand env U registry target goal goalOutput expression old
  | domain {support : Profile n} {rows : List (Key n × Profile n)}
      (member : atom ∈ support.atoms)
      (continuation : RetainedTermDemand env U registry target goal goalOutput A atom) :
      RetainedTermDemand env U registry target goal goalOutput (.forallE A B)
        (n := n + 1) (.pi prototypeDomain prototypeBody support rows)
  | body {support result : Profile n} {rows : List (Key n × Profile n)}
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedTermDemand env U registry target goal goalOutput B atom) :
      RetainedTermDemand env U registry target goal goalOutput (.forallE A B)
        (n := n + 1) (.pi prototypeDomain prototypeBody support rows)
  | levels (equal : EqUpToLevels U sourceExpression expression)
      (continuation : RetainedTermDemand env U registry target goal goalOutput expression atom) :
      RetainedTermDemand env U registry target goal goalOutput sourceExpression atom
  | rename (ρ : Lift)
      (continuation : RetainedTermDemand env U registry target goal goalOutput expression atom) :
      RetainedTermDemand env U registry target goal goalOutput (expression.lift' ρ) atom

noncomputable def RetainedTermDemand.readback
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (τ : Subst) : VExpr :=
  by
    induction demand generalizing τ with
    | terminal => exact goal.subst τ
    | output _ _ ih | domain _ _ ih | levels _ _ ih => exact ih τ
    | body _ _ anchor _ _ ih => exact ih (τ.cons anchor)
    | rename ρ _ ih => exact ih (Subst.lift_l ρ τ)

private theorem termReadback_transport (same : expression = next)
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (τ : Subst) : (same ▸ demand).readback τ = demand.readback τ := by
  cases same
  rfl

/-- Only variables actually occurring in the input expression affect the
eventual requested operands. This also covers pending binder instructions. -/
theorem RetainedTermDemand.readback_congr
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (same : expression.subst σ = expression.subst τ) :
    demand.readback σ = demand.readback τ := by
  induction demand generalizing σ τ with
  | terminal => exact same
  | output path continuation ih => exact ih same
  | domain member continuation ih => exact ih (VExpr.forallE.inj same).1
  | body selected member anchor admitted continuation ih =>
    apply ih
    have body := congrArg (fun e : VExpr => e.inst anchor) (VExpr.forallE.inj same).2
    simpa only [inst_lift_cons] using body
  | levels equal continuation ih => exact ih (levelsSubstitutionKernel equal same)
  | rename ρ continuation ih =>
    apply ih
    simpa only [subst_lift'] using same

theorem RetainedTermDemand.readback_closed
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (closed : expression.Closed) : demand.readback σ = demand.readback τ := by
  apply demand.readback_congr
  exact (closed.subst_eq Subst.Fixes.zero).trans (closed.subst_eq Subst.Fixes.zero).symm


/-- Existing application demands embed without changing any instruction or
selected output. This is the compatibility connection for sharing the same
recipe machinery with projection terminals. -/
noncomputable def RetainedApplicationDemand.toTerm
    (demand : RetainedApplicationDemand env U registry target function argument goalOutput expression atom) :
    RetainedTermDemand env U registry target (.app function argument) goalOutput expression atom := by
  induction demand with
  | application => exact .terminal
  | output path _ ih => exact .output path ih
  | domain member _ ih => exact .domain member ih
  | body selected member anchor admitted _ ih => exact .body selected member anchor admitted ih
  | levels equal _ ih => exact .levels equal ih
  | rename rename _ ih => exact .rename rename ih

theorem RetainedApplicationDemand.toTerm_readback
    (demand : RetainedApplicationDemand env U registry target function argument goalOutput expression atom)
    (realization : Subst) :
    demand.toTerm.readback realization =
      .app (demand.readback realization).1 (demand.readback realization).2 := by
  induction demand generalizing realization with
  | application => rfl
  | output _ _ ih | domain _ _ ih | levels _ _ ih => exact ih realization
  | body _ _ anchor _ _ ih => exact ih (realization.cons anchor)
  | rename rename _ ih => exact ih (Subst.lift_l rename realization)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
