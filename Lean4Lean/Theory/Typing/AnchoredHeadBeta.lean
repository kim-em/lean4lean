import Lean4Lean.Theory.Typing.AnchoredDataExposureTransport
import Lean4Lean.Theory.Typing.CanonicalDataHeadApplication
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction
import Lean4Lean.Theory.Typing.DependentTypeConversion
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Typing.NativeCaptureAbstraction

/-! Head beta expansion retains the actual typed conversion path and final
display. It never aligns independently assigned universes by type uniqueness. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

inductive HeadBeta : VExpr → VExpr → Prop where
  | refl : HeadBeta expression expression
  | contract : HeadBeta (mkApps (.lam A body) (argument :: trailing))
      (mkApps (body.inst argument) trailing)
  | apply : HeadBeta left right → HeadBeta (.app left argument) (.app right argument)
  | proj : HeadBeta left right → HeadBeta (.proj name index left) (.proj name index right)

private theorem mkApps_lift' (head : VExpr) (arguments : List VExpr) (ρ : Lift) :
    (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument trailing ih => exact ih (.app head argument)

theorem HeadBeta.lift (h : HeadBeta left right) (ρ : Lift) :
    HeadBeta (left.lift' ρ) (right.lift' ρ) := by
  induction h with
  | refl => exact .refl
  | apply h ih => exact .apply ih
  | proj h ih => exact .proj ih
  | @contract A body argument trailing =>
    simpa only [mkApps_lift', lift', List.map_cons, lift'_inst_hi] using
      (HeadBeta.contract (A := A.lift' ρ) (body := body.lift' ρ.cons)
        (argument := argument.lift' ρ) (trailing := List.map (·.lift' ρ) trailing))

theorem HeadBeta.app (h : HeadBeta left right) (argument : VExpr) :
    HeadBeta (.app left argument) (.app right argument) := .apply h

/-- A genuine beta step cannot start with a constructor constant, including
when the redex occurs under applications and primitive projections. -/
theorem HeadBeta.not_const_spine (h : HeadBeta left right) (different : left ≠ right) :
    ∀ name levels, left.getAppFnArgs.1 ≠ .const name levels := by
  induction h with
  | refl => exact (different rfl).elim
  | contract =>
    intro name levels
    rw [InductiveSignature.spine_mkApps_exact _ _ rfl]
    intro impossible
    cases impossible
  | @apply left right argument h ih =>
    have inner : left ≠ right := fun eq => different (congrArg (VExpr.app · argument) eq)
    simpa only [getAppFnArgs_app] using ih inner
  | proj => intro name levels impossible; cases impossible

/-- The syntactic beta relation is one step of the actual data machine.
Projection dispatch cannot preempt it because its major has no constant head. -/
theorem HeadBeta.step (h : HeadBeta left right) (different : left ≠ right) :
    CanonicalDataHead.step registry left = some ⟨[], right⟩ := by
  induction h with
  | refl => exact (different rfl).elim
  | contract =>
    apply CanonicalDataHead.step_of_legacy
    unfold CanonicalHead.step
    rw [InductiveSignature.spine_mkApps_exact _ _ rfl]
    rfl
  | @apply left right argument h ih =>
    have inner : left ≠ right := fun eq => different (congrArg (VExpr.app · argument) eq)
    simpa only [CanonicalHead.Output.apply, List.length_nil, liftN_zero] using
      CanonicalDataHead.step_app (ih inner) argument
  | @proj left right name index h ih =>
    have inner : left ≠ right := fun eq => different (congrArg (VExpr.proj name index) eq)
    have noProject : CanonicalDataHead.project registry name index left = none := by
      unfold CanonicalDataHead.project
      cases lookup : registry.projections name with
      | none => rfl
      | some info =>
        simp only [lookup, bind, Option.bind_some]
        cases spine : left.getAppFnArgs with
        | mk head args =>
          cases head <;> try rfl
          case const ctor levels =>
            exact ((h.not_const_spine inner ctor levels) (congrArg Prod.fst spine)).elim
    simp only [CanonicalDataHead.step, CanonicalHead.step, getAppFnArgs, getAppFnArgs.go,
      CanonicalHead.spineStep, noProject, ih inner, Option.map_some, CanonicalDataHead.projMajor]

theorem HeadBeta.prepend_trace (h : HeadBeta left right)
    (trace : CanonicalDataHead.Trace registry right added result) :
    CanonicalDataHead.Trace registry left added result := by
  by_cases equal : left = right
  · exact equal ▸ trace
  · simpa only [List.append_nil] using CanonicalDataHead.Trace.next (h.step equal) trace

def Exposure.headBeta (henv : env.Ordered)
    (reduction : HeadBeta expanded expression)
    (path : TypeConversion env U Γ expanded expression)
    (E : Exposure env U registry Γ expression Δ ρ head) :
    Exposure env U registry Γ expanded Δ ρ head where
  added := E.added
  result := E.result
  postMap := E.postMap
  trace := reduction.prepend_trace E.trace
  generated := E.generated
  postContext := E.postContext
  post := E.post
  terminal := E.terminal
  map_eq := E.map_eq
  result_eq := E.result_eq
  sound := ((E.insertion henv).path henv path).trans E.sound
  headType := E.headType

def ConstructorExposure.headBeta (henv : env.Ordered)
    (reduction : HeadBeta expanded expression)
    (equal : env.IsDefEq U Γ expanded expression type)
    (E : ConstructorExposure env U registry Γ expression type Δ ρ head) :
    ConstructorExposure env U registry Γ expanded type Δ ρ head where
  added := E.added
  result := E.result
  postMap := E.postMap
  trace := reduction.prepend_trace E.trace
  generated := E.generated
  postContext := E.postContext
  post := E.post
  terminal := E.terminal
  map_eq := E.map_eq
  result_eq := E.result_eq
  sound := ((E.insertion henv).eq henv equal).trans E.sound

theorem ConstructorOrigin.ofHeadBeta (henv : env.Ordered)
    (formed : OnCtx Γ (env.IsType U))
    (reduction : HeadBeta expanded expression)
    (equal : env.IsDefEq U Γ expanded expression type) :
    ConstructorOrigin env U registry Γ expanded expression type := by
  have trace : CanonicalDataHead.Trace registry expanded [] expression :=
    reduction.prepend_trace .refl
  have origin := ConstructorOrigin.ofTrace henv trace (.refl formed)
    (by simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl] using equal)
  simpa only [List.nil_append, List.length_nil, Lift.skipN, lift'_refl] using origin

def ConstructorDisplay.headBeta (henv : env.Ordered)
    (reduction : HeadBeta expanded expression)
    (equal : env.IsDefEq U Γ expanded expression type)
    (display : ConstructorDisplay env U registry Γ expression type Δ ρ head) :
    ConstructorDisplay env U registry Γ expanded type Δ ρ head :=
  display.prepend henv (ConstructorOrigin.ofHeadBeta henv display.baseWF reduction equal)

def RankedData.ConstructorWitness.headBeta (henv : env.Ordered)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (W : RankedData.ConstructorWitness env U registry lower Γ left right type demand) :
    RankedData.ConstructorWitness env U registry lower Γ leftExpanded rightExpanded type demand :=
  { W with
    leftExposure := W.leftExposure.headBeta henv hl cl
    rightExposure := W.rightExposure.headBeta henv hr cr }

theorem RankedData.ConstructorRelation.headBeta (henv : env.Ordered)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : RankedData.ConstructorRelation env U registry lower Γ left right type demand) :
    RankedData.ConstructorRelation env U registry lower Γ leftExpanded rightExpanded type demand := by
  intro Δ ρ future
  obtain ⟨W⟩ := H Δ ρ future
  exact ⟨W.headBeta henv (hl.lift ρ) (hr.lift ρ)
    (cl.weak' henv future.weakening) (cr.weak' henv future.weakening)⟩

/-- A sort contains no private variables, so both endpoints of this raw path
are lifts of base expressions. Only the typed path is retracted. -/
theorem Exposure.sortPath (henv : env.Ordered)
    (E : Exposure env U registry Γ expression Δ ρ (.sort level)) :
    TypeConversion env U Γ expression (.sort level) := by
  apply (E.insertion henv).pathBack henv
  exact E.sound

theorem SortRelated.path (henv : env.Ordered)
    (H : SortRelated env U registry Γ left right relevant) :
    ∃ level, TypeConversion env U Γ left (.sort level) := by
  obtain ⟨_, _, level, _, ⟨leftExposure⟩, _⟩ := H
  exact ⟨level, leftExposure.sortPath henv⟩

theorem TypeRelated.headBeta (henv : env.Ordered)
    {leftExpanded rightExpanded left right : VExpr} {profile : Profile n}
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : TypeConversion env U Γ leftExpanded left)
    (cr : TypeConversion env U Γ rightExpanded right)
    (H : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ leftExpanded rightExpanded profile := by
  induction n generalizing Γ leftExpanded rightExpanded left right with
  | zero =>
    intro Δ ρ future atom hm
    obtain ⟨Ω, τ, u, v, ⟨el⟩, ⟨er⟩, huv, hu⟩ := H Δ ρ future atom hm
    exact ⟨Ω, τ, u, v,
      ⟨el.headBeta henv (hl.lift ρ) (cl.weak' henv future.weakening)⟩,
      ⟨er.headBeta henv (hr.lift ρ) (cr.weak' henv future.weakening)⟩, huv, hu⟩
  | succ n ih =>
    intro Δ ρ future atom hm
    have h := H Δ ρ future atom hm
    have hl := hl.lift ρ
    have hr := hr.lift ρ
    have cl := cl.weak' henv future.weakening
    have cr := cr.weak' henv future.weakening
    cases atom with
    | sort relevant =>
      obtain ⟨Ω, τ, u, v, ⟨el⟩, ⟨er⟩, huv, hu⟩ := h
      exact ⟨Ω, τ, u, v, ⟨el.headBeta henv hl cl⟩,
        ⟨er.headBeta henv hr cr⟩, huv, hu⟩
    | fn | ctor | record => exact h.elim
    | family demand =>
      obtain ⟨display⟩ := h
      refine ⟨{ display with
        leftExposure := display.leftExposure.headBeta henv hl cl
        rightExposure := display.rightExposure.headBeta henv hr cr
        path := ?_ }⟩
      exact (((display.leftExposure.insertion henv).path henv cl).trans display.path).trans
        ((display.rightExposure.insertion henv).path henv cr).symm
    | pad atom => exact ih hl hr cl cr h
    | pi A B domain rows =>
      obtain ⟨display⟩ := h
      exact ⟨{ display with
        leftExposure := display.leftExposure.headBeta henv hl cl
        rightExposure := display.rightExposure.headBeta henv hr cr }⟩

end Lean4Lean.AnchoredSemantics
