import Lean4Lean.Theory.Typing.AnchoredDataExposureTransport

/-! Constructor observations retain finite typed provenance in addition to
actual computational traces. Structure eta and unit-like equality are
explicit constructors; neither is reported as a canonical machine trace. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

inductive ConstructorOrigin (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry) :
    List VExpr → VExpr → VExpr → VExpr → Prop where
  | exposure (display : ConstructorExposure env U registry Γ expression type Δ ρ head) :
      ConstructorOrigin env U registry Δ (expression.lift' ρ) head (type.lift' ρ)
  | refl (typed : env.HasType U Γ expression type) :
      ConstructorOrigin env U registry Γ expression expression type
  | eta {info : VProjectionInfo} {name : Name} {params : List VExpr} {levels : List VLevel}
      (registered : env.projections name info)
      (paramCount : params.length = info.nparams) (unindexed : info.nindices = 0)
      (majorTyped : env.HasType U Γ major (mkApps (.const name levels) params))
      (expansionTyped : env.HasType U Γ
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map (fun index => .proj name index major)))
        (mkApps (.const name levels) params)) :
      ConstructorOrigin env U registry Γ major
        (mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map (fun index => .proj name index major)))
        (mkApps (.const name levels) params)
  | unitLike {info : VProjectionInfo} {name : Name} {params : List VExpr} {levels : List VLevel}
      (registered : env.projections name info)
      (paramCount : params.length = info.nparams) (unindexed : info.nindices = 0)
      (noFields : info.numFields = 0)
      (leftTyped : env.HasType U Γ left (mkApps (.const name levels) params))
      (rightTyped : env.HasType U Γ right (mkApps (.const name levels) params)) :
      ConstructorOrigin env U registry Γ left right (mkApps (.const name levels) params)
  | symm (origin : ConstructorOrigin env U registry Γ left right type) :
      ConstructorOrigin env U registry Γ right left type
  | trans (first : ConstructorOrigin env U registry Γ left middle type)
      (second : ConstructorOrigin env U registry Γ middle right type) :
      ConstructorOrigin env U registry Γ left right type
  | convert (path : TypeConversion env U Γ type type')
      (origin : ConstructorOrigin env U registry Γ left right type) :
      ConstructorOrigin env U registry Γ left right type'
  | weaken (route : Ctx.Lift' ρ Γ Δ)
      (origin : ConstructorOrigin env U registry Γ left right type) :
      ConstructorOrigin env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
  | context (route : ContextChain env U Γ Δ)
      (origin : ConstructorOrigin env U registry Γ left right type) :
      ConstructorOrigin env U registry Δ left right type
  | substitute (formed : OnCtx Δ (env.IsType U)) (typed : Ctx.SubstEq env U Δ σ σ Γ)
      (origin : ConstructorOrigin env U registry Γ left right type) :
      ConstructorOrigin env U registry Δ (left.subst σ) (right.subst σ) (type.subst σ)
  | levels (formed : OnCtx Γ (env.IsType U)) (typed : env.HasType U Γ left type)
      (equal : EqUpToLevels U left right) :
      ConstructorOrigin env U registry Γ left right type

theorem ConstructorOrigin.sound (henv : env.Ordered)
    (origin : ConstructorOrigin env U registry Γ left right type) :
    env.IsDefEq U Γ left right type := by
  induction origin with
  | exposure display => exact display.sound
  | refl typed => exact typed
  | eta registered count unindexed majorTyped expansionTyped =>
    exact (IsDefEq.structEta registered count unindexed majorTyped expansionTyped).symm
  | unitLike registered count unindexed noFields leftTyped rightTyped =>
    exact .unitLike registered count unindexed noFields leftTyped rightTyped
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | convert path _ ih => exact path.cast ih
  | weaken route _ ih => exact ih.weak' henv route
  | context route _ ih => exact route.eq henv ih
  | substitute formed typed _ ih => exact ih.subst henv typed formed
  | levels formed typed equal => exact typed.eqUpToLevels henv formed equal

theorem ConstructorOrigin.mixed (henv : env.Ordered)
    (origin : ConstructorOrigin env U registry Γ left right type)
    (route : MixedInsertion env U Γ Δ ρ) :
    ConstructorOrigin env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) := by
  induction route generalizing left right type with
  | proof insertion => exact .weaken insertion.weakening origin
  | context chain => simpa only [lift'_refl] using ConstructorOrigin.context chain origin
  | comp _ _ first second => simpa only [← lift'_comp] using second (first origin)

theorem ConstructorOrigin.ofTrace
    (henv : env.Ordered)
    {type : VExpr}
    (trace : CanonicalDataHead.Trace registry expression front result)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (equal : env.IsDefEq U (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) result (type.lift' (.skipN .refl front.length))) :
    ConstructorOrigin env U registry (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) result (type.lift' (.skipN .refl front.length)) := by
  exact .exposure {
    added := front
    result := result
    postMap := .refl
    trace := trace
    generated := generated
    postContext := front ++ Γ
    post := .refl (generated.targetWF henv)
    terminal := .refl
    map_eq := by simp only [Lift.comp]
    result_eq := lift'_refl
    sound := equal }

structure ConstructorDisplay (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (Γ : List VExpr) (expression type : VExpr) (Δ : List VExpr) (ρ : Lift)
    (head : VExpr) : Type where
  baseWF : OnCtx Γ (env.IsType U)
  route : MixedInsertion env U Γ Δ ρ
  origin : ConstructorOrigin env U registry Δ (expression.lift' ρ) head (type.lift' ρ)
  sound : env.IsDefEq U Δ (expression.lift' ρ) head (type.lift' ρ)

namespace ConstructorDisplay

def ofExposure (henv : env.Ordered)
    (display : ConstructorExposure env U registry Γ expression type Δ ρ head) :
    ConstructorDisplay env U registry Γ expression type Δ ρ head where
  baseWF := display.generated.baseWF
  route := display.insertion henv
  origin := .exposure display
  sound := display.sound

theorem insertion (_henv : env.Ordered)
    (display : ConstructorDisplay env U registry Γ expression type Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := display.route

theorem targetWF (henv : env.Ordered)
    (display : ConstructorDisplay env U registry Γ expression type Δ ρ head) :
    OnCtx Δ (env.IsType U) := display.route.targetWF henv display.baseWF

theorem transport (henv : env.Ordered)
    (display : ConstructorDisplay env U registry Γ expression type Δ ρ head)
    (route : MixedInsertion env U Δ Ω τ) :
    Nonempty (ConstructorDisplay env U registry Γ expression type Ω (ρ.comp τ) (head.lift' τ)) := by
  exact ⟨{
    baseWF := display.baseWF
    route := display.route.comp route
    origin := by simpa only [← lift'_comp] using display.origin.mixed henv route
    sound := by simpa only [← lift'_comp] using route.eq henv display.sound }⟩

def context (henv : env.Ordered) (chain : ContextChain env U Γ Γ')
    (display : ConstructorDisplay env U registry Γ expression type Δ ρ head) :
    ConstructorDisplay env U registry Γ' expression type Δ ρ head where
  baseWF := chain.targetWF henv display.baseWF
  route := by simpa only [Lift.refl_comp] using
    MixedInsertion.comp (.context (chain.symm henv)) display.route
  origin := display.origin
  sound := display.sound

def convert (display : ConstructorDisplay env U registry Γ expression type Δ ρ head)
    (path : TypeConversion env U Δ (type.lift' ρ) (type'.lift' ρ)) :
    ConstructorDisplay env U registry Γ expression type' Δ ρ head :=
  { display with origin := .convert path display.origin, sound := path.cast display.sound }

def prepend (henv : env.Ordered)
    (origin : ConstructorOrigin env U registry Γ expanded expression type)
    (display : ConstructorDisplay env U registry Γ expression type Δ ρ head) :
    ConstructorDisplay env U registry Γ expanded type Δ ρ head :=
  { display with
    origin := .trans (origin.mixed henv display.route) display.origin
    sound := (display.route.eq henv (origin.sound henv)).trans display.sound }

theorem absorb (henv : env.Ordered) (_hscoped : registry.Scoped)
    (insertion : ProofInsertion env U Γ Δ ρ)
    (display : ConstructorDisplay env U registry Δ (expression.lift' ρ) (type.lift' ρ) Ω τ head) :
    Nonempty (ConstructorDisplay env U registry Γ expression type Ω (ρ.comp τ) head) := by
  exact ⟨{
    baseWF := insertion.baseWF
    route := MixedInsertion.comp (.proof insertion) display.route
    origin := by simpa only [← lift'_comp] using display.origin
    sound := by simpa only [← lift'_comp] using display.sound }⟩

end ConstructorDisplay
end Lean4Lean.AnchoredSemantics
