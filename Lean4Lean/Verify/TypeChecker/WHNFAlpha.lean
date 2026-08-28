import Lean4Lean.Verify.TypeChecker.AlphaLocality
import Batteries.Tactic.OpenPrivate

namespace Lean4Lean

open Lean hiding Environment Exception

namespace TypeChecker

open private getAppNumArgsAux from Lean.Expr

/-- Source forms which reach the public WHNF cache after the cheap syntactic
cases have been discharged.  Free variables are absent because inductive
checker contexts contain only constant declarations, so their WHNF branch
returns before consulting the cache. -/
inductive Expr.WhnfCacheable : Expr → Prop
  | lam : Expr.WhnfCacheable (.lam name domain body bi)
  | app : Expr.WhnfCacheable (.app fn arg)
  | const : Expr.WhnfCacheable (.const name levels)
  | letE : Expr.WhnfCacheable (.letE name type value body nondep)
  | proj : Expr.WhnfCacheable (.proj name index body)

/-- An existing public-WHNF cache entry is returned literally without
changing checker state. -/
theorem Inner.whnf'_cache_hit
    (Hform : Expr.WhnfCacheable input)
    (hcache : state.whnfCache[input]? = some result)
    (methods : Methods) (context : Context) :
    Inner.whnf' input methods context state = .ok (result, state) := by
  cases Hform <;>
    simp [Inner.whnf', hcache, Bind.bind, Monad.toBind,
      ReaderT.instMonad, ReaderT.bind, StateT.instMonad, StateT.bind,
      liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
      instMonadLiftTOfMonadLift, instMonadLiftT,
      getThe, MonadState.get,
      MonadStateOf.get, instMonadStateOfMonadStateOf,
      instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
      StateT.get, ReaderT.instMonadLift, StateT.instMonadLift,
      StateT.lift, Pure.pure, Applicative.toPure,
      Monad.toApplicative, ReaderT.pure, StateT.pure,
      Except.instMonad, Except.pure, Except.bind]

/-- A successful public WHNF run whose input is already cached returns that
cached value and leaves the state unchanged.  Success rules out zero
recursion depth internally. -/
theorem whnf_cache_hit_result_eq
    (Hform : Expr.WhnfCacheable input)
    (hcache : state.whnfCache[input]? = some cached)
    (Hrun : whnf input context state = .ok (result, outState)) :
    result = cached ∧ outState = state := by
  unfold whnf RecM.run Inner.whnf at Hrun
  simp only [Bind.bind, Monad.toBind, ReaderT.instMonad, ReaderT.bind,
    StateT.instMonad, StateT.bind] at Hrun
  rw [readContext_run] at Hrun
  simp only [Except.bind] at Hrun
  cases hdepth : context.fuel.recDepth with
  | zero =>
      rw [hdepth] at Hrun
      simp [Methods.withFuel, MonadExcept.throw, throwThe,
        MonadExceptOf.throw, ReaderT.instMonadExceptOf,
        StateT.instMonadExceptOf, instMonadExceptOfExcept,
        liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
        instMonadLiftTOfMonadLift, instMonadLiftT,
        ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
        Functor.map, Except.map] at Hrun
  | succ depth =>
      rw [hdepth] at Hrun
      simp only [Methods.withFuel] at Hrun
      rw [Inner.whnf'_cache_hit Hform hcache] at Hrun
      have hpairs := (Except.ok.inj Hrun).symm
      exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

/-- On a public-cache miss, `whnf'` is exactly its fuel-bounded reduction
loop followed by insertion of the successful result.  Exposing the local
loop makes the recursive alpha proof independent of monad elaboration. -/
theorem Inner.whnf'_cache_miss_eq
    (Hform : Expr.WhnfCacheable input)
    (hcache : state.whnfCache[input]? = Option.none) :
    Inner.whnf' input methods context state =
      (Inner.whnf'.loop input
        (if context.eagerReduce then context.fuel.whnfEager
          else context.fuel.whnf)
        methods context state).map fun (result, loopState) =>
          (result, ({ loopState with whnfCache :=
            (loopState.whnfCache.insert input result) } : State)) := by
  cases Hform <;>
    simp only [Inner.whnf', Bind.bind, Monad.toBind,
      ReaderT.instMonad, ReaderT.bind, StateT.instMonad, StateT.bind,
      liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
      instMonadLiftTOfMonadLift, instMonadLiftT,
      getThe, MonadState.get,
      MonadStateOf.get, instMonadStateOfMonadStateOf,
      instMonadStateOfOfMonadLift, instMonadStateOfStateTOfMonad,
      StateT.get, StateT.modifyGet, _root_.modify,
      modifyGetThe, MonadState.modifyGet,
      MonadStateOf.modifyGet,
      ReaderT.instMonadLift, StateT.instMonadLift,
      StateT.lift, Pure.pure, Applicative.toPure,
      Monad.toApplicative, ReaderT.pure, StateT.pure,
      Except.instMonad, Except.pure, Except.bind] <;>
    rw [hcache] <;>
    simp only [Except.bind, ReaderT.bind, ReaderT.read, MonadReader.read,
      instMonadReaderOfMonadReaderOf, readThe, MonadReaderOf.read,
      instMonadReaderOfReaderTOfMonad] <;>
    simp [hcache, liftM, monadLift, MonadLiftT.monadLift,
      MonadLift.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT,
      ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
      Functor.map, StateT.map,
      getThe, MonadState.get, MonadStateOf.get,
      instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,
      instMonadStateOfStateTOfMonad, StateT.get,
      StateT.modifyGet, _root_.modify,
      modifyGetThe, MonadState.modifyGet, MonadStateOf.modifyGet,
      Bind.bind, Monad.toBind, ReaderT.bind, StateT.bind,
      ReaderT.read, MonadReader.read, instMonadReaderOfMonadReaderOf,
      readThe, MonadReaderOf.read, instMonadReaderOfReaderTOfMonad,
      Pure.pure, Applicative.toPure, Monad.toApplicative,
      ReaderT.pure, StateT.pure, Except.pure, Except.bind, Except.map]

/-- Inverting the cache-miss equation retains the exact successful loop
state before the public cache insertion. -/
theorem Inner.whnf'_cache_miss_result
    (Hform : Expr.WhnfCacheable input)
    (hcache : state.whnfCache[input]? = Option.none)
    (Hrun : Inner.whnf' input methods context state =
      .ok (result, outState)) :
    ∃ loopState,
      Inner.whnf'.loop input
        (if context.eagerReduce then context.fuel.whnfEager
          else context.fuel.whnf)
        methods context state = .ok (result, loopState) ∧
      outState = ({ loopState with whnfCache :=
        (loopState.whnfCache.insert input result) } : State) := by
  rw [Inner.whnf'_cache_miss_eq Hform hcache] at Hrun
  generalize hloop : Inner.whnf'.loop _ _ _ _ _ = loopResult at Hrun
  cases loopResult with
  | error error =>
      simp only [Except.map] at Hrun
      cases Hrun
  | ok pair =>
      rcases pair with ⟨loopResult, loopState⟩
      simp only [Except.map] at Hrun
      cases Hrun
      exact ⟨loopState, rfl, rfl⟩

/-- Alpha equality together with the source well-scoping required to make
simultaneous closure injective.  WHNF cache keys and values arising from the
inductive checker satisfy this relation; packaging closure here keeps the
cache proof honest about the possible collision with loose bound variables. -/
structure ClosedExprAlphaUnder (left right : List FVarId)
    (leftExpr rightExpr : Expr) : Prop where
  left_closed : Closed leftExpr
  right_closed : Closed rightExpr
  alpha : ExprAlphaUnder left right leftExpr rightExpr

theorem ClosedExprAlphaUnder.symm
    (H : ClosedExprAlphaUnder left right leftExpr rightExpr) :
    ClosedExprAlphaUnder right left rightExpr leftExpr where
  left_closed := H.right_closed
  right_closed := H.left_closed
  alpha := H.alpha.symm

/-- For fixed duplicate-free binder spines, paired closed alpha expressions
make exactly the same concrete equality decision.  This is the collision
fact needed to show that inserting paired WHNF cache entries preserves
paired lookup. -/
theorem ClosedExprAlphaUnder.eq_iff
    (Hbinders : LocalContext.OrderedBinderRenaming
      leftContext rightContext left right)
    (H₁ : ClosedExprAlphaUnder left right left₁ right₁)
    (H₂ : ClosedExprAlphaUnder left right left₂ right₂) :
    left₁ = left₂ ↔ right₁ = right₂ := by
  constructor
  · intro hleft
    subst left₂
    apply Expr.abstractList_injective_of_closed Hbinders.right_nodup
      H₁.right_closed H₂.right_closed
    exact H₁.alpha.symm.trans H₂.alpha
  · intro hright
    subst right₂
    apply Expr.abstractList_injective_of_closed Hbinders.left_nodup
      H₁.left_closed H₂.left_closed
    exact H₁.alpha.trans H₂.alpha.symm

theorem Expr.instantiateRevList_eqv_alpha
    {leftExpr rightExpr : Expr}
    (H : leftExpr == rightExpr) (values : List Expr) (k : Nat) :
    leftExpr.instantiateRevList values k ==
      rightExpr.instantiateRevList values k := by
  rw [← Expr.instantiateList_reverse, ← Expr.instantiateList_reverse]
  exact Expr.instantiateList_eqv H

/-- The non-strict expression equality used by `ExprMap` is likewise
reflected across paired closed alpha forms. -/
theorem ClosedExprAlphaUnder.eqv_iff
    (Hbinders : LocalContext.OrderedBinderRenaming
      leftContext rightContext left right)
    (H₁ : ClosedExprAlphaUnder left right left₁ right₁)
    (H₂ : ClosedExprAlphaUnder left right left₂ right₂) :
    (left₁ == left₂) ↔ (right₁ == right₂) := by
  constructor
  · intro hleft
    have hclosed := Expr.abstractList_eqv
      (vars := left) (k := 0) hleft
    rw [H₁.alpha, H₂.alpha] at hclosed
    have hreopened := Expr.instantiateRevList_eqv_alpha hclosed
      (right.map Expr.fvar) 0
    simpa [Expr.abstractList_instantiateRevList_eq_self
      Hbinders.right_nodup H₁.right_closed,
      Expr.abstractList_instantiateRevList_eq_self
        Hbinders.right_nodup H₂.right_closed] using hreopened
  · intro hright
    have hclosed := Expr.abstractList_eqv
      (vars := right) (k := 0) hright
    rw [← H₁.alpha, ← H₂.alpha] at hclosed
    have hreopened := Expr.instantiateRevList_eqv_alpha hclosed
      (left.map Expr.fvar) 0
    simpa [Expr.abstractList_instantiateRevList_eq_self
      Hbinders.left_nodup H₁.left_closed,
      Expr.abstractList_instantiateRevList_eq_self
        Hbinders.left_nodup H₂.left_closed] using hreopened

theorem ClosedExprAlphaUnder.beq_eq
    (Hbinders : LocalContext.OrderedBinderRenaming
      leftContext rightContext left right)
    (H₁ : ClosedExprAlphaUnder left right left₁ right₁)
    (H₂ : ClosedExprAlphaUnder left right left₂ right₂) :
    (left₁ == left₂) = (right₁ == right₂) := by
  apply Bool.eq_iff_iff.mpr
  exact H₁.eqv_iff Hbinders H₂

/-- Pointwise relation on optional cache results. -/
inductive ClosedExprOptionAlphaUnder (left right : List FVarId) :
    Option Expr → Option Expr → Prop
  | none : ClosedExprOptionAlphaUnder left right none none
  | some : ClosedExprAlphaUnder left right leftExpr rightExpr →
      ClosedExprOptionAlphaUnder left right (some leftExpr) (some rightExpr)

theorem ClosedExprOptionAlphaUnder.some_left
    {leftExpr : Expr} {rightResult : Option Expr}
    (H : ClosedExprOptionAlphaUnder left right
      (Option.some leftExpr) rightResult) :
    ∃ rightExpr, rightResult = Option.some rightExpr ∧
      ClosedExprAlphaUnder left right leftExpr rightExpr := by
  cases H with
  | some Hvalue => exact ⟨_, rfl, Hvalue⟩

theorem ClosedExprOptionAlphaUnder.none_left
    {rightResult : Option Expr}
    (H : ClosedExprOptionAlphaUnder left right Option.none rightResult) :
    rightResult = Option.none := by
  cases H
  rfl

theorem ClosedExprOptionAlphaUnder.none_iff
    (H : ClosedExprOptionAlphaUnder left right leftResult rightResult) :
    leftResult = Option.none ↔ rightResult = Option.none := by
  cases H <;> simp

/-- Paired construction history for the two expression maps used as WHNF
caches.  Recording the actual synchronized inserts is stronger and more
reviewable than an extensional oracle about arbitrary maps. -/
inductive ExprMap.AlphaHistory
    (left right : List FVarId) :
    ExprMap Expr → ExprMap Expr → Prop
  | empty : ExprMap.AlphaHistory left right {} {}
  | insert
      (previous : ExprMap.AlphaHistory left right leftMap rightMap)
      (key : ClosedExprAlphaUnder left right leftKey rightKey)
      (value : ClosedExprAlphaUnder left right leftValue rightValue) :
      ExprMap.AlphaHistory left right
        (leftMap.insert leftKey leftValue)
        (rightMap.insert rightKey rightValue)

/-- Every paired cache history gives synchronized lookup on a paired closed
query.  The key step is `beq_eq`: an insertion shadows the query on the left
exactly when its paired insertion shadows the paired query on the right. -/
theorem ExprMap.AlphaHistory.getElem?
    (Hbinders : LocalContext.OrderedBinderRenaming
      leftContext rightContext left right)
    (H : ExprMap.AlphaHistory left right leftMap rightMap)
    (query : ClosedExprAlphaUnder left right leftQuery rightQuery) :
    ClosedExprOptionAlphaUnder left right
      leftMap[leftQuery]? rightMap[rightQuery]? := by
  induction H with
  | empty =>
      simp only [Std.HashMap.getElem?_empty]
      exact .none
  | @insert leftMap rightMap leftKey rightKey leftValue rightValue
      previous key value ih =>
      rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert,
        key.beq_eq Hbinders query]
      split
      · exact .some value
      · exact ih

theorem ExprMap.AlphaHistory.getElem?_none_iff
    (Hbinders : LocalContext.OrderedBinderRenaming
      leftContext rightContext left right)
    (H : ExprMap.AlphaHistory left right leftMap rightMap)
    (query : ClosedExprAlphaUnder left right leftQuery rightQuery) :
    leftMap[leftQuery]? = Option.none ↔ rightMap[rightQuery]? = Option.none :=
  (H.getElem? Hbinders query).none_iff

/-- Paired checker states for the cache-manipulating WHNF fragment.  The
four expression caches carry explicit synchronized insertion histories.
Fields only touched by inference/definitional equality are initially kept
literally equal; later reduction lemmas can refine those fields without
weakening the cache invariant. -/
structure State.WhnfAlpha
    (left right : List FVarId) (leftState rightState : State) : Prop where
  ngen_eq : leftState.ngen = rightState.ngen
  inferTypeI : ExprMap.AlphaHistory left right
    leftState.inferTypeI rightState.inferTypeI
  inferTypeC : ExprMap.AlphaHistory left right
    leftState.inferTypeC rightState.inferTypeC
  whnfCoreCache : ExprMap.AlphaHistory left right
    leftState.whnfCoreCache rightState.whnfCoreCache
  whnfCache : ExprMap.AlphaHistory left right
    leftState.whnfCache rightState.whnfCache
  eqvManager_eq : leftState.eqvManager = rightState.eqvManager
  failure_eq : leftState.failure = rightState.failure
  unfold_eq : leftState.unfold = rightState.unfold

def State.WhnfAlpha.empty (left right : List FVarId) :
    State.WhnfAlpha left right {} {} where
  ngen_eq := rfl
  inferTypeI := .empty
  inferTypeC := .empty
  whnfCoreCache := .empty
  whnfCache := .empty
  eqvManager_eq := rfl
  failure_eq := rfl
  unfold_eq := rfl

def State.WhnfAlpha.insertWhnf
    (H : State.WhnfAlpha left right leftState rightState)
    (key : ClosedExprAlphaUnder left right leftKey rightKey)
    (value : ClosedExprAlphaUnder left right leftValue rightValue) :
    State.WhnfAlpha left right
      { leftState with whnfCache :=
          leftState.whnfCache.insert leftKey leftValue }
      { rightState with whnfCache :=
          rightState.whnfCache.insert rightKey rightValue } where
  ngen_eq := H.ngen_eq
  inferTypeI := H.inferTypeI
  inferTypeC := H.inferTypeC
  whnfCoreCache := H.whnfCoreCache
  whnfCache := .insert H.whnfCache key value
  eqvManager_eq := H.eqvManager_eq
  failure_eq := H.failure_eq
  unfold_eq := H.unfold_eq

def State.WhnfAlpha.insertWhnfCore
    (H : State.WhnfAlpha left right leftState rightState)
    (key : ClosedExprAlphaUnder left right leftKey rightKey)
    (value : ClosedExprAlphaUnder left right leftValue rightValue) :
    State.WhnfAlpha left right
      { leftState with whnfCoreCache :=
          leftState.whnfCoreCache.insert leftKey leftValue }
      { rightState with whnfCoreCache :=
          rightState.whnfCoreCache.insert rightKey rightValue } where
  ngen_eq := H.ngen_eq
  inferTypeI := H.inferTypeI
  inferTypeC := H.inferTypeC
  whnfCoreCache := .insert H.whnfCoreCache key value
  whnfCache := H.whnfCache
  eqvManager_eq := H.eqvManager_eq
  failure_eq := H.failure_eq
  unfold_eq := H.unfold_eq

/-- Result relation for two successful WHNF executions. -/
structure WhnfSuccessAlpha
    (left right : List FVarId)
    (leftResult rightResult : Expr)
    (leftState rightState : State) : Prop where
  result : ClosedExprAlphaUnder left right leftResult rightResult
  state : State.WhnfAlpha left right leftState rightState

/-- Alpha-equivariance of the recursive reduction loop at one fixed fuel and
pair of inputs.  This is an induction predicate over the transparent local
loop, not a caller-facing compatibility boundary. -/
def WhnfLoopAlphaOn
    (methods : Methods) (leftContext rightContext : Context)
    (left right : List FVarId) (leftInput rightInput : Expr)
    (fuel : Nat) : Prop :=
  ∀ {leftState rightState leftOut rightOut : State}
    {leftResult rightResult : Expr},
    State.WhnfAlpha left right leftState rightState →
    ClosedExprAlphaUnder left right leftInput rightInput →
    Inner.whnf'.loop leftInput fuel methods leftContext leftState =
      .ok (leftResult, leftOut) →
    Inner.whnf'.loop rightInput fuel methods rightContext rightState =
      .ok (rightResult, rightOut) →
    WhnfSuccessAlpha left right leftResult rightResult leftOut rightOut

/-- The zero-fuel loop cannot produce a successful run on either side. -/
theorem WhnfLoopAlphaOn.zero
    (methods : Methods) (leftContext rightContext : Context)
    (left right : List FVarId) (leftInput rightInput : Expr) :
    WhnfLoopAlphaOn methods leftContext rightContext left right
      leftInput rightInput 0 := by
  intro leftState rightState leftOut rightOut leftResult rightResult
    Hstates Hinput Hleft Hright
  simp [Inner.whnf'.loop, MonadExcept.throw, throwThe,
    MonadExceptOf.throw, ReaderT.instMonadExceptOf,
    StateT.instMonadExceptOf, instMonadExceptOfExcept,
    liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    instMonadLiftTOfMonadLift, instMonadLiftT,
    ReaderT.instMonadLift, StateT.instMonadLift, StateT.lift,
    Functor.map, Except.map] at Hleft

/-- Alpha-equivariance of the inner public-WHNF implementation on one fixed
pair of inputs. -/
def InnerWhnfAlphaOn
    (methods : Methods) (leftContext rightContext : Context)
    (left right : List FVarId) (leftInput rightInput : Expr) : Prop :=
  ∀ {leftState rightState leftOut rightOut : State}
    {leftResult rightResult : Expr},
    State.WhnfAlpha left right leftState rightState →
    ClosedExprAlphaUnder left right leftInput rightInput →
    Inner.whnf' leftInput methods leftContext leftState =
      .ok (leftResult, leftOut) →
    Inner.whnf' rightInput methods rightContext rightState =
      .ok (rightResult, rightOut) →
    WhnfSuccessAlpha left right leftResult rightResult leftOut rightOut

/-- Once the transparent recursive loop has been proved alpha-equivariant,
synchronized cache lookup and insertion lift it to `Inner.whnf'`. -/
theorem WhnfLoopAlphaOn.inner
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (HleftForm : Expr.WhnfCacheable leftInput)
    (HrightForm : Expr.WhnfCacheable rightInput)
    (Hloop : WhnfLoopAlphaOn methods leftContext rightContext left right
      leftInput rightInput
      (if leftContext.eagerReduce then leftContext.fuel.whnfEager
        else leftContext.fuel.whnf)) :
    InnerWhnfAlphaOn methods leftContext rightContext left right
      leftInput rightInput := by
  intro leftState rightState leftOut rightOut leftResult rightResult
    Hstates Hinput Hleft Hright
  have Hlookup := Hstates.whnfCache.getElem? Hcontexts.binders Hinput
  cases hleftCache : leftState.whnfCache[leftInput]? with
  | some leftCached =>
      rw [hleftCache] at Hlookup
      rcases Hlookup.some_left with
        ⟨rightCached, hrightCache, Hcached⟩
      rw [Inner.whnf'_cache_hit HleftForm hleftCache] at Hleft
      rw [Inner.whnf'_cache_hit HrightForm hrightCache] at Hright
      cases Hleft
      cases Hright
      exact ⟨Hcached, Hstates⟩
  | none =>
      have hrightCache : rightState.whnfCache[rightInput]? = Option.none :=
        Hstates.whnfCache.getElem?_none_iff Hcontexts.binders Hinput |>.mp
          hleftCache
      rcases Inner.whnf'_cache_miss_result HleftForm hleftCache Hleft with
        ⟨leftLoopState, HleftLoop, hleftOut⟩
      rcases Inner.whnf'_cache_miss_result HrightForm hrightCache Hright with
        ⟨rightLoopState, HrightLoop, hrightOut⟩
      have hloopFuel :
          (if rightContext.eagerReduce then rightContext.fuel.whnfEager
            else rightContext.fuel.whnf) =
          (if leftContext.eagerReduce then leftContext.fuel.whnfEager
            else leftContext.fuel.whnf) := by
        rw [← Hcontexts.eagerReduce_eq, ← Hcontexts.fuel_eq]
      rw [hloopFuel] at HrightLoop
      have HloopResult := Hloop Hstates Hinput HleftLoop HrightLoop
      subst leftOut
      subst rightOut
      exact ⟨HloopResult.result,
        HloopResult.state.insertWhnf Hinput HloopResult.result⟩

/-- The cache-free immediate branches of public WHNF preserve both the
closed alpha result and the paired state. -/
theorem whnf_immediate_success_alpha
    (Hstates : State.WhnfAlpha left right leftState rightState)
    (Hinput : ClosedExprAlphaUnder left right leftInput rightInput)
    (HleftImmediate : Expr.WhnfImmediate leftInput)
    (HrightImmediate : Expr.WhnfImmediate rightInput)
    (Hleft : whnf leftInput leftContext leftState =
      .ok (leftResult, leftOut))
    (Hright : whnf rightInput rightContext rightState =
      .ok (rightResult, rightOut)) :
    WhnfSuccessAlpha left right leftResult rightResult leftOut rightOut := by
  rcases whnf_immediate_result_eq HleftImmediate leftContext leftState
      leftOut leftResult Hleft with ⟨hleftResult, hleftState⟩
  rcases whnf_immediate_result_eq HrightImmediate rightContext rightState
      rightOut rightResult Hright with ⟨hrightResult, hrightState⟩
  subst leftResult
  subst rightResult
  subst leftOut
  subst rightOut
  exact ⟨Hinput, Hstates⟩

/-- A cache hit on one side of a paired state forces the paired cache hit on
the other side, and the two public WHNF results are the retained alpha pair. -/
theorem whnf_cache_hit_success_alpha
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (Hstates : State.WhnfAlpha left right leftState rightState)
    (Hinput : ClosedExprAlphaUnder left right leftInput rightInput)
    (HleftForm : Expr.WhnfCacheable leftInput)
    (HrightForm : Expr.WhnfCacheable rightInput)
    (hleftCache : leftState.whnfCache[leftInput]? = some leftCached)
    (Hleft : whnf leftInput leftContext leftState =
      .ok (leftResult, leftOut))
    (Hright : whnf rightInput rightContext rightState =
      .ok (rightResult, rightOut)) :
    WhnfSuccessAlpha left right leftResult rightResult leftOut rightOut := by
  have Hlookup := Hstates.whnfCache.getElem? Hcontexts.binders Hinput
  rw [hleftCache] at Hlookup
  rcases Hlookup.some_left with
    ⟨rightCached, hrightCache, Hcached⟩
  rcases whnf_cache_hit_result_eq HleftForm hleftCache Hleft with
    ⟨hleftResult, hleftState⟩
  rcases whnf_cache_hit_result_eq HrightForm hrightCache Hright with
    ⟨hrightResult, hrightState⟩
  subst leftResult
  subst rightResult
  subst leftOut
  subst rightOut
  exact ⟨Hcached, Hstates⟩

/-- Public WHNF is alpha-equivariant on one fixed pair of inputs, including
the paired state relation required by recursive cache use. -/
def WhnfAlphaOn
    (leftContext rightContext : Context) (left right : List FVarId)
    (leftInput rightInput : Expr) : Prop :=
  ∀ {leftState rightState leftOut rightOut : State}
    {leftResult rightResult : Expr},
    State.WhnfAlpha left right leftState rightState →
    ClosedExprAlphaUnder left right leftInput rightInput →
    whnf leftInput leftContext leftState = .ok (leftResult, leftOut) →
    whnf rightInput rightContext rightState = .ok (rightResult, rightOut) →
    WhnfSuccessAlpha left right leftResult rightResult leftOut rightOut

/-- Metadata erasure delegates to the strictly smaller body execution. -/
theorem WhnfAlphaOn.mdata
    (Hbody : WhnfAlphaOn leftContext rightContext left right
      leftBody rightBody) :
    WhnfAlphaOn leftContext rightContext left right
      (.mdata leftData leftBody) (.mdata rightData rightBody) := by
  intro leftState rightState leftOut rightOut leftResult rightResult
    Hstates Hinput Hleft Hright
  rw [whnf_mdata_run_eq] at Hleft Hright
  apply Hbody Hstates
  · exact {
      left_closed := Hinput.left_closed
      right_closed := Hinput.right_closed
      alpha := Hinput.alpha.mdata_body }
  · exact Hleft
  · exact Hright

/-- A paired generated free variable is an operational identity in the
all-`cdecl` contexts used by inductive processing. -/
theorem Context.OrderedBinderRenaming.whnfAlphaOnFVarAt
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (i : Nat) (hi : i < left.length) :
    WhnfAlphaOn leftContext rightContext left right
      (.fvar (left[i]'hi))
      (.fvar (right[i]'(H.binders.length_eq ▸ hi))) := by
  intro leftState rightState leftOut rightOut leftResult rightResult
    Hstates Hinput Hleft Hright
  rcases whnf_fvar_result_eq leftContext leftState leftOut
      H.left_lctx_wf H.left_only_cdecls (left[i]'hi) leftResult Hleft with
    ⟨hleftResult, hleftState⟩
  rcases whnf_fvar_result_eq rightContext rightState rightOut
      H.right_lctx_wf H.right_only_cdecls
      (right[i]'(H.binders.length_eq ▸ hi)) rightResult Hright with
    ⟨hrightResult, hrightState⟩
  subst leftResult
  subst rightResult
  subst leftOut
  subst rightOut
  exact ⟨Hinput, Hstates⟩

/-- A literally shared outer free variable is also an operational identity
on both sides of an ordered binder renaming. -/
theorem Context.OrderedBinderRenaming.whnfAlphaOnSharedFVar
    (H : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (hfv : shared fv) :
    WhnfAlphaOn leftContext rightContext left right (.fvar fv) (.fvar fv) := by
  intro leftState rightState leftOut rightOut leftResult rightResult
    Hstates Hinput Hleft Hright
  rcases whnf_fvar_result_eq leftContext leftState leftOut
      H.left_lctx_wf H.left_only_cdecls fv leftResult Hleft with
    ⟨hleftResult, hleftState⟩
  rcases whnf_fvar_result_eq rightContext rightState rightOut
      H.right_lctx_wf H.right_only_cdecls fv rightResult Hright with
    ⟨hrightResult, hrightState⟩
  subst leftResult
  subst rightResult
  subst leftOut
  subst rightOut
  exact ⟨Hinput, Hstates⟩

/-- Simultaneous closure does not change whether an expression is an
application. -/
private theorem Expr.abstractList_isApp_alpha
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).isApp = e.isApp := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Expr.abstractList]
      rw [ih]
      cases e <;> simp only [Expr.abstract1, Expr.isApp]
      all_goals try rfl
      rename_i id
      by_cases h : (fv == id) = true <;> simp [h, Expr.isApp]

theorem ExprAlphaUnder.isApp_eq
    (H : ExprAlphaUnder left right leftExpr rightExpr) :
    leftExpr.isApp = rightExpr.isApp := by
  have hclosed := congrArg Expr.isApp H
  simpa only [Expr.abstractList_isApp_alpha] using hclosed

theorem ClosedExprAlphaUnder.const_eq_iff
    (Hbinders : LocalContext.OrderedBinderRenaming
      leftContext rightContext left right)
    (H : ClosedExprAlphaUnder left right leftExpr rightExpr)
    (name : Name) (levels : List Level) :
    leftExpr = .const name levels ↔ rightExpr = .const name levels := by
  let Hconst : ClosedExprAlphaUnder left right
      (.const name levels) (.const name levels) :=
    ⟨by simp [Closed], by simp [Closed], by
      unfold ExprAlphaUnder
      rw [Expr.abstractList_const_alpha,
        Expr.abstractList_const_alpha]⟩
  exact H.eq_iff Hbinders Hconst

private def Expr.constData? : Expr → Option (Name × List Level)
  | .const name levels => some (name, levels)
  | _ => none

private theorem ClosedExprAlphaUnder.constData?_eq
    (Hbinders : LocalContext.OrderedBinderRenaming
      leftContext rightContext left right)
    (H : ClosedExprAlphaUnder left right leftExpr rightExpr) :
    Expr.constData? leftExpr = Expr.constData? rightExpr := by
  cases leftExpr with
  | const name levels =>
      have hright := (H.const_eq_iff Hbinders name levels).mp rfl
      subst rightExpr
      rfl
  | bvar | fvar | mvar | sort | app | lam | forallE | letE | lit | mdata
    | proj =>
      cases rightExpr <;> try rfl
      rename_i name levels
      have hleft := (H.const_eq_iff Hbinders name levels).mpr rfl
      contradiction

/-- Native-reduction dispatch observes only application shape, fixed
reduction-marker constants, and the name of a constant argument.  All three
observations are invariant on paired closed alpha expressions. -/
theorem Inner.reduceNative_eq_of_closed_alpha
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (Hinput : ClosedExprAlphaUnder left right leftInput rightInput)
    (HleftForm : Expr.WhnfCacheable leftInput)
    (HrightForm : Expr.WhnfCacheable rightInput) :
    Inner.reduceNative leftContext.env leftInput =
      Inner.reduceNative rightContext.env rightInput := by
  cases HleftForm with
  | lam =>
      cases HrightForm with
      | app =>
          have happ := Hinput.alpha.isApp_eq
          simp [Expr.isApp] at happ
      | lam | const | letE | proj => rfl
  | const =>
      cases HrightForm with
      | app =>
          have happ := Hinput.alpha.isApp_eq
          simp [Expr.isApp] at happ
      | lam | const | letE | proj => rfl
  | letE =>
      cases HrightForm with
      | app =>
          have happ := Hinput.alpha.isApp_eq
          simp [Expr.isApp] at happ
      | lam | const | letE | proj => rfl
  | proj =>
      cases HrightForm with
      | app =>
          have happ := Hinput.alpha.isApp_eq
          simp [Expr.isApp] at happ
      | lam | const | letE | proj => rfl
  | @app leftFn leftArg =>
      cases HrightForm with
      | lam | const | letE | proj =>
          have happ := Hinput.alpha.isApp_eq
          simp [Expr.isApp] at happ
      | @app rightFn rightArg =>
          have Hparts := Hinput.alpha.app_parts
          rcases Hinput.left_closed with ⟨hleftFnClosed, hleftArgClosed⟩
          rcases Hinput.right_closed with ⟨hrightFnClosed,
            hrightArgClosed⟩
          let Hfn : ClosedExprAlphaUnder left right leftFn rightFn :=
            ⟨hleftFnClosed, hrightFnClosed, Hparts.1⟩
          let Harg : ClosedExprAlphaUnder left right leftArg rightArg :=
            ⟨hleftArgClosed, hrightArgClosed, Hparts.2⟩
          let HreduceBool : ClosedExprAlphaUnder left right
              (.const ``reduceBool []) (.const ``reduceBool []) :=
            ⟨by simp [Closed], by simp [Closed], by
              unfold ExprAlphaUnder
              rw [Expr.abstractList_const_alpha,
                Expr.abstractList_const_alpha]⟩
          let HreduceNat : ClosedExprAlphaUnder left right
              (.const ``Lean.reduceNat []) (.const ``Lean.reduceNat []) :=
            ⟨by simp [Closed], by simp [Closed], by
              unfold ExprAlphaUnder
              rw [Expr.abstractList_const_alpha,
                Expr.abstractList_const_alpha]⟩
          have hbool := Hfn.beq_eq Hcontexts.binders HreduceBool
          have hnat := Hfn.beq_eq Hcontexts.binders HreduceNat
          have hargConst := ClosedExprAlphaUnder.constData?_eq
            Hcontexts.binders Harg
          cases leftArg <;> cases rightArg <;>
            simp_all [Inner.reduceNative, Expr.constData?]

/-- Closing a free-variable spine cannot change a literal payload. -/
private theorem Expr.rawNatLit?_abstractList
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).rawNatLit? = e.rawNatLit? := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Expr.abstractList]
      rw [ih]
      cases e <;> simp [Expr.abstract1, Expr.rawNatLit?]
      rename_i id
      by_cases h : (fv == id) = true <;>
        simp [h, Expr.rawNatLit?]

/-- Reading an extended natural literal is invariant under closing paired
fresh-variable spines.  A successful read forces both expressions to be the
same closed literal (including the special `Nat.zero` constant). -/
theorem rawNatLitExt?_eq_of_closed_alpha
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (H : ClosedExprAlphaUnder left right leftExpr rightExpr) :
    Inner.rawNatLitExt? leftExpr = Inner.rawNatLitExt? rightExpr := by
  let Hzero : ClosedExprAlphaUnder left right Expr.natZero Expr.natZero :=
    ⟨by simp [Expr.natZero, Closed], by simp [Expr.natZero, Closed], by
      simp [ExprAlphaUnder, Expr.natZero,
        Expr.abstractList_const_alpha]⟩
  have hzero := H.beq_eq Hcontexts.binders Hzero
  have hlit := congrArg Expr.rawNatLit? H.alpha
  simp only [Expr.rawNatLit?_abstractList] at hlit
  simp [Inner.rawNatLitExt?, hzero, hlit]

/-- Successful paired reductions returning optional expressions preserve both
the optional result and the WHNF-relevant checker state. -/
structure OptionalExprSuccessAlpha
    (left right : List FVarId)
    (leftResult rightResult : Option Expr)
    (leftState rightState : State) : Prop where
  result : ClosedExprOptionAlphaUnder left right leftResult rightResult
  state : State.WhnfAlpha left right leftState rightState

/-- Alpha-equivariance required of the lower-fuel WHNF method while proving
one structural reduction step.  For `Methods.withFuel (n + 1)` this is
supplied by the induction hypothesis for fuel `n`, rather than by a caller. -/
def MethodWhnfAlphaOn
    (methods : Methods) (leftContext rightContext : Context)
    (left right : List FVarId) (leftInput rightInput : Expr) : Prop :=
  ∀ {leftState rightState leftOut rightOut : State}
    {leftResult rightResult : Expr},
    State.WhnfAlpha left right leftState rightState →
    ClosedExprAlphaUnder left right leftInput rightInput →
    Inner.whnf leftInput methods leftContext leftState =
      .ok (leftResult, leftOut) →
    Inner.whnf rightInput methods rightContext rightState =
      .ok (rightResult, rightOut) →
    WhnfSuccessAlpha left right leftResult rightResult leftOut rightOut

/-- Literal construction is insensitive to the names of the paired binder
spines. -/
private theorem Expr.abstractList_lit_alpha
    (fvars : List FVarId) (k : Nat) :
    (Expr.lit value).abstractList fvars k = .lit value := by
  induction fvars with
  | nil => rfl
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      exact ih

def ClosedExprAlphaUnder.literal (value : Literal) :
    ClosedExprAlphaUnder left right (.lit value) (.lit value) where
  left_closed := by simp [Closed]
  right_closed := by simp [Closed]
  alpha := by
    simp [ExprAlphaUnder, Expr.abstractList_lit_alpha]

/-- A constant is closed-alpha under any two binder spines. -/
def ClosedExprAlphaUnder.constant (name : Name) (levels : List Level) :
    ClosedExprAlphaUnder left right (.const name levels) (.const name levels) where
  left_closed := by simp [Closed]
  right_closed := by simp [Closed]
  alpha := by
    simp [ExprAlphaUnder, Expr.abstractList_const_alpha]

/-- Reflected booleans are constants and hence independent of binder names. -/
def ClosedExprAlphaUnder.reflectedBool (value : Bool) :
    ClosedExprAlphaUnder left right (toExpr value) (toExpr value) := by
  cases value
  · exact .constant ``Bool.false []
  · exact .constant ``Bool.true []

/-- Expose the two public-WHNF calls performed by binary natural reduction as
an `Except` computation over explicit states. -/
theorem Inner.reduceBinNatOp_run_eq
    (f : Nat → Nat → Nat) (a b : Expr)
    (methods : Methods) (context : Context) (state : State) :
    Inner.reduceBinNatOp f a b methods context state = do
      let (aResult, aState) ← Inner.whnf a methods context state
      let some v₁ := Inner.rawNatLitExt? aResult |
        return (Option.none, aState)
      let (bResult, bState) ← Inner.whnf b methods context aState
      let some v₂ := Inner.rawNatLitExt? bResult |
        return (Option.none, bState)
      return (some (.lit (.natVal (f v₁ v₂))), bState) := by
  simp only [Inner.reduceBinNatOp, Inner.whnf, Bind.bind, Monad.toBind,
    ReaderT.instMonad, ReaderT.bind, StateT.instMonad, StateT.bind,
    Pure.pure, Applicative.toPure, Monad.toApplicative,
    ReaderT.pure, StateT.pure]
  cases ha : methods.whnf a context state with
  | error err => rfl
  | ok pair =>
      rcases pair with ⟨aResult, aState⟩
      simp only [ha, Except.bind]
      cases hva : Inner.rawNatLitExt? aResult with
      | none =>
          simp [hva, ReaderT.pure, StateT.pure,
            Pure.pure, Applicative.toPure, Monad.toApplicative]
      | some v₁ =>
          simp only [hva]
          cases hb : methods.whnf b context aState with
          | error err =>
              simp [hb, Inner.whnf, Bind.bind, Monad.toBind,
                ReaderT.bind, StateT.bind, Except.bind]
          | ok pair =>
              rcases pair with ⟨bResult, bState⟩
              simp only [hb, Except.bind]
              cases hvb : Inner.rawNatLitExt? bResult <;>
                simp [hvb, hb, Inner.whnf, Bind.bind, Monad.toBind,
                  ReaderT.bind, StateT.bind,
                  ReaderT.pure, StateT.pure, Pure.pure,
                  Applicative.toPure, Monad.toApplicative, Except.bind]

/-- Binary natural-literal reduction preserves alpha equality when its two
lower-fuel operand reductions do. -/
theorem Inner.reduceBinNatOp_success_alpha
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (Hstates : State.WhnfAlpha left right leftState rightState)
    (Ha : ClosedExprAlphaUnder left right leftA rightA)
    (Hb : ClosedExprAlphaUnder left right leftB rightB)
    (HwhnfA : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftA rightA)
    (HwhnfB : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftB rightB)
    (Hleft : Inner.reduceBinNatOp f leftA leftB methods leftContext
      leftState = .ok (leftResult, leftOut))
    (Hright : Inner.reduceBinNatOp f rightA rightB methods rightContext
      rightState = .ok (rightResult, rightOut)) :
    OptionalExprSuccessAlpha left right leftResult rightResult
      leftOut rightOut := by
  rw [Inner.reduceBinNatOp_run_eq] at Hleft Hright
  cases hla : Inner.whnf leftA methods leftContext leftState with
  | error err =>
      simp [hla, Bind.bind, Monad.toBind, Except.instMonad,
        Except.bind] at Hleft
  | ok leftPair =>
    rcases leftPair with ⟨leftAResult, leftAState⟩
    cases hra : Inner.whnf rightA methods rightContext rightState with
    | error err =>
      simp [hra, Bind.bind, Monad.toBind, Except.instMonad,
        Except.bind] at Hright
    | ok rightPair =>
      rcases rightPair with ⟨rightAResult, rightAState⟩
      have HA := HwhnfA Hstates Ha hla hra
      have hrawA := rawNatLitExt?_eq_of_closed_alpha Hcontexts HA.result
      cases hva : Inner.rawNatLitExt? leftAResult with
      | none =>
          have hvra : Inner.rawNatLitExt? rightAResult = none := by
            rw [← hrawA, hva]
          simp [hla, hra, hva, hvra, Bind.bind, Monad.toBind,
            Except.instMonad, Except.bind, Pure.pure, Applicative.toPure,
            Monad.toApplicative, Except.pure] at Hleft Hright
          rcases Hleft with ⟨hleftResult, hleftState⟩
          rcases Hright with ⟨hrightResult, hrightState⟩
          subst leftResult
          subst leftOut
          subst rightResult
          subst rightOut
          exact ⟨.none, HA.state⟩
      | some v₁ =>
          have hvra : Inner.rawNatLitExt? rightAResult = some v₁ := by
            rw [← hrawA, hva]
          cases hlb : Inner.whnf leftB methods leftContext leftAState with
          | error err =>
            simp [hla, hva, hlb, Bind.bind, Monad.toBind,
              Except.instMonad, Except.bind] at Hleft
          | ok leftPair =>
            rcases leftPair with ⟨leftBResult, leftBState⟩
            cases hrb : Inner.whnf rightB methods rightContext rightAState with
            | error err =>
              simp [hra, hvra, hrb, Bind.bind, Monad.toBind,
                Except.instMonad, Except.bind] at Hright
            | ok rightPair =>
              rcases rightPair with ⟨rightBResult, rightBState⟩
              have HB := HwhnfB HA.state Hb hlb hrb
              have hrawB := rawNatLitExt?_eq_of_closed_alpha Hcontexts HB.result
              cases hvb : Inner.rawNatLitExt? leftBResult with
              | none =>
                  have hvrb : Inner.rawNatLitExt? rightBResult = none := by
                    rw [← hrawB, hvb]
                  simp [hla, hra, hva, hvra, hlb, hrb, hvb, hvrb,
                    Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
                    Pure.pure, Applicative.toPure, Monad.toApplicative,
                    Except.pure] at Hleft Hright
                  rcases Hleft with ⟨hleftResult, hleftState⟩
                  rcases Hright with ⟨hrightResult, hrightState⟩
                  subst leftResult
                  subst leftOut
                  subst rightResult
                  subst rightOut
                  exact ⟨.none, HB.state⟩
              | some v₂ =>
                  have hvrb : Inner.rawNatLitExt? rightBResult = some v₂ := by
                    rw [← hrawB, hvb]
                  simp [hla, hra, hva, hvra, hlb, hrb, hvb, hvrb,
                    Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
                    Pure.pure, Applicative.toPure, Monad.toApplicative,
                    Except.pure] at Hleft Hright
                  rcases Hleft with ⟨hleftResult, hleftState⟩
                  rcases Hright with ⟨hrightResult, hrightState⟩
                  subst leftResult
                  subst leftOut
                  subst rightResult
                  subst rightOut
                  exact ⟨.some (.literal (.natVal (f v₁ v₂))), HB.state⟩

/-- Proof-only normal form for reductions which first WHNF two operands and
then compute an optional expression from the two natural literals. -/
def Inner.reduceTwoNatRun
    (finish : Nat → Nat → Option Expr) (a b : Expr)
    (methods : Methods) (context : Context) (state : State) :
    Except Kernel.Exception (Option Expr × State) := do
  let (aResult, aState) ← Inner.whnf a methods context state
  let some v₁ := Inner.rawNatLitExt? aResult |
    return (Option.none, aState)
  let (bResult, bState) ← Inner.whnf b methods context aState
  let some v₂ := Inner.rawNatLitExt? bResult |
    return (Option.none, bState)
  return (finish v₁ v₂, bState)

/-- The common two-operand execution skeleton preserves alpha and state when
its pure finishing operation produces paired closed-alpha optional results. -/
theorem Inner.reduceTwoNatRun_success_alpha
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (Hstates : State.WhnfAlpha left right leftState rightState)
    (Ha : ClosedExprAlphaUnder left right leftA rightA)
    (Hb : ClosedExprAlphaUnder left right leftB rightB)
    (HwhnfA : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftA rightA)
    (HwhnfB : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftB rightB)
    (Hfinish : ∀ v₁ v₂,
      ClosedExprOptionAlphaUnder left right
        (finish v₁ v₂) (finish v₁ v₂))
    (Hleft : Inner.reduceTwoNatRun finish leftA leftB methods leftContext
      leftState = .ok (leftResult, leftOut))
    (Hright : Inner.reduceTwoNatRun finish rightA rightB methods rightContext
      rightState = .ok (rightResult, rightOut)) :
    OptionalExprSuccessAlpha left right leftResult rightResult
      leftOut rightOut := by
  unfold Inner.reduceTwoNatRun at Hleft Hright
  cases hla : Inner.whnf leftA methods leftContext leftState with
  | error err =>
      simp [hla, Bind.bind, Monad.toBind, Except.instMonad,
        Except.bind] at Hleft
  | ok leftPair =>
    rcases leftPair with ⟨leftAResult, leftAState⟩
    cases hra : Inner.whnf rightA methods rightContext rightState with
    | error err =>
      simp [hra, Bind.bind, Monad.toBind, Except.instMonad,
        Except.bind] at Hright
    | ok rightPair =>
      rcases rightPair with ⟨rightAResult, rightAState⟩
      have HA := HwhnfA Hstates Ha hla hra
      have hrawA := rawNatLitExt?_eq_of_closed_alpha Hcontexts HA.result
      cases hva : Inner.rawNatLitExt? leftAResult with
      | none =>
          have hvra : Inner.rawNatLitExt? rightAResult = none := by
            rw [← hrawA, hva]
          simp [hla, hra, hva, hvra, Bind.bind, Monad.toBind,
            Except.instMonad, Except.bind, Pure.pure, Applicative.toPure,
            Monad.toApplicative, Except.pure] at Hleft Hright
          rcases Hleft with ⟨hleftResult, hleftState⟩
          rcases Hright with ⟨hrightResult, hrightState⟩
          subst leftResult
          subst leftOut
          subst rightResult
          subst rightOut
          exact ⟨.none, HA.state⟩
      | some v₁ =>
          have hvra : Inner.rawNatLitExt? rightAResult = some v₁ := by
            rw [← hrawA, hva]
          cases hlb : Inner.whnf leftB methods leftContext leftAState with
          | error err =>
            simp [hla, hva, hlb, Bind.bind, Monad.toBind,
              Except.instMonad, Except.bind] at Hleft
          | ok leftPair =>
            rcases leftPair with ⟨leftBResult, leftBState⟩
            cases hrb : Inner.whnf rightB methods rightContext rightAState with
            | error err =>
              simp [hra, hvra, hrb, Bind.bind, Monad.toBind,
                Except.instMonad, Except.bind] at Hright
            | ok rightPair =>
              rcases rightPair with ⟨rightBResult, rightBState⟩
              have HB := HwhnfB HA.state Hb hlb hrb
              have hrawB := rawNatLitExt?_eq_of_closed_alpha Hcontexts HB.result
              cases hvb : Inner.rawNatLitExt? leftBResult with
              | none =>
                  have hvrb : Inner.rawNatLitExt? rightBResult = none := by
                    rw [← hrawB, hvb]
                  simp [hla, hra, hva, hvra, hlb, hrb, hvb, hvrb,
                    Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
                    Pure.pure, Applicative.toPure, Monad.toApplicative,
                    Except.pure] at Hleft Hright
                  rcases Hleft with ⟨hleftResult, hleftState⟩
                  rcases Hright with ⟨hrightResult, hrightState⟩
                  subst leftResult
                  subst leftOut
                  subst rightResult
                  subst rightOut
                  exact ⟨.none, HB.state⟩
              | some v₂ =>
                  have hvrb : Inner.rawNatLitExt? rightBResult = some v₂ := by
                    rw [← hrawB, hvb]
                  simp [hla, hra, hva, hvra, hlb, hrb, hvb, hvrb,
                    Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
                    Pure.pure, Applicative.toPure, Monad.toApplicative,
                    Except.pure] at Hleft Hright
                  rcases Hleft with ⟨hleftResult, hleftState⟩
                  rcases Hright with ⟨hrightResult, hrightState⟩
                  subst leftResult
                  subst leftOut
                  subst rightResult
                  subst rightOut
                  exact ⟨Hfinish v₁ v₂, HB.state⟩

/-- `reducePow` has the common two-natural execution skeleton, with its
maximum-exponent guard entirely in the pure finishing step. -/
theorem Inner.reducePow_run_eq
    (a b : Expr) (methods : Methods) (context : Context) (state : State) :
    Inner.reducePow a b methods context state =
      Inner.reduceTwoNatRun
        (fun v₁ v₂ =>
          if v₂ > Inner.reducePowMaxExp then none
          else some (.lit (.natVal (Nat.pow v₁ v₂))))
        a b methods context state := by
  unfold Inner.reducePow Inner.reduceTwoNatRun
  simp only [Inner.whnf, Bind.bind, Monad.toBind,
    ReaderT.instMonad, ReaderT.bind, StateT.instMonad, StateT.bind,
    Pure.pure, Applicative.toPure, Monad.toApplicative,
    ReaderT.pure, StateT.pure]
  cases ha : methods.whnf a context state with
  | error err => rfl
  | ok pair =>
      rcases pair with ⟨aResult, aState⟩
      simp only [ha, Except.bind]
      cases hva : Inner.rawNatLitExt? aResult with
      | none =>
          simp [hva, ReaderT.pure, StateT.pure,
            Pure.pure, Applicative.toPure, Monad.toApplicative]
      | some v₁ =>
          simp only [hva]
          cases hb : methods.whnf b context aState with
          | error err =>
              simp [hb, Inner.whnf, Bind.bind, Monad.toBind,
                ReaderT.bind, StateT.bind, Except.bind]
          | ok pair =>
              rcases pair with ⟨bResult, bState⟩
              simp only [hb, Except.bind]
              cases hvb : Inner.rawNatLitExt? bResult with
              | none =>
                  simp [hvb, hb, Inner.whnf, Bind.bind, Monad.toBind,
                    ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
                    Pure.pure, Applicative.toPure, Monad.toApplicative,
                    Except.bind]
              | some v₂ =>
                  by_cases hmax : v₂ > Inner.reducePowMaxExp <;>
                    simp [hvb, hb, hmax, Inner.whnf, Bind.bind, Monad.toBind,
                      ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
                      Pure.pure, Applicative.toPure, Monad.toApplicative,
                      Except.bind]

/-- Power reduction preserves alpha equality and the paired state, including
the guarded `none` result for exponents beyond the executable limit. -/
theorem Inner.reducePow_success_alpha
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (Hstates : State.WhnfAlpha left right leftState rightState)
    (Ha : ClosedExprAlphaUnder left right leftA rightA)
    (Hb : ClosedExprAlphaUnder left right leftB rightB)
    (HwhnfA : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftA rightA)
    (HwhnfB : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftB rightB)
    (Hleft : Inner.reducePow leftA leftB methods leftContext leftState =
      .ok (leftResult, leftOut))
    (Hright : Inner.reducePow rightA rightB methods rightContext rightState =
      .ok (rightResult, rightOut)) :
    OptionalExprSuccessAlpha left right leftResult rightResult
      leftOut rightOut := by
  rw [Inner.reducePow_run_eq] at Hleft Hright
  apply Inner.reduceTwoNatRun_success_alpha Hcontexts Hstates Ha Hb
    HwhnfA HwhnfB _ Hleft Hright
  intro v₁ v₂
  by_cases hmax : v₂ > Inner.reducePowMaxExp
  · simpa [hmax] using
      (ClosedExprOptionAlphaUnder.none (left := left) (right := right))
  · simpa [hmax] using
      (ClosedExprOptionAlphaUnder.some
        (ClosedExprAlphaUnder.literal (left := left) (right := right)
          (.natVal (Nat.pow v₁ v₂))))

/-- `reduceBinNatPred` is the common two-natural execution skeleton followed
by construction of a reflected boolean constant. -/
theorem Inner.reduceBinNatPred_run_eq
    (f : Nat → Nat → Bool) (a b : Expr)
    (methods : Methods) (context : Context) (state : State) :
    Inner.reduceBinNatPred f a b methods context state =
      Inner.reduceTwoNatRun (fun v₁ v₂ => some (toExpr (f v₁ v₂)))
        a b methods context state := by
  unfold Inner.reduceBinNatPred Inner.reduceTwoNatRun
  simp only [Inner.whnf, Bind.bind, Monad.toBind,
    ReaderT.instMonad, ReaderT.bind, StateT.instMonad, StateT.bind,
    Pure.pure, Applicative.toPure, Monad.toApplicative,
    ReaderT.pure, StateT.pure]
  cases ha : methods.whnf a context state with
  | error err => rfl
  | ok pair =>
      rcases pair with ⟨aResult, aState⟩
      simp only [ha, Except.bind]
      cases hva : Inner.rawNatLitExt? aResult with
      | none =>
          simp [hva, ReaderT.pure, StateT.pure,
            Pure.pure, Applicative.toPure, Monad.toApplicative]
      | some v₁ =>
          simp only [hva]
          cases hb : methods.whnf b context aState with
          | error err =>
              simp [hb, Inner.whnf, Bind.bind, Monad.toBind,
                ReaderT.bind, StateT.bind, Except.bind]
          | ok pair =>
              rcases pair with ⟨bResult, bState⟩
              simp only [hb, Except.bind]
              cases hvb : Inner.rawNatLitExt? bResult <;>
                simp [hvb, hb, Inner.whnf, Bind.bind, Monad.toBind,
                  ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
                  Pure.pure, Applicative.toPure, Monad.toApplicative,
                  Except.bind]

/-- Binary natural predicates preserve alpha equality and paired state. -/
theorem Inner.reduceBinNatPred_success_alpha
    (Hcontexts : Context.OrderedBinderRenaming shared left right
      leftContext rightContext)
    (Hstates : State.WhnfAlpha left right leftState rightState)
    (Ha : ClosedExprAlphaUnder left right leftA rightA)
    (Hb : ClosedExprAlphaUnder left right leftB rightB)
    (HwhnfA : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftA rightA)
    (HwhnfB : MethodWhnfAlphaOn methods leftContext rightContext
      left right leftB rightB)
    (Hleft : Inner.reduceBinNatPred f leftA leftB methods leftContext
      leftState = .ok (leftResult, leftOut))
    (Hright : Inner.reduceBinNatPred f rightA rightB methods rightContext
      rightState = .ok (rightResult, rightOut)) :
    OptionalExprSuccessAlpha left right leftResult rightResult
      leftOut rightOut := by
  rw [Inner.reduceBinNatPred_run_eq] at Hleft Hright
  apply Inner.reduceTwoNatRun_success_alpha Hcontexts Hstates Ha Hb
    HwhnfA HwhnfB _ Hleft Hright
  intro v₁ v₂
  exact .some (.reflectedBool (f v₁ v₂))

/-- A proof-facing, bounded view of an application spine.  Three steps are
enough to distinguish exactly the arities `0`, `1`, `2`, and `> 2` used by
`reduceNat`, without exposing Lean's private `getAppNumArgsAux`. -/
def Expr.appSpineDepthUpTo : Nat → Expr → Nat
  | 0, _ => 0
  | fuel + 1, .app fn _ => 1 + Expr.appSpineDepthUpTo fuel fn
  | _ + 1, _ => 0

/-- Closing paired binder spines preserves every bounded observation of the
application spine. -/
theorem ExprAlphaUnder.appSpineDepthUpTo_eq
    (H : ExprAlphaUnder left right leftExpr rightExpr) (fuel : Nat) :
    Expr.appSpineDepthUpTo fuel leftExpr =
      Expr.appSpineDepthUpTo fuel rightExpr := by
  induction fuel generalizing leftExpr rightExpr with
  | zero => rfl
  | succ fuel ih =>
      cases leftExpr <;> cases rightExpr <;>
        simp only [Expr.appSpineDepthUpTo]
      case app.app =>
        have Hparts := ExprAlphaUnder.app_parts H
        exact congrArg (fun n => 1 + n) (ih Hparts.1)
      all_goals first
        | rfl
        | (exfalso
           have happ := ExprAlphaUnder.isApp_eq H
           simp only [Expr.isApp] at happ
           cases happ)

/-- The executable tail-recursive application counter is local under paired
binder abstraction.  Opening Lean's private helper here exposes only the
implementation being proved about; it adds no executable code or assumption. -/
private theorem ExprAlphaUnder.getAppNumArgsAux_eq
    (H : ExprAlphaUnder left right leftExpr rightExpr) (acc : Nat) :
    getAppNumArgsAux leftExpr acc = getAppNumArgsAux rightExpr acc := by
  induction leftExpr generalizing rightExpr acc with
  | app leftFn leftArg ihFn ihArg =>
      cases rightExpr with
      | app rightFn rightArg =>
          simp only [getAppNumArgsAux]
          exact ihFn H.app_parts.1 (acc + 1)
      | bvar | fvar | mvar | sort | const | lam | forallE | letE |
          lit | mdata | proj =>
          have happ := ExprAlphaUnder.isApp_eq H
          simp only [Expr.isApp] at happ
          cases happ
  | bvar | fvar | mvar | sort | const | lam | forallE | letE |
      lit | mdata | proj =>
      cases rightExpr <;> simp only [getAppNumArgsAux]
      all_goals try rfl
      all_goals
        have happ := ExprAlphaUnder.isApp_eq H
        simp only [Expr.isApp] at happ
        cases happ

/-- Paired alpha expressions have exactly the same executable application
arity. -/
theorem ExprAlphaUnder.getAppNumArgs_eq
    (H : ExprAlphaUnder left right leftExpr rightExpr) :
    leftExpr.getAppNumArgs = rightExpr.getAppNumArgs := by
  unfold Expr.getAppNumArgs
  exact H.getAppNumArgsAux_eq 0

end TypeChecker
end Lean4Lean
