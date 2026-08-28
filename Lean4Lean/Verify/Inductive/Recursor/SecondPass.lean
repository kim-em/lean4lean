import Lean4Lean.Verify.Inductive.Recursor.Rules

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Semantic evidence retained by one successful recursive-call blueprint
producer.  The first pass does not yet know the completed mutual minor array,
so the certificate is deliberately polymorphic in that array and in the
generated recursor levels.  Instantiation is nevertheless exact: its value is
the executable `RecCallBlueprint.build`, not a replayed call. -/
structure RecInfoCallBlueprintSemanticOrigin
    (stats : AddInductive.InductiveStats)
    (motives : Array Expr)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams) (rootScope : FVarId → Prop)
    (decl : VInductDecl) (depth : Nat) (field : Expr)
    (call : AddInductive.RecCallBlueprint) : Prop where
  semantic : ∀ (indTypes : Array InductiveType) (minors : Array Expr)
      (lvls : List Level),
    ∃ S : SemanticBoundGeneratedRecursiveCall indTypes stats
        motives minors lvls R decl depth field
        (call.build indTypes stats motives minors lvls),
      S.rootScope = rootScope ∧
        Nonempty S.ProducerMotiveApplication

/-- Array alignment for the semantic call certificates emitted by
`loopUBlueprints`.  Entry `j` is rooted after exactly the `j` earlier
hypotheses installed by that same loop, hence its validation depth is
`depth + j`. -/
structure RecInfoHypothesisCallSemanticOrigins
    {recLparams : List Name}
    (Rroot : RecursorContextWF fieldRoot recLparams)
    (decl : VInductDecl) (depth : Nat)
    (stats : AddInductive.InductiveStats) (motives : Array Expr)
    (rootScope : FVarId → Prop)
    (fields hypotheses : Array Expr)
    (calls : Array AddInductive.RecCallBlueprint) : Prop where
  size_eq : calls.size = hypotheses.size
  entry : ∀ j (hj : j < hypotheses.size),
    ∃ originRoot,
      ∃ Rorigin : RecursorContextWF originRoot recLparams,
        ∃ priorHypotheses : Array Expr,
          ∃ _ : RecursorRecentBoundFVarArray Rroot Rorigin priorHypotheses,
            priorHypotheses.size = j ∧
              Nonempty (RecInfoCallBlueprintSemanticOrigin stats motives
                Rorigin rootScope decl (depth + j) fields[j]! calls[j]!)

theorem RecInfoHypothesisCallSemanticOrigins.empty
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (decl : VInductDecl) (depth : Nat)
    (stats : AddInductive.InductiveStats) (motives : Array Expr)
    (rootScope : FVarId → Prop)
    (fields : Array Expr) :
    RecInfoHypothesisCallSemanticOrigins R decl depth stats motives rootScope
      fields #[] #[] where
  size_eq := rfl
  entry j hj := by simp at hj

theorem RecInfoHypothesisCallSemanticOrigins.pushCurrent
    {recLparams : List Name}
    {Rroot : RecursorContextWF fieldRoot recLparams}
    {R : RecursorContextWF c recLparams}
    {calls : Array AddInductive.RecCallBlueprint}
    (Hsem : RecInfoHypothesisCallSemanticOrigins Rroot decl depth stats
      motives rootScope fields hypotheses calls)
    (hnext : hypotheses.size < fields.size)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R hypotheses)
    (call : AddInductive.RecCallBlueprint)
    (S : RecInfoCallBlueprintSemanticOrigin stats motives R rootScope decl
      (depth + hypotheses.size) fields[hypotheses.size]! call) :
    RecInfoHypothesisCallSemanticOrigins Rroot decl depth stats motives rootScope
      fields (hypotheses.push (.fvar ⟨c.ngen.curr⟩)) (calls.push call) := by
  refine {
    size_eq := by simpa using congrArg Nat.succ Hsem.size_eq
    entry := ?_ }
  intro j hj
  by_cases hlast : j = hypotheses.size
  · subst j
    have hcall : (calls.push call)[hypotheses.size]! = call := by
      rw [show hypotheses.size = calls.size from Hsem.size_eq.symm]
      simp
    rw [hcall]
    exact ⟨c, R, hypotheses, Hrecent, rfl, ⟨S⟩⟩
  · have hjOld : j < hypotheses.size := by
      have : j < hypotheses.size + 1 := by simpa using hj
      omega
    rcases Hsem.entry j hjOld with
      ⟨originRoot, Rorigin, priorHypotheses, Hprior, hpriorSize, S⟩
    have hjCalls : j < calls.size := by rw [Hsem.size_eq]; exact hjOld
    have hcall : (calls.push call)[j]! = calls[j]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos (by simp; omega), dif_pos hjCalls]
      exact Array.getElem_push_lt hjCalls
    rw [hcall]
    exact ⟨originRoot, Rorigin, priorHypotheses, Hprior,
      hpriorSize, S⟩

/-- Field-traversal semantics retained at the exact producer contexts. -/
structure RecInfoRuleFieldSemanticSource
    {recLparams : List Name}
    (Rambient : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (S : RecInfoMinorTypeShape) where
  traversal : RecInfoMinorTraversalShape
  traversal_eq : S.traversal = some traversal
  traversal_constructor : traversal.constructor = S.constructor
  traversal_fields : traversal.fields = S.fields
  traversal_recursiveFields : traversal.recursiveFields = S.recursiveFields
  traversal_stats : traversal.stats = stats
  rootWF : RecursorContextWF traversal.rootContext recLparams
  terminalWF : RecursorContextWF traversal.terminalContext recLparams
  parameterDepth : Nat
  parameterSuffix : RecursorParameterContextSuffix rootWF stats parameterDepth
  terminalExtension : RecursorContextExtension terminalWF Rambient
  fieldsRecent : RecursorRecentBoundFVarArray rootWF terminalWF S.fields
  parameterTarget : VExpr
  parameterTail_params : traversal.parameterTail.FVarsIn
    (· ∈ ExprArrayFVarIds stats.params)
  parameterTranslation : TrExprS rootWF.venv recLparams rootWF.mlctx.vlctx
    traversal.parameterTail parameterTarget
  parameterType : rootWF.venv.IsType recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
  fieldOpening : ConstructorFieldOpening traversal.parameterTail
    traversal.terminal S.fields
  fieldParameterUp : IsFVarUpSet (fun fv => fv ∈ fieldsRecent.fvars ∨
    fv ∈ ExprArrayFVarIds stats.params) terminalWF.mlctx.vlctx
  terminalTarget : VExpr
  terminalTranslation : TrExprS terminalWF.venv recLparams
    terminalWF.mlctx.vlctx traversal.terminal terminalTarget
  terminalType : terminalWF.venv.IsType recLparams.length
    terminalWF.mlctx.vlctx.toCtx terminalTarget
  constructorApplication : RecursorConstructorApplicationAt terminalWF stats
    traversal.constructor traversal.terminal S.fields terminalTarget
  fieldTargetDefEq : rootWF.venv.IsDefEqU recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
      (terminalWF.mlctx.mkForall' S.fields.size fieldsRecent.size_le
        terminalTarget)

def RecInfoRuleFieldSemanticSource.mono
    (F : RecInfoRuleFieldSemanticSource R stats S)
    (E : RecursorContextExtension R R') :
    RecInfoRuleFieldSemanticSource R' stats S :=
  { F with terminalExtension := F.terminalExtension.trans E }

/-- Producer-rooted lookup of the motive binder and its canonical telescope
for every member of a completed mutual block.  This package is constructed
from first-pass bindings, origins, shapes, and telescopes; consumers supply
only the later context and the inductive application already validated by the
checker. -/
structure RecInfoMotiveTelescopeLookup
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) : Prop where
  evidence : ∀ target (htarget : target < recInfos.size)
      {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      (Hext : RecursorContextExtension Rroot Rcurrent)
      {depth : Nat} {exposedType : Expr} {syntaxTarget : VExpr},
    TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
    Rcurrent.venv.IsType recLparams.length Rcurrent.mlctx.vlctx.toCtx
        syntaxTarget →
    RecursorValidatedIndAppAt Rcurrent.venv recLparams
        Rcurrent.mlctx.vlctx stats decl depth exposedType syntaxTarget target →
    ∃ binding : RecursorMotiveBinding Rcurrent recInfos[target]! elimLevel,
      Nonempty (RecursorMotiveTelescopeEvidence Rcurrent stats
        recInfos[target]! binding exposedType syntaxTarget)

def RecInfoMotiveTelescopeLookup.of
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (T : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoTypeOrigins root recInfos)
    (Hshapes : RecInfoMotiveTypeShapes root recInfos Horigins.motiveTypes
      elimLevel) :
    RecInfoMotiveTelescopeLookup Rroot stats decl recInfos elimLevel where
  evidence target htarget _current Rcurrent Hext _depth _exposedType
      _syntaxTarget Hexposed HsyntaxType Hvalidated := by
    rcases Hshapes.motiveBindingAtMono (Rcurrent := Rcurrent)
        Hbindings Horigins Hext.contextLE target htarget with ⟨Hbinding⟩
    let binding := Hbinding.toBinding
    exact ⟨binding, T.telescope target htarget Rcurrent Hext binding
      Hexposed HsyntaxType Hvalidated⟩

/-- Stable rule-row form of the producer semantic origins.  It is indexed by
the exact retained minor shape and blueprint, so later installation cannot
pair a semantic call row with an unrelated executable rule. -/
def RecInfoRuleBlueprintSemanticOriginAt
    {recLparams : List Name}
    (Rambient : RecursorContextWF c recLparams) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (elimLevel : Level) (parameterDecls : VLCtx)
    (expectedOwnerIdx : Nat) (S : RecInfoMinorTypeShape)
    (B : AddInductive.RecRuleBlueprint) : Prop :=
  ∃ origins : RecInfoMinorHypothesisTypeOrigins S.sourceFullContext
      S.recursiveFields S.hypotheses,
    S.hypothesis_type_origins = some origins ∧
    origins.stats = stats ∧
    origins.recInfos.map (·.motive) = recInfos.map (·.motive) ∧
    ∃ F : RecInfoRuleFieldSemanticSource Rambient stats S,
      F.parameterSuffix.parameterDecls = parameterDecls ∧
      ∃ depth,
        RecursorValidAppStatsWF F.terminalWF.venv recLparams
          F.terminalWF.mlctx.vlctx stats decl depth ∧
        ∃ fields : List (RecursorRecursiveDomainAt F.terminalWF.venv decl
            recLparams.length),
          RecursorFieldSelectionsAt F.terminalWF.venv decl recLparams.length
            S.fields S.recursiveFields fields ∧
          AddInductive.isValidIndAppIdx stats F.traversal.terminal
            expectedOwnerIdx = true ∧
          expectedOwnerIdx < decl.types.length ∧
          ∃ ownerIdx,
            AddInductive.isValidIndApp? stats F.traversal.terminal =
              some ownerIdx ∧
            Nonempty (RecursorValidatedIndAppAt F.terminalWF.venv recLparams
              F.terminalWF.mlctx.vlctx stats decl depth F.traversal.terminal
              F.terminalTarget ownerIdx) ∧
        ∃ binding : RecursorMotiveBinding F.terminalWF
            recInfos[ownerIdx]! elimLevel,
          Nonempty (RecursorMotiveTelescopeEvidence F.terminalWF stats
            recInfos[ownerIdx]! binding F.traversal.terminal
            F.terminalTarget) ∧
        Nonempty (RecInfoMotiveTelescopeLookup F.terminalWF stats decl recInfos
          elimLevel) ∧
        Nonempty (RecInfoHypothesisCallSemanticOrigins F.terminalWF decl depth
          stats (recInfos.map (·.motive))
          (fun fv => fv ∈ F.fieldsRecent.fvars ∨
            fv ∈ ExprArrayFVarIds stats.params)
          S.recursiveFields S.hypotheses B.recursiveCalls)

theorem RecInfoRuleBlueprintSemanticOriginAt.mono
    {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {R' : RecursorContextWF c' recLparams}
    (H : RecInfoRuleBlueprintSemanticOriginAt R decl stats recInfos elimLevel
      parameterDecls
      expectedOwnerIdx S B)
    (E : RecursorContextExtension R R') :
    RecInfoRuleBlueprintSemanticOriginAt R' decl stats recInfos elimLevel
      parameterDecls
      expectedOwnerIdx S B := by
  unfold RecInfoRuleBlueprintSemanticOriginAt at H ⊢
  rcases H with
    ⟨origins, hshape, hstats, hmotives, F, hparams, depth, HvalidStats,
      fields, Hselection, hexpectedValid, hexpectedLt,
      ownerIdx, htargetValid, Hvalidated, binding, Hevidence,
      Hlookup, Hcalls⟩
  exact ⟨origins, hshape, hstats, hmotives, F.mono E, hparams, depth,
    HvalidStats, fields, Hselection, hexpectedValid, hexpectedLt,
    ownerIdx, htargetValid, Hvalidated, binding, Hevidence, Hlookup, Hcalls⟩

/-- Owner/minor-indexed persistence of the semantic blueprint rows through
the complete mutual second pass. -/
structure RecInfoRuleBlueprintSemanticOrigins
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (elimLevel : Level) (parameterDecls : VLCtx)
    (Horigins : RecInfoTypeOrigins c recInfos) : Prop where
  rows_size : ∀ owner (howner : owner < recInfos.size),
    recInfos[owner]!.ruleBlueprints.size =
      Horigins.minorTypes[owner]!.size
  entry : ∀ owner (howner : owner < recInfos.size)
      (localIndex : Nat)
      (hlocal : localIndex < Horigins.minorTypes[owner]!.size),
    Nonempty (RecInfoRuleBlueprintSemanticOriginAt R decl stats recInfos elimLevel
      parameterDecls
      owner
      (Horigins.minorShapes owner howner localIndex hlocal)
      recInfos[owner]!.ruleBlueprints[localIndex]!)
  /-- Every retained field binder is distinct from every binder in the
  completed recursor prefix.  This is producer evidence: later minor
  allocations preserve earlier rows because their fresh id is not in the
  current context, while a newly completed row was opened after the prefix
  that already existed. -/
  fields_outer_fresh : ∀ owner (howner : owner < recInfos.size)
      (localIndex : Nat)
      (hlocal : localIndex < Horigins.minorTypes[owner]!.size)
      (fv : FVarId),
    fv ∈ (Horigins.minorShapes owner howner localIndex hlocal).fields_bound.fvars →
    fv ∉ (ExprArrayFVarIds stats.params ++
      ExprArrayFVarIds (recInfos.map (·.motive))) ++
      ExprArrayFVarIds (recInfos.flatMap (·.minors))

theorem RecInfoRuleBlueprintSemanticOrigins.mono
    {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {R' : RecursorContextWF c' recLparams}
    (H : RecInfoRuleBlueprintSemanticOrigins R decl stats recInfos elimLevel
      parameterDecls Horigins)
    (E : RecursorContextExtension R R') :
    RecInfoRuleBlueprintSemanticOrigins R' decl stats recInfos elimLevel
      parameterDecls
      (Horigins.mono E.contextLE) := by
  refine {
    rows_size := H.rows_size
    entry := ?_
    fields_outer_fresh := ?_ }
  · intro owner howner localIndex hlocal
    have hlocalOld : localIndex < Horigins.minorTypes[owner]!.size := by
      simpa [RecInfoTypeOrigins.mono] using hlocal
    rcases H.entry owner howner localIndex hlocalOld with ⟨Hentry⟩
    exact ⟨by simpa [RecInfoTypeOrigins.mono] using Hentry.mono E⟩
  · intro owner howner localIndex hlocal fv hfv
    simpa [RecInfoTypeOrigins.mono] using
      H.fields_outer_fresh owner howner localIndex hlocal fv hfv

/-- Before the executable second pass begins, every minor/blueprint row is
empty, so the semantic-origin table is established without any entries. -/
theorem RecInfoRuleBlueprintSemanticOrigins.ofEmpty
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (decl : VInductDecl)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hcounts : RecInfoBlueprintCounts recInfos) (elimLevel : Level) :
    RecInfoRuleBlueprintSemanticOrigins R decl stats recInfos elimLevel
      parameterDecls Horigins where
  rows_size owner howner :=
    (Hcounts owner howner).trans
      (Horigins.minors owner howner).size_eq.symm
  entry owner howner localIndex hlocal := by
    have hsize := (Horigins.minors owner howner).size_eq
    rw [Hempty owner howner] at hsize
    omega
  fields_outer_fresh owner howner localIndex hlocal := by
    have hsize := (Horigins.minors owner howner).size_eq
    rw [Hempty owner howner] at hsize
    omega

namespace mkRecRules.loopU

/-- Binder-aware refinement of the production recursive-result loop. -/
theorem boundGeneratedCalls
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hc : BindingContextWF c)
    (Hprefix : BoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls c u v i)
    (Hk : ∀ v,
      BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
        c u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    let buildCall : Expr → Array Expr → AddInductive.M Expr :=
      mkRecRules.buildRecursiveCall indTypes stats motives minors lvls u[i]
    have hval :
        (AddInductive.mkRecInfos.loopUArgs u[i] buildCall c).WF
          (fun value => Nonempty (BoundGeneratedRecursiveCall indTypes stats
            motives minors lvls c u[i] value)) := by
      refine mkRecInfos.loopUArgs.resultBindings
        (Q := fun value => Nonempty (BoundGeneratedRecursiveCall indTypes
          stats motives minors lvls c u[i] value)) u[i] buildCall c Hc ?_
      intro uiTy xs c' Hc' Hxs Hle
      unfold buildCall mkRecRules.buildRecursiveCall
      cases hvalid : AddInductive.isValidIndApp? stats uiTy with
      | none =>
        simp only [hvalid, bind, Except.bind]
        exact Except.WF.throw
      | some target =>
        simp only [hvalid, bind, Except.bind]
        refine Except.WF.pure ⟨{
          exposedType := uiTy
          ownerIdx := target
          owner_valid := hvalid
          localArgs := xs
          current := c'
          current_wf := Hc'
          current_extends := Hle
          arguments_bound := Hxs
          value_eq := ?_ }⟩
        simp [AddInductive.getIIndices, hvalid]
    exact hval.bind fun value Hvalue => by
      rcases Hvalue with ⟨Hvalue⟩
      exact boundGeneratedCalls Hc
        (Hprefix.push hnext Hvalue) Hk
  · rw [dif_neg hnext]
    apply Hk
    have hcovered := Hprefix.covered
    have hdone : i = u.size := by omega
    simpa [hdone] using Hprefix
termination_by u.size - i

/-- Semantic binder-aware refinement of the production recursive-result
loop.  Every selected source field is supplied with its translation in the
root recursor context; `loopUArgs` then reconstructs and couples the complete
recursive domain to the exact generated call at the same array position. -/
theorem semanticBoundGeneratedCalls
    {alpha : Type} {Q : alpha → Prop}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ i (hi : i < u.size),
      ∃ fv fieldTarget,
        u[i] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    {P : FVarId → Prop}
    (HfieldScope : ∀ i (hi : i < u.size) {fv},
      u[i] = .fvar fv → P fv)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx)
    {k : Array Expr → AddInductive.M alpha}
    (Hprefix : SemanticBoundGeneratedRecursiveCalls indTypes stats motives
      minors lvls R decl depth P u v i)
    (Hk : ∀ v,
      SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
        lvls R decl depth P u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    rcases Hfields i hnext with ⟨fv, fieldTarget, hfield, Hfield⟩
    let buildCall : Expr → Array Expr → AddInductive.M Expr :=
      mkRecRules.buildRecursiveCall indTypes stats motives minors lvls u[i]
    have hval :
        (AddInductive.mkRecInfos.loopUArgs u[i] buildCall c).WF
          (fun value => ∃ S :
            SemanticBoundGeneratedRecursiveCall indTypes stats motives
              minors lvls R decl depth u[i] value,
            S.rootScope = P) := by
      rw [hfield]
      simpa only [buildCall, hfield] using
        mkRecRules.boundGeneratedCallSemantic indTypes stats motives minors
        lvls R Hstats hconsume hlit hctx hproj fv Hfield
        (HfieldScope i hnext hfield) hrootUp
    exact hval.bind fun value Hvalue => by
      rcases Hvalue with ⟨Hvalue, hscope⟩
      exact semanticBoundGeneratedCalls R Hstats hconsume hlit hctx
        hproj Hfields HfieldScope hrootUp
          (Hprefix.push hnext Hvalue hscope) Hk
  · rw [dif_neg hnext]
    apply Hk
    have hcovered := Hprefix.covered
    have hdone : i = u.size := by omega
    simpa [hdone] using Hprefix
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.boundGeneratedCallsFromEmpty
    {α : Type} {Q : α → Prop}
    {k : Array Expr → AddInductive.M α}
    (Hc : BindingContextWF c)
    (Hk : ∀ v,
      BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
        c u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.boundGeneratedCalls Hc
    (BoundGeneratedRecursiveCalls.empty
      indTypes stats motives minors lvls c u) Hk

theorem mkRecRules.loopU.semanticBoundGeneratedCallsFromEmpty
    {alpha : Type} {Q : alpha → Prop}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ i (hi : i < u.size),
      ∃ fv fieldTarget,
        u[i] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    {P : FVarId → Prop}
    (HfieldScope : ∀ i (hi : i < u.size) {fv},
      u[i] = .fvar fv → P fv)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx)
    {k : Array Expr → AddInductive.M alpha}
    (Hk : ∀ v,
      SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
        lvls R decl depth P u v u.size →
      (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.semanticBoundGeneratedCalls R Hstats hconsume hlit
    hctx hproj Hfields HfieldScope hrootUp
    (SemanticBoundGeneratedRecursiveCalls.empty indTypes stats motives minors
      lvls R decl depth P u) Hk

namespace mkRecInfos.loopCtorArgs.loop

/-- Operational binder refinement for constructor-field classification. -/
theorem resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hbu : FreshBoundFVarArray root c bu)
    (Hu : FreshBoundFVarArray root c u)
    (Hselected : u.toList.Sublist bu.toList)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ t bu u c, BindingContextWF c →
      FreshBoundFVarArray root c bu → FreshBoundFVarArray root c u →
      u.toList.Sublist bu.toList → BindingContextLE root c →
      (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      cases hparam : stats.params[i]? with
      | some param =>
        change (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
          (body.instantiate1 param) (i + 1) bu u fuel c).WF Q
        exact ih Hc Hbu Hu Hselected Hroot
      | none =>
        change (Lean4Lean.withLocalDecl name bi dom.consumeTypeAnnotationsVerified
          (fun arg => do
            let bu := bu.push arg
            let u := if (← AddInductive.isRecArg stats dom).isSome then
              u.push arg else u
            AddInductive.mkRecInfos.loopCtorArgs.loop stats k
              (body.instantiate1 arg) (i + 1) bu u fuel) c).WF Q
        unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
          AddInductive.instMonadLocalNameGeneratorM
          AddInductive.instMonadWithReaderOfLocalContextM
        let c' : AddInductive.Context := { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotationsVerified bi }
        change (AddInductive.isRecArg stats dom c' >>= fun selected =>
          AddInductive.mkRecInfos.loopCtorArgs.loop stats
            k (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
            (bu.push (.fvar ⟨c.ngen.curr⟩))
            (if selected.isSome then u.push (.fvar ⟨c.ngen.curr⟩) else u)
            fuel c') |>.WF Q
        have hclass : (AddInductive.isRecArg stats dom c').WF
            (fun _ => True) := by
          intro _ _
          trivial
        refine hclass.bind fun selected _ => ?_
        let Hc' := Hc.withLocalDecl name dom.consumeTypeAnnotationsVerified bi
        let hstep := BindingContextLE.withLocalDecl c Hc name
          dom.consumeTypeAnnotationsVerified bi
        cases selected with
        | none =>
          have hselected' : u.toList.Sublist
              (bu.push (.fvar ⟨c.ngen.curr⟩)).toList := by
            simpa using Hselected.trans
              (List.sublist_append_left bu.toList
                [.fvar ⟨c.ngen.curr⟩])
          exact ih Hc'
            (Hbu.pushCurrent Hc Hroot name dom.consumeTypeAnnotationsVerified bi)
            (Hu.weaken name dom.consumeTypeAnnotationsVerified bi)
            hselected'
            (Hroot.trans hstep)
        | some target =>
          have hselected' : (u.push (.fvar ⟨c.ngen.curr⟩)).toList.Sublist
              (bu.push (.fvar ⟨c.ngen.curr⟩)).toList := by
            simpa using
              Hselected.append_right [.fvar ⟨c.ngen.curr⟩]
          exact ih Hc'
            (Hbu.pushCurrent Hc Hroot name dom.consumeTypeAnnotationsVerified bi)
            (Hu.pushCurrent Hc Hroot name dom.consumeTypeAnnotationsVerified bi)
            hselected'
            (Hroot.trans hstep)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj =>
      change (k _ bu u c).WF Q
      exact Hk _ _ _ _ Hc Hbu Hu Hselected Hroot

end mkRecInfos.loopCtorArgs.loop

theorem mkRecInfos.loopCtorArgs.resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats) (t : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {Q : alpha → Prop}
    (Hc : BindingContextWF c)
    (Hk : ∀ t bu u c', BindingContextWF c' →
      FreshBoundFVarArray c c' bu → FreshBoundFVarArray c c' u →
      u.toList.Sublist bu.toList → BindingContextLE c c' →
      (k t bu u c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopCtorArgs
  exact mkRecInfos.loopCtorArgs.loop.resultBindings stats k Hc
    (FreshBoundFVarArray.empty c) (FreshBoundFVarArray.empty c)
    .slnil (BindingContextLE.refl c) Hk

namespace mkRecRules.loopCtors

/-- Semantic refinement of one exact production rule-generation iteration.
The constructor-field traversal supplies the ordered recursive-domain trace;
the recursive-call traversal then couples every generated IH application to
that trace.  The result retains both the existing binder-aware operational
certificate and the new pointwise semantic payload. -/
theorem oneRuleSemantics
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctor : Constructor) (minorIdx ownerIdx : Nat)
    {recLparams : List Name} {depth : Nat}
    {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {tail : Expr} {tailTarget introTarget : VExpr}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (hprefix : RecursorParamPrefix stats 0 ctor.type tail)
    (htailFVars : tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params))
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (howner : ownerIdx < decl.types.length)
    (Hnormal : CheckedConstructorOwnerNormalForm stats ownerIdx tail)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    (HtailType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
      tailTarget)
    (Hintro : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN (.const ctor.name stats.levels) stats.params) introTarget)
    (HintroType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      introTarget tailTarget)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminor : minorIdx < minors.size) :
    (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type
      (fun _ allArgs recursiveArgs =>
        AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
          recursiveArgs 0 #[] fun recursiveResults => do
            let lctx ← getLCtx
            let rule : RecursorRule := {
              ctor := ctor.name
              nfields := allArgs.size
              rhs := lctx.mkLambda stats.params <|
                lctx.mkLambda motives <| lctx.mkLambda minors <|
                lctx.mkLambda allArgs <|
                mkAppN (mkAppN minors[minorIdx]! allArgs)
                  recursiveResults }
            return (rule, minorIdx + 1)) c).WF fun out =>
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors
          lvls ctor minorIdx out.1,
        Nonempty (Hrule.Semantics R decl ownerIdx) ∧
        out.2 = minorIdx + 1 := by
  let process : Expr → Array Expr → Array Expr →
      AddInductive.M (RecursorRule × Nat) := fun _ allArgs recursiveArgs =>
    AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      recursiveArgs 0 #[] fun recursiveResults => do
        let lctx ← getLCtx
        let rule : RecursorRule := {
          ctor := ctor.name
          nfields := allArgs.size
          rhs := lctx.mkLambda stats.params <|
            lctx.mkLambda motives <| lctx.mkLambda minors <|
            lctx.mkLambda allArgs <|
            mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults }
        return (rule, minorIdx + 1)
  change (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type process c).WF _
  apply mkRecInfos.loopCtorArgs.recursiveDomainsRecursorRecent
    (Q := fun out =>
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors
          lvls ctor minorIdx out.1,
        Nonempty (Hrule.Semantics R decl ownerIdx) ∧
        out.2 = minorIdx + 1)
    stats ctor.type tail
      (mkAppN (.const ctor.name stats.levels) stats.params)
      process c R Hstats hprefix hconsume hlit hctx hproj Htail
      HtailType htailFVars hparameterUp Hintro HintroType
  intro current Rargs terminal terminalTarget appliedTarget allArgs
    recursiveArgs fields positions args hterminalNonforall Hterminal HterminalType
    Hselection Hdecisions Hrecursive HfieldsRecent _Hopening HfieldTargetDefEq
    _HterminalScope
    _HfieldParameterUp _HintroApplied _HintroAppliedType
  let HstatsArgs := Hstats.weakenRecent HfieldsRecent
  have hctxArgs : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rargs.mlctx.vlctx :=
    HfieldsRecent.noIndConsts (names := decl.types.map (·.name)) hctx
  have hvalidIdx : AddInductive.isValidIndAppIdx stats terminal ownerIdx =
      true :=
    Hnormal.validOfOpening _Hopening Hparams
      HfieldsRecent.toFreshBoundFVarArray
      (Hstats.indConstAt howner) hterminalNonforall
  rcases checkPositivityStep.isValidIndApp?_exists_of_valid hvalidIdx
      (Hstats.indConstAt howner) with ⟨selectedOwner, hselectedOwner⟩
  have hselectedStats :=
    checkPositivityStep.isValidIndApp?_some hselectedOwner
  have hselectedOwnerLt : selectedOwner < decl.types.length := by
    rw [← Hstats.types_size]
    exact hselectedStats.1
  let buildRule : Array Expr →
      AddInductive.M (RecursorRule × Nat) := fun recursiveResults => do
    let lctx ← getLCtx
    let rule : RecursorRule := {
      ctor := ctor.name
      nfields := allArgs.size
      rhs := lctx.mkLambda stats.params <|
        lctx.mkLambda motives <| lctx.mkLambda minors <|
        lctx.mkLambda allArgs <|
        mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults }
    return (rule, minorIdx + 1)
  change (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
    recursiveArgs 0 #[] buildRule current).WF _
  apply mkRecRules.loopU.semanticBoundGeneratedCallsFromEmpty
    (Q := fun out =>
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors
          lvls ctor minorIdx out.1,
        Nonempty (Hrule.Semantics R decl ownerIdx) ∧
        out.2 = minorIdx + 1)
    (indTypes := indTypes) (stats := stats) (motives := motives)
    (minors := minors) (lvls := lvls) (u := recursiveArgs)
    (k := buildRule) (c := current) (decl := decl) Rargs
    HstatsArgs hconsume
      (by simpa only [HfieldsRecent.venv_eq] using hlit) hctxArgs hproj
    (Hselection.selectedFVars
      HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray Hrecursive)
    (P := fun fv => fv ∈ _Hopening.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params)
    (by
      intro i hi fv hfv
      have hselectedExpr : Expr.fvar fv ∈ recursiveArgs.toList := by
        rw [← hfv]
        exact Array.getElem_mem_toList hi
      have hallExpr : Expr.fvar fv ∈ allArgs.toList :=
        Hselection.toSource.selectedSublist.subset hselectedExpr
      have hallFv : fv ∈
          HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.fvars := by
        rw [HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.expressions]
          at hallExpr
        simpa using hallExpr
      exact Or.inl (by
        rw [_Hopening.fvars_eq_bound
          HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
        exact hallFv))
    _HfieldParameterUp
  intro recursiveResults Hcalls
  simp only [buildRule, getLCtx, readThe, read, ReaderT.read]
  let Hparams' := Hparams.mono HfieldsRecent.contextLE
  let Hmotives' := Hmotives.mono HfieldsRecent.contextLE
  let Hminors' := Hminors.mono HfieldsRecent.contextLE
  have HouterNodup' :
      ((Hparams'.fvars ++ Hmotives'.fvars) ++ Hminors'.fvars).Nodup := by
    change ((Hparams.fvars ++ Hmotives.fvars) ++ Hminors.fvars).Nodup
    exact HouterNodup
  have hselected : recursiveArgs.toList.Sublist allArgs.toList :=
    Hselection.toSource.selectedSublist
  rcases BoundFVarArray.ofSublist
      HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray hselected with
    ⟨HrecursiveBound⟩
  have hrecursiveNodup : HrecursiveBound.fvars.Nodup := by
    have hallExpr : allArgs.toList.Nodup := by
      rw [HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.expressions]
      exact List.Pairwise.map Expr.fvar
        (fun _ _ hne heq => hne (Expr.fvar.inj heq))
        HfieldsRecent.toFreshBoundFVarArray.nodup
    have hrecursiveExpr := hallExpr.sublist hselected
    rw [HrecursiveBound.expressions] at hrecursiveExpr
    change List.Pairwise (fun a b : Expr => a ≠ b)
      (HrecursiveBound.fvars.map Expr.fvar) at hrecursiveExpr
    rw [List.pairwise_map] at hrecursiveExpr
    change List.Pairwise (fun a b : FVarId => a ≠ b)
      HrecursiveBound.fvars
    exact hrecursiveExpr.imp fun hneq heq =>
      hneq (congrArg Expr.fvar heq)
  let Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx {
        ctor := ctor.name
        nfields := allArgs.size
        rhs := current.lctx.mkLambda stats.params <|
          current.lctx.mkLambda motives <| current.lctx.mkLambda minors <|
          current.lctx.mkLambda allArgs <|
          mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults } := {
    root := current
    outerRoot := current
    root_wf := Rargs.toBindingContextWF
    outer_wf := Rargs.toBindingContextWF
    root_le_outer := BindingContextLE.refl current
    target := terminal
    allArgs := allArgs
    recursiveArgs := recursiveArgs
    recursiveResults := recursiveResults
    minor_valid := hminor
    params_bound := Hparams'
    motives_bound := Hmotives'
    minors_bound := Hminors'
    outer_binders_nodup := HouterNodup'
    all_args_bound :=
      HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    recursive_args_bound := HrecursiveBound
    recursive_args_sublist := hselected
    all_args_nodup := HfieldsRecent.toFreshBoundFVarArray.nodup
    recursive_args_nodup := hrecursiveNodup
    all_args_outer_fresh := by
      intro fv hfv houter
      apply HfieldsRecent.toFreshBoundFVarArray.fresh fv hfv
      rcases List.mem_append.mp houter with hpm | hminor
      · rcases List.mem_append.mp hpm with hparam | hmotive
        · exact Hparams.members fv hparam
        · exact Hmotives.members fv hmotive
      · exact Hminors.members fv hminor
    recursive_calls := Hcalls.bound
    ctor_eq := rfl
    fields_eq := rfl
    rhs_eq := rfl }
  let Hsemantic : Hrule.Semantics R decl ownerIdx := {
    depth := depth + allArgs.size
    context := Rargs
    fieldRoot := c
    fieldRootContext := R
    parameterDepth := depth
    parameterSuffix := Hsuffix
    parameterDecls := Hsuffix.parameterDecls
    parameterDecls_eq := rfl
    fieldRootExtension := .refl R
    fieldsRecent := HfieldsRecent
    parameterTail := tail
    parameterPrefix := hprefix
    parameterTail_fvars := htailFVars
    parameterTarget := tailTarget
    parameterTranslation := Htail
    parameterType := HtailType
    fieldOpening := _Hopening
    fieldParameterUp := by
      rw [_Hopening.fvars_eq_bound
        HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] at _HfieldParameterUp
      exact _HfieldParameterUp
    context_venv := HfieldsRecent.venv_eq
    validStats := HstatsArgs
    ownerIdx := selectedOwner
    owner_lt := hselectedOwnerLt
    expected_owner_lt := howner
    expected_target_valid := hvalidIdx
    targetTarget := terminalTarget
    target_not_forall := hterminalNonforall
    target_translation := Hterminal
    target_type := HterminalType
    fieldTargetDefEq := HfieldTargetDefEq
    constructorTarget := appliedTarget
    constructor_translation := by
      simpa [BoundGeneratedRecursorRule.sourceConstructorMajor, mkAppN] using
        _HintroApplied
    constructor_typing := _HintroAppliedType
    target_valid := hselectedOwner
    validated := HstatsArgs.validatedIndAppAt Hterminal hselectedOwner
      hselectedOwnerLt
        (by simpa only [HfieldsRecent.venv_eq] using hlit) hctxArgs hproj
    fields := fields
    selection := Hselection
    decisionPositions := positions
    decisions := Hdecisions
    calls := Hcalls.toStaged (.refl Rargs) }
  apply Except.WF.pure
  refine Exists.intro Hrule ?_
  exact And.intro (Nonempty.intro Hsemantic) rfl

/-- Semantic traversal of a complete constructor batch.  It follows the
production accumulator and minor-state equations exactly, while obtaining
each constructor seed from the earlier checker certificate. -/
theorem semanticGeneratedRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (acc : Array RecursorRule) (start ownerIdx : Nat)
    {recLparams : List Name} {depth : Nat} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (howner : ownerIdx < decl.types.length)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (hminorsRoom : start + ctors.length ≤ minors.size)
    (Hseed : ∀ ctor, ctor ∈ ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats ownerIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
        R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params) introTarget ∧
        R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
          tailTarget) :
    (AddInductive.mkRecRules.loopCtors indTypes stats motives minors lvls
      ctors acc start c).WF fun out =>
        ∃ generated,
          out.1 = acc.toList ++ generated ∧
          SemanticBoundGeneratedRecursorRules indTypes stats motives minors
            lvls R decl ownerIdx ctors start generated ∧
          out.2 = start + ctors.length := by
  induction ctors generalizing acc start with
  | nil =>
      simp [AddInductive.mkRecRules.loopCtors]
      intro out hout
      cases hout
      exact ⟨[], by simp, .nil, by simp⟩
  | cons ctor ctors ih =>
      rcases Hseed ctor (by simp) with
        ⟨tail, tailTarget, introTarget, Hprefix, ⟨Hnormal⟩, HtailFVars,
          Htail, HtailType, Hintro, HintroType⟩
      rw [AddInductive.mkRecRules.loopCtors]
      have Hone := oneRuleSemantics indTypes stats motives minors lvls ctor
        start ownerIdx R Hstats Hsuffix Hprefix HtailFVars hparameterUp howner Hnormal
        hconsume hlit hctx hproj Htail
        HtailType Hintro HintroType Hparams Hmotives Hminors HouterNodup
        (by simp at hminorsRoom; omega)
      exact Hone.bind fun out Hout => by
        rcases Hout with ⟨Hrule, Hsemantic, hnext⟩
        have HtailSeed : ∀ nextCtor, nextCtor ∈ ctors →
            ∃ tail tailTarget introTarget,
              RecursorParamPrefix stats 0 nextCtor.type tail ∧
              Nonempty
                (CheckedConstructorOwnerNormalForm stats ownerIdx tail) ∧
              tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
              TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
              R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
                tailTarget ∧
              TrExprS R.venv recLparams R.mlctx.vlctx
                (mkAppN (.const nextCtor.name stats.levels) stats.params)
                introTarget ∧
              R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
                introTarget tailTarget := by
          intro nextCtor hmem
          exact Hseed nextCtor (by simp [hmem])
        have hminorsRoom' : out.2 + ctors.length ≤ minors.size := by
          rw [hnext]
          simp at hminorsRoom ⊢
          omega
        have Htail := ih (acc := acc.push out.1) (start := out.2)
          hminorsRoom' HtailSeed
        exact Htail.mono fun result Hresult => by
          rcases Hresult with ⟨generated, hout, Hgenerated, hend⟩
          refine ⟨out.1 :: generated, ?_, ?_, ?_⟩
          · simpa [hout]
          · exact SemanticBoundGeneratedRecursorRules.cons Hrule Hsemantic
              (by simpa [hnext] using Hgenerated)
          · simp at hend ⊢
            omega

/-- The complete rule traversal retains the constructor-field binding context
and the bound recursive-call evidence for every emitted rule. -/
theorem boundGeneratedRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (acc : Array RecursorRule)
    (start : Nat) (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminorsRoom : start + ctors.length ≤ minors.size) :
    (AddInductive.mkRecRules.loopCtors indTypes stats motives minors lvls
      ctors acc start c).WF fun out =>
        ∃ generated,
          out.1 = acc.toList ++ generated ∧
          BoundGeneratedRecursorRules indTypes stats motives minors lvls
            ctors start generated ∧
          out.2 = start + ctors.length := by
  induction ctors generalizing acc start c with
  | nil =>
      simp [AddInductive.mkRecRules.loopCtors]
      intro out hout
      cases hout
      refine ⟨[], ?_, .nil, by simp⟩
      simp
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecRules.loopCtors]
      have hone :
          ((fun minorIdx => AddInductive.mkRecInfos.loopCtorArgs stats
            ctor.type fun _ bu u =>
              AddInductive.mkRecRules.loopU indTypes stats motives minors
                lvls u 0 #[] fun v => do
                  let lctx ← getLCtx
                  let rule := {
                    ctor := ctor.name
                    nfields := bu.size
                    rhs := lctx.mkLambda stats.params <|
                      lctx.mkLambda motives <| lctx.mkLambda minors <|
                      lctx.mkLambda bu <|
                      mkAppN (mkAppN minors[minorIdx]! bu) v }
                  return (rule, minorIdx + 1)) start c).WF fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1 := by
        dsimp only
        apply mkRecInfos.loopCtorArgs.resultBindings stats ctor.type
          (Q := fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1)
          (k := fun _ bu u =>
            AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
              u 0 #[] fun v => do
                let lctx ← getLCtx
                let rule : RecursorRule := {
                  ctor := ctor.name
                  nfields := bu.size
                  rhs := lctx.mkLambda stats.params <|
                    lctx.mkLambda motives <| lctx.mkLambda minors <|
                    lctx.mkLambda bu <|
                    mkAppN (mkAppN minors[start]! bu) v }
                return (rule, start + 1))
          (c := c) (Hc := Hc)
        intro target bu u c' Hc' Hbu Hu hselected hroot
        let buildRule : Array Expr →
            AddInductive.M (RecursorRule × Nat) := fun v => do
          let lctx ← getLCtx
          let rule := {
            ctor := ctor.name
            nfields := bu.size
            rhs := lctx.mkLambda stats.params <|
              lctx.mkLambda motives <| lctx.mkLambda minors <|
              lctx.mkLambda bu <|
              mkAppN (mkAppN minors[start]! bu) v }
          return (rule, start + 1)
        change (AddInductive.mkRecRules.loopU indTypes stats motives minors
          lvls u 0 #[] buildRule c').WF _
        apply mkRecRules.loopU.boundGeneratedCallsFromEmpty
          (Q := fun out =>
            Nonempty (BoundGeneratedRecursorRule indTypes stats motives
              minors lvls ctor start out.1) ∧ out.2 = start + 1)
          (indTypes := indTypes) (stats := stats) (motives := motives)
          (minors := minors) (lvls := lvls) (u := u) (k := buildRule)
          (c := c') Hc'
        intro v Hcalls
        simp only [buildRule, getLCtx, readThe, read, ReaderT.read]
        refine Except.WF.pure ⟨?_, rfl⟩
        let Hparams' := Hparams.mono hroot
        let Hmotives' := Hmotives.mono hroot
        let Hminors' := Hminors.mono hroot
        have HouterNodup' :
            ((Hparams'.fvars ++ Hmotives'.fvars) ++
              Hminors'.fvars).Nodup := by
          change ((Hparams.fvars ++ Hmotives.fvars) ++
            Hminors.fvars).Nodup
          exact HouterNodup
        exact ⟨{
          root := c'
          outerRoot := c'
          root_wf := Hc'
          outer_wf := Hc'
          root_le_outer := BindingContextLE.refl c'
          target := target
          allArgs := bu
          recursiveArgs := u
          recursiveResults := v
          minor_valid := by simp at hminorsRoom; omega
          params_bound := Hparams'
          motives_bound := Hmotives'
          minors_bound := Hminors'
          outer_binders_nodup := HouterNodup'
          all_args_bound := Hbu.toBoundFVarArray
          recursive_args_bound := Hu.toBoundFVarArray
          recursive_args_sublist := hselected
          all_args_nodup := Hbu.nodup
          recursive_args_nodup := Hu.nodup
          all_args_outer_fresh := by
            intro fv hfv houter
            apply Hbu.fresh fv hfv
            rcases List.mem_append.mp houter with hpm | hminor
            · rcases List.mem_append.mp hpm with hparam | hmotive
              · exact Hparams.members fv hparam
              · exact Hmotives.members fv hmotive
            · exact Hminors.members fv hminor
          recursive_calls := Hcalls
          ctor_eq := rfl
          fields_eq := rfl
          rhs_eq := rfl }⟩
      exact hone.bind fun out Hout => by
        rcases Hout with ⟨Hrule, hnext⟩
        have htail := ih (acc := acc.push out.1)
          (start := out.2) (c := c) Hc Hparams Hmotives Hminors
            HouterNodup (by simp at hminorsRoom; omega)
        exact htail.mono fun result Hresult => by
          rcases Hresult with ⟨generated, hout, Hgenerated, hend⟩
          refine ⟨out.1 :: generated, ?_, .cons Hrule ?_, ?_⟩
          · simpa [hout]
          · simpa [hnext] using Hgenerated
          · simp at hend ⊢
            omega

end mkRecRules.loopCtors

/-- Public binder-aware rule-generator boundary. -/
theorem mkRecRules.boundGeneratedRules
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats) (dIdx : Nat)
    (motives minors : Array Expr) (start : Nat)
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hminorsRoom : start + indTypes[dIdx]!.ctors.length ≤ minors.size) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx motives minors
      start c).WF fun out =>
        BoundGeneratedRecursorRules indTypes stats motives minors
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[dIdx]!.ctors start out.1 ∧
        out.2 = start + indTypes[dIdx]!.ctors.length := by
  unfold AddInductive.mkRecRules
  have H := mkRecRules.loopCtors.boundGeneratedRules indTypes stats
    motives minors (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[dIdx]!.ctors #[] start c Hc Hparams Hmotives Hminors
      HouterNodup hminorsRoom
  exact H.mono fun out Hout => by
    rcases Hout with ⟨generated, hout, Hgenerated, hend⟩
    simpa using ⟨hout ▸ Hgenerated, hend⟩

/-- Public semantic rule-generator boundary for one mutual-family owner. -/
theorem mkRecRules.semanticGeneratedRules
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats) (dIdx : Nat)
    (motives minors : Array Expr) (start : Nat)
    {recLparams : List Name} {depth : Nat} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (howner : dIdx < decl.types.length)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hparams : BoundFVarArray c stats.params)
    (Hmotives : BoundFVarArray c motives)
    (Hminors : BoundFVarArray c minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (hminorsRoom : start + indTypes[dIdx]!.ctors.length ≤ minors.size)
    (Hseed : ∀ ctor, ctor ∈ indTypes[dIdx]!.ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats dIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
        R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params) introTarget ∧
        R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
          tailTarget) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx motives minors
      start c).WF fun out =>
        SemanticBoundGeneratedRecursorRules indTypes stats motives minors
          (AddInductive.getRecLevels elimLevel stats.levels) R decl dIdx
          indTypes[dIdx]!.ctors start out.1 ∧
        out.2 = start + indTypes[dIdx]!.ctors.length := by
  unfold AddInductive.mkRecRules
  have H := mkRecRules.loopCtors.semanticGeneratedRules indTypes stats
    motives minors (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[dIdx]!.ctors #[] start dIdx R Hstats Hsuffix howner hconsume hlit hctx
    hproj Hparams Hmotives Hminors HouterNodup hparameterUp hminorsRoom Hseed
  exact H.mono fun out Hout => by
    rcases Hout with ⟨generated, hout, Hgenerated, hend⟩
    simpa using ⟨hout ▸ Hgenerated, hend⟩

/-- One iteration of the production recursor loop consumes exactly the
constructor-sized slice assigned to its mutual-family owner. The starting
state and available room are consequences of source translation and the
`mkRecInfos` cardinality certificate, not extra executable assumptions. -/
theorem RecursorCardinalityCertificate.mkRecRulesAtOffsetWF
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (elimLevel : Level) (dIdx : Nat) (hidx : dIdx < indTypes.size)
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        BoundGeneratedRecursorRules indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[dIdx]!.ctors (recursorMinorOffset indTypes dIdx) out.1 ∧
        out.2 = recursorMinorOffset indTypes (dIdx + 1) := by
  have htotal :
      (indTypes.toList.flatMap (fun type => type.ctors)).length =
        (recInfos.flatMap (·.minors)).size := by
    have howners :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl
    have howners' :
        (indTypes.toList.flatMap (fun type => type.ctors)).length =
          decl.ownedConstructors.length := by
      simpa [ownedConstructors, List.length_flatMap] using howners
    exact howners'.trans Hcard.minors.symm
  have hroom := recursorMinorOffset_room indTypes dIdx hidx
  rw [htotal] at hroom
  have H := mkRecRules.boundGeneratedRules indTypes elimLevel stats dIdx
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (recursorMinorOffset indTypes dIdx) c Hc Hparams Hbindings.motives
    Hbindings.flatMinors (Hbindings.outerNodup Hparams hnoalias) hroom
  exact H.mono fun out Hout => by
    refine ⟨Hout.1, ?_⟩
    rw [Hout.2, recursorMinorOffset_step indTypes dIdx hidx]

/-- Semantic strengthening of `mkRecRulesAtOffsetWF`.  Cardinality supplies
the flattened minor slice while the retained recursor context and checker
seed supply the pointwise field/call semantics. -/
theorem RecursorCardinalityCertificate.mkRecRulesAtOffsetSemanticWF
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (elimLevel : Level) (dIdx : Nat) (hidx : dIdx < indTypes.size)
    {recLparams : List Name} {depth : Nat} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth)
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hparameterUp : IsFVarUpSet
      (fun fv => fv ∈ ExprArrayFVarIds stats.params) R.mlctx.vlctx)
    (Hseed : ∀ ctor, ctor ∈ indTypes[dIdx]!.ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats dIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget ∧
        R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params) introTarget ∧
        R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx introTarget
          tailTarget) :
    (AddInductive.mkRecRules indTypes elimLevel stats dIdx
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes dIdx) c).WF fun out =>
        SemanticBoundGeneratedRecursorRules indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels) R decl dIdx
          indTypes[dIdx]!.ctors
          (recursorMinorOffset indTypes dIdx) out.1 ∧
        out.2 = recursorMinorOffset indTypes (dIdx + 1) := by
  have htotal :
      (indTypes.toList.flatMap (fun type => type.ctors)).length =
        (recInfos.flatMap (·.minors)).size := by
    have howners :=
      Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length Hdecl
    have howners' :
        (indTypes.toList.flatMap (fun type => type.ctors)).length =
          decl.ownedConstructors.length := by
      simpa [ownedConstructors, List.length_flatMap] using howners
    exact howners'.trans Hcard.minors.symm
  have hroom := recursorMinorOffset_room indTypes dIdx hidx
  rw [htotal] at hroom
  have howner : dIdx < decl.types.length := by
    have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
    have hsize : indTypes.size = decl.types.length := by simpa using htypes
    rwa [← hsize]
  have H := mkRecRules.semanticGeneratedRules indTypes elimLevel stats dIdx
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (recursorMinorOffset indTypes dIdx) R Hstats Hsuffix howner hconsume hlit hctx
    hproj Hparams Hbindings.motives Hbindings.flatMinors
    (Hbindings.outerNodup Hparams hnoalias) hparameterUp hroom Hseed
  exact H.mono fun out Hout => by
    refine ⟨Hout.1, ?_⟩
    rw [Hout.2, recursorMinorOffset_step indTypes dIdx hidx]

/-- Binder-aware analogue of `appendGeneratedRules`. Traversal, ordering, and
flattened constructor indexing are discharged here; the remaining pointwise
premise receives all local-binding evidence needed to construct `IotaRule`. -/
theorem IotaBuildCertificate.appendBoundGeneratedRules
    (Hbuild : IotaBuildCertificate env decl block prior)
    (Hgenerated : BoundGeneratedRecursorRules
      indTypes stats motives minors lvls ctors start sourceRules)
    (hlength : abstractRules.length = sourceRules.length)
    (hroom : abstractRules.length + prior.length ≤
      decl.ownedConstructors.length)
    (hsemantic : ∀ i (hctor : i < ctors.length)
      (hsource : i < sourceRules.length)
      (habstract : i < abstractRules.length),
      BoundGeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) sourceRules[i] →
      Nonempty (decl.IotaRule env block
        decl.ownedConstructors[prior.length + i].1
        decl.ownedConstructors[prior.length + i].2 abstractRules[i])) :
    IotaBuildCertificate env decl block (prior ++ abstractRules) := by
  apply Hbuild.append hroom
  intro i habstract
  have hsource : i < sourceRules.length := by omega
  have hctor : i < ctors.length := by
    rw [← Hgenerated.length]
    exact hsource
  rcases Hgenerated.entry i hctor hsource with ⟨Hrule⟩
  exact hsemantic i hctor hsource habstract Hrule

namespace mkRecInfos.loopU

/-- Every induction-hypothesis declaration introduced by `loopU` is retained
and appended to the certified hypothesis array. -/
theorem resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha) {Q : alpha → Prop}
    (i : Nat) (v : Array Expr) (c : AddInductive.Context)
    (Hc : BindingContextWF c) (Hv : FreshBoundFVarArray root c v)
    (Hroot : BindingContextLE root c)
    (Hk : ∀ outValues c, BindingContextWF c →
      FreshBoundFVarArray root c outValues →
      BindingContextLE root c →
      outValues.size = v.size + (u.size - i) →
      (k outValues c).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopU]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hviTy :
        ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
          let some itIdx := AddInductive.isValidIndApp? stats uiTy
            | throw (.other
              "recursive constructor field lost its inductive result type")
          let itIndices := uiTy.getAppArgs[stats.params.size:]
          let motiveApp := .app
            (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
          return (← getLCtx).mkForall xs motiveApp) c).WF
          (fun _ => True) := by
      intro _ _
      trivial
    refine hviTy.bind fun viTy _ => ?_
    have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
        (fun lctx => lctx = c.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName := (c.lctx.get! u[i].fvarId!).userName.appendAfter "_ih"
    apply withLocalDecl.continueRaw
    refine resultBindings stats u recInfos k (i + 1)
      (v.push (.fvar ⟨c.ngen.curr⟩)) _
      (Hc.withLocalDecl vName viTy.consumeTypeAnnotationsVerified .default)
      (Hv.pushCurrent Hc Hroot vName viTy.consumeTypeAnnotationsVerified .default)
      (Hroot.trans <| BindingContextLE.withLocalDecl c Hc vName
        viTy.consumeTypeAnnotationsVerified .default) ?_
    intro outValues out Hout Hvalues HrootOut hsize
    apply Hk outValues out Hout Hvalues HrootOut
    simp only [Array.size_push] at hsize
    omega
  · rw [dif_neg hnext]
    exact Hk v c Hc Hv Hroot (by omega)
termination_by u.size - i

/-- Semantic orchestration for the induction-hypothesis loop.  The only
operation-specific premise is the pointwise typing of the exact `viTy`
computed by `loopUArgs`; once supplied, every production `withLocalDecl` is
mirrored in `RecursorContextWF`, and the continuation receives the complete
recent-binder trace.  Keeping this separate makes the dependent motive
application used for `viTy` the sole remaining local semantic obligation. -/
theorem resultSemanticBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name}
    {root current : AddInductive.Context}
    (Rroot : RecursorContextWF root recLparams)
    (R : RecursorContextWF current recLparams)
    (i : Nat) (v : Array Expr)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R v)
    (Horigins : RecInfoHypothesisTypeOrigins stats recInfos root current u v)
    (hprocessed : v.size = i)
    (Hvi : ∀ {next : AddInductive.Context}
      (Rnext : RecursorContextWF next recLparams)
      {prior : Array Expr}
      (Hprior : RecursorRecentBoundFVarArray Rroot Rnext prior)
      (j : Nat) (hj : j < u.size),
      ((AddInductive.mkRecInfos.loopUArgs u[j] fun uiTy xs => do
        let some itIdx := AddInductive.isValidIndApp? stats uiTy
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let itIndices := uiTy.getAppArgs[stats.params.size:]
        let motiveApp := .app
          (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[j] xs)
        return (← getLCtx).mkForall xs motiveApp) next).WF fun viTy =>
          ∃ viTarget,
            TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
              viTy.consumeTypeAnnotationsVerified viTarget ∧
            Rnext.venv.IsType recLparams.length
              Rnext.mlctx.vlctx.toCtx viTarget ∧
            Nonempty (RecInfoHypothesisTypeOrigin
              stats recInfos next u[j]! viTy))
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray Rroot Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos root out u values →
      values.size = v.size + (u.size - i) →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k current).WF Q := by
  rw [AddInductive.mkRecInfos.loopU]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    refine (Hvi R Hrecent i hnext).bind fun viTy HviTy => ?_
    rcases HviTy with ⟨viTarget, HviTr, HviType, HviOrigin⟩
    have hget : ((getLCtx : AddInductive.M LocalContext) current).WF
        (fun lctx => lctx = current.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName :=
      (current.lctx.get! u[i].fvarId!).userName.appendAfter "_ih"
    refine withLocalDecl.recursorWF (name := vName) (bi := .default)
      R HviTr HviType ?_
    let R' := R.withLocalDecl (name := vName) (bi := .default)
      HviTr HviType
    have HviOrigin' := HviOrigin
    rw [← hprocessed] at HviOrigin'
    refine resultSemanticBindings stats u recInfos k Rroot R' (i + 1)
      (v.push (.fvar ⟨current.ngen.curr⟩))
      (Hrecent.pushCurrent vName viTy.consumeTypeAnnotationsVerified viTarget
        .default HviTr HviType)
      (Horigins.pushCurrent R.toBindingContextWF vName viTy .default
        (by rw [hprocessed]; exact hnext) Hrecent.contextLE HviOrigin')
      (by simp [hprocessed])
      Hvi ?_
    intro out Rout values Hvalues HvalueOrigins hsize
    apply Hk Rout values Hvalues HvalueOrigins
    simp only [Array.size_push] at hsize
    omega
  · rw [dif_neg hnext]
    exact Hk R v Hrecent Horigins (by omega)
termination_by u.size - i

/-- Semantic refinement of the actual induction-hypothesis loop, factored
through one explicit motive-application compatibility premise.  Recursive
field translations and positivity statistics are weakened automatically
across all previously generated hypotheses; the continuation therefore sees
the exact final production context as a `RecursorContextWF`. -/
theorem resultSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name}
    {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    (Hmotives : BoundFVarArray c (recInfos.map (·.motive)))
    (hrecords : recInfos.size = stats.indConsts.size)
    (Happ : ∀ {base current : AddInductive.Context}
      (Rbase : RecursorContextWF base recLparams)
      (Rcurrent : RecursorContextWF current recLparams)
      {fv : FVarId} {exposedType : Expr}
      {syntaxTarget terminalTarget fieldTarget appliedTarget : VExpr}
      {args : Array Expr} {target : Nat},
      TrExprS Rbase.venv recLparams Rbase.mlctx.vlctx
        (.fvar fv) fieldTarget →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hargs : RecursorRecentBoundFVarArray Rbase Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      (hvalid : AddInductive.isValidIndApp? stats exposedType =
        some target) →
      let itIndices := exposedType.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive itIndices)
        (mkAppN (.fvar fv) args)
      ∃ motiveTarget,
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          motiveApp motiveTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx motiveTarget)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray R Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos c out u values →
      values.size = u.size →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] k c).WF Q := by
  refine resultSemanticBindings stats u recInfos k R R 0 #[]
    (RecursorRecentBoundFVarArray.empty R)
    (RecInfoHypothesisTypeOrigins.empty stats recInfos c u) rfl ?_ ?_
  intro next Rnext prior Hprior j hj
  rcases Hfields j hj with ⟨fv, fieldTarget, hfieldEq, Hfield⟩
  let W := Rnext.onlyLams.dropN_fvlift prior.size Hprior.size_le
  have HfieldAt : TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
      (.fvar fv) (fieldTarget.liftN prior.size 0) := by
    have HfieldBase : TrExprS Rnext.venv recLparams
        (Rnext.mlctx.dropN prior.size Hprior.size_le).vlctx
        (.fvar fv) fieldTarget := by
      simpa only [Hprior.venv_eq, Hprior.drop_eq] using Hfield
    exact HfieldBase.weakFV Rnext.checking.tr.wf.ordered W
      Rnext.mlctx_wf.tr.wf
  have HstatsAt := Hstats.weakenRecent Hprior
  have hctxAt : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rnext.mlctx.vlctx :=
    Hprior.noIndConsts (names := decl.types.map (·.name)) hctx
  have hfieldBang : u[j]! = .fvar fv := by
    rw [getElem!_pos u j hj]
    exact hfieldEq
  rw [hfieldEq, hfieldBang]
  apply mkRecInfos.loopUArgs.inductionHypothesisTypeOrigin fv stats recInfos next
    Rnext HstatsAt hconsume
      (by simpa only [Hprior.venv_eq] using hlit) hctxAt hproj HfieldAt
      (Hmotives.mono Hprior.contextExtension.contextLE) hrecords
  intro current Rcurrent exposedType syntaxTarget terminalTarget
    appliedTarget args target Hexposed Hdefeq Hterminal Hargs Happlied
    HappliedType hvalid
  exact Happ Rnext Rcurrent HfieldAt Hexposed Hdefeq Hterminal Hargs
    Happlied HappliedType hvalid
  · intro out Rout values Hvalues HvalueOrigins hsize
    apply Hk Rout values Hvalues HvalueOrigins
    simpa using hsize

/-- Close the semantic induction-hypothesis loop from the retained
target-indexed motive contracts.  Unlike `resultSemantics`, this public
strengthening has no ad hoc motive-application premise: the terminal
classifier result is upgraded to `RecursorValidatedIndAppAt`, its target is
bounded by the completed mutual record cardinality, and the corresponding
independent motive contract is selected directly. -/
theorem resultSemanticsOfMotiveApplications
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    (Happlications : RecInfoMotiveApplications R stats decl recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray R Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos c out u values →
      values.size = u.size →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] k c).WF Q := by
  refine resultSemanticBindings stats u recInfos k R R 0 #[]
    (RecursorRecentBoundFVarArray.empty R)
    (RecInfoHypothesisTypeOrigins.empty stats recInfos c u) rfl ?_ ?_
  intro next Rnext prior Hprior j hj
  rcases Hfields j hj with ⟨fv, fieldTarget, hfieldEq, Hfield⟩
  let W := Rnext.onlyLams.dropN_fvlift prior.size Hprior.size_le
  have HfieldAt : TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
      (.fvar fv) (fieldTarget.liftN prior.size 0) := by
    have HfieldBase : TrExprS Rnext.venv recLparams
        (Rnext.mlctx.dropN prior.size Hprior.size_le).vlctx
        (.fvar fv) fieldTarget := by
      simpa only [Hprior.venv_eq, Hprior.drop_eq] using Hfield
    exact HfieldBase.weakFV Rnext.checking.tr.wf.ordered W
      Rnext.mlctx_wf.tr.wf
  have HstatsNext := Hstats.weakenRecent Hprior
  have hctxNext : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rnext.mlctx.vlctx :=
    Hprior.noIndConsts (names := decl.types.map (·.name)) hctx
  have hfieldBang : u[j]! = .fvar fv := by
    rw [getElem!_pos u j hj]
    exact hfieldEq
  rw [hfieldEq, hfieldBang]
  apply mkRecInfos.loopUArgs.inductionHypothesisTypeOrigin fv stats recInfos next
    Rnext HstatsNext hconsume
      (by simpa only [Hprior.venv_eq] using hlit) hctxNext hproj HfieldAt
      (Hbindings.motives.mono Hprior.contextExtension.contextLE) hrecords
  intro current Rcurrent exposedType syntaxTarget terminalTarget
    appliedTarget args target Hexposed Hdefeq Hterminal Hargs Happlied
    HappliedType hvalid
  let HstatsCurrent := HstatsNext.weakenRecent Hargs
  have htargetStats : target < stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some hvalid).1
  have htarget : target < recInfos.size := by
    rw [hrecords]
    exact htargetStats
  have htargetDecl : target < decl.types.length := by
    rw [← HstatsCurrent.types_size]
    exact htargetStats
  have hctxCurrent : VLCtx.NoIndConsts
      (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
    Hargs.noIndConsts (names := decl.types.map (·.name)) hctxNext
  let Hvalidated := HstatsCurrent.validatedIndAppAt Hexposed hvalid
    htargetDecl
      (by simpa only [Hargs.venv_eq, Hprior.venv_eq] using hlit)
    hctxCurrent hproj
  exact Happlications.applyAtMono Hbindings Horigins Hshape
    (Hprior.contextExtension.trans Hargs.contextExtension)
    target htarget Hexposed Hdefeq
    Hterminal Happlied HappliedType Hvalidated
  · intro out Rout values Hvalues HvalueOrigins hsize
    apply Hk Rout values Hvalues HvalueOrigins
    simpa using hsize

/-- Shared-telescope form used by the strengthened first pass. -/
theorem resultSemanticsOfMotiveTelescopes
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr),
      RecursorRecentBoundFVarArray R Rout values →
      RecInfoHypothesisTypeOrigins stats recInfos c out u values →
      values.size = u.size →
      (k values out).WF Q) :
    (AddInductive.mkRecInfos.loopU stats u recInfos 0 #[] k c).WF Q :=
  resultSemanticsOfMotiveApplications stats u recInfos k R Hstats
    hconsume hlit hctx hproj Hfields Htelescopes.applications Hbindings
    Horigins Hshape hrecords Hk

end mkRecInfos.loopU

namespace mkRecInfos.loopUBlueprints

/-- The blueprint-retaining hypothesis loop introduces the same fresh
hypothesis binders as `loopU`, while retaining exactly one call blueprint for
each binder. -/
theorem resultBindings {alpha : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallBlueprint →
      AddInductive.M alpha) {Q : alpha → Prop}
    (i : Nat) (v : Array Expr)
    (calls : Array AddInductive.RecCallBlueprint)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c) (Hv : FreshBoundFVarArray root c v)
    (Hroot : BindingContextLE root c)
    (hcalls : calls.size = v.size)
    (Hk : ∀ outValues outCalls c, BindingContextWF c →
      FreshBoundFVarArray root c outValues →
      BindingContextLE root c →
      outValues.size = v.size + (u.size - i) →
      outCalls.size = outValues.size →
      (k outValues outCalls c).WF Q) :
    (AddInductive.mkRecInfos.loopUBlueprints stats u recInfos i v calls
      k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopUBlueprints]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hviTy :
        ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
          let some itIdx := AddInductive.isValidIndApp? stats uiTy
            | throw (.other
              "recursive constructor field lost its inductive result type")
          let itIndices := uiTy.getAppArgs[stats.params.size:]
          let lctx ← getLCtx
          let motiveApp := .app
            (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
          let viTy := lctx.mkForall xs motiveApp
          return (viTy, ({
            major := u[i]
            args := xs
            lctx := lctx
            targetTypeIdx := itIdx
            targetIndices := itIndices
            template := lctx.mkLambda xs <|
              (mkAppN (.bvar 0) itIndices).app (mkAppN u[i] xs) } :
              AddInductive.RecCallBlueprint))) c).WF
          (fun _ => True) := by
      intro _ _
      trivial
    refine hviTy.bind fun result _ => ?_
    rcases result with ⟨viTy, call⟩
    have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
        (fun lctx => lctx = c.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName := (c.lctx.get! u[i].fvarId!).userName.appendAfter "_ih"
    apply withLocalDecl.continueRaw
    refine resultBindings stats u recInfos k (i + 1)
      (v.push (.fvar ⟨c.ngen.curr⟩)) (calls.push call) _
      (Hc.withLocalDecl vName viTy.consumeTypeAnnotationsVerified .default)
      (Hv.pushCurrent Hc Hroot vName viTy.consumeTypeAnnotationsVerified .default)
      (Hroot.trans <| BindingContextLE.withLocalDecl c Hc vName
        viTy.consumeTypeAnnotationsVerified .default) (by simp [hcalls]) ?_
    intro outValues outCalls out Hout Hvalues HrootOut hsize hcallSize
    apply Hk outValues outCalls out Hout Hvalues HrootOut
    · simp only [Array.size_push] at hsize
      omega
    · exact hcallSize
  · rw [dif_neg hnext]
    exact Hk v calls c Hc Hv Hroot (by omega) hcalls
termination_by u.size - i

/-- Semantic orchestration for the blueprint-retaining hypothesis loop.  The
proof follows the exact producer run; the continuation receives both the
fresh hypotheses and the equally-sized retained call-blueprint row. -/
theorem resultSemanticBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallBlueprint →
      AddInductive.M alpha)
    {recLparams : List Name}
    {root current : AddInductive.Context}
    (Rroot : RecursorContextWF root recLparams)
    (R : RecursorContextWF current recLparams)
    (rootScope : FVarId → Prop)
    (i : Nat) (v : Array Expr)
    (calls : Array AddInductive.RecCallBlueprint)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R v)
    (Horigins : RecInfoHypothesisTypeOrigins stats recInfos root current u v)
    (HcallOrigins : RecInfoHypothesisCallBlueprintOrigins Horigins calls)
    (HcallSemantics : RecInfoHypothesisCallSemanticOrigins Rroot decl depth
      stats (recInfos.map (·.motive)) rootScope u v calls)
    (hprocessed : v.size = i)
    (hcalls : calls.size = v.size)
    (Hvi : ∀ {next : AddInductive.Context}
      (Rnext : RecursorContextWF next recLparams)
      {prior : Array Expr}
      (Hprior : RecursorRecentBoundFVarArray Rroot Rnext prior)
      (j : Nat) (hj : j < u.size),
      ((AddInductive.mkRecInfos.loopUArgs u[j] fun uiTy xs => do
        let some itIdx := AddInductive.isValidIndApp? stats uiTy
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let itIndices := uiTy.getAppArgs[stats.params.size:]
        let lctx ← getLCtx
        let motiveApp := .app
          (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[j] xs)
        let viTy := lctx.mkForall xs motiveApp
        return (viTy, ({
          major := u[j]
          args := xs
          lctx := lctx
          targetTypeIdx := itIdx
          targetIndices := itIndices
          template := lctx.mkLambda xs <|
            (mkAppN (.bvar 0) itIndices).app (mkAppN u[j] xs) } :
            AddInductive.RecCallBlueprint))) next).WF fun result =>
          ∃ viTarget,
            TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
              result.1.consumeTypeAnnotationsVerified viTarget ∧
            Rnext.venv.IsType recLparams.length
              Rnext.mlctx.vlctx.toCtx viTarget ∧
            ∃ O : RecInfoHypothesisTypeOrigin
                stats recInfos next u[j]! result.1,
              result.2 = {
                major := u[j]!
                args := O.args
                lctx := O.current.lctx
                targetTypeIdx := O.ownerIdx
                targetIndices :=
                  O.exposedType.getAppArgs[stats.params.size:]
                template := O.current.lctx.mkLambda O.args <|
                  (mkAppN (.bvar 0)
                    O.exposedType.getAppArgs[stats.params.size:]).app
                      (mkAppN u[j]! O.args) } ∧
              RecInfoCallBlueprintSemanticOrigin stats
                (recInfos.map (·.motive)) Rnext rootScope decl
                (depth + prior.size) u[j]! result.2)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr)
      (outCalls : Array AddInductive.RecCallBlueprint),
      RecursorRecentBoundFVarArray Rroot Rout values →
      (HoutOrigins : RecInfoHypothesisTypeOrigins
        stats recInfos root out u values) →
      RecInfoHypothesisCallBlueprintOrigins HoutOrigins outCalls →
      RecInfoHypothesisCallSemanticOrigins Rroot decl depth stats
        (recInfos.map (·.motive)) rootScope u values outCalls →
      values.size = v.size + (u.size - i) →
      outCalls.size = values.size →
      (k values outCalls out).WF Q) :
    (AddInductive.mkRecInfos.loopUBlueprints stats u recInfos i v calls
      k current).WF Q := by
  rw [AddInductive.mkRecInfos.loopUBlueprints]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    refine (Hvi R Hrecent i hnext).bind fun result Hresult => ?_
    rcases result with ⟨viTy, call⟩
    rcases Hresult with
      ⟨viTarget, HviTr, HviType, O, hcall, HcallSemantic⟩
    subst i
    have hget : ((getLCtx : AddInductive.M LocalContext) current).WF
        (fun lctx => lctx = current.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    let vName :=
      (current.lctx.get! u[v.size].fvarId!).userName.appendAfter "_ih"
    refine withLocalDecl.recursorWF (name := vName) (bi := .default)
      R HviTr HviType ?_
    let R' := R.withLocalDecl (name := vName) (bi := .default)
      HviTr HviType
    refine resultSemanticBindings stats u recInfos k Rroot R' rootScope
      (v.size + 1)
      (v.push (.fvar ⟨current.ngen.curr⟩)) (calls.push call)
      (Hrecent.pushCurrent vName viTy.consumeTypeAnnotationsVerified viTarget
        .default HviTr HviType)
      (Horigins.pushCurrent R.toBindingContextWF vName viTy .default
        hnext Hrecent.contextLE ⟨O⟩)
      (HcallOrigins.pushCurrent R.toBindingContextWF vName viTy .default
        hnext Hrecent.contextLE O call hcall)
      (HcallSemantics.pushCurrent hnext Hrecent call HcallSemantic)
      (by simp) (by simp [hcalls]) Hvi ?_
    intro out Rout values outCalls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics hsize hcallSize
    apply Hk Rout values outCalls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics
    · simp only [Array.size_push] at hsize
      omega
    · exact hcallSize
  · rw [dif_neg hnext]
    exact Hk R v calls Hrecent Horigins HcallOrigins HcallSemantics
      (by omega) hcalls
termination_by u.size - i

/-- Pointwise semantic certificate for the exact pair returned by the
blueprint-producing `loopUArgs` callback. -/
theorem inductionHypothesisTypeOrigin
    (fv : FVarId) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (c : AddInductive.Context) {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    {fieldTarget : VExpr}
    (hfield : TrExprS R.venv recLparams R.mlctx.vlctx
      (.fvar fv) fieldTarget)
    {rootScope : FVarId → Prop}
    (hfieldScope : rootScope fv)
    (hrootUp : IsFVarUpSet rootScope R.mlctx.vlctx)
    (Hmotives : BoundFVarArray c (recInfos.map (·.motive)))
    (hrecords : recInfos.size = stats.indConsts.size)
    (Happ : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {exposedType : Expr} {syntaxTarget terminalTarget : VExpr}
      {appliedTarget : VExpr} {args : Array Expr} {target : Nat},
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        exposedType syntaxTarget →
      Rcurrent.venv.IsDefEqU recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx terminalTarget →
      (Hargs : RecursorRecentBoundFVarArray R Rcurrent args) →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN (.fvar fv) args) appliedTarget →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget terminalTarget →
      (hvalid : AddInductive.isValidIndApp? stats exposedType =
        some target) →
      let itIndices := exposedType.getAppArgs[stats.params.size:]
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive itIndices)
        (mkAppN (.fvar fv) args)
      ∃ motiveTarget,
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          motiveApp motiveTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx motiveTarget) :
    (AddInductive.mkRecInfos.loopUArgs (.fvar fv)
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        let targetIndices := exposedType.getAppArgs[stats.params.size:]
        let lctx ← getLCtx
        let motiveApp := Expr.app
          (mkAppN recInfos[target]!.motive targetIndices)
          (mkAppN (.fvar fv) args)
        let viTy := lctx.mkForall args motiveApp
        return (viTy, ({
          major := .fvar fv
          args := args
          lctx := lctx
          targetTypeIdx := target
          targetIndices := targetIndices
          template := lctx.mkLambda args <|
            (mkAppN (.bvar 0) targetIndices).app
              (mkAppN (.fvar fv) args) } :
            AddInductive.RecCallBlueprint))) c).WF fun result =>
        ∃ viTarget,
          TrExprS R.venv recLparams R.mlctx.vlctx
            result.1.consumeTypeAnnotationsVerified viTarget ∧
          R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx viTarget ∧
          ∃ O : RecInfoHypothesisTypeOrigin
              stats recInfos c (.fvar fv) result.1,
            result.2 = {
              major := .fvar fv
              args := O.args
              lctx := O.current.lctx
              targetTypeIdx := O.ownerIdx
              targetIndices :=
                O.exposedType.getAppArgs[stats.params.size:]
              template := O.current.lctx.mkLambda O.args <|
                (mkAppN (.bvar 0)
                  O.exposedType.getAppArgs[stats.params.size:]).app
                    (mkAppN (.fvar fv) O.args) } ∧
            RecInfoCallBlueprintSemanticOrigin stats
              (recInfos.map (·.motive)) R rootScope decl depth
              (.fvar fv) result.2 := by
  let build : Expr → Array Expr → Nat →
      AddInductive.M (Expr × AddInductive.RecCallBlueprint) :=
    fun exposedType args target => do
      let targetIndices := exposedType.getAppArgs[stats.params.size:]
      let lctx ← getLCtx
      let motiveApp := Expr.app
        (mkAppN recInfos[target]!.motive targetIndices)
        (mkAppN (.fvar fv) args)
      let viTy := lctx.mkForall args motiveApp
      return (viTy, {
        major := .fvar fv
        args := args
        lctx := lctx
        targetTypeIdx := target
        targetIndices := targetIndices
        template := lctx.mkLambda args <|
          (mkAppN (.bvar 0) targetIndices).app
            (mkAppN (.fvar fv) args) })
  have hfvScope : fv ∈ R.mlctx.vlctx.fvars := by
    simpa only [FVarsIn] using hfield.fvarsIn
  have hfvRoot : fv ∈ c.lctx.fvars := by
    rw [← R.lctx_eq, R.mlctx_wf.tr.fvars_eq]
    exact hfvScope
  have Hrun := mkRecInfos.loopUArgs.resultRecursiveDomain fv stats build c R
    Hstats hconsume hlit hctx hproj hfield hfieldScope hrootUp
    (Q := fun target result => ∃ viTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx
        result.1.consumeTypeAnnotationsVerified viTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx viTarget ∧
      ∃ O : RecInfoHypothesisTypeOrigin
          stats recInfos c (.fvar fv) result.1,
        O.ownerIdx = target ∧
        result.2 = {
          major := .fvar fv
          args := O.args
          lctx := O.current.lctx
          targetTypeIdx := O.ownerIdx
          targetIndices :=
            O.exposedType.getAppArgs[stats.params.size:]
          template := O.current.lctx.mkLambda O.args <|
            (mkAppN (.bvar 0)
              O.exposedType.getAppArgs[stats.params.size:]).app
                (mkAppN (.fvar fv) O.args) } ∧
        ∀ (domain : VExpr),
          R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
            fieldTarget domain →
          ∀ (htarget : O.ownerIdx < decl.types.length),
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[O.ownerIdx]'htarget).name
              R.mlctx.vlctx.toCtx depth domain →
          RecInfoCallBlueprintSemanticOrigin stats
            (recInfos.map (·.motive)) R rootScope decl depth
            (.fvar fv) result.2) ?_
  · change (AddInductive.mkRecInfos.loopUArgs (.fvar fv)
      (fun exposedType args => do
        let some target := AddInductive.isValidIndApp? stats exposedType
          | throw (.other
            "recursive constructor field lost its inductive result type")
        build exposedType args target) c).WF _
    exact Hrun.mono (fun result Hout => by
      rcases Hout with ⟨domain, hfieldType, target, htarget,
        hrecursive, viTarget, Hvi, HviType, O, howner, hcall, Hsemantic⟩
      subst target
      exact ⟨viTarget, Hvi, HviType, O, hcall,
        Hsemantic domain hfieldType htarget hrecursive⟩)
  · intro Hinput current Rcurrent exposedType syntaxTarget terminalTarget
      appliedTarget args target Htrace Hexposed Hdefeq Hterminal Hargs Happlied
      HappliedType hvalid hexposedScope hup
    rcases Happ Rcurrent Hexposed Hdefeq Hterminal Hargs Happlied
        HappliedType hvalid with ⟨motiveTarget, Hmotive, HmotiveType⟩
    have htargetStats : target < stats.indConsts.size :=
      (checkPositivityStep.isValidIndApp?_some hvalid).1
    have htarget : target < recInfos.size := by
      rw [hrecords]
      exact htargetStats
    rcases Hmotives.get_eq_fvar target
        (by simpa using htarget) with
      ⟨motiveFVar, hmotiveFVar, hmotiveMember⟩
    rcases Hargs.mkForall Hmotive HmotiveType with
      ⟨viTarget, Hvi, HviType⟩
    let targetIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[target]!.motive targetIndices)
      (mkAppN (.fvar fv) args)
    rcases hconsume c recLparams R Hvi HviType with
      ⟨consumedTarget, Hconsumed⟩
    change (Except.ok (current.lctx.mkForall args motiveApp,
      ({
        major := .fvar fv
        args := args
        lctx := current.lctx
        targetTypeIdx := target
        targetIndices := targetIndices
        template := current.lctx.mkLambda args <|
          (mkAppN (.bvar 0) targetIndices).app
            (mkAppN (.fvar fv) args) } :
          AddInductive.RecCallBlueprint))).WF _
    let O : RecInfoHypothesisTypeOrigin stats recInfos c
        (.fvar fv) (current.lctx.mkForall args motiveApp) := {
        current := current
        current_wf := Rcurrent.toBindingContextWF
        current_extends := Hargs.contextLE
        exposedType := exposedType
        args := args
        arguments_bound := Hargs.toFreshBoundFVarArray
        loopInput := Hinput
        loopTrace := Htrace
        field_fvar := ⟨fv, rfl, hfvRoot⟩
        ownerIdx := target
        owner_valid := hvalid
        motive_is_fvar := ⟨motiveFVar, by
          rw [getElem!_pos recInfos target htarget]
          simpa only [Array.getElem_map] using hmotiveFVar,
          hmotiveMember⟩
        type_eq := rfl }
    refine Except.WF.pure
      ⟨consumedTarget, Hconsumed.consumed, Hconsumed.isType, O, rfl, rfl, ?_⟩
    intro domain hfieldTyping htargetDecl hrecursive
    refine { semantic := ?_ }
    intro indTypes minors lvls
    let call : AddInductive.RecCallBlueprint := {
      major := .fvar fv
      args := args
      lctx := current.lctx
      targetTypeIdx := target
      targetIndices := targetIndices
      template := current.lctx.mkLambda args <|
        (mkAppN (.bvar 0) targetIndices).app
          (mkAppN (.fvar fv) args) }
    let value := call.build indTypes stats (recInfos.map (·.motive))
      minors lvls
    let Hgenerated : BoundGeneratedRecursiveCall indTypes stats
        (recInfos.map (·.motive)) minors lvls c (.fvar fv) value := {
      exposedType := exposedType
      ownerIdx := target
      owner_valid := hvalid
      localArgs := args
      current := current
      current_wf := Rcurrent.toBindingContextWF
      current_extends := Hargs.contextLE
      arguments_bound := Hargs.toFreshBoundFVarArray
      value_eq := by
        simp [value, call, AddInductive.RecCallBlueprint.build,
          AddInductive.getIIndices, hvalid, targetIndices] }
    let HstatsCurrent := Hstats.weakenRecent Hargs
    have hctxCurrent : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
      Hargs.noIndConsts (names := decl.types.map (·.name)) hctx
    let Hvalidated := HstatsCurrent.validatedIndAppAt Hexposed hvalid
      htargetDecl (by simpa only [Hargs.venv_eq] using hlit)
      hctxCurrent hproj
    have HexposedType : Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx syntaxTarget :=
      VEnv.IsType.defeqU_l Rcurrent.checking.tr.wf
        Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm Hterminal
    have HappliedType' : Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget syntaxTarget :=
      HappliedType.defeqU_r Rcurrent.checking.tr.wf
        Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm
    let commonDomains := MLCtxForallDomains Rcurrent.mlctx
      args.size Hargs.size_le
    have HexposedClosed := Hargs.mkForallExact Hexposed HexposedType
    have HappliedClosed := Hargs.mkLambda Happlied HappliedType'
    let S : SemanticBoundGeneratedRecursiveCall indTypes stats
        (recInfos.map (·.motive)) minors lvls R decl depth (.fvar fv)
        value := {
      generated := Hgenerated
      current_context := Rcurrent
      recent := Hargs
      rootScope := rootScope
      exposed_scope := hexposedScope
      current_scope_up := hup
      exposedTarget := syntaxTarget
      exposed_translation := Hexposed
      terminalTarget := terminalTarget
      exposed_defeq := Hdefeq
      terminal_type := Hterminal
      appliedFieldTarget := appliedTarget
      applied_field_translation := Happlied
      applied_field_typing := HappliedType
      validated := Hvalidated
      commonDomains := commonDomains
      commonDomains_length :=
        Rcurrent.onlyLams.forallDomains_length args.size Hargs.size_le
      common_exposed_translation := by
        simpa [commonDomains] using HexposedClosed.1
      common_exposed_type := by
        simpa [commonDomains] using HexposedClosed.2
      common_applied_translation := by
        simpa [commonDomains] using HappliedClosed.1
      common_applied_typing := by
        simpa [commonDomains] using HappliedClosed.2
      fieldTarget := fieldTarget
      domain := domain
      field_translation := hfield
      field_typing := hfieldTyping
      owner_lt := htargetDecl
      recursive := hrecursive }
    refine ⟨S, rfl, ⟨?_⟩⟩
    refine {
      target := motiveTarget
      translation := ?_
      typing := HmotiveType }
    simpa [S, Hgenerated, targetIndices, Array.getElem!_eq_getD,
      Array.getD, htarget] using Hmotive

/-- Close the retained-blueprint hypothesis loop from the independently
verified motive applications.  The additional output is produced by the same
successful traversal, so no replay or alpha-compatibility premise is needed. -/
theorem resultSemanticsOfMotiveApplications
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallBlueprint →
      AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (rootScope : FVarId → Prop)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget ∧ rootScope fv)
    (rootScopeInContext : ∀ fv, rootScope fv → fv ∈ R.mlctx.vlctx.fvars)
    (hrootUp : IsFVarUpSet rootScope R.mlctx.vlctx)
    (Happlications : RecInfoMotiveApplications R stats decl recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr)
      (calls : Array AddInductive.RecCallBlueprint),
      RecursorRecentBoundFVarArray R Rout values →
      (HoutOrigins : RecInfoHypothesisTypeOrigins
        stats recInfos c out u values) →
      RecInfoHypothesisCallBlueprintOrigins HoutOrigins calls →
      RecInfoHypothesisCallSemanticOrigins R decl depth stats
        (recInfos.map (·.motive)) rootScope u values calls →
      values.size = u.size →
      calls.size = values.size →
      (k values calls out).WF Q) :
    (AddInductive.mkRecInfos.loopUBlueprints stats u recInfos 0 #[] #[]
      k c).WF Q := by
  refine resultSemanticBindings stats u recInfos k R R rootScope 0 #[] #[]
    (RecursorRecentBoundFVarArray.empty R)
    (RecInfoHypothesisTypeOrigins.empty stats recInfos c u)
    (RecInfoHypothesisCallBlueprintOrigins.empty
      (RecInfoHypothesisTypeOrigins.empty stats recInfos c u))
    (RecInfoHypothesisCallSemanticOrigins.empty R decl depth stats
      (recInfos.map (·.motive)) rootScope u)
    rfl rfl ?_ ?_
  intro next Rnext prior Hprior j hj
  rcases Hfields j hj with ⟨fv, fieldTarget, hfieldEq, Hfield, hfieldScope⟩
  let W := Rnext.onlyLams.dropN_fvlift prior.size Hprior.size_le
  have HfieldAt : TrExprS Rnext.venv recLparams Rnext.mlctx.vlctx
      (.fvar fv) (fieldTarget.liftN prior.size 0) := by
    have HfieldBase : TrExprS Rnext.venv recLparams
        (Rnext.mlctx.dropN prior.size Hprior.size_le).vlctx
        (.fvar fv) fieldTarget := by
      simpa only [Hprior.venv_eq, Hprior.drop_eq] using Hfield
    exact HfieldBase.weakFV Rnext.checking.tr.wf.ordered W
      Rnext.mlctx_wf.tr.wf
  have HstatsNext := Hstats.weakenRecent Hprior
  have hctxNext : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rnext.mlctx.vlctx :=
    Hprior.noIndConsts (names := decl.types.map (·.name)) hctx
  have hfieldBang : u[j]! = .fvar fv := by
    rw [getElem!_pos u j hj]
    exact hfieldEq
  rw [hfieldEq, hfieldBang]
  apply inductionHypothesisTypeOrigin fv stats recInfos next
    Rnext HstatsNext hconsume
      (by simpa only [Hprior.venv_eq] using hlit) hctxNext hproj HfieldAt
      hfieldScope (Hprior.upsetRoot rootScopeInContext hrootUp)
      (Hbindings.motives.mono Hprior.contextExtension.contextLE) hrecords
  intro current Rcurrent exposedType syntaxTarget terminalTarget
    appliedTarget args target Hexposed Hdefeq Hterminal Hargs Happlied
    HappliedType hvalid
  let HstatsCurrent := HstatsNext.weakenRecent Hargs
  have htargetStats : target < stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some hvalid).1
  have htarget : target < recInfos.size := by
    rw [hrecords]
    exact htargetStats
  have htargetDecl : target < decl.types.length := by
    rw [← HstatsCurrent.types_size]
    exact htargetStats
  have hctxCurrent : VLCtx.NoIndConsts
      (decl.types.map (·.name)) Rcurrent.mlctx.vlctx :=
    Hargs.noIndConsts (names := decl.types.map (·.name)) hctxNext
  let Hvalidated := HstatsCurrent.validatedIndAppAt Hexposed hvalid
    htargetDecl
      (by simpa only [Hargs.venv_eq, Hprior.venv_eq] using hlit)
    hctxCurrent hproj
  exact Happlications.applyAtMono Hbindings Horigins Hshape
    (Hprior.contextExtension.trans Hargs.contextExtension)
    target htarget Hexposed Hdefeq
    Hterminal Happlied HappliedType Hvalidated
  · intro out Rout values calls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics hsize hcallSize
    apply Hk Rout values calls Hvalues HvalueOrigins HvalueCallOrigins
      HvalueCallSemantics
    · simpa using hsize
    · exact hcallSize

/-- Shared-telescope form of the blueprint-retaining first pass. -/
theorem resultSemanticsOfMotiveTelescopes
    {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → Array AddInductive.RecCallBlueprint →
      AddInductive.M alpha)
    {recLparams : List Name} {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (rootScope : FVarId → Prop)
    {decl : VInductDecl} {depth : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hfields : ∀ j (hj : j < u.size),
      ∃ fv fieldTarget,
        u[j] = .fvar fv ∧
        TrExprS R.venv recLparams R.mlctx.vlctx
          (.fvar fv) fieldTarget ∧ rootScope fv)
    (rootScopeInContext : ∀ fv, rootScope fv → fv ∈ R.mlctx.vlctx.fvars)
    (hrootUp : IsFVarUpSet rootScope R.mlctx.vlctx)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hk : ∀ {out : AddInductive.Context}
      (Rout : RecursorContextWF out recLparams)
      (values : Array Expr)
      (calls : Array AddInductive.RecCallBlueprint),
      RecursorRecentBoundFVarArray R Rout values →
      (HoutOrigins : RecInfoHypothesisTypeOrigins
        stats recInfos c out u values) →
      RecInfoHypothesisCallBlueprintOrigins HoutOrigins calls →
      RecInfoHypothesisCallSemanticOrigins R decl depth stats
        (recInfos.map (·.motive)) rootScope u values calls →
      values.size = u.size →
      calls.size = values.size →
      (k values calls out).WF Q) :
    (AddInductive.mkRecInfos.loopUBlueprints stats u recInfos 0 #[] #[]
      k c).WF Q :=
  resultSemanticsOfMotiveApplications stats u recInfos k R rootScope Hstats
    hconsume hlit hctx hproj Hfields rootScopeInContext hrootUp
    Htelescopes.applications Hbindings
    Horigins Hshape hrecords Hk

end mkRecInfos.loopUBlueprints

/-- Equality of the four pre-existing semantic projections of a `RecInfo`
array.  Retaining executable rule blueprints changes no binding, type-origin,
or telescope input. -/
structure RecInfoCoreEq (left right : Array AddInductive.RecInfo) : Prop where
  size_eq : left.size = right.size
  motive_eq_all : ∀ (i : Nat), left[i]!.motive = right[i]!.motive
  motive_eq : ∀ i (hi : i < left.size),
    left[i]!.motive = right[i]!.motive
  minors_eq : ∀ i (hi : i < left.size),
    left[i]!.minors = right[i]!.minors
  indices_eq : ∀ i (hi : i < left.size),
    left[i]!.indices = right[i]!.indices
  major_eq : ∀ i (hi : i < left.size),
    left[i]!.major = right[i]!.major

theorem RecInfoCoreEq.map_motive
    (H : RecInfoCoreEq left right) :
    left.map (·.motive) = right.map (·.motive) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.motive_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

theorem RecInfoCoreEq.map_major
    (H : RecInfoCoreEq left right) :
    left.map (·.major) = right.map (·.major) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.major_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

theorem RecInfoCoreEq.map_minors
    (H : RecInfoCoreEq left right) :
    left.map (·.minors) = right.map (·.minors) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.minors_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

theorem RecInfoCoreEq.map_indices
    (H : RecInfoCoreEq left right) :
    left.map (·.indices) = right.map (·.indices) := by
  apply Array.ext
  · simpa using H.size_eq
  · intro i hiLeft hiRight
    have hi : i < left.size := by simpa using hiLeft
    have h := H.indices_eq i hi
    rw [getElem!_pos left i hi,
      getElem!_pos right i (by simpa [← H.size_eq] using hi)] at h
    simpa only [Array.getElem_map] using h

theorem RecInfoCoreEq.indices_eq_all
    (H : RecInfoCoreEq left right) (i : Nat) :
    left[i]!.indices = right[i]!.indices := by
  by_cases hi : i < left.size
  · exact H.indices_eq i hi
  · have hi' : ¬ i < right.size := by
      intro hi'
      apply hi
      rwa [H.size_eq]
    simp [Array.getElem!_eq_getD, Array.getD, hi, hi']

theorem RecInfoCoreEq.major_eq_all
    (H : RecInfoCoreEq left right) (i : Nat) :
    left[i]!.major = right[i]!.major := by
  by_cases hi : i < left.size
  · exact H.major_eq i hi
  · have hi' : ¬ i < right.size := by
      intro hi'
      apply hi
      rwa [H.size_eq]
    simp [Array.getElem!_eq_getD, Array.getD, hi, hi']

def RecursorMotiveBinding.congrInfo
    (B : RecursorMotiveBinding R info elimLevel)
    (hmotive : info.motive = info'.motive)
    (hindices : info.indices = info'.indices)
    (hmajor : info.major = info'.major) :
    RecursorMotiveBinding R info' elimLevel where
  motiveTarget := B.motiveTarget
  motiveTypeTarget := B.motiveTypeTarget
  motive := by simpa only [← hmotive] using B.motive
  motiveType := by
    simpa only [← hindices, ← hmajor] using B.motiveType
  typing := B.typing
  typeIsType := B.typeIsType

def RecursorMotiveTelescopeEvidence.congrInfo
    (E : RecursorMotiveTelescopeEvidence R stats info B exposedType
      syntaxTarget)
    (hmotive : info.motive = info'.motive)
    (hindices : info.indices = info'.indices)
    (hmajor : info.major = info'.major) :
    RecursorMotiveTelescopeEvidence R stats info'
      (B.congrInfo hmotive hindices hmajor) exposedType syntaxTarget where
  indices := E.indices
  family := E.family
  familyActualType := E.familyActualType
  familyType := E.familyType
  motiveType := E.motiveType
  resultLevel := E.resultLevel
  syntax_eq := E.syntax_eq
  indices_translation := E.indices_translation
  family_typing := E.family_typing
  family_type_defeq := E.family_type_defeq
  motive_type_defeq := E.motive_type_defeq
  telescope := E.telescope

structure RecInfoMotiveCoreEq
    (left right : Array AddInductive.RecInfo) : Prop where
  map_motive : left.map (·.motive) = right.map (·.motive)
  motive_eq : ∀ (i : Nat), left[i]!.motive = right[i]!.motive
  indices_eq : ∀ (i : Nat), left[i]!.indices = right[i]!.indices
  major_eq : ∀ (i : Nat), left[i]!.major = right[i]!.major

theorem RecInfoMotiveCoreEq.size_eq
    (H : RecInfoMotiveCoreEq left right) : left.size = right.size := by
  have h := congrArg Array.size H.map_motive
  simpa using h

theorem RecInfoMotiveTelescopes.rebaseMotiveCore
    (T : RecInfoMotiveTelescopes R stats decl parameterCtx left elimLevel)
    (H : RecInfoMotiveCoreEq left right) :
    RecInfoMotiveTelescopes R stats decl parameterCtx right elimLevel := by
  refine ⟨?_, ?_, ?_⟩
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    apply RecursorMotiveTelescopeAt.congrInfo (T.telescope target htarget')
    · exact (H.motive_eq target).symm
    · exact (H.indices_eq target).symm
    · exact (H.major_eq target).symm
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases T.seed target htarget' with ⟨S, hparams⟩
    let S' := S.congrInfo (H.indices_eq target).symm
      (H.major_eq target).symm
    exact ⟨S', by
      simpa [S', RecursorMotiveTelescopeSeed.congrInfo] using hparams⟩
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases T.seed target htarget' with ⟨S, hparams⟩
    let S' := S.congrInfo (H.indices_eq target).symm
      (H.major_eq target).symm
    exact ⟨S'.canonical, by
      simpa [S', RecursorMotiveTelescopeSeed.congrInfo] using hparams⟩

theorem RecInfoMotiveTelescopeLookup.rebaseMotiveCore
    (K : RecInfoMotiveTelescopeLookup R stats decl left elimLevel)
    (H : RecInfoMotiveCoreEq left right) :
    RecInfoMotiveTelescopeLookup R stats decl right elimLevel where
  evidence target htarget _current Rcurrent Hext _depth _exposedType
      _syntaxTarget Hexposed HsyntaxType Hvalidated := by
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases K.evidence target htarget' Rcurrent Hext Hexposed HsyntaxType
        Hvalidated with ⟨binding, ⟨evidence⟩⟩
    let binding' := binding.congrInfo (H.motive_eq target)
      (H.indices_eq target) (H.major_eq target)
    let evidence' := evidence.congrInfo (H.motive_eq target)
      (H.indices_eq target) (H.major_eq target)
    exact ⟨binding', ⟨evidence'⟩⟩

theorem RecInfoRuleBlueprintSemanticOriginAt.rebaseMotiveCore
    (Horigin : RecInfoRuleBlueprintSemanticOriginAt R decl stats left
      elimLevel parameterDecls expectedOwnerIdx S B)
    (H : RecInfoMotiveCoreEq left right) :
    RecInfoRuleBlueprintSemanticOriginAt R decl stats right elimLevel
      parameterDecls expectedOwnerIdx S B := by
  unfold RecInfoRuleBlueprintSemanticOriginAt at Horigin ⊢
  rcases Horigin with
    ⟨origins, hshape, hstats, hmotives, F, hparams, depth, HvalidStats,
      fields, Hselection, hexpectedValid, hexpectedLt, ownerIdx,
      htargetValid, Hvalidated, binding, ⟨Hevidence⟩,
      ⟨Hlookup⟩, Hcalls⟩
  let binding' := binding.congrInfo (H.motive_eq ownerIdx)
    (H.indices_eq ownerIdx) (H.major_eq ownerIdx)
  let evidence' := Hevidence.congrInfo (H.motive_eq ownerIdx)
    (H.indices_eq ownerIdx) (H.major_eq ownerIdx)
  have Hcalls' := Hcalls
  rw [H.map_motive] at Hcalls'
  exact ⟨origins, hshape, hstats, hmotives.trans H.map_motive,
    F, hparams, depth, HvalidStats, fields, Hselection, hexpectedValid,
    hexpectedLt, ownerIdx, htargetValid, Hvalidated,
    binding', ⟨evidence'⟩,
    ⟨Hlookup.rebaseMotiveCore H⟩, Hcalls'⟩

theorem RecInfoCoreEq.flatMap_minors
    (H : RecInfoCoreEq left right) :
    left.flatMap (·.minors) = right.flatMap (·.minors) := by
  apply Array.toList_inj.mp
  simpa [Array.toList_flatMap, Array.toList_map, List.flatMap_map] using
    congrArg (fun a : Array (Array Expr) =>
      a.toList.flatMap Array.toList) H.map_minors

theorem RecInfoCoreEq.flatMap_indices
    (H : RecInfoCoreEq left right) :
    left.flatMap (·.indices) = right.flatMap (·.indices) := by
  apply Array.toList_inj.mp
  simpa [Array.toList_flatMap, Array.toList_map, List.flatMap_map] using
    congrArg (fun a : Array (Array Expr) =>
      a.toList.flatMap Array.toList) H.map_indices

def BoundFVarArray.rebaseExprs
    (B : BoundFVarArray c xs) (h : xs = ys) : BoundFVarArray c ys where
  fvars := B.fvars
  expressions := h.symm.trans B.expressions
  members := B.members

def RecInfoBindings.rebaseCore
    (B : RecInfoBindings c left) (H : RecInfoCoreEq left right) :
    RecInfoBindings c right where
  motives := B.motives.rebaseExprs H.map_motive
  majors := B.majors.rebaseExprs H.map_major
  indices i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    exact (B.indices i hi').rebaseExprs (H.indices_eq i hi')
  minors i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    exact (B.minors i hi').rebaseExprs (H.minors_eq i hi')

theorem RecInfoBindings.rebaseCore_motives_fvars
    (B : RecInfoBindings c left) (H : RecInfoCoreEq left right) :
    (B.rebaseCore H).motives.fvars = B.motives.fvars := rfl

theorem RecInfoBindings.rebaseCore_majors_fvars
    (B : RecInfoBindings c left) (H : RecInfoCoreEq left right) :
    (B.rebaseCore H).majors.fvars = B.majors.fvars := rfl

theorem RecInfoBindings.rebaseCore_flatMinors_fvars
    (B : RecInfoBindings c left) (H : RecInfoCoreEq left right) :
    (B.rebaseCore H).flatMinors.fvars = B.flatMinors.fvars := by
  calc
    (B.rebaseCore H).flatMinors.fvars =
        ExprArrayFVarIds (right.flatMap (·.minors)) :=
      ((B.rebaseCore H).flatMinors.exprArrayFVarIds).symm
    _ = ExprArrayFVarIds (left.flatMap (·.minors)) := by rw [H.flatMap_minors]
    _ = B.flatMinors.fvars := B.flatMinors.exprArrayFVarIds

theorem RecInfoBindings.rebaseCore_flatIndices_fvars
    (B : RecInfoBindings c left) (H : RecInfoCoreEq left right) :
    (B.rebaseCore H).flatIndices.fvars = B.flatIndices.fvars := by
  calc
    (B.rebaseCore H).flatIndices.fvars =
        ExprArrayFVarIds (right.flatMap (·.indices)) :=
      ((B.rebaseCore H).flatIndices.exprArrayFVarIds).symm
    _ = ExprArrayFVarIds (left.flatMap (·.indices)) := by rw [H.flatMap_indices]
    _ = B.flatIndices.fvars := B.flatIndices.exprArrayFVarIds

theorem RecInfoBindings.NoAlias.rebaseCore
    {stats : AddInductive.InductiveStats}
    (B : RecInfoBindings c left) (params : BoundFVarArray c stats.params)
    (N : RecInfoBindings.NoAlias B params)
    (H : RecInfoCoreEq left right) :
    RecInfoBindings.NoAlias (B.rebaseCore H) params := by
  unfold RecInfoBindings.NoAlias at N ⊢
  unfold RecInfoBindings.allFvars at N ⊢
  rw [← H.map_motive, ← H.map_major, ← H.flatMap_minors,
    ← H.flatMap_indices]
  exact N

theorem RecInfoOuterOrder.rebaseCore
    (B : RecInfoBindings c left)
    (O : RecInfoOuterOrder R params B) (H : RecInfoCoreEq left right) :
    RecInfoOuterOrder R params (B.rebaseCore H) := by
  unfold RecInfoOuterOrder at O ⊢
  simpa only [B.rebaseCore_motives_fvars H,
    B.rebaseCore_flatMinors_fvars H] using O

def RecInfoTypeOrigins.rebaseCore
    (O : RecInfoTypeOrigins c left) (H : RecInfoCoreEq left right) :
    RecInfoTypeOrigins c right where
  motiveTypes := O.motiveTypes
  majorTypes := O.majorTypes
  indexTypes := O.indexTypes
  minorTypes := O.minorTypes
  indexTypes_size := O.indexTypes_size.trans H.size_eq
  minorTypes_size := O.minorTypes_size.trans H.size_eq
  motives := H.map_motive ▸ O.motives
  majors := H.map_major ▸ O.majors
  indices i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    rw [← H.indices_eq i hi']
    exact O.indices i hi'
  minors i hi := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    rw [← H.minors_eq i hi']
    exact O.minors i hi'
  minorShapes i hi j hj := by
    have hi' : i < left.size := by simpa [H.size_eq] using hi
    exact O.minorShapes i hi' j hj

theorem RecInfoMajorTypeShapes.rebaseCore
    (S : RecInfoMajorTypeShapes stats left majorTypes)
    (H : RecInfoCoreEq left right) :
    RecInfoMajorTypeShapes stats right majorTypes := by
  refine ⟨S.size_eq.trans H.size_eq, ?_⟩
  intro i hi
  have hi' : i < left.size := by simpa [H.size_eq] using hi
  rw [← H.indices_eq i hi']
  exact S.shape i hi'

theorem RecInfoMotiveTypeShapes.rebaseCore
    (S : RecInfoMotiveTypeShapes c left motiveTypes elimLevel)
    (H : RecInfoCoreEq left right) :
    RecInfoMotiveTypeShapes c right motiveTypes elimLevel := by
  refine ⟨S.size_eq.trans H.size_eq, ?_⟩
  intro i hi
  have hi' : i < left.size := by simpa [H.size_eq] using hi
  rw [← H.indices_eq i hi', ← H.major_eq i hi']
  exact S.shape i hi'

theorem RecInfoMotiveTelescopes.rebaseCore
    (T : RecInfoMotiveTelescopes R stats decl parameterCtx left elimLevel)
    (H : RecInfoCoreEq left right) :
    RecInfoMotiveTelescopes R stats decl parameterCtx right elimLevel := by
  refine ⟨?_, ?_, ?_⟩
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    apply RecursorMotiveTelescopeAt.congrInfo (T.telescope target htarget')
    · exact (H.motive_eq target htarget').symm
    · exact (H.indices_eq target htarget').symm
    · exact (H.major_eq target htarget').symm
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases T.seed target htarget' with ⟨S, hparams⟩
    let S' := S.congrInfo (H.indices_eq target htarget').symm
      (H.major_eq target htarget').symm
    exact ⟨S', by
      simpa [S', RecursorMotiveTelescopeSeed.congrInfo] using hparams⟩
  · intro target htarget
    have htarget' : target < left.size := by
      simpa [H.size_eq] using htarget
    rcases T.seed target htarget' with ⟨S, hparams⟩
    let S' := S.congrInfo (H.indices_eq target htarget').symm
      (H.major_eq target htarget').symm
    exact ⟨S'.canonical, by
      simpa [S', RecursorMotiveTelescopeSeed.congrInfo] using hparams⟩

theorem RecInfoArities.rebaseCore
    (A : RecInfoArities stats left) (H : RecInfoCoreEq left right) :
    RecInfoArities stats right := by
  intro i hi
  have hi' : i < left.size := by simpa [H.size_eq] using hi
  rw [← H.indices_eq i hi']
  exact A i hi'

theorem RecInfoMinorTypeShape.HasHypothesisTypeOrigins.rebaseCore
    (S : RecInfoMinorTypeShape)
    (P : RecInfoMinorTypeShape.HasHypothesisTypeOrigins S stats left)
    (H : RecInfoCoreEq left right) :
    RecInfoMinorTypeShape.HasHypothesisTypeOrigins S stats right := by
  unfold RecInfoMinorTypeShape.HasHypothesisTypeOrigins at P ⊢
  cases hopt : S.hypothesis_type_origins with
  | none => simp [hopt] at P
  | some origins =>
      simp only [hopt, Option.some.injEq] at P ⊢
      exact ⟨P.1, P.2.trans H.map_motive⟩

theorem RecInfoMinorSemanticAlignment.rebaseCore
    (O : RecInfoTypeOrigins c left)
    (A : RecInfoMinorSemanticAlignment R O parameterDecls)
    (H : RecInfoCoreEq left right) :
    RecInfoMinorSemanticAlignment R (O.rebaseCore H) parameterDecls := by
  intro owner howner localIndex hlocal
  have howner' : owner < left.size := by simpa [H.size_eq] using howner
  simpa [RecInfoTypeOrigins.rebaseCore] using
    A owner howner' localIndex hlocal

theorem RecInfoMinorSourceAlignment.rebaseCore
    (O : RecInfoTypeOrigins c left)
    (A : RecInfoMinorSourceAlignment stats indTypes O)
    (H : RecInfoCoreEq left right) :
    RecInfoMinorSourceAlignment stats indTypes (O.rebaseCore H) := by
  intro owner howner hsourceOwner localIndex hlocal
  have howner' : owner < left.size := by simpa [H.size_eq] using howner
  rcases A owner howner' hsourceOwner localIndex hlocal with
    ⟨horigin, hindex, hsource, hhypotheses, traversal, htraversal,
      hctor, hfields, hrecursive, hstats, hvalid, hmotive,
      hroot, hterminal, hfull⟩
  refine ⟨horigin, hindex, hsource,
    RecInfoMinorTypeShape.HasHypothesisTypeOrigins.rebaseCore _
      hhypotheses H,
    traversal, htraversal, hctor, hfields, hrecursive, hstats, hvalid,
    ?_, hroot, hterminal, hfull⟩
  rcases hindices : AddInductive.getIIndices stats traversal.terminal with
    ⟨motiveOwner, indices⟩
  change (O.minorShapes owner howner' localIndex hlocal).motiveApp =
    Expr.app (mkAppN right[motiveOwner]!.motive indices)
      (mkAppN
        (mkAppN (.const
          (O.minorShapes owner howner' localIndex hlocal).constructor.name
            stats.levels) stats.params)
        (O.minorShapes owner howner' localIndex hlocal).fields)
  rw [← H.motive_eq_all]
  simpa only [hindices] using hmotive

theorem modifyMinorAndBlueprint_coreEq
    (recInfos : Array AddInductive.RecInfo) (dIdx : Nat)
    (hidx : dIdx < recInfos.size) (minor : Expr)
    (blueprint : AddInductive.RecRuleBlueprint) :
    RecInfoCoreEq
      (recInfos.modify dIdx fun info =>
        { info with minors := info.minors.push minor })
      (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push minor
          ruleBlueprints := info.ruleBlueprints.push blueprint }) := by
  constructor
  · simp
  · intro i
    by_cases hi : i < recInfos.size
    · by_cases hself : dIdx = i
      · subst i
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hself]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hself]
    · simp [Array.getElem!_eq_getD, Array.getD, hi]
  all_goals
    intro i hi
    have hi' : i < recInfos.size := by simpa using hi
    by_cases hself : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi' hself]
      rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi' hself]

theorem modifyMinorAndBlueprint_motiveCoreEq
    (recInfos : Array AddInductive.RecInfo) (dIdx : Nat)
    (hidx : dIdx < recInfos.size)
    (minor : Expr) (blueprint : AddInductive.RecRuleBlueprint) :
    RecInfoMotiveCoreEq recInfos
      (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push minor
          ruleBlueprints := info.ruleBlueprints.push blueprint }) := by
  let next := recInfos.modify dIdx fun info =>
    { info with
      minors := info.minors.push minor
      ruleBlueprints := info.ruleBlueprints.push blueprint }
  have hfield : ∀ (i : Nat),
      recInfos[i]!.motive = next[i]!.motive ∧
      recInfos[i]!.indices = next[i]!.indices ∧
      recInfos[i]!.major = next[i]!.major := by
    intro i
    by_cases hi : i < recInfos.size
    · by_cases hself : dIdx = i
      · subst i
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
        simp
      · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi
          hself]
        simp
    · have hiNext : ¬ i < next.size := by simpa [next] using hi
      simp [Array.getElem!_eq_getD, Array.getD, hi, hiNext]
  refine {
    map_motive := ?_
    motive_eq := fun i => (hfield i).1
    indices_eq := fun i => (hfield i).2.1
    major_eq := fun i => (hfield i).2.2 }
  apply Array.ext
  · simp [next]
  · intro i hiLeft hiRight
    have hiLeft' : i < recInfos.size := by simpa using hiLeft
    have hiRight' : i < next.size := by
      dsimp [next]
      simpa using hiRight
    rw [Array.getElem_map, Array.getElem_map]
    have h := (hfield i).1
    rw [getElem!_pos recInfos i hiLeft', getElem!_pos next i hiRight'] at h
    exact h

namespace mkRecInfos.loopCtors

/-- Semantic boundary for the final action of one constructor iteration.
Once the complete minor domain has been independently translated and typed,
this mirrors production's `withLocalDecl`, updates the owning minor row, and
transports every first-pass semantic invariant into the new context. -/
theorem continueMinorSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (minorName : Name) (minorTy : Expr)
    (mkBlueprint : Expr → AddInductive.RecRuleBlueprint)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hblueprints : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (HblueprintSemantics : RecInfoRuleBlueprintSemanticOrigins R decl stats
      recInfos elimLevel Hsuffix.parameterDecls Horigins)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    {minorTarget : VExpr}
    (Hminor : TrExprS R.venv recLparams R.mlctx.vlctx
      minorTy.consumeTypeAnnotationsVerified minorTarget)
    (HminorType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx minorTarget)
    (HminorShape : RecInfoMinorTypeShape)
    (HminorShapePosition :
      HminorShape.localIndex = Horigins.minorTypes[dIdx]!.size ∧
      HminorShape.origin = minorTy.consumeTypeAnnotationsVerified)
    (HminorSource : HminorShape.sourceConstructors =
      indTypes[dIdx]!.ctors)
    (HminorHypothesisOrigins :
      HminorShape.HasHypothesisTypeOrigins stats recInfos)
    (HminorSemantic :
      Nonempty (RecInfoMinorSemanticSourceAt R HminorShape
        Hsuffix.parameterDecls))
    (HminorFieldsFresh : ∀ fv ∈ HminorShape.fields_bound.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars)
    (HminorTraversal : ∃ traversal,
      HminorShape.traversal = some traversal ∧
      traversal.constructor = HminorShape.constructor ∧
      traversal.fields = HminorShape.fields ∧
      traversal.recursiveFields = HminorShape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      HminorShape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const HminorShape.constructor.name stats.levels)
              stats.params)
            HminorShape.fields)) ∧
      BindingContextLE traversal.rootContext c ∧
      BindingContextLE traversal.terminalContext c ∧
      BindingContextLE HminorShape.sourceFullContext c)
    (HminorBlueprint : RecInfoRuleBlueprintOriginAt stats
      HminorShape (.fvar ⟨c.ngen.curr⟩)
      (mkBlueprint (.fvar ⟨c.ngen.curr⟩)))
    (HminorBlueprintSemantic : Nonempty
      (RecInfoRuleBlueprintSemanticOriginAt R decl stats recInfos elimLevel
        Hsuffix.parameterDecls dIdx HminorShape
        (mkBlueprint (.fvar ⟨c.ngen.curr⟩))))
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams)
      (henvOut : Rout.venv = R.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (HstatsOut : RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth)
      (hctxOut : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rout.mlctx.vlctx)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoTypeOrigins outCtx out),
      RecInfoRuleBlueprintOrigins stats out HoriginsOut →
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + 1 →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (withLocalDecl minorName .default minorTy.consumeTypeAnnotationsVerified
      (fun minor =>
        let next := recInfos.modify dIdx fun info =>
          { info with
            minors := info.minors.push minor
            ruleBlueprints := info.ruleBlueprints.push (mkBlueprint minor) }
        k next) c).WF Q := by
  refine withLocalDecl.recursorWF (name := minorName) (bi := .default)
    R Hminor HminorType ?_
  let Rminor := R.withLocalDecl (name := minorName) (bi := .default)
    Hminor HminorType
  let cMinor : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ minorName
      minorTy.consumeTypeAnnotationsVerified .default }
  let next := recInfos.modify dIdx fun info =>
    { info with
      minors := info.minors.push (.fvar ⟨c.ngen.curr⟩)
      ruleBlueprints := info.ruleBlueprints.push
        (mkBlueprint (.fvar ⟨c.ngen.curr⟩)) }
  let Hstep := RecursorContextExtension.withLocalDecl
    (name := minorName) (bi := .default) R Hminor HminorType
  let HbindingsMinor := Hbindings.addMinor dIdx hidx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
      minorTy.consumeTypeAnnotationsVerified .default
  let HoriginsMinor := Horigins.addMinor dIdx hidx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
      minorTy.consumeTypeAnnotationsVerified .default HminorShape
      HminorShapePosition
  let HminorSourcesMinor := HminorSources.addMinor dIdx hidx hsourceIdx
    (BindingContextLE.refl c) R.toBindingContextWF minorName
    minorTy.consumeTypeAnnotationsVerified .default HminorShape
    HminorShapePosition HminorSource HminorHypothesisOrigins HminorTraversal
  let HminorSemanticsMinor := HminorSemantics.addMinor
    (RecursorContextExtension.refl R) dIdx hidx minorName
    minorTy.consumeTypeAnnotationsVerified .default Hminor HminorType HminorShape
    HminorShapePosition HminorSemantic
  let Hcore := modifyMinorAndBlueprint_coreEq recInfos dIdx hidx
    (.fvar ⟨c.ngen.curr⟩) (mkBlueprint (.fvar ⟨c.ngen.curr⟩))
  let HmotiveCore := modifyMinorAndBlueprint_motiveCoreEq recInfos dIdx hidx
    (.fvar ⟨c.ngen.curr⟩) (mkBlueprint (.fvar ⟨c.ngen.curr⟩))
  have hmotivesNext : next.map (·.motive) = recInfos.map (·.motive) := by
    apply Array.ext
    · simp [next]
    · intro i hiNext hiOld
      rw [Array.getElem_map, Array.getElem_map]
      rw [Array.getElem_modify (by simpa [next] using hiNext)]
      split <;> rfl
  let HbindingsNext : RecInfoBindings cMinor next :=
    HbindingsMinor.rebaseCore Hcore
  let HoriginsNext : RecInfoTypeOrigins cMinor next :=
    HoriginsMinor.rebaseCore Hcore
  let HparamsMinor := Hparams.mono Hstep.contextLE
  have hmotivesFVarsNext : HbindingsNext.motives.fvars =
      Hbindings.motives.fvars := by
    change (HbindingsMinor.rebaseCore Hcore).motives.fvars = _
    rw [HbindingsMinor.rebaseCore_motives_fvars Hcore]
    exact Hbindings.addMinor_motives_fvars dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName
      minorTy.consumeTypeAnnotationsVerified .default
  have hflatMinorsFVarsNext : HbindingsNext.flatMinors.fvars =
      Hbindings.flatMinors.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)] := by
    change (HbindingsMinor.rebaseCore Hcore).flatMinors.fvars = _
    rw [HbindingsMinor.rebaseCore_flatMinors_fvars Hcore]
    exact Hbindings.addMinor_flatMinors_fvars dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName
      minorTy.consumeTypeAnnotationsVerified .default Hlater
  have HblueprintsNext :
      RecInfoRuleBlueprintOrigins stats next HoriginsNext := by
    refine {
      rows_size := ?_
      entry := ?_
      fields_outer_fresh := ?_ }
    · intro owner howner
      have hownerOld : owner < recInfos.size := by
        simpa [next] using howner
      by_cases hdi : dIdx = owner
      · subst owner
        have hrow := Hblueprints.rows_size dIdx hidx
        have hminorSize := (Horigins.minors dIdx hidx).size_eq
        have hidxTypes : dIdx < Horigins.minorTypes.size := by
          rw [Horigins.minorTypes_size]
          exact hidx
        dsimp [next, HoriginsNext, HoriginsMinor,
          RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self Horigins.minorTypes
          dIdx _ hidxTypes]
        simp only [Array.size_push]
        omega
      · have hrow := Hblueprints.rows_size owner hownerOld
        have hownerTypes : owner < Horigins.minorTypes.size := by
          rw [Horigins.minorTypes_size]
          exact hownerOld
        dsimp [next, HoriginsNext, HoriginsMinor,
          RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx owner _
          hownerOld hdi]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
          dIdx owner _ hownerTypes hdi]
        exact hrow
    · intro owner howner localIndex hlocal
      have hownerOld : owner < recInfos.size := by
        simpa [next] using howner
      by_cases hdi : dIdx = owner
      · subst owner
        by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
        · subst localIndex
          have hminorIndex : Horigins.minorTypes[dIdx]!.size =
              recInfos[dIdx]!.minors.size :=
            (Horigins.minors dIdx hidx).size_eq
          have hblueprintIndex : Horigins.minorTypes[dIdx]!.size =
              recInfos[dIdx]!.ruleBlueprints.size :=
            (Hblueprints.rows_size dIdx hidx).symm
          have hminorLast :
              (recInfos[dIdx]!.minors.push (.fvar ⟨c.ngen.curr⟩))[
                Horigins.minorTypes[dIdx]!.size]! =
                .fvar ⟨c.ngen.curr⟩ := by
            rw [hminorIndex]
            simp
          have hblueprintLast :
              (recInfos[dIdx]!.ruleBlueprints.push
                (mkBlueprint (.fvar ⟨c.ngen.curr⟩)))[
                  Horigins.minorTypes[dIdx]!.size]! =
                mkBlueprint (.fvar ⟨c.ngen.curr⟩) := by
            rw [hblueprintIndex]
            simp
          have hshapeLast :
              HoriginsNext.minorShapes dIdx howner
                Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
            simp [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
          rw [hshapeLast]
          simpa [next, HoriginsNext, HoriginsMinor,
            RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
            RecInfoRuleBlueprintOriginAt,
            mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
            hminorLast, hblueprintLast]
            using HminorBlueprint
        · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
            dsimp [HoriginsNext, HoriginsMinor, RecInfoTypeOrigins.rebaseCore,
              RecInfoTypeOrigins.addMinor] at hlocal
            have hidxTypes : dIdx < Horigins.minorTypes.size := by
              rw [Horigins.minorTypes_size]
              exact hidx
            rw [mkRecInfos.loopCtors.getElemBang_modify_self
              Horigins.minorTypes dIdx _ hidxTypes] at hlocal
            simp only [Array.size_push] at hlocal
            omega
          have holdMinor : localIndex < recInfos[dIdx]!.minors.size := by
            rw [← (Horigins.minors dIdx hidx).size_eq]
            exact hold
          have holdBlueprint :
              localIndex < recInfos[dIdx]!.ruleBlueprints.size := by
            rw [Hblueprints.rows_size dIdx hidx]
            exact hold
          have holdMinor' : localIndex < recInfos[dIdx].minors.size := by
            simpa [getElem!_pos recInfos dIdx hidx] using holdMinor
          have holdBlueprint' :
              localIndex < recInfos[dIdx].ruleBlueprints.size := by
            simpa [getElem!_pos recInfos dIdx hidx] using holdBlueprint
          have hminorGet :
              (recInfos[dIdx]!.minors.push
                (.fvar ⟨c.ngen.curr⟩))[localIndex]! =
                recInfos[dIdx]!.minors[localIndex]! := by
            simp [Array.getElem!_eq_getD, Array.getD, hidx, holdMinor',
              Array.getElem_push_lt holdMinor'] <;> omega
          have hblueprintGet :
              (recInfos[dIdx]!.ruleBlueprints.push
                (mkBlueprint (.fvar ⟨c.ngen.curr⟩)))[localIndex]! =
                recInfos[dIdx]!.ruleBlueprints[localIndex]! := by
            simp [Array.getElem!_eq_getD, Array.getD, hidx, holdBlueprint',
              Array.getElem_push_lt holdBlueprint'] <;> omega
          have Hentry := Hblueprints.entry dIdx hidx localIndex hold
          have hshapeOld :
              HoriginsNext.minorShapes dIdx howner localIndex hlocal =
                Horigins.minorShapes dIdx hidx localIndex hold := by
            simp [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              hlast]
          rw [hshapeOld]
          simpa [next, HoriginsNext, HoriginsMinor,
            RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
            RecInfoRuleBlueprintOriginAt,
            mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
            hlast, Array.getElem_push_lt hold,
            Array.getElem_push_lt holdMinor,
            Array.getElem_push_lt holdBlueprint,
            hminorGet, hblueprintGet] using Hentry
      · have hlocalOld : localIndex < Horigins.minorTypes[owner]!.size := by
          simpa [HoriginsNext, HoriginsMinor, RecInfoTypeOrigins.rebaseCore,
            RecInfoTypeOrigins.addMinor,
            mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
              dIdx owner _ (by simpa [Horigins.minorTypes_size] using hownerOld)
              hdi] using hlocal
        have Hentry := Hblueprints.entry owner hownerOld localIndex hlocalOld
        have hshapeOld :
            HoriginsNext.minorShapes owner howner localIndex hlocal =
              Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
          simp [HoriginsNext, HoriginsMinor,
            RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor, hdi]
        rw [hshapeOld]
        simpa [next, HoriginsNext, HoriginsMinor,
          RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
          RecInfoRuleBlueprintOriginAt,
          hdi,
          mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx owner _
            hownerOld hdi] using Hentry
    · intro owner howner localIndex hlocal fv hfv
      have hownerOld : owner < recInfos.size := by
        simpa [next] using howner
      rw [hmotivesNext, Hparams.exprArrayFVarIds,
        Hbindings.motives.exprArrayFVarIds,
        HbindingsNext.flatMinors.exprArrayFVarIds,
        hflatMinorsFVarsNext]
      intro houter
      have holdOrCurrent :
          fv ∈ (Hparams.fvars ++ Hbindings.motives.fvars) ++
              Hbindings.flatMinors.fvars ∨
            fv = (⟨c.ngen.curr⟩ : FVarId) := by
        rcases List.mem_append.mp houter with hpm | hminorCurrent
        · exact Or.inl (List.mem_append.mpr (Or.inl hpm))
        · rcases List.mem_append.mp hminorCurrent with hminor | hcurrent
          · exact Or.inl (List.mem_append.mpr (Or.inr hminor))
          · exact Or.inr (by simpa using hcurrent)
      rcases holdOrCurrent with holdOuter | hcurrent
      · by_cases hdi : dIdx = owner
        · subst owner
          by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
          · subst localIndex
            have hshapeLast :
                HoriginsNext.minorShapes dIdx howner
                    Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
            rw [hshapeLast] at hfv
            exact HminorFieldsFresh fv hfv holdOuter
          · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
              dsimp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore,
                RecInfoTypeOrigins.addMinor] at hlocal
              have hidxTypes : dIdx < Horigins.minorTypes.size := by
                rw [Horigins.minorTypes_size]
                exact hidx
              rw [mkRecInfos.loopCtors.getElemBang_modify_self
                Horigins.minorTypes dIdx _ hidxTypes] at hlocal
              simp only [Array.size_push] at hlocal
              omega
            have hshapeOld :
                HoriginsNext.minorShapes dIdx howner localIndex hlocal =
                  Horigins.minorShapes dIdx hidx localIndex hold := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
                hlast]
            rw [hshapeOld] at hfv
            apply Hblueprints.fields_outer_fresh dIdx hidx
              localIndex hold fv hfv
            simpa only [Hparams.exprArrayFVarIds,
              Hbindings.motives.exprArrayFVarIds,
              Hbindings.flatMinors.exprArrayFVarIds] using holdOuter
        · have hlocalOld :
              localIndex < Horigins.minorTypes[owner]!.size := by
            simpa [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
                dIdx owner _
                  (by simpa [Horigins.minorTypes_size] using hownerOld) hdi]
              using hlocal
          have hshapeOld :
              HoriginsNext.minorShapes owner howner localIndex hlocal =
                Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
            simp [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              hdi]
          rw [hshapeOld] at hfv
          apply Hblueprints.fields_outer_fresh owner hownerOld
            localIndex hlocalOld fv hfv
          simpa only [Hparams.exprArrayFVarIds,
            Hbindings.motives.exprArrayFVarIds,
            Hbindings.flatMinors.exprArrayFVarIds] using holdOuter
      · subst fv
        apply R.toBindingContextWF.current_not_mem
        by_cases hdi : dIdx = owner
        · subst owner
          by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
          · subst localIndex
            have hshapeLast :
                HoriginsNext.minorShapes dIdx howner
                    Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
            rw [hshapeLast] at hfv
            rcases HminorSemantic with ⟨HS⟩
            exact HS.semantic.extension.contextLE.fvars
              (HminorShape.fields_bound.members _ hfv)
          · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
              dsimp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore,
                RecInfoTypeOrigins.addMinor] at hlocal
              have hidxTypes : dIdx < Horigins.minorTypes.size := by
                rw [Horigins.minorTypes_size]
                exact hidx
              rw [mkRecInfos.loopCtors.getElemBang_modify_self
                Horigins.minorTypes dIdx _ hidxTypes] at hlocal
              simp only [Array.size_push] at hlocal
              omega
            have hshapeOld :
                HoriginsNext.minorShapes dIdx howner localIndex hlocal =
                  Horigins.minorShapes dIdx hidx localIndex hold := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
                hlast]
            rw [hshapeOld] at hfv
            rcases HminorSemantics dIdx hidx localIndex hold with ⟨HS⟩
            exact HS.semantic.extension.contextLE.fvars
              ((Horigins.minorShapes dIdx hidx localIndex hold
                ).fields_bound.members _ hfv)
        · have hlocalOld :
              localIndex < Horigins.minorTypes[owner]!.size := by
            simpa [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
                dIdx owner _
                  (by simpa [Horigins.minorTypes_size] using hownerOld) hdi]
              using hlocal
          have hshapeOld :
              HoriginsNext.minorShapes owner howner localIndex hlocal =
                Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
            simp [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              hdi]
          rw [hshapeOld] at hfv
          rcases HminorSemantics owner hownerOld localIndex hlocalOld with ⟨HS⟩
          exact HS.semantic.extension.contextLE.fvars
            ((Horigins.minorShapes owner hownerOld localIndex hlocalOld
              ).fields_bound.members _ hfv)
  have HblueprintSemanticsNext :
      RecInfoRuleBlueprintSemanticOrigins Rminor decl stats next elimLevel
        Hsuffix.parameterDecls HoriginsNext := by
    refine {
      rows_size := HblueprintsNext.rows_size
      entry := ?_
      fields_outer_fresh := ?_ }
    intro owner howner localIndex hlocal
    have hownerOld : owner < recInfos.size := by
      simpa [next] using howner
    by_cases hdi : dIdx = owner
    · subst owner
      by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
      · subst localIndex
        have hblueprintIndex : Horigins.minorTypes[dIdx]!.size =
            recInfos[dIdx]!.ruleBlueprints.size :=
          (Hblueprints.rows_size dIdx hidx).symm
        have hblueprintLast :
            (recInfos[dIdx]!.ruleBlueprints.push
              (mkBlueprint (.fvar ⟨c.ngen.curr⟩)))[
                Horigins.minorTypes[dIdx]!.size]! =
              mkBlueprint (.fvar ⟨c.ngen.curr⟩) := by
          rw [hblueprintIndex]
          simp
        have hshapeLast :
            HoriginsNext.minorShapes dIdx howner
              Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
          simp [HoriginsNext, HoriginsMinor,
            RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
        rw [hshapeLast]
        rcases HminorBlueprintSemantic with ⟨HminorBlueprintSemantic⟩
        have HminorBlueprintSemantic' :=
          (HminorBlueprintSemantic.mono Hstep).rebaseMotiveCore HmotiveCore
        simpa [next, Rminor, RecInfoRuleBlueprintSemanticOriginAt,
          mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
          hblueprintLast, hmotivesNext] using HminorBlueprintSemantic'
      · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
          dsimp [HoriginsNext, HoriginsMinor, RecInfoTypeOrigins.rebaseCore,
            RecInfoTypeOrigins.addMinor] at hlocal
          have hidxTypes : dIdx < Horigins.minorTypes.size := by
            rw [Horigins.minorTypes_size]
            exact hidx
          rw [mkRecInfos.loopCtors.getElemBang_modify_self
            Horigins.minorTypes dIdx _ hidxTypes] at hlocal
          simp only [Array.size_push] at hlocal
          omega
        have holdBlueprint :
            localIndex < recInfos[dIdx]!.ruleBlueprints.size := by
          rw [Hblueprints.rows_size dIdx hidx]
          exact hold
        have holdBlueprint' :
            localIndex < recInfos[dIdx].ruleBlueprints.size := by
          simpa [getElem!_pos recInfos dIdx hidx] using holdBlueprint
        have hblueprintGet :
            (recInfos[dIdx]!.ruleBlueprints.push
              (mkBlueprint (.fvar ⟨c.ngen.curr⟩)))[localIndex]! =
              recInfos[dIdx]!.ruleBlueprints[localIndex]! := by
          simp [Array.getElem!_eq_getD, Array.getD, hidx, holdBlueprint',
            Array.getElem_push_lt holdBlueprint'] <;> omega
        rcases HblueprintSemantics.entry dIdx hidx localIndex hold with ⟨Hentry⟩
        have Hentry := (Hentry.mono Hstep).rebaseMotiveCore HmotiveCore
        have hshapeOld :
            HoriginsNext.minorShapes dIdx howner localIndex hlocal =
              Horigins.minorShapes dIdx hidx localIndex hold := by
          simp [HoriginsNext, HoriginsMinor,
            RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
            hlast]
        rw [hshapeOld]
        simpa [next, Rminor, RecInfoRuleBlueprintSemanticOriginAt,
          mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx,
          hlast, Array.getElem_push_lt holdBlueprint, hblueprintGet,
          hmotivesNext] using
            Hentry
    · have hlocalOld : localIndex < Horigins.minorTypes[owner]!.size := by
        simpa [HoriginsNext, HoriginsMinor, RecInfoTypeOrigins.rebaseCore,
          RecInfoTypeOrigins.addMinor,
          mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
            dIdx owner _ (by simpa [Horigins.minorTypes_size] using hownerOld)
            hdi] using hlocal
      rcases HblueprintSemantics.entry owner hownerOld localIndex
        hlocalOld with ⟨Hentry⟩
      have Hentry := (Hentry.mono Hstep).rebaseMotiveCore HmotiveCore
      have hshapeOld :
          HoriginsNext.minorShapes owner howner localIndex hlocal =
            Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
        simp [HoriginsNext, HoriginsMinor,
          RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor, hdi]
      rw [hshapeOld]
      simpa [next, Rminor, RecInfoRuleBlueprintSemanticOriginAt, hdi,
        mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx owner _
          hownerOld hdi, hmotivesNext] using Hentry
    · intro owner howner localIndex hlocal fv hfv
      have hownerOld : owner < recInfos.size := by
        simpa [next] using howner
      rw [hmotivesNext, Hparams.exprArrayFVarIds,
        Hbindings.motives.exprArrayFVarIds,
        HbindingsNext.flatMinors.exprArrayFVarIds,
        hflatMinorsFVarsNext]
      intro houter
      have holdOrCurrent :
          fv ∈ (Hparams.fvars ++ Hbindings.motives.fvars) ++
              Hbindings.flatMinors.fvars ∨
            fv = (⟨c.ngen.curr⟩ : FVarId) := by
        rcases List.mem_append.mp houter with hpm | hminorCurrent
        · exact Or.inl (List.mem_append.mpr (Or.inl hpm))
        · rcases List.mem_append.mp hminorCurrent with hminor | hcurrent
          · exact Or.inl (List.mem_append.mpr (Or.inr hminor))
          · exact Or.inr (by simpa using hcurrent)
      rcases holdOrCurrent with holdOuter | hcurrent
      · by_cases hdi : dIdx = owner
        · subst owner
          by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
          · subst localIndex
            have hshapeLast :
                HoriginsNext.minorShapes dIdx howner
                    Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
            rw [hshapeLast] at hfv
            exact HminorFieldsFresh fv hfv holdOuter
          · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
              dsimp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore,
                RecInfoTypeOrigins.addMinor] at hlocal
              have hidxTypes : dIdx < Horigins.minorTypes.size := by
                rw [Horigins.minorTypes_size]
                exact hidx
              rw [mkRecInfos.loopCtors.getElemBang_modify_self
                Horigins.minorTypes dIdx _ hidxTypes] at hlocal
              simp only [Array.size_push] at hlocal
              omega
            have hshapeOld :
                HoriginsNext.minorShapes dIdx howner localIndex hlocal =
                  Horigins.minorShapes dIdx hidx localIndex hold := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
                hlast]
            rw [hshapeOld] at hfv
            apply HblueprintSemantics.fields_outer_fresh dIdx hidx
              localIndex hold fv hfv
            simpa only [Hparams.exprArrayFVarIds,
              Hbindings.motives.exprArrayFVarIds,
              Hbindings.flatMinors.exprArrayFVarIds] using holdOuter
        · have hlocalOld :
              localIndex < Horigins.minorTypes[owner]!.size := by
            simpa [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
                dIdx owner _
                  (by simpa [Horigins.minorTypes_size] using hownerOld) hdi]
              using hlocal
          have hshapeOld :
              HoriginsNext.minorShapes owner howner localIndex hlocal =
                Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
            simp [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              hdi]
          rw [hshapeOld] at hfv
          apply HblueprintSemantics.fields_outer_fresh owner hownerOld
            localIndex hlocalOld fv hfv
          simpa only [Hparams.exprArrayFVarIds,
            Hbindings.motives.exprArrayFVarIds,
            Hbindings.flatMinors.exprArrayFVarIds] using holdOuter
      · subst fv
        apply R.toBindingContextWF.current_not_mem
        by_cases hdi : dIdx = owner
        · subst owner
          by_cases hlast : localIndex = Horigins.minorTypes[dIdx]!.size
          · subst localIndex
            have hshapeLast :
                HoriginsNext.minorShapes dIdx howner
                    Horigins.minorTypes[dIdx]!.size hlocal = HminorShape := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor]
            rw [hshapeLast] at hfv
            rcases HminorSemantic with ⟨HS⟩
            exact HS.semantic.extension.contextLE.fvars
              (HminorShape.fields_bound.members _ hfv)
          · have hold : localIndex < Horigins.minorTypes[dIdx]!.size := by
              dsimp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore,
                RecInfoTypeOrigins.addMinor] at hlocal
              have hidxTypes : dIdx < Horigins.minorTypes.size := by
                rw [Horigins.minorTypes_size]
                exact hidx
              rw [mkRecInfos.loopCtors.getElemBang_modify_self
                Horigins.minorTypes dIdx _ hidxTypes] at hlocal
              simp only [Array.size_push] at hlocal
              omega
            have hshapeOld :
                HoriginsNext.minorShapes dIdx howner localIndex hlocal =
                  Horigins.minorShapes dIdx hidx localIndex hold := by
              simp [HoriginsNext, HoriginsMinor,
                RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
                hlast]
            rw [hshapeOld] at hfv
            rcases HminorSemantics dIdx hidx localIndex hold with ⟨HS⟩
            exact HS.semantic.extension.contextLE.fvars
              ((Horigins.minorShapes dIdx hidx localIndex hold
                ).fields_bound.members _ hfv)
        · have hlocalOld :
              localIndex < Horigins.minorTypes[owner]!.size := by
            simpa [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              mkRecInfos.loopCtors.getElemBang_modify_ne Horigins.minorTypes
                dIdx owner _
                  (by simpa [Horigins.minorTypes_size] using hownerOld) hdi]
              using hlocal
          have hshapeOld :
              HoriginsNext.minorShapes owner howner localIndex hlocal =
                Horigins.minorShapes owner hownerOld localIndex hlocalOld := by
            simp [HoriginsNext, HoriginsMinor,
              RecInfoTypeOrigins.rebaseCore, RecInfoTypeOrigins.addMinor,
              hdi]
          rw [hshapeOld] at hfv
          rcases HminorSemantics owner hownerOld localIndex hlocalOld with ⟨HS⟩
          exact HS.semantic.extension.contextLE.fvars
            ((Horigins.minorShapes owner hownerOld localIndex hlocalOld
              ).fields_bound.members _ hfv)
  have HminorSourcesNext :
      RecInfoMinorSourceAlignment stats indTypes HoriginsNext := by
    exact RecInfoMinorSourceAlignment.rebaseCore _ HminorSourcesMinor Hcore
  have HminorSemanticsNext :
      RecInfoMinorSemanticAlignment Rminor HoriginsNext
        Hsuffix.parameterDecls := by
    exact RecInfoMinorSemanticAlignment.rebaseCore _ HminorSemanticsMinor Hcore
  have HorderMinor : RecInfoOuterOrder Rminor HparamsMinor
      HbindingsMinor := by
    refine RecInfoOuterOrder.addMinor
      (minor := (⟨c.ngen.curr⟩ : FVarId)) Horder ?_ ?_ ?_ ?_
    · rfl
    · exact Hbindings.addMinor_motives_fvars dIdx hidx
        (BindingContextLE.refl c) R.toBindingContextWF minorName
          minorTy.consumeTypeAnnotationsVerified .default
    · exact Hbindings.addMinor_flatMinors_fvars dIdx hidx
        (BindingContextLE.refl c) R.toBindingContextWF minorName
          minorTy.consumeTypeAnnotationsVerified .default Hlater
    · rfl
  have HorderNext : RecInfoOuterOrder Rminor HparamsMinor HbindingsNext :=
    RecInfoOuterOrder.rebaseCore HbindingsMinor HorderMinor Hcore
  refine Hk next Rminor rfl (Hsuffix.withAmbient Hminor HminorType) rfl
    (Hstats.withFVar Rminor.checking.tr.wf Rminor.mlctx_wf.tr.wf)
    (VLCtx.NoIndConsts.cons hctx rfl)
    HbindingsNext HoriginsNext HblueprintsNext HblueprintSemanticsNext
      HminorSourcesNext
      HminorSemanticsNext
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      HparamsMinor ?_ ?_ ?_ ?_
  · simp [next]
  · dsimp [next]
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
    simp
  · intro i hi hine
    dsimp [next]
    rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hi hine]
  · change RecursorTranslatedOriginTypes Rminor Horigins.majorTypes
    simpa [Rminor] using HmajorTypes.mono Hstep
  · exact (HmajorShapes.modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · change RecursorTranslatedOriginTypes Rminor Horigins.motiveTypes
    simpa [Rminor] using HmotiveTypes.mono Hstep
  · exact ((HmotiveShapes.mono Hbindings Hstep.contextLE).modifyMinors
      dIdx (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · exact ((Htelescopes.mono Hstep).modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · change RecursorTranslatedOriginTypeRows Rminor Horigins.indexTypes
    simpa [Rminor] using HindexRows.mono Hstep
  · exact RecInfoBindings.NoAlias.rebaseCore
      HbindingsMinor HparamsMinor
      (Hbindings.addMinor_noAlias Hparams HnoAlias dIdx hidx
      (BindingContextLE.refl c) R.toBindingContextWF minorName
        minorTy.consumeTypeAnnotationsVerified .default) Hcore
  · exact HorderNext
  · exact (Harities.modifyMinors dIdx
      (fun minors => minors.push (.fvar ⟨c.ngen.curr⟩))).rebaseCore Hcore
  · exact Hroot.trans Hstep.contextLE

/-- Complete semantic refinement of one constructor iteration in the second
`mkRecInfos` pass.  The only constructor-specific premise is the independent
introduction certificate for the exact terminal application exposed by the
field traversal; all recursive-field motives, generated IH binders, telescope
closure, and minor insertion are derived here. -/
theorem oneConstructorSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctor : Constructor) (tail : Expr)
    (sourceConstructors : List Constructor) (sourceIndex : Nat)
    (hsourceConstructor : sourceConstructors[sourceIndex]? = some ctor)
    (hsourceFamily : sourceConstructors = indTypes[dIdx]!.ctors)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl} {tailTarget : VExpr}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hprefix : RecursorParamPrefix stats 0 ctor.type tail)
    (htailScope : tail.FVarsIn
      (fun fv => fv ∈ ExprArrayFVarIds stats.params))
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    (htailType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx tailTarget)
    {introTarget : VExpr}
    (Hintro : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN (.const ctor.name stats.levels) stats.params) introTarget)
    (HintroType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx introTarget tailTarget)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hblueprints : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (HblueprintSemantics : RecInfoRuleBlueprintSemanticOrigins R decl stats
      recInfos elimLevel Hsuffix.parameterDecls Horigins)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (horiginIndex : Horigins.minorTypes[dIdx]!.size = sourceIndex)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hnormal : Nonempty
      (CheckedConstructorOwnerNormalForm stats dIdx tail))
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams)
      (henvOut : Rout.venv = R.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (hparameterDeclsOut :
        HsuffixOut.parameterDecls = Hsuffix.parameterDecls)
      (HstatsOut : RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth)
      (hctxOut : VLCtx.NoIndConsts
        (decl.types.map (·.name)) Rout.mlctx.vlctx)
      (HbindingsOut : RecInfoBindings outCtx out)
      (HoriginsOut : RecInfoTypeOrigins outCtx out),
      RecInfoRuleBlueprintOrigins stats out HoriginsOut →
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + 1 →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type
      (fun terminal allFields recursiveFields =>
        let (ownerIdx, indices) := AddInductive.getIIndices stats terminal
        let introApp := mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields
        let motiveApp := Expr.app
          (mkAppN recInfos[ownerIdx]!.motive indices) introApp
        AddInductive.mkRecInfos.loopUBlueprints stats recursiveFields recInfos
          0 #[] #[] fun hypotheses calls => do
            let lctx ← getLCtx
            let minorTy := lctx.mkForall allFields <|
              lctx.mkForall hypotheses motiveApp
            let minorName :=
              ctor.name.replacePrefix indTypeName .anonymous
            withLocalDecl minorName .default
                minorTy.consumeTypeAnnotationsVerified fun minor =>
              let next := recInfos.modify dIdx fun info =>
                { info with
                  minors := info.minors.push minor
                  ruleBlueprints := info.ruleBlueprints.push {
                    ctor := ctor.name
                    fields := allFields
                    lctx := lctx
                    recursiveCalls := calls
                    targetTypeIdx := ownerIdx
                    targetIndices := indices
                    minor := minor } }
              k next) c).WF Q := by
  let process := fun terminal allFields recursiveFields =>
    let (ownerIdx, indices) := AddInductive.getIIndices stats terminal
    let introApp := mkAppN
      (mkAppN (.const ctor.name stats.levels) stats.params) allFields
    let motiveApp := Expr.app
      (mkAppN recInfos[ownerIdx]!.motive indices) introApp
    AddInductive.mkRecInfos.loopUBlueprints stats recursiveFields recInfos
      0 #[] #[] fun hypotheses calls => do
        let lctx ← getLCtx
        let minorTy := lctx.mkForall allFields <|
          lctx.mkForall hypotheses motiveApp
        let minorName := ctor.name.replacePrefix indTypeName .anonymous
        withLocalDecl minorName .default minorTy.consumeTypeAnnotationsVerified
            fun minor =>
          let next := recInfos.modify dIdx fun info =>
            { info with
              minors := info.minors.push minor
              ruleBlueprints := info.ruleBlueprints.push {
                ctor := ctor.name
                fields := allFields
                lctx := lctx
                recursiveCalls := calls
                targetTypeIdx := ownerIdx
                targetIndices := indices
                minor := minor } }
          k next
  change (AddInductive.mkRecInfos.loopCtorArgs stats ctor.type process c).WF Q
  apply mkRecInfos.loopCtorArgs.recursiveDomainsRecursorRecent (Q := Q)
    stats ctor.type tail
      (mkAppN (.const ctor.name stats.levels) stats.params)
      process c R Hstats hprefix hconsume hlit hctx hproj htail
      htailType htailScope Hsuffix.parameterFVarsUp Hintro HintroType
  intro current Rargs terminal terminalTarget appliedTarget allFields
    recursiveFields fields positions args HterminalNonforall Hterminal
    HterminalType Hselections Hdecisions Hrecursive HfieldsRecent Hopening
    HfieldTargetDefEq _HterminalScope _HfieldParameterUp
    HintroApplied HintroAppliedType
  let HextArgs := HfieldsRecent.contextExtension
  let HstatsArgs := Hstats.weakenRecent HfieldsRecent
  have hctxArgs : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rargs.mlctx.vlctx :=
    HfieldsRecent.noIndConsts (names := decl.types.map (·.name)) hctx
  have hdidxDecl : dIdx < decl.types.length := by
    rw [← Hstats.types_size, ← hrecords]
    exact hidx
  have hdidxConst := Hstats.indConstAt hdidxDecl
  rcases Hnormal with ⟨Hnormal⟩
  have hdidxValid := Hnormal.validOfOpening Hopening Hparams
    HfieldsRecent.toFreshBoundFVarArray hdidxConst HterminalNonforall
  rcases checkPositivityStep.isValidIndApp?_exists_of_valid
      hdidxValid hdidxConst with
    ⟨ownerIdx, hownerValid⟩
  let Happlication : RecursorConstructorApplicationAt Rargs stats ctor
      terminal allFields terminalTarget := {
    ownerIdx := ownerIdx
    owner_valid := hownerValid
    terminal_type := HterminalType
    introTarget := appliedTarget
    intro := by simpa [mkAppN] using HintroApplied
    typing := HintroAppliedType }
  have htargetStats : Happlication.ownerIdx < stats.indConsts.size :=
    (checkPositivityStep.isValidIndApp?_some Happlication.owner_valid).1
  have htarget : Happlication.ownerIdx < recInfos.size := by
    rw [hrecords]
    exact htargetStats
  have htargetDecl : Happlication.ownerIdx < decl.types.length := by
    rw [← HstatsArgs.types_size]
    exact htargetStats
  let Hvalidated := HstatsArgs.validatedIndAppAt Hterminal
    Happlication.owner_valid htargetDecl
      (by simpa only [HfieldsRecent.venv_eq] using hlit) hctxArgs hproj
  rcases HmotiveShapes.motiveBindingAtRecent Hbindings Horigins
      HfieldsRecent Happlication.ownerIdx htarget with ⟨HbindingAt⟩
  let Hbinding := HbindingAt.toBinding
  have HmotiveEvidence := Htelescopes.telescope Happlication.ownerIdx
    htarget Rargs HextArgs Hbinding Hterminal HterminalType Hvalidated
  have HterminalWF : VExpr.WF Rargs.venv recLparams.length
      Rargs.mlctx.vlctx.toCtx terminalTarget := by
    rcases Happlication.terminal_type with ⟨u, Htyped⟩
    exact ⟨.sort u, Htyped⟩
  rcases Htelescopes.applications.applyAtMono Hbindings Horigins
      HmotiveShapes HextArgs Happlication.ownerIdx htarget Hterminal
      (.refl HterminalWF) Happlication.terminal_type
      Happlication.intro Happlication.typing Hvalidated with
    ⟨motiveTarget, Hmotive, HmotiveType⟩
  let indices : Array Expr := terminal.getAppArgs[stats.params.size:]
  have howner : AddInductive.getIIndices stats terminal =
      (Happlication.ownerIdx, indices) := by
    simp only [AddInductive.getIIndices, indices]
    rw [Happlication.owner_valid]
    rfl
  dsimp only [process]
  rw [howner]
  let finish := fun hypotheses calls => do
    let lctx ← getLCtx
    let motiveApp := Expr.app
      (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
      (mkAppN
        (mkAppN (.const ctor.name stats.levels) stats.params) allFields)
    let minorTy := lctx.mkForall allFields <|
      lctx.mkForall hypotheses motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName .default minorTy.consumeTypeAnnotationsVerified
        fun minor =>
      let next := recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push minor
          ruleBlueprints := info.ruleBlueprints.push {
            ctor := ctor.name
            fields := allFields
            lctx := lctx
            recursiveCalls := calls
            targetTypeIdx := Happlication.ownerIdx
            targetIndices := indices
            minor := minor } }
      k next
  change (AddInductive.mkRecInfos.loopUBlueprints stats recursiveFields
    recInfos 0 #[] #[] finish current).WF Q
  let HbindingsArgs := Hbindings.mono HextArgs.contextLE
  let HoriginsArgs := Horigins.mono HextArgs.contextLE
  let HmotiveShapesArgs := HmotiveShapes.mono Hbindings HextArgs.contextLE
  let HtelescopesArgs := Htelescopes.mono HextArgs
  let producerScope : FVarId → Prop := fun fv =>
    fv ∈ HfieldsRecent.fvars ∨ fv ∈ ExprArrayFVarIds stats.params
  apply mkRecInfos.loopUBlueprints.resultSemanticsOfMotiveTelescopes (Q := Q)
    stats recursiveFields recInfos finish Rargs producerScope HstatsArgs hconsume
      (by simpa only [HfieldsRecent.venv_eq] using hlit)
      hctxArgs hproj
      (by
        intro j hj
        rcases Hselections.selectedFVars
            HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray Hrecursive
            j hj with ⟨fv, target, heq, Htr⟩
        refine ⟨fv, target, heq, Htr, Or.inl ?_⟩
        have hselectedExpr : Expr.fvar fv ∈ recursiveFields.toList := by
          rw [← heq]
          exact Array.getElem_mem_toList hj
        have hallExpr : Expr.fvar fv ∈ allFields.toList :=
          Hselections.toSource.selectedSublist.subset hselectedExpr
        rw [HfieldsRecent.expressions] at hallExpr
        simpa using hallExpr)
      (by
        intro fv hfv
        rcases hfv with hfield | hparam
        · have hmem := HfieldsRecent.members fv hfield
          rw [← Rargs.lctx_eq, Rargs.mlctx_wf.tr.fvars_eq] at hmem
          exact hmem
        · have hp : fv ∈ Hparams.fvars := by
            rw [← Hparams.exprArrayFVarIds]
            exact hparam
          have hmem := HextArgs.contextLE (Hparams.members fv hp)
          rw [← Rargs.lctx_eq, Rargs.mlctx_wf.tr.fvars_eq] at hmem
          exact hmem)
      (by
        dsimp only [producerScope]
        rw [Hopening.fvars_eq_bound
          HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] at _HfieldParameterUp
        exact _HfieldParameterUp)
      HtelescopesArgs HbindingsArgs HoriginsArgs HmotiveShapesArgs hrecords
  intro outCtx Rout hypotheses calls HhypothesesRecent HhypothesisOrigins
    HhypothesisCallOrigins HhypothesisCallSemantics hhypothesesSize hcallsSize
  let HextAll := HextArgs.trans HhypothesesRecent.contextExtension
  have HmotiveAt : TrExprS Rout.venv recLparams Rout.mlctx.vlctx
      (Expr.app
        (mkAppN recInfos[Happlication.ownerIdx]!.motive
          terminal.getAppArgs[stats.params.size:])
        (mkAppN
          (mkAppN (.const ctor.name stats.levels) stats.params) allFields))
      (motiveTarget.lift' (HhypothesesRecent.contextExtension.shift.consN 0)) :=
    HhypothesesRecent.contextExtension.weakTrExprS Hmotive
  have HmotiveTypeAt : Rout.venv.IsType recLparams.length
      Rout.mlctx.vlctx.toCtx
      (motiveTarget.lift' (HhypothesesRecent.contextExtension.shift.consN 0)) :=
    HhypothesesRecent.contextExtension.weakIsType HmotiveType
  rcases HhypothesesRecent.mkForall HmotiveAt HmotiveTypeAt with
    ⟨hypothesesTarget, Hhypotheses, HhypothesesType⟩
  have houter : outCtx.lctx.mkForall allFields
        (outCtx.lctx.mkForall hypotheses
          (Expr.app
            (mkAppN recInfos[Happlication.ownerIdx]!.motive
              terminal.getAppArgs[stats.params.size:])
            (mkAppN
              (mkAppN (.const ctor.name stats.levels) stats.params)
              allFields))) =
      current.lctx.mkForall allFields
        (outCtx.lctx.mkForall hypotheses
          (Expr.app
            (mkAppN recInfos[Happlication.ownerIdx]!.motive
              terminal.getAppArgs[stats.params.size:])
            (mkAppN
              (mkAppN (.const ctor.name stats.levels) stats.params)
              allFields))) :=
    HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.mkForall_mono
      HhypothesesRecent.contextLE _
  rcases HfieldsRecent.mkForall Hhypotheses HhypothesesType with
    ⟨minorTarget, HminorRaw, HminorRawType⟩
  have HminorRaw' : TrExprS R.venv recLparams R.mlctx.vlctx
      (outCtx.lctx.mkForall allFields
        (outCtx.lctx.mkForall hypotheses
          (Expr.app
            (mkAppN recInfos[Happlication.ownerIdx]!.motive
              terminal.getAppArgs[stats.params.size:])
            (mkAppN
              (mkAppN (.const ctor.name stats.levels) stats.params)
              allFields)))) minorTarget := by
    rw [houter]
    exact HminorRaw
  have hget : ((getLCtx : AddInductive.M LocalContext) outCtx).WF
      (fun lctx => lctx = outCtx.lctx) := by
    intro lctx h
    cases h
    rfl
  dsimp only [finish]
  refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
    hget fun lctx hlctx => ?_
  subst lctx
  have HminorRawAt := HextAll.weakTrExprS HminorRaw'
  have HminorRawTypeAt := HextAll.weakIsType HminorRawType
  rcases hconsume outCtx recLparams Rout HminorRawAt HminorRawTypeAt with
    ⟨consumedTarget, Hconsumed⟩
  let HsuffixOut :=
    (Hsuffix.weakenRecent HfieldsRecent).weakenRecent HhypothesesRecent
  let HstatsOut := HstatsArgs.weakenRecent HhypothesesRecent
  have hctxOut : VLCtx.NoIndConsts (decl.types.map (·.name))
      Rout.mlctx.vlctx :=
    HhypothesesRecent.noIndConsts
      (names := decl.types.map (·.name)) hctxArgs
  let traversal : RecInfoMinorTraversalShape := {
    constructor := ctor
    rootContext := c
    terminalContext := current
    terminal := terminal
    fields := allFields
    recursiveFields := recursiveFields
    stats := stats
    recursivePositions := positions
    decisions := Hdecisions
    recursivePositions_ordered := Hdecisions.positions_ordered
    recursivePositions_lt := Hdecisions.positions_lt
    recursivePositions_length := Hdecisions.positions_length
    parameterTail := tail
    parameterTail_fvars := by
      apply htailScope.mono
      intro fv hfv
      rw [Hparams.exprArrayFVarIds] at hfv
      exact Hparams.members fv hfv
    parameterPrefix := hprefix
    fieldFVars := Hopening.fvars
    fields_eq := Hopening.expressions
    fieldFVars_nodup := Hopening.nodup
    fieldResidual := Hopening.residual
    fieldTelescope := Hopening.telescope
    fieldClosed := Hopening.closed
    fieldResidual_not_forall := by
      rw [← Hopening.closed, Expr.abstractList_isForall]
      exact HterminalNonforall }
  let HbindingsOut := Hbindings.mono HextAll.contextLE
  let HoriginsOut := Horigins.mono HextAll.contextLE
  let HparamsOut := Hparams.mono HextAll.contextLE
  have HorderArgs := Horder.monoRecent HfieldsRecent
  have HorderOut0 := HorderArgs.monoRecent HhypothesesRecent
  have HorderOut : RecInfoOuterOrder Rout HparamsOut HbindingsOut := by
    unfold RecInfoOuterOrder at HorderOut0 ⊢
    change (Hparams.fvars ++ Hbindings.motives.fvars ++
      Hbindings.flatMinors.fvars).reverse <+ Rout.mlctx.vlctx.fvars
    exact HorderOut0
  let HminorSemanticsOut := HminorSemantics.mono HextAll
  let HcompletedOrigins : RecInfoMinorHypothesisTypeOrigins
      outCtx recursiveFields hypotheses := {
    stats := stats
    recInfos := recInfos
    fieldRoot := current
    fieldRoot_wf := Rargs.toBindingContextWF
    hypotheses_outer_fresh := by
      intro fv houter hhypothesis
      rw [Hparams.exprArrayFVarIds,
        Hbindings.motives.exprArrayFVarIds] at houter
      rw [(HhypothesesRecent.toFreshBoundFVarArray.toBoundFVarArray
        ).exprArrayFVarIds] at hhypothesis
      apply HhypothesesRecent.toFreshBoundFVarArray.fresh fv hhypothesis
      apply HextArgs.contextLE.fvars
      rcases List.mem_append.mp houter with hparam | hmotive
      · exact Hparams.members fv hparam
      · exact Hbindings.motives.members fv hmotive
    entry := by
      intro j hj
      rcases HhypothesisOrigins.entry j hj with
        ⟨originRoot, sourceType, HoriginRoot, ⟨O⟩, D, htype⟩
      exact ⟨originRoot, sourceType, HoriginRoot, ⟨O.toMinor⟩, D, htype⟩ }
  have HcompletedCalls :
      RecInfoCallBlueprintOrigins HcompletedOrigins calls := by
    refine {
      size_eq := HhypothesisCallOrigins.size_eq
      entry := ?_ }
    intro j hj
    rcases HhypothesisCallOrigins.entry j hj with
      ⟨originRoot, sourceType, O, D, HoriginRoot, htype, hcall⟩
    exact ⟨originRoot, sourceType, O, D, HoriginRoot, htype, hcall⟩
  refine continueMinorSemantics (Q := Q) stats indTypes dIdx recInfos
    (ctor.name.replacePrefix indTypeName .anonymous)
    (outCtx.lctx.mkForall allFields
      (outCtx.lctx.mkForall hypotheses
        (Expr.app
          (mkAppN recInfos[Happlication.ownerIdx]!.motive
            indices)
          (mkAppN
            (mkAppN (.const ctor.name stats.levels) stats.params)
            allFields))))
    (fun minor => {
      ctor := ctor.name
      fields := allFields
      lctx := outCtx.lctx
      recursiveCalls := calls
      targetTypeIdx := Happlication.ownerIdx
      targetIndices := indices
      minor := minor })
    k Rout HsuffixOut HstatsOut hctxOut HbindingsOut HoriginsOut
      (Hblueprints.mono HextAll.contextLE)
      (HblueprintSemantics.mono HextAll)
      (HminorSources.mono HextAll.contextLE)
      HminorSemanticsOut
      (HmajorTypes.mono HextAll) HmajorShapes
      (HmotiveTypes.mono HextAll)
      (HmotiveShapes.mono Hbindings HextAll.contextLE)
      (Htelescopes.mono HextAll) (HindexRows.mono HextAll)
      HparamsOut
      (Hbindings.mono_noAlias Hparams HextAll.contextLE HnoAlias)
      HorderOut (Hroot.trans HextAll.contextLE) hidx hsourceIdx Harities
      Hlater Hconsumed.consumed
      Hconsumed.isType {
        localIndex := HoriginsOut.minorTypes[dIdx]!.size
        origin := (outCtx.lctx.mkForall allFields
          (outCtx.lctx.mkForall hypotheses
            (Expr.app
              (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
              (mkAppN
                (mkAppN (.const ctor.name stats.levels) stats.params)
                allFields)))).consumeTypeAnnotationsVerified
        constructor := ctor
        sourceConstructors := sourceConstructors
        sourceConstructor := by
          simpa [HoriginsOut, RecInfoTypeOrigins.mono, horiginIndex] using
            hsourceConstructor
        sourceFullContext := outCtx
        sourceFullWF := Rout.toBindingContextWF
        sourceContext := outCtx.lctx
        sourceContext_eq := rfl
        fields := allFields
        fields_bound :=
          HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.mono
            HhypothesesRecent.contextExtension.contextLE
        fields_nodup := HfieldsRecent.toFreshBoundFVarArray.nodup
        recursiveFields := recursiveFields
        hypotheses := hypotheses
        hypotheses_bound :=
          HhypothesesRecent.toFreshBoundFVarArray.toBoundFVarArray
        hypotheses_nodup :=
          HhypothesesRecent.toFreshBoundFVarArray.nodup
        hypotheses_fields_fresh := by
          intro fv hhypothesis hfield
          apply HhypothesesRecent.toFreshBoundFVarArray.fresh fv
            hhypothesis
          exact HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.members
            fv hfield
        hypothesis_type_origins := some HcompletedOrigins
        hypotheses_size := hhypothesesSize
        traversal := some traversal
        hypothesis_origins_fieldRoot := by
          intro origins' T horigins htraversal
          simp only [Option.some.injEq] at horigins htraversal
          subst origins'
          subst T
          rfl
        motiveApp := Expr.app
          (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
          (mkAppN
            (mkAppN (.const ctor.name stats.levels) stats.params)
            allFields)
        sourceType := outCtx.lctx.mkForall allFields
          (outCtx.lctx.mkForall hypotheses
            (Expr.app
              (mkAppN recInfos[Happlication.ownerIdx]!.motive indices)
              (mkAppN
                (mkAppN (.const ctor.name stats.levels) stats.params)
                allFields)))
        sourceType_eq := rfl
        consumed_eq := rfl } ⟨rfl, rfl⟩ (by
          simpa [HoriginsOut, RecInfoTypeOrigins.mono, horiginIndex] using
            hsourceFamily)
      (by exact ⟨rfl, rfl⟩)
      ⟨{
        semantic := {
          sourceWF := Rout
          extension := RecursorContextExtension.refl Rout
          traversal := traversal
          traversal_eq := rfl
          traversal_fields := rfl
          rootWF := R
          terminalWF := Rargs
          parameterDepth := depth
          parameterSuffix := Hsuffix
          parameterScope := by
            apply htailScope.mono
            intro fv hfv
            rw [Hsuffix.parameterDecls_fvars]
            simpa using hfv
          parameterTarget := tailTarget
          parameterTranslation := htail
          parameterType := htailType
          fieldsRecent := HfieldsRecent
          fieldOpening := Hopening
          fieldParameterUp := by
            rw [Hopening.fvars_eq_bound
              HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] at _HfieldParameterUp
            exact _HfieldParameterUp
          hypothesesRecent := HhypothesesRecent
          terminalTarget := terminalTarget
          terminalTranslation := Hterminal
          terminalType := HterminalType
          constructorApplication := Happlication
          fieldTargetDefEq := HfieldTargetDefEq
          motivePreTarget := motiveTarget
          motivePreTranslation := Hmotive
          motivePreType := HmotiveType
          motiveHeadRoot := by
            have hownerMotive : Happlication.ownerIdx <
                (recInfos.map (·.motive)).size := by
              simpa using htarget
            rcases Hbindings.motives.getElem_eq_fvar
                Happlication.ownerIdx hownerMotive with
              ⟨hmotiveFVars, hmotiveSource⟩
            let motiveFVar :=
              Hbindings.motives.fvars[Happlication.ownerIdx]
            have hmotiveBang : recInfos[Happlication.ownerIdx]!.motive =
                .fvar motiveFVar := by
              rw [getElem!_pos recInfos Happlication.ownerIdx htarget]
              simpa [motiveFVar] using hmotiveSource
            refine ⟨motiveFVar, ?_, ?_⟩
            · simp [Expr.getAppFn, Expr.getAppFn_mkAppN, hmotiveBang]
            · apply Horder.subset
              apply List.mem_reverse.mpr
              simp [motiveFVar, List.getElem_mem hmotiveFVars]
          motiveTarget := motiveTarget.lift'
            (HhypothesesRecent.contextExtension.shift.consN 0)
          motiveTranslation := HmotiveAt
          motiveType := HmotiveTypeAt
          sourceTarget := minorTarget.lift' (HextAll.shift.consN 0)
          consumedTarget := consumedTarget
          consumption := Hconsumed }
        parameterDecls_eq := rfl }⟩
      (by
        intro fv hfield houter
        apply HfieldsRecent.toFreshBoundFVarArray.fresh fv hfield
        rcases List.mem_append.mp houter with hpm | hminor
        · rcases List.mem_append.mp hpm with hparam | hmotive
          · exact Hparams.members fv hparam
          · exact Hbindings.motives.members fv hmotive
        · exact Hbindings.flatMinors.members fv hminor)
      ⟨traversal, rfl, rfl, rfl, rfl, rfl, by
        rw [howner]
        exact Happlication.owner_valid, by rw [howner],
        HextAll.contextLE,
        HhypothesesRecent.contextExtension.contextLE,
        BindingContextLE.refl outCtx⟩
      (by
        refine ⟨rfl, rfl, rfl, rfl, traversal, HcompletedOrigins,
          rfl, rfl, ?_, ?_, HcompletedCalls⟩
        · rw [howner]
        · rw [howner])
      (by
        refine ⟨HcompletedOrigins, rfl, rfl, rfl, {
          traversal := traversal
          traversal_eq := rfl
          traversal_constructor := rfl
          traversal_fields := rfl
          traversal_recursiveFields := rfl
          traversal_stats := rfl
          rootWF := R
          terminalWF := Rargs
          parameterDepth := depth
          parameterSuffix := Hsuffix
          terminalExtension := HhypothesesRecent.contextExtension
          fieldsRecent := HfieldsRecent
          parameterTarget := tailTarget
          parameterTail_params := htailScope
          parameterTranslation := htail
          parameterType := htailType
          fieldOpening := Hopening
          fieldParameterUp := by
            rw [Hopening.fvars_eq_bound
              HfieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] at _HfieldParameterUp
            exact _HfieldParameterUp
          terminalTarget := terminalTarget
          terminalTranslation := Hterminal
          terminalType := HterminalType
          constructorApplication := Happlication
          fieldTargetDefEq := HfieldTargetDefEq }, rfl,
          depth + allFields.size, HstatsArgs, fields, Hselections,
          hdidxValid, hdidxDecl,
          Happlication.ownerIdx,
          Happlication.owner_valid, ⟨Hvalidated⟩,
          Hbinding, HmotiveEvidence,
          ⟨RecInfoMotiveTelescopeLookup.of HtelescopesArgs HbindingsArgs
            HoriginsArgs HmotiveShapesArgs⟩, ⟨?_⟩⟩
        · simpa using HhypothesisCallSemantics) ?_
  intro nextCtx nextDepth next Rnext henvNext HsuffixNext
    hparameterDeclsNext HstatsNext hctxNext HbindingsNext HoriginsNext
    HblueprintsNext HblueprintSemanticsNext HminorSourcesNext
    HminorSemanticsNext
    hsizeNext hcountNext hotherNext
    HmajorTypesNext HmajorShapesNext
    HmotiveTypesNext HmotiveShapesNext HtelescopesNext HindexRowsNext
    HparamsNext HnoAliasNext HorderNext HaritiesNext HrootNext
  exact Hk next Rnext (henvNext.trans HextAll.venv_eq) HsuffixNext
    (hparameterDeclsNext.trans (by rfl)) HstatsNext hctxNext
    HbindingsNext HoriginsNext HblueprintsNext HblueprintSemanticsNext
    HminorSourcesNext
    HminorSemanticsNext
    hsizeNext hcountNext hotherNext
    HmajorTypesNext HmajorShapesNext HmotiveTypesNext HmotiveShapesNext
    HtelescopesNext HindexRowsNext HparamsNext HnoAliasNext HorderNext
    HaritiesNext HrootNext

/-- Semantic refinement of the complete constructor list for one mutual
family.  Each iteration consumes the checker-produced runtime seed for its
constructor and adds exactly one verified minor to the owning recursor row. -/
theorem resultSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType)
    (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors sourceConstructors : List Constructor) (sourceIndex : Nat)
    (hconstructors : ctors = sourceConstructors.drop sourceIndex)
    (hsourceFamily : sourceConstructors = indTypes[dIdx]!.ctors)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hblueprints : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (HblueprintSemantics : RecInfoRuleBlueprintSemanticOrigins R decl stats
      recInfos elimLevel Hsuffix.parameterDecls Horigins)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      Hsuffix.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (hminorIndex : recInfos[dIdx]!.minors.size = sourceIndex)
    (Harities : RecInfoArities stats recInfos)
    (Hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Hseed : ∀ {current : AddInductive.Context} {currentDepth : Nat}
      (Rcurrent : RecursorContextWF current recLparams),
      Rcurrent.venv = R.venv →
      (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
        currentDepth) →
      HsuffixCurrent.parameterDecls = Hsuffix.parameterDecls →
      ∀ ctor, ctor ∈ ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty (CheckedConstructorOwnerNormalForm stats dIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          tail tailTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params)
          introTarget ∧
        Rcurrent.venv.HasType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams),
      Rout.venv = R.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls = Hsuffix.parameterDecls →
      RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (HbindingsOut : RecInfoBindings outCtx out) →
      (HoriginsOut : RecInfoTypeOrigins outCtx out) →
      RecInfoRuleBlueprintOrigins stats out HoriginsOut →
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = recInfos.size →
      out[dIdx]!.minors.size =
        recInfos[dIdx]!.minors.size + ctors.length →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
      ctors k c).WF Q := by
  induction ctors generalizing recInfos c depth sourceIndex with
  | nil =>
      exact Hk recInfos R rfl Hsuffix rfl Hstats hctx Hbindings Horigins
        Hblueprints HblueprintSemantics HminorSources HminorSemantics rfl (by simp)
        (by intros; rfl)
        HmajorTypes HmajorShapes
        HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams HnoAlias
        Horder Harities Hroot
  | cons ctor ctors ih =>
      have hsourceConstructor :
          sourceConstructors[sourceIndex]? = some ctor := by
        have hhead := congrArg (fun xs => xs[0]?) hconstructors
        simpa using hhead.symm
      have htailConstructors :
          ctors = sourceConstructors.drop (sourceIndex + 1) := by
        have htail := congrArg List.tail hconstructors
        simpa [List.tail_drop] using htail
      have horiginIndex : Horigins.minorTypes[dIdx]!.size = sourceIndex := by
        rw [(Horigins.minors dIdx hidx).size_eq]
        exact hminorIndex
      rcases Hseed R rfl Hsuffix rfl ctor (by simp) with
        ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailScope, Htail,
          HtailType, Hintro, HintroType⟩
      rw [AddInductive.mkRecInfos.loopCtors]
      refine oneConstructorSemantics (Q := Q) stats indTypes indTypeName dIdx recInfos
        ctor tail sourceConstructors sourceIndex hsourceConstructor hsourceFamily
        (fun next => AddInductive.mkRecInfos.loopCtors stats indTypeName
          dIdx next ctors k)
        R Hsuffix Hstats Hprefix HtailScope hconsume hlit hctx hproj Htail
        HtailType Hintro HintroType Hbindings Horigins Hblueprints
        HblueprintSemantics HminorSources
        HminorSemantics HmajorTypes
        HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexRows
        Hparams HnoAlias Horder Hroot hidx hsourceIdx horiginIndex Harities
        Hlater hrecords Hnormal ?_
      intro nextCtx nextDepth next Rnext henvNext HsuffixNext
        hparameterDeclsNext HstatsNext hctxNext HbindingsNext HoriginsNext
        HblueprintsNext HblueprintSemanticsNext HminorSourcesNext HminorSemanticsNext
        hsizeNext hcountNext hotherNext
        HmajorTypesNext HmajorShapesNext
        HmotiveTypesNext HmotiveShapesNext HtelescopesNext HindexRowsNext
        HparamsNext HnoAliasNext HorderNext HaritiesNext HrootNext
      refine ih next (sourceIndex + 1) htailConstructors Rnext HsuffixNext
        HstatsNext (by simpa only [henvNext] using hlit) hctxNext HbindingsNext
        HoriginsNext HblueprintsNext HblueprintSemanticsNext HminorSourcesNext
        HminorSemanticsNext
        HmajorTypesNext
        HmajorShapesNext HmotiveTypesNext
        HmotiveShapesNext HtelescopesNext HindexRowsNext HparamsNext
        HnoAliasNext HorderNext HrootNext ?_ ?_ HaritiesNext ?_ ?_ ?_ ?_
      · simpa [hsizeNext] using hidx
      · rw [hcountNext, hminorIndex]
      · intro i hdi hiNext
        rw [hotherNext i (by simpa [hsizeNext] using hiNext)
          (Nat.ne_of_lt hdi)]
        exact Hlater i hdi (by simpa [hsizeNext] using hiNext)
      · exact hsizeNext.trans hrecords
      · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
          hparameterDeclsCurrent nextCtor hnextCtor
        apply Hseed Rcurrent (henvCurrent.trans henvNext) HsuffixCurrent
          (hparameterDeclsCurrent.trans hparameterDeclsNext) nextCtor
        simp [hnextCtor]
      · intro outCtx outDepth out Rout henvOut HsuffixOut
          hparameterDeclsOut HstatsOut hctxOut HbindingsOut HoriginsOut
          HblueprintsOut HblueprintSemanticsOut HminorSourcesOut HminorSemanticsOut
          houtSize houtCount houtOther
          HmajorTypesOut HmajorShapesOut
          HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
          HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
        have houtSize' : out.size = recInfos.size :=
          houtSize.trans hsizeNext
        have houtCount' : out[dIdx]!.minors.size =
            recInfos[dIdx]!.minors.size + (ctor :: ctors).length := by
          rw [houtCount, hcountNext]
          simp
          omega
        have houtOther' : ∀ i, i < recInfos.size → dIdx ≠ i →
            out[i]!.minors.size = recInfos[i]!.minors.size := by
          intro i hi hine
          rw [houtOther i (by simpa [hsizeNext] using hi) hine]
          exact hotherNext i hi hine
        exact Hk out Rout (henvOut.trans henvNext) HsuffixOut
          (hparameterDeclsOut.trans hparameterDeclsNext) HstatsOut hctxOut
          HbindingsOut HoriginsOut HblueprintsOut HblueprintSemanticsOut HminorSourcesOut
          HminorSemanticsOut
          houtSize' houtCount' houtOther'
          HmajorTypesOut HmajorShapesOut HmotiveTypesOut HmotiveShapesOut
          HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
          HaritiesOut HrootOut

/-- Processing constructors retains every field and induction-hypothesis
binder and appends the resulting minor binder to the certificate of its
owning inductive. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats) (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors : List Constructor)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hidx : dIdx < recInfos.size)
    (Harities : RecInfoArities stats recInfos)
    (Hk : ∀ out c, out.size = recInfos.size →
      out[dIdx]!.minors.size =
        recInfos[dIdx]!.minors.size + ctors.length →
      (∀ i, i < recInfos.size → dIdx ≠ i →
        out[i]!.minors.size = recInfos[i]!.minors.size) →
      BindingContextWF c →
      (Hbindings : RecInfoBindings c out) →
      (Horigins : RecInfoTypeOrigins c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams → RecInfoArities stats out →
      BindingContextLE root c →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
      ctors k c).WF Q := by
  induction ctors generalizing recInfos c with
  | nil =>
      simpa [AddInductive.mkRecInfos.loopCtors] using
        Hk recInfos c rfl (by simp) (by intros; rfl)
          Hc Hbindings Horigins Hparams HnoAlias Harities Hroot
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecInfos.loopCtors]
      refine mkRecInfos.loopCtorArgs.resultBindings (Q := Q) stats ctor.type
        (fun t bu u =>
          let (itIdx, itIndices) := AddInductive.getIIndices stats t
          let introApp := mkAppN
            (mkAppN (.const ctor.name stats.levels) stats.params) bu
          let motiveApp := Expr.app
            (mkAppN recInfos[itIdx]!.motive itIndices) introApp
          AddInductive.mkRecInfos.loopUBlueprints stats u recInfos 0 #[] #[]
              fun v calls => do
            let lctx ← getLCtx
            let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
            let minorName := ctor.name.replacePrefix indTypeName .anonymous
            withLocalDecl minorName .default minorTy.consumeTypeAnnotationsVerified fun minor =>
              let recInfos := recInfos.modify dIdx fun s =>
                { s with
                  minors := s.minors.push minor
                  ruleBlueprints := s.ruleBlueprints.push {
                    ctor := ctor.name
                    fields := bu
                    lctx := lctx
                    recursiveCalls := calls
                    targetTypeIdx := itIdx
                    targetIndices := itIndices
                    minor := minor } }
              AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
                ctors k)
        c Hc ?_
      intro t bu u cArgs HcArgs Hbu Hu _hselected hArgs
      rcases hindices : AddInductive.getIIndices stats t with
        ⟨itIdx, itIndices⟩
      simp only
      let introApp := mkAppN
        (mkAppN (.const ctor.name stats.levels) stats.params) bu
      let motiveApp := Expr.app
        (mkAppN recInfos[itIdx]!.motive itIndices) introApp
      apply mkRecInfos.loopUBlueprints.resultBindings (root := cArgs) (Q := Q)
        stats u recInfos
        (fun v calls => do
          let lctx ← getLCtx
          let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
          let minorName := ctor.name.replacePrefix indTypeName .anonymous
          withLocalDecl minorName .default minorTy.consumeTypeAnnotationsVerified fun minor =>
            let recInfos := recInfos.modify dIdx fun s =>
              { s with
                minors := s.minors.push minor
                ruleBlueprints := s.ruleBlueprints.push {
                  ctor := ctor.name
                  fields := bu
                  lctx := lctx
                  recursiveCalls := calls
                  targetTypeIdx := itIdx
                  targetIndices := itIndices
                  minor := minor } }
            AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos
              ctors k)
        0 #[] #[] cArgs HcArgs (FreshBoundFVarArray.empty cArgs)
          (BindingContextLE.refl cArgs) rfl
      intro v calls cIH HcIH Hv hIH hvSize hcallsSize
      have hget : ((getLCtx : AddInductive.M LocalContext) cIH).WF
          (fun lctx => lctx = cIH.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      let minorTy := cIH.lctx.mkForall bu <| cIH.lctx.mkForall v motiveApp
      let minorName := ctor.name.replacePrefix indTypeName .anonymous
      apply withLocalDecl.continueRaw
      let next := recInfos.modify dIdx fun s =>
        { s with
          minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩)
          ruleBlueprints := s.ruleBlueprints.push {
            ctor := ctor.name
            fields := bu
            lctx := cIH.lctx
            recursiveCalls := calls
            targetTypeIdx := itIdx
            targetIndices := itIndices
            minor := .fvar ⟨cIH.ngen.curr⟩ } }
      let cMinor : AddInductive.Context := { cIH with
        ngen := cIH.ngen.next
        lctx := cIH.lctx.mkLocalDecl ⟨cIH.ngen.curr⟩ minorName
          minorTy.consumeTypeAnnotationsVerified .default }
      let HcMinor := HcIH.withLocalDecl minorName
        minorTy.consumeTypeAnnotationsVerified .default
      let HbindingsMinor := Hbindings.addMinor dIdx hidx (hArgs.trans hIH)
        HcIH minorName minorTy.consumeTypeAnnotationsVerified .default
      let HoriginsMinor := Horigins.addMinor dIdx hidx (hArgs.trans hIH)
        HcIH minorName minorTy.consumeTypeAnnotationsVerified .default {
          localIndex := Horigins.minorTypes[dIdx]!.size
          origin := minorTy.consumeTypeAnnotationsVerified
          constructor := ctor
          sourceConstructors :=
            List.replicate Horigins.minorTypes[dIdx]!.size ctor ++ [ctor]
          sourceConstructor := by simp
          sourceFullContext := cIH
          sourceFullWF := HcIH
          sourceContext := cIH.lctx
          sourceContext_eq := rfl
          fields := bu
          fields_bound := Hbu.mono hIH
          fields_nodup := Hbu.nodup
          recursiveFields := u
          hypotheses := v
          hypotheses_bound := Hv.toBoundFVarArray
          hypotheses_nodup := Hv.nodup
          hypotheses_fields_fresh := by
            intro fv hhypothesis hfield
            exact Hv.fresh fv hhypothesis
              (Hbu.toBoundFVarArray.members fv hfield)
          hypothesis_type_origins := none
          hypotheses_size := by simpa using hvSize
          traversal := none
          hypothesis_origins_fieldRoot := by
            intro origins T horigins _htraversal
            simp at horigins
          motiveApp := motiveApp
          sourceType := minorTy
          sourceType_eq := rfl
          consumed_eq := rfl } ⟨rfl, rfl⟩
      let blueprint : AddInductive.RecRuleBlueprint := {
        ctor := ctor.name
        fields := bu
        lctx := cIH.lctx
        recursiveCalls := calls
        targetTypeIdx := itIdx
        targetIndices := itIndices
        minor := .fvar ⟨cIH.ngen.curr⟩ }
      let Hcore := modifyMinorAndBlueprint_coreEq recInfos dIdx hidx
        (.fvar ⟨cIH.ngen.curr⟩) blueprint
      let HbindingsNext : RecInfoBindings cMinor next :=
        HbindingsMinor.rebaseCore Hcore
      let HoriginsNext : RecInfoTypeOrigins cMinor next :=
        HoriginsMinor.rebaseCore Hcore
      let HparamsMinor := Hparams.mono <| (hArgs.trans hIH).trans <|
          BindingContextLE.withLocalDecl cIH HcIH minorName
            minorTy.consumeTypeAnnotationsVerified .default
      let HnoAliasMinor := Hbindings.addMinor_noAlias Hparams HnoAlias
        dIdx hidx (hArgs.trans hIH) HcIH minorName
          minorTy.consumeTypeAnnotationsVerified .default
      have HnoAliasNext : HbindingsNext.NoAlias HparamsMinor := by
        exact RecInfoBindings.NoAlias.rebaseCore HbindingsMinor HparamsMinor
          HnoAliasMinor Hcore
      let HrootMinor := (Hroot.trans hArgs).trans <| hIH.trans <|
          BindingContextLE.withLocalDecl cIH HcIH minorName
            minorTy.consumeTypeAnnotationsVerified .default
      refine ih next cMinor HcMinor HbindingsNext HoriginsNext
        HparamsMinor HnoAliasNext
        HrootMinor ?_ ?_ ?_
      · simpa [next] using hidx
      · exact (Harities.modifyMinors dIdx (fun minors =>
          minors.push (.fvar ⟨cIH.ngen.curr⟩))).rebaseCore Hcore
      · intro out cOut houtSize houtCount houtOther HcOut HbindingsOut
          HoriginsOut HparamsOut HnoAliasOut HaritiesOut HrootOut
        have houtSize' : out.size = recInfos.size := by
          simpa [next] using houtSize
        have houtCount' : out[dIdx]!.minors.size =
            recInfos[dIdx]!.minors.size + (ctor :: ctors).length := by
          rw [houtCount]
          dsimp [next]
          rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _
            hidx]
          simp
          omega
        have houtOther' : ∀ i, i < recInfos.size → dIdx ≠ i →
            out[i]!.minors.size = recInfos[i]!.minors.size := by
          intro i hi hine
          rw [houtOther i (by simpa [next] using hi) hine]
          rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
            hi hine]
        exact Hk out cOut houtSize' houtCount' houtOther' HcOut HbindingsOut
          HoriginsOut HparamsOut HnoAliasOut HaritiesOut HrootOut

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

/-- The second mutual pass preserves all retained recursor binders while it
visits each owner and inserts that owner's constructor minors. -/
theorem resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Hroot : BindingContextLE root c)
    (hsize : recInfos.size = indTypes.size)
    (Harities : RecInfoArities stats recInfos)
    (Hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (Hsuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      BindingContextWF c →
      (Hbindings : RecInfoBindings c out) →
      (Horigins : RecInfoTypeOrigins c out) →
      (Hparams : BoundFVarArray c stats.params) →
      Hbindings.NoAlias Hparams → RecInfoArities stats out →
      BindingContextLE root c →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultBindings (Q := Q) stats
      indTypes[dIdx].name dIdx recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes
        (dIdx + 1) out k)
      c Hc Hbindings Horigins Hparams HnoAlias Hroot
      (by simpa [hsize] using hidx)
      Harities
    intro out cOut houtSize houtCount houtOther HcOut HbindingsOut
      HoriginsOut HparamsOut HnoAliasOut HaritiesOut HrootOut
    apply resultBindings (root := root) (Q := Q) stats indTypes (dIdx + 1)
      out k cOut HcOut HbindingsOut HoriginsOut HparamsOut HnoAliasOut HrootOut
    · exact houtSize.trans hsize
    · exact HaritiesOut
    · intro i hiDone hiOut
      by_cases hieq : i = dIdx
      · subst i
        rw [houtCount, Hsuffix dIdx (Nat.le_refl _) (by
          simpa [houtSize] using hiOut)]
        simp [Array.getElem!_eq_getD, Array.getD, hidx]
      · rw [houtOther i (by simpa [houtSize] using hiOut) (Ne.symm hieq)]
        exact Hprefix i (by omega) (by simpa [houtSize] using hiOut)
    · intro i hiNext hiOut
      have hine : dIdx ≠ i := by omega
      rw [houtOther i (by simpa [houtSize] using hiOut) hine]
      exact Hsuffix i (by omega) (by simpa [houtSize] using hiOut)
    · exact Hk
  · rw [dif_neg hidx]
    exact Hk recInfos c hsize (fun i hi => Hprefix i (by omega) hi)
      Hc Hbindings Horigins Hparams HnoAlias Harities Hroot
termination_by indTypes.size - dIdx

/-- Semantic refinement of the complete second mutual pass.  The processed
prefix has its exact constructor/minor cardinalities, the unprocessed suffix
is empty, and every checker-produced constructor seed is consumed at its
original mutual-family owner. -/
theorem resultSemantics {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    {recLparams : List Name} {depth : Nat}
    {root c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    {decl : VInductDecl}
    (HsuffixCtx : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) R.mlctx.vlctx)
    (hproj : ∀ {Delta : VLCtx} {s j e' e''},
      TrProj Delta.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hblueprints : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (HblueprintSemantics : RecInfoRuleBlueprintSemanticOrigins R decl stats
      recInfos elimLevel HsuffixCtx.parameterDecls Horigins)
    (HminorSources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (HminorSemantics : RecInfoMinorSemanticAlignment R Horigins
      HsuffixCtx.parameterDecls)
    (HmajorTypes : RecursorTranslatedOriginTypes R Horigins.majorTypes)
    (HmajorShapes : RecInfoMajorTypeShapes stats recInfos
      Horigins.majorTypes)
    (HmotiveTypes : RecursorTranslatedOriginTypes R Horigins.motiveTypes)
    (HmotiveShapes : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (Htelescopes : RecInfoMotiveTelescopes R stats decl parameterCtx recInfos
      elimLevel)
    (HindexRows : RecursorTranslatedOriginTypeRows R Horigins.indexTypes)
    (Hparams : BoundFVarArray c stats.params)
    (HnoAlias : Hbindings.NoAlias Hparams)
    (Horder : RecInfoOuterOrder R Hparams Hbindings)
    (Hroot : BindingContextLE root c)
    (hsize : recInfos.size = indTypes.size)
    (hrecords : recInfos.size = stats.indConsts.size)
    (Harities : RecInfoArities stats recInfos)
    (Hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (HemptySuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hseed : ∀ {current : AddInductive.Context} {currentDepth : Nat}
      (Rcurrent : RecursorContextWF current recLparams),
      Rcurrent.venv = R.venv →
      (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
        currentDepth) →
      HsuffixCurrent.parameterDecls = HsuffixCtx.parameterDecls →
      ∀ familyIdx, (hfamily : familyIdx < indTypes.size) →
      ∀ ctor, ctor ∈ indTypes[familyIdx].ctors →
      ∃ tail tailTarget introTarget,
        RecursorParamPrefix stats 0 ctor.type tail ∧
        Nonempty
          (CheckedConstructorOwnerNormalForm stats familyIdx tail) ∧
        tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          tail tailTarget ∧
        Rcurrent.venv.IsType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
        TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
          (mkAppN (.const ctor.name stats.levels) stats.params)
          introTarget ∧
        Rcurrent.venv.HasType recLparams.length
          Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget)
    (Hk : ∀ {outCtx : AddInductive.Context} {outDepth : Nat}
      (out : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF outCtx recLparams),
      Rout.venv = R.venv →
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) →
      HsuffixOut.parameterDecls = HsuffixCtx.parameterDecls →
      RecursorValidAppStatsWF Rout.venv recLparams
        Rout.mlctx.vlctx stats decl outDepth →
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx →
      (HbindingsOut : RecInfoBindings outCtx out) →
      (HoriginsOut : RecInfoTypeOrigins outCtx out) →
      RecInfoRuleBlueprintOrigins stats out HoriginsOut →
      RecInfoRuleBlueprintSemanticOrigins Rout decl stats out elimLevel
        HsuffixOut.parameterDecls HoriginsOut →
      RecInfoMinorSourceAlignment stats indTypes HoriginsOut →
      RecInfoMinorSemanticAlignment Rout HoriginsOut
        HsuffixOut.parameterDecls →
      out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      RecursorTranslatedOriginTypes Rout HoriginsOut.majorTypes →
      RecInfoMajorTypeShapes stats out HoriginsOut.majorTypes →
      RecursorTranslatedOriginTypes Rout HoriginsOut.motiveTypes →
      RecInfoMotiveTypeShapes outCtx out HoriginsOut.motiveTypes elimLevel →
      RecInfoMotiveTelescopes Rout stats decl parameterCtx out elimLevel →
      RecursorTranslatedOriginTypeRows Rout HoriginsOut.indexTypes →
      (HparamsOut : BoundFVarArray outCtx stats.params) →
      HbindingsOut.NoAlias HparamsOut →
      RecInfoOuterOrder Rout HparamsOut HbindingsOut →
      RecInfoArities stats out →
      BindingContextLE root outCtx →
      (k out outCtx).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hfamily : dIdx < indTypes.size
  · rw [dif_pos hfamily]
    refine mkRecInfos.loopCtors.resultSemantics (Q := Q) stats indTypes
      indTypes[dIdx].name dIdx recInfos indTypes[dIdx].ctors
      indTypes[dIdx].ctors 0 rfl
      (by simp [getElem!_pos indTypes dIdx hfamily])
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes
        (dIdx + 1) out k)
      R HsuffixCtx Hstats hconsume hlit hctx hproj Hbindings
      Horigins Hblueprints HblueprintSemantics HminorSources HminorSemantics
      HmajorTypes HmajorShapes
      HmotiveTypes HmotiveShapes
      Htelescopes HindexRows Hparams HnoAlias Horder Hroot
      (by simpa [hsize] using hfamily)
      hfamily
      (by
        exact HemptySuffix dIdx (Nat.le_refl _) (by
          simpa [hsize] using hfamily))
      Harities (fun i hdi hi => HemptySuffix i (by omega) hi) hrecords ?_ ?_
    · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
        hparameterDeclsCurrent ctor hctor
      exact Hseed Rcurrent henvCurrent HsuffixCurrent
        hparameterDeclsCurrent dIdx hfamily ctor hctor
    · intro outCtx outDepth out Rout henvOut HsuffixOut
        hparameterDeclsOut HstatsOut hctxOut HbindingsOut HoriginsOut
        HblueprintsOut HblueprintSemanticsOut HminorSourcesOut HminorSemanticsOut
        houtSize houtCount houtOther
        HmajorTypesOut HmajorShapesOut
        HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
        HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
      refine resultSemantics (root := root) (Q := Q) stats indTypes
        (dIdx + 1) out k Rout HsuffixOut HstatsOut hconsume
        (by simpa only [henvOut] using hlit)
        hctxOut hproj HbindingsOut HoriginsOut HblueprintsOut
        HblueprintSemanticsOut HminorSourcesOut
        HminorSemanticsOut HmajorTypesOut
        HmajorShapesOut HmotiveTypesOut HmotiveShapesOut HtelescopesOut
        HindexRowsOut HparamsOut HnoAliasOut HorderOut HrootOut ?_ ?_
        HaritiesOut
        ?_ ?_ ?_ ?_
      · exact houtSize.trans hsize
      · exact houtSize.trans hrecords
      · intro i hiDone hiOut
        by_cases hieq : i = dIdx
        · subst i
          rw [houtCount, HemptySuffix dIdx (Nat.le_refl _) (by
            simpa [houtSize] using hiOut)]
          simp [Array.getElem!_eq_getD, Array.getD, hfamily]
        · rw [houtOther i (by simpa [houtSize] using hiOut)
            (Ne.symm hieq)]
          exact Hprefix i (by omega) (by simpa [houtSize] using hiOut)
      · intro i hiNext hiOut
        have hine : dIdx ≠ i := by omega
        rw [houtOther i (by simpa [houtSize] using hiOut) hine]
        exact HemptySuffix i (by omega) (by simpa [houtSize] using hiOut)
      · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
          hparameterDeclsCurrent familyIdx hfamilyIdx ctor hctor
        exact Hseed Rcurrent (henvCurrent.trans henvOut) HsuffixCurrent
          (hparameterDeclsCurrent.trans hparameterDeclsOut) familyIdx
          hfamilyIdx ctor hctor
      · intro finalCtx finalDepth final Rfinal henvFinal HsuffixFinal
          hparameterDeclsFinal HstatsFinal hctxFinal HbindingsFinal
          HoriginsFinal HblueprintsFinal HblueprintSemanticsFinal
          HminorSourcesFinal HminorSemanticsFinal
          hfinalSize hfinalCounts HmajorTypesFinal
          HmajorShapesFinal HmotiveTypesFinal HmotiveShapesFinal
          HtelescopesFinal HindexRowsFinal HparamsFinal HnoAliasFinal
          HorderFinal HaritiesFinal HrootFinal
        exact Hk final Rfinal (henvFinal.trans henvOut) HsuffixFinal
          (hparameterDeclsFinal.trans hparameterDeclsOut) HstatsFinal
          hctxFinal HbindingsFinal HoriginsFinal HblueprintsFinal
          HblueprintSemanticsFinal HminorSourcesFinal
          HminorSemanticsFinal hfinalSize hfinalCounts
          HmajorTypesFinal HmajorShapesFinal HmotiveTypesFinal
          HmotiveShapesFinal HtelescopesFinal HindexRowsFinal HparamsFinal
          HnoAliasFinal HorderFinal HaritiesFinal HrootFinal
  · rw [dif_neg hfamily]
    exact Hk recInfos R rfl HsuffixCtx rfl Hstats hctx Hbindings Horigins
      Hblueprints HblueprintSemantics HminorSources HminorSemantics hsize
      (fun i hi => Hprefix i (by omega) hi) HmajorTypes
      HmajorShapes HmotiveTypes HmotiveShapes Htelescopes HindexRows Hparams
      HnoAlias Horder Harities Hroot
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd2

/-- End-to-end operational certificate for `mkRecInfos`: every successful
result has one retained frame per mutual inductive, and all binders created by
both passes remain selectable in the final local context. -/
theorem mkRecInfos.resultBindings {alpha : Type} {Q : alpha → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hparamsNodup : Hparams.fvars.Nodup)
    (Hk : ∀ out cOut, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      BindingContextWF cOut → (Hbindings : RecInfoBindings cOut out) →
      (Horigins : RecInfoTypeOrigins cOut out) →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecInfoArities stats out →
      BindingContextLE c cOut → (k out cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  unfold AddInductive.mkRecInfos
  apply mkRecInfos.loopInd1.resultBindings (root := c) (Q := Q)
    stats indTypes elimLevel 0 #[]
    (fun recInfos => AddInductive.mkRecInfos.loopInd2 stats indTypes 0
      recInfos k)
    c Hc (RecInfoBindings.empty c) (RecInfoTypeOrigins.empty c) Hparams
      (RecInfoBindings.empty_noAlias c Hparams hparamsNodup)
      (BindingContextLE.refl c) rfl
      (RecInfoArities.empty stats) RecInfoMinorsEmpty.empty
      RecInfoBlueprintCounts.empty
  intro recInfos cFrames hsize HcFrames HbindingsFrames HoriginsFrames HparamsFrames
    HnoAliasFrames HaritiesFrames HemptyFrames HblueprintsFrames HrootFrames
  apply mkRecInfos.loopInd2.resultBindings (root := c) (Q := Q)
    stats indTypes 0 recInfos k cFrames HcFrames HbindingsFrames HoriginsFrames
      HparamsFrames HnoAliasFrames HrootFrames
  · simpa using hsize
  · exact HaritiesFrames
  · intro i hi
    omega
  · intro i _ hi
    exact HemptyFrames i hi
  · intro out cOut houtSize houtCounts HcOut HbindingsOut HoriginsOut HparamsOut
      HnoAliasOut HaritiesOut HrootOut
    exact Hk out cOut houtSize houtCounts HcOut HbindingsOut HoriginsOut HparamsOut
      HnoAliasOut HaritiesOut HrootOut

/-- Unified projection used by recursor generation: a single successful run
supplies both the retained executable binders and the independent cardinality
certificate derived from the translated source declaration. -/
theorem mkRecInfos.resultCertificate {alpha : Type} {Q : alpha → Prop}
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore env lparams nparams indTypes.toList isUnsafe
      decl envTypes envCtors)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        headerEnv lparams Δ stats decl depth)
    (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M alpha)
    (c : AddInductive.Context)
    (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hparamsNodup : Hparams.fvars.Nodup)
    (Hk : ∀ out cOut, BindingContextWF cOut →
      (Hbindings : RecInfoBindings cOut out) →
      (Horigins : RecInfoTypeOrigins cOut out) →
      (Hparams : BoundFVarArray cOut stats.params) →
      Hbindings.NoAlias Hparams →
      RecursorCardinalityCertificate stats out decl →
      BindingContextLE c cOut → (k out cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultBindings (Q := Q) stats indTypes elimLevel k c Hc
    Hparams hparamsNodup
  intro out cOut hsize hcounts HcOut Hbindings Horigins HparamsOut HnoAlias
    Harities Hroot
  apply Hk out cOut HcOut Hbindings Horigins HparamsOut HnoAlias
  · exact RecursorCardinalityCertificate.ofResult Hdecl Hmaterialized
      hsize hcounts Harities
  · exact Hroot


end VerifyInductive
end Lean4Lean
