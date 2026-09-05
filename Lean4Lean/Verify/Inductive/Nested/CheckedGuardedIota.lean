import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Recursor.Telescope
import Lean4Lean.Verify.Typing.ProjectionRelation
import Lean4Lean.Inductive.Add

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Concrete guarded-iota syntax and strict translation

This is the source-language counterpart of `VExpr.GuardedIota`.  It is kept
deliberately syntax-directed so the restored-rule validation pass can decide
it on the literal `Lean.Expr` stored in a `RecursorRule`.  The soundness
theorem below passes primitive projections through `TrProj` and its
environment-indexed support expansion; it does not use a global projection
preservation property. -/

/-- A checker context maps every concrete de Bruijn variable to the same
abstract de Bruijn variable.  This holds for the empty context and is
preserved by lambda/forall binders. -/
def ConcreteBVarIdentity (Delta : VLCtx) : Prop :=
  ∀ index target type,
    Delta.find? (.inl index) = some (target, type) →
      target = .bvar index

theorem ConcreteBVarIdentity.nil : ConcreteBVarIdentity [] := by
  intro index target type h
  cases h

theorem ConcreteBVarIdentity.consLam
    (H : ConcreteBVarIdentity Delta) (domain : VExpr) :
    ConcreteBVarIdentity ((none, .vlam domain) :: Delta) := by
  intro index target type h
  cases index with
  | zero =>
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value] at h
      exact h.1.symm
  | succ index =>
      simp [VLCtx.find?, VLCtx.next] at h
      rcases h with ⟨source, sourceType, hsource, rfl, rfl⟩
      rw [H index source sourceType hsource]
      simp [VExpr.liftN, liftVar, VLocalDecl.depth, Nat.add_comm]

theorem concreteBVarIdentity_lambdaContext
    (domains : List VExpr) :
    ConcreteBVarIdentity
      (domains.map fun domain => (none, VLocalDecl.vlam domain)) := by
  induction domains with
  | nil => exact ConcreteBVarIdentity.nil
  | cons domain domains ih => exact ih.consLam domain

theorem ConcreteBVarIdentity.abstractForallContext
    (domains : List VExpr) :
    ConcreteBVarIdentity
      (_root_.Lean4Lean.VerifyInductive.abstractForallContext domains []) := by
  simpa [_root_.Lean4Lean.VerifyInductive.abstractForallContext] using
    _root_.Lean4Lean.VerifyInductive.concreteBVarIdentity_lambdaContext
      domains.reverse

/-- Concrete field-application shape.  The indices agree exactly with the
abstract `IsFieldApp` judgment. -/
def ConcreteIsFieldApp (fieldVars : List Nat) (depth : Nat)
    (expression : Expr) : Prop :=
  ∃ field ∈ fieldVars, ∃ args,
    expression.getAppFn = .bvar (field + depth) ∧
      expression.getAppArgsList = args

/-- Guarded recursive-call syntax before translation.  Let expressions and
free/metavariables are intentionally absent: restored rules are closed, and
the executable validator rejects those forms instead of assigning them an
unverifiable abstract meaning. -/
inductive ConcreteGuardedIota (recursors : List Name)
    (fieldVars : List Nat) : Nat → Expr → Prop
  | bvar : ConcreteGuardedIota recursors fieldVars depth (.bvar index)
  | sort : ConcreteGuardedIota recursors fieldVars depth (.sort level)
  | const (fresh : name ∉ recursors) :
      ConcreteGuardedIota recursors fieldVars depth (.const name levels)
  | app : ConcreteGuardedIota recursors fieldVars depth fn →
      ConcreteGuardedIota recursors fieldVars depth arg →
      ConcreteGuardedIota recursors fieldVars depth (.app fn arg)
  | lam : ConcreteGuardedIota recursors fieldVars depth domain →
      ConcreteGuardedIota recursors fieldVars (depth + 1) body →
      ConcreteGuardedIota recursors fieldVars depth
        (.lam name domain body binderInfo)
  | forallE : ConcreteGuardedIota recursors fieldVars depth domain →
      ConcreteGuardedIota recursors fieldVars (depth + 1) body →
      ConcreteGuardedIota recursors fieldVars depth
        (.forallE name domain body binderInfo)
  | lit : ConcreteGuardedIota recursors fieldVars depth literal.toConstructor →
      ConcreteGuardedIota recursors fieldVars depth (.lit literal)
  | mdata : ConcreteGuardedIota recursors fieldVars depth body →
      ConcreteGuardedIota recursors fieldVars depth (.mdata data body)
  | proj : ConcreteGuardedIota recursors fieldVars depth major →
      ConcreteGuardedIota recursors fieldVars depth
        (.proj structName index major)
  | recCall (recursor : Name) (levels : List Level)
      (init : List Expr) (major : Expr)
      (recursor_mem : recursor ∈ recursors)
      (arguments_guarded : ∀ argument ∈ init ++ [major],
        ConcreteGuardedIota recursors fieldVars depth argument)
      (major_is_field : ConcreteIsFieldApp fieldVars depth major) :
      ConcreteGuardedIota recursors fieldVars depth
        (Expr.mkAppList (.const recursor levels) (init ++ [major]))

/-- A de Bruijn-headed concrete application retains its head and ordered
argument spine under strict translation in an identity-bvar context. -/
theorem TrExprS.bvarAppSpine
    (Hidentity : ConcreteBVarIdentity Delta)
    (H : TrExprS env Us Delta expression target)
    (hhead : expression.getAppFn = .bvar index) :
    ∃ args,
      target.getAppFnArgs = (.bvar index, args) ∧
      List.Forall₂ (TrExprS env Us Delta) expression.getAppArgsList args := by
  induction expression generalizing target with
  | bvar _ =>
      cases H with
      | bvar hfind =>
        cases hhead
        have htarget := Hidentity _ _ _ hfind
        subst_vars
        exact ⟨[], rfl, .nil⟩
  | app fn arg ihFn _ =>
      cases H
      rename_i fnTarget _ _ argTarget _ _ Hfn Harg
      rcases ihFn Hfn hhead with ⟨args, hspine, Hargs⟩
      refine ⟨args ++ [argTarget], ?_, ?_⟩
      · simp [hspine]
      · simpa only [Expr.getAppArgsList_app] using
          Lean4Lean.VerifyInductive.checkPositivityStep.forall₂_append
            Hargs (.cons Harg .nil)
  | fvar _ => cases hhead
  | mvar _ => cases H
  | sort _ => cases hhead
  | const _ _ => cases hhead
  | lit _ => cases hhead
  | lam _ _ _ _ _ _ => cases hhead
  | forallE _ _ _ _ _ _ => cases hhead
  | letE _ _ _ _ _ _ _ _ => cases hhead
  | mdata _ _ _ => cases hhead
  | proj _ _ _ => cases hhead

/-- Checked strict translation sends a concrete field application to the
same abstract field application. -/
theorem ConcreteIsFieldApp.translate
    (Hidentity : ConcreteBVarIdentity Delta)
    (Hfield : ConcreteIsFieldApp fieldVars depth expression)
    (Htranslation : TrExprS env Us Delta expression target) :
    target.IsFieldApp fieldVars depth := by
  rcases Hfield with ⟨field, hfield, args, hhead, _hargs⟩
  rcases TrExprS.bvarAppSpine Hidentity Htranslation hhead with
    ⟨targetArgs, htarget, _⟩
  exact ⟨field, hfield, targetArgs, htarget⟩

/-- Soundness of concrete guardedness through strict translation. -/
theorem ConcreteGuardedIota.translate
    (Hguard : ConcreteGuardedIota recursors fieldVars depth expression)
    (Hidentity : ConcreteBVarIdentity Delta)
    (Htranslation : TrExprS env Us Delta expression target) :
    target.GuardedIota recursors fieldVars depth := by
  induction Hguard generalizing Delta target with
  | bvar =>
      cases Htranslation with
      | bvar hfind =>
        rw [Hidentity _ _ _ hfind]
        exact .bvar
  | sort => cases Htranslation; exact .sort
  | const fresh => cases Htranslation; exact .const fresh
  | app _ _ ihFn ihArg =>
      cases Htranslation
      exact .app (ihFn Hidentity (by assumption))
        (ihArg Hidentity (by assumption))
  | lam _ _ ihDomain ihBody =>
      cases Htranslation
      exact .lam (ihDomain Hidentity (by assumption))
        (ihBody (Hidentity.consLam _) (by assumption))
  | forallE _ _ ihDomain ihBody =>
      cases Htranslation
      exact .forallE (ihDomain Hidentity (by assumption))
        (ihBody (Hidentity.consLam _) (by assumption))
  | lit _ ih => cases Htranslation; exact ih Hidentity (by assumption)
  | mdata _ ih => cases Htranslation; exact ih Hidentity (by assumption)
  | proj _ ih =>
      cases Htranslation
      rename_i majorTarget projectionTarget _ Hprojection
      cases Hprojection
      exact .proj (ih Hidentity (by assumption))
  | @recCall callDepth recursor levels init major recursor_mem
      arguments_guarded major_is_field ihArguments =>
      have Hstrict := Htranslation
      rcases checkPositivityStep.TrExprS.mkAppList_inv Hstrict with
        ⟨headTarget, targetArgs, Hhead, Hargs, rfl⟩
      cases Hhead with
      | const _ hlevels _ =>
        rcases List.Forall₂.unsnoc Hargs with
          ⟨targetInit, targetMajor, rfl, Hinit, Hmajor⟩
        apply VExpr.GuardedIota.recCall recursor_mem
        · intro argument hargument
          rcases List.mem_append.mp hargument with hinit | hmajor
          · rcases Lean4Lean.List.Forall₂.forall_exists_r Hinit argument hinit with
              ⟨source, hsource, Hsource⟩
            exact ihArguments source (by simp [hsource]) Hidentity
              Hsource
          · simp only [List.mem_singleton] at hmajor
            subst argument
            exact ihArguments major (by simp) Hidentity Hmajor
        · exact major_is_field.translate Hidentity Hmajor

/-- Concrete analogue of `VExpr.GuardedRuleRhs`, separating the closed rule
telescope from the residual iota body. -/
inductive ConcreteGuardedRuleRhs (recursors : List Name)
    (fieldVars : List Nat) : Expr → Prop
  | body : ConcreteGuardedIota recursors fieldVars 0 expression →
      ConcreteGuardedRuleRhs recursors fieldVars expression
  | lam : ConcreteGuardedIota recursors [] 0 domain →
      ConcreteGuardedRuleRhs recursors fieldVars body →
      ConcreteGuardedRuleRhs recursors fieldVars
        (.lam name domain body binderInfo)

theorem ConcreteGuardedRuleRhs.translate
    (Hguard : ConcreteGuardedRuleRhs recursors fieldVars expression)
    (Hidentity : ConcreteBVarIdentity Delta)
    (Htranslation : TrExprS env Us Delta expression target) :
    target.GuardedRuleRhs recursors := by
  induction Hguard generalizing Delta target with
  | body Hbody =>
      exact .body fieldVars
        (Hbody.translate Hidentity Htranslation)
  | lam Hdomain Hbody ih =>
      cases Htranslation
      exact .lam
        (Hdomain.translate Hidentity (by assumption))
        (ih (Hidentity.consLam _) (by assumption))

/-- Soundness of the terminating executable guardedness predicate. -/
theorem validateRestoredRecursorRules.guardedIotaCheck_sound
    (hcheck : Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck
      recursors fieldVars fuel depth expression = true) :
    ConcreteGuardedIota recursors fieldVars depth expression := by
  induction fuel generalizing depth expression with
  | zero => simp [Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck] at hcheck
  | succ fuel ih =>
    cases expression with
    | bvar index => exact .bvar
    | sort level => exact .sort
    | const name levels =>
        simp only [Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck,
          Bool.not_eq_true] at hcheck
        exact .const (by simpa [List.contains_iff_mem] using hcheck)
    | app fn arg =>
        simp only [Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck]
          at hcheck
        split at hcheck
        next headName headLevels hhead =>
          split at hcheck
          next hmember =>
            split at hcheck
            next => simp at hcheck
            next major reversedInit hreverse =>
              have hboth :
                  (match major.getAppFn with
                    | .bvar index => fieldVars.any fun field =>
                        index == field + depth
                    | _ => false) = true ∧
                  (Expr.app fn arg).getAppArgs.toList.all
                    (Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck
                      recursors fieldVars fuel depth) = true := by
                simp only [Bool.and_eq_true] at hcheck
                exact hcheck
              have hfield := hboth.1
              have hall := hboth.2
              have hargsEq :
                  (Expr.app fn arg).getAppArgsList =
                    reversedInit.reverse ++ [major] := by
                have := congrArg List.reverse hreverse
                simpa [Expr.getAppArgs_toList] using this
              have hrecursor : headName ∈ recursors := by
                simpa [List.contains_iff_mem] using hmember
              have hfieldShape :
                  ConcreteIsFieldApp fieldVars depth major := by
                split at hfield
                next index hmajorHead =>
                  have hexists : ∃ field ∈ fieldVars,
                      index = field + depth := by
                    simpa [List.any_eq_true, beq_iff_eq] using hfield
                  rcases hexists with ⟨field, hfieldMem, hindex⟩
                  exact ⟨field, hfieldMem, major.getAppArgsList,
                    by simpa [hindex] using hmajorHead, rfl⟩
                next hnotBVar => simp at hfield
              rw [← Expr.mkAppList_getAppArgsList (Expr.app fn arg)]
              rw [hhead, hargsEq]
              apply ConcreteGuardedIota.recCall headName headLevels
                reversedInit.reverse major hrecursor
              · intro argument hargument
                apply ih
                have hargumentAll : argument ∈
                    (Expr.app fn arg).getAppArgs.toList := by
                  simpa [Expr.getAppArgs_toList, hargsEq] using hargument
                exact List.all_eq_true.mp hall argument hargumentAll
              · exact hfieldShape
          next hnotMember =>
            simp only [Bool.and_eq_true] at hcheck
            rcases hcheck with ⟨hfn, harg⟩
            exact .app (ih hfn) (ih harg)
        next hnotConst =>
          simp only [Bool.and_eq_true] at hcheck
          rcases hcheck with ⟨hfn, harg⟩
          exact .app (ih hfn) (ih harg)
    | lam name domain body binderInfo =>
        simp only [Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck,
          Bool.and_eq_true] at hcheck
        rcases hcheck with ⟨hdomain, hbody⟩
        exact .lam (ih hdomain) (ih hbody)
    | forallE name domain body binderInfo =>
        simp only [Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck,
          Bool.and_eq_true] at hcheck
        rcases hcheck with ⟨hdomain, hbody⟩
        exact .forallE (ih hdomain) (ih hbody)
    | lit literal => exact .lit (ih hcheck)
    | mdata data body => exact .mdata (ih hcheck)
    | proj structName index major => exact .proj (ih hcheck)
    | mvar id | fvar id =>
        simp [Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck] at hcheck
    | letE name type value body nondep =>
        simp [Lean4Lean.validateRestoredRecursorRules.guardedIotaCheck] at hcheck

theorem validateRestoredRecursorRules.guardedRuleCheck_sound
    (hcheck : Lean4Lean.validateRestoredRecursorRules.guardedRuleCheck
      recursors fieldVars fuel expression = true) :
    ConcreteGuardedRuleRhs recursors fieldVars expression := by
  induction fuel generalizing expression with
  | zero =>
      simp [Lean4Lean.validateRestoredRecursorRules.guardedRuleCheck] at hcheck
  | succ fuel ih =>
      cases expression <;>
        simp only [Lean4Lean.validateRestoredRecursorRules.guardedRuleCheck,
          Bool.and_eq_true] at hcheck
      case lam =>
        exact .lam
          (validateRestoredRecursorRules.guardedIotaCheck_sound hcheck.1)
          (ih hcheck.2)
      all_goals
        exact .body
          (validateRestoredRecursorRules.guardedIotaCheck_sound hcheck)

/-- When the caller retains the complete generated rule telescope, the
executable check exposes guardedness of its exact residual with the exact
producer-selected field list.  The non-lambda side condition says that the
retained telescope is maximal; generated recursor rules provide precisely
that fact. -/
theorem validateRestoredRecursorRules.guardedRuleCheck_residual_sound
    (hcheck : Lean4Lean.validateRestoredRecursorRules.guardedRuleCheck
      recursors fieldVars fuel expression = true)
    (Htelescope : Expr.LambdaTelescope expression arity residual)
    (hresidual : residual.isLambda = false) :
    ConcreteGuardedIota recursors fieldVars 0 residual := by
  induction Htelescope generalizing fuel with
  | nil =>
      have Hguard :=
        validateRestoredRecursorRules.guardedRuleCheck_sound hcheck
      cases Hguard with
      | body Hbody => exact Hbody
      | lam =>
          change true = false at hresidual
          contradiction
  | @cons body arity residual name domain binderInfo Htail ih =>
      cases fuel with
      | zero =>
          simp [Lean4Lean.validateRestoredRecursorRules.guardedRuleCheck] at hcheck
      | succ fuel =>
          simp only [Lean4Lean.validateRestoredRecursorRules.guardedRuleCheck,
            Bool.and_eq_true] at hcheck
          exact ih hcheck.2 hresidual

/-- Soundness of the exact executable lambda-arity check. -/
theorem validateRestoredRecursorRules.exactLambdaArity_sound
    (hcheck : Lean4Lean.validateRestoredRecursorRules.exactLambdaArity
      arity expression = true) :
    ∃ residual,
      Expr.LambdaTelescope expression arity residual ∧
      residual.isLambda = false := by
  induction arity generalizing expression with
  | zero =>
    cases expression <;>
      simp only [Lean4Lean.validateRestoredRecursorRules.exactLambdaArity,
        Bool.false_eq_true] at hcheck ⊢
        <;> exact ⟨_, .nil _, rfl⟩
  | succ arity ih =>
    cases expression <;>
      simp only [Lean4Lean.validateRestoredRecursorRules.exactLambdaArity,
        Bool.false_eq_true] at hcheck
    case lam name domain body binderInfo =>
      rcases ih hcheck with ⟨residual, Htel, hresidual⟩
      exact ⟨residual, .cons Htel, hresidual⟩

/-- A complete lambda telescope ending in a non-lambda computes back to its
retained arity. -/
theorem Expr.LambdaTelescope.getNumHeadLambdas_eq
    (H : Expr.LambdaTelescope expression arity residual)
    (hresidual : residual.getNumHeadLambdas = 0) :
    expression.getNumHeadLambdas = arity := by
  induction H with
  | nil => exact hresidual
  | cons H ih =>
    simp [Expr.getNumHeadLambdas, ih hresidual]

/-- A successful arity-indexed guard check retains both of its executable
components: exact telescope cardinality and exact-field guardedness. -/
theorem validateRestoredRecursorRules.of_checkGuardedWithFieldsAtArity
    (hcheck :
      Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFieldsAtArity
        recursors fieldVars arity expression = .ok ()) :
    Lean4Lean.validateRestoredRecursorRules.exactLambdaArity arity
        expression = true ∧
      Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFields
        recursors fieldVars expression = .ok () := by
  unfold Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFieldsAtArity
    at hcheck
  split at hcheck
  next hexact => exact ⟨hexact, hcheck⟩
  next => simp [bind, Except.bind] at hcheck

/-- Proof-side view of the executable primary-rule shape pass.  Every field
is a literal fact about the generated/restored rule pair selected by the
checker; no semantic restoration premise occurs here. -/
structure validateRestoredRecursorRules.PrimaryRuleShapeCertificate
    (recInfo : RecursorVal) (sourceRecursors : List Name)
    (sourceRule restoredRule : RecursorRule) where
  arity : Nat
  arity_eq : arity = recInfo.numParams + recInfo.numMotives +
    recInfo.numMinors + restoredRule.nfields
  source_arity : sourceRule.rhs.getNumHeadLambdas = arity
  residual : Expr
  telescope : Expr.LambdaTelescope restoredRule.rhs arity residual
  minorVar : Nat
  minor_head : residual.getAppFn = .bvar minorVar
  minor_in_scope : minorVar < arity
  field_prefix : residual.getAppArgs.toList.take restoredRule.nfields =
    (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
      restoredRule.nfields).map Expr.bvar
  recursive_in_range : ∀ field ∈
      Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
        sourceRecursors sourceRule.rhs,
    field < restoredRule.nfields
  positions_ordered :
    ((Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
      sourceRecursors sourceRule.rhs).map fun field =>
        restoredRule.nfields - 1 - field).Pairwise (· < ·)
  recursive_args_sublist :
    (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
      sourceRecursors sourceRule.rhs).Sublist
        (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
          restoredRule.nfields)
  recursive_results :
    (residual.getAppArgs.toList.drop restoredRule.nfields).length =
      (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
        sourceRecursors sourceRule.rhs).length

theorem validateRestoredRecursorRules.dropHeadLambdas_sound
    (H : Lean4Lean.validateRestoredRecursorRules.dropHeadLambdas arity
      expression = some residual) :
    Expr.LambdaTelescope expression arity residual := by
  induction arity generalizing expression with
  | zero =>
      simp only [Lean4Lean.validateRestoredRecursorRules.dropHeadLambdas,
        Option.some.injEq] at H
      subst residual
      exact .nil expression
  | succ arity ih =>
      cases expression with
      | lam name domain body binderInfo => exact .cons (ih H)
      | bvar | fvar | mvar | sort | const | app | letE | forallE | lit |
          mdata | proj =>
          simp [Lean4Lean.validateRestoredRecursorRules.dropHeadLambdas] at H

/-- Replacing the residual of a concrete rule preserves its literal lambda
prefix on both the source rule and the reconstructed equation LHS. -/
theorem validateRestoredRecursorRules.replaceEquationBody_sound
    (H : Lean4Lean.validateRestoredRecursorRules.replaceEquationBody ctorName
      arity expression body = .ok output) :
    ∃ residual,
      Expr.LambdaTelescope expression arity residual ∧
      Expr.LambdaTelescope output arity body ∧
      Expr.SameLambdaPrefix arity expression output := by
  induction arity generalizing expression output with
  | zero =>
      unfold Lean4Lean.validateRestoredRecursorRules.replaceEquationBody at H
      change (Except.ok body : Except Exception Expr) = .ok output at H
      cases H
      exact ⟨expression, .nil _, .nil _, .nil⟩
  | succ arity ih =>
      unfold Lean4Lean.validateRestoredRecursorRules.replaceEquationBody at H
      simp only [Nat.succ_ne_zero, ↓reduceIte] at H
      cases expression with
      | lam name domain inner binderInfo =>
          simp only [Nat.succ_sub_one] at H
          change
            Except.map
              (fun innerOutput : Expr =>
                Expr.lam name domain innerOutput binderInfo)
              (Lean4Lean.validateRestoredRecursorRules.replaceEquationBody
                ctorName arity inner body) = .ok output at H
          cases hrest :
              Lean4Lean.validateRestoredRecursorRules.replaceEquationBody
                ctorName arity inner body with
          | error error =>
              rw [hrest] at H
              change (Except.error error : Except Exception Expr) =
                .ok output at H
              contradiction
          | ok innerOutput =>
              rw [hrest] at H
              change Except.ok (.lam name domain innerOutput binderInfo) =
                .ok output at H
              cases H
              rcases ih hrest with ⟨residual, Hsource, Htarget, Hsame⟩
              exact ⟨residual, .cons Hsource, .cons Htarget, .cons Hsame⟩
      | bvar | fvar | mvar | sort | const | app | letE | forallE | lit |
          mdata | proj => simp at H

private theorem except_bind_success
    {first : Except error alpha} {next : alpha → Except error beta}
    (H : first >>= next = .ok value) :
    ∃ intermediate, first = .ok intermediate ∧
      next intermediate = .ok value := by
  cases hfirst : first with
  | error err => rw [hfirst] at H; contradiction
  | ok intermediate =>
      simp only [hfirst, bind, Except.bind] at H
      exact ⟨intermediate, rfl, H⟩

/-- A successful LHS reconstruction exposes the exact executable plan and
the final prefix-preserving body replacement. -/
theorem validateRestoredRecursorRules.buildEquationLhs_success
    (H : Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env recInfo
      rule = .ok lhs) :
    ∃ plan,
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhsPlan env recInfo
          rule = .ok plan ∧
      Lean4Lean.validateRestoredRecursorRules.replaceEquationBody rule.ctor
        (recInfo.numParams + recInfo.numMotives + recInfo.numMinors +
          rule.nfields)
        rule.rhs (plan.body recInfo rule) = .ok lhs := by
  unfold Lean4Lean.validateRestoredRecursorRules.buildEquationLhs at H
  exact except_bind_success H

/-- A successful canonical primary LHS reconstruction exposes the actual
inferred plan together with the source-facing parameter canonicalization and
the final prefix-preserving replacement. -/
theorem validateRestoredRecursorRules.buildPrimaryEquationLhs_success
    (H : Lean4Lean.validateRestoredRecursorRules.buildPrimaryEquationLhs env
      expectedCtorUvars expectedPrefix recInfo rule = .ok lhs) :
    ∃ plan canonicalPlan :
        Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan,
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhsPlan env recInfo
          rule = .ok plan ∧
      plan.indices.size = recInfo.numIndices ∧
      plan.ctorLevels.length = expectedCtorUvars ∧
      recInfo.numParams + recInfo.numMotives + recInfo.numMinors =
        expectedPrefix ∧
      let binderCount := recInfo.numParams + recInfo.numMotives +
        recInfo.numMinors + rule.nfields
      let binders := (List.range binderCount).toArray.map fun i =>
        Expr.bvar (binderCount - 1 - i)
      let params := binders.extract 0 recInfo.numParams
      canonicalPlan = { plan with ctorParams := params } ∧
        Lean4Lean.validateRestoredRecursorRules.replaceEquationBody rule.ctor
          binderCount rule.rhs (canonicalPlan.body recInfo rule) = .ok lhs := by
  unfold Lean4Lean.validateRestoredRecursorRules.buildPrimaryEquationLhs at H
  rcases except_bind_success H with ⟨plan, hplan, H⟩
  rcases except_bind_success H with ⟨unit, hindices, H⟩
  rcases unit with ⟨⟩
  rcases except_bind_success H with ⟨unit, huvars, hreplace⟩
  rcases unit with ⟨⟩
  rcases except_bind_success hreplace with ⟨unit, hprefix, hreplace⟩
  rcases unit with ⟨⟩
  have hindicesBool :
      (plan.indices.size == recInfo.numIndices) = true := by
    unfold Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleCondition at hindices
    split at hindices
    next h => exact h
    next => simp at hindices
  have huvarsBool :
      (plan.ctorLevels.length == expectedCtorUvars) = true := by
    unfold Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleCondition at huvars
    split at huvars
    next h => exact h
    next => simp at huvars
  have hprefixBool :
      (recInfo.numParams + recInfo.numMotives + recInfo.numMinors ==
        expectedPrefix) = true := by
    unfold Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleCondition at hprefix
    split at hprefix
    next h => exact h
    next => simp at hprefix
  exact ⟨plan, _, hplan,
    by simpa using hindicesBool,
    by simpa using huvarsBool,
    by simpa using hprefixBool,
    rfl, hreplace⟩

/-- Exact abstract application spine obtained by translating the canonical
primary LHS residual.  The common parameters and constructor fields are
identified with their canonical de Bruijn variables, so no translation
uniqueness principle for constants or projections is used. -/
structure validateRestoredRecursorRules.CanonicalPrimaryLhsSpine
    (recInfo : RecursorVal) (rule : RecursorRule)
    (plan : Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan)
    (domains : List VExpr) (lhsBody : VExpr) where
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern : lhsBody = VExpr.mkApps
    (.const recInfo.name recursorLevels)
    (leadingArgs ++
      [VExpr.mkApps (.const rule.ctor ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recInfo.levelParams.length
  ctor_levels : ctorLevels.length = plan.ctorLevels.length
  leading_arity : leadingArgs.length = recInfo.numParams +
    recInfo.numMotives + recInfo.numMinors + plan.indices.size
  constructor_arity : ctorArgs.length = recInfo.numParams + rule.nfields
  parameter_args : ctorArgs.take recInfo.numParams =
    leadingArgs.take recInfo.numParams
  field_args : ctorArgs.drop recInfo.numParams =
    (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
      rule.nfields).map VExpr.bvar

theorem validateRestoredRecursorRules.canonicalPrimaryLhsSpine_of_translation
    (hcanonical :
      let binderCount := recInfo.numParams + recInfo.numMotives +
        recInfo.numMinors + rule.nfields
      let binders := (List.range binderCount).toArray.map fun i =>
        Expr.bvar (binderCount - 1 - i)
      let params := binders.extract 0 recInfo.numParams
      canonicalPlan = { plan with ctorParams := params })
    (htranslation : TrExprS venv recInfo.levelParams
      (abstractForallContext domains [])
      (canonicalPlan.body recInfo rule) lhsBody)
    (hdomains : domains.length = recInfo.numParams + recInfo.numMotives +
      recInfo.numMinors + rule.nfields) :
    Nonempty (validateRestoredRecursorRules.CanonicalPrimaryLhsSpine recInfo
      rule plan domains lhsBody) := by
  let binderCount := recInfo.numParams + recInfo.numMotives +
    recInfo.numMinors + rule.nfields
  let binders := (List.range binderCount).toArray.map fun i =>
    Expr.bvar (binderCount - 1 - i)
  let params := binders.extract 0 recInfo.numParams
  let motives := binders.extract recInfo.numParams
    (recInfo.numParams + recInfo.numMotives)
  let minors := binders.extract
    (recInfo.numParams + recInfo.numMotives)
    (recInfo.numParams + recInfo.numMotives + recInfo.numMinors)
  let fields := binders.extract
    (recInfo.numParams + recInfo.numMotives + recInfo.numMinors)
    binderCount
  have hcanonical' : canonicalPlan = { plan with ctorParams := params } := by
    simpa only [binderCount, binders, params] using hcanonical
  subst canonicalPlan
  let ctorSource := mkAppN
    (mkAppN (.const rule.ctor plan.ctorLevels) params) fields
  have hrecursorHead :
      (({ plan with ctorParams := params } :
          Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan).body
        recInfo rule).getAppFn =
        .const recInfo.name (recInfo.levelParams.map Level.param) := by
    unfold Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan.body
    simp only [Expr.getAppFn_mkAppN, Expr.getAppFn]
  rcases checkPositivityStep.TrExprS.constAppSpine htranslation
      hrecursorHead with
    ⟨recursorLevels, translatedArgs, hrecursorSpine,
      hrecursorLevels, HtranslatedArgs⟩
  have HtranslatedArgs' : List.Forall₂
      (TrExprS venv recInfo.levelParams
        (abstractForallContext domains []))
      (params.toList ++ motives.toList ++ minors.toList ++
        plan.indices.toList ++ [ctorSource])
      translatedArgs := by
    unfold Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan.body at HtranslatedArgs
    simp only [Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
      List.nil_append, Array.toList_push, Array.toList_append,
      List.append_assoc] at HtranslatedArgs
    simpa only [binderCount, binders, params, motives, minors, fields,
      ctorSource, List.append_assoc] using HtranslatedArgs
  rcases checkPositivityStep.List.Forall₂.split_left HtranslatedArgs' with
    ⟨leadingArgs, majorTail, rfl, Hleading, HmajorTail⟩
  have hmajor : ∃ majorTarget, majorTail = [majorTarget] ∧
      TrExprS venv recInfo.levelParams
        (abstractForallContext domains []) ctorSource majorTarget := by
    cases HmajorTail with
    | cons Hctor Hnil =>
      cases Hnil
      exact ⟨_, rfl, Hctor⟩
  next =>
    rcases hmajor with ⟨majorTarget, rfl, Hctor⟩
    have hctorHead : ctorSource.getAppFn =
        .const rule.ctor plan.ctorLevels := by
      simp only [ctorSource, Expr.getAppFn_mkAppN, Expr.getAppFn]
    rcases checkPositivityStep.TrExprS.constAppSpine Hctor hctorHead with
      ⟨ctorLevels, ctorArgs, hctorSpine, hctorLevels, HctorArgs⟩
    have HctorArgs' : List.Forall₂
        (TrExprS venv recInfo.levelParams
          (abstractForallContext domains []))
        (params.toList ++ fields.toList) ctorArgs := by
      simp only [ctorSource, Expr.getAppArgsList_mkAppN,
        Expr.getAppArgsList_const, List.nil_append, Array.toList_append,
        List.append_assoc] at HctorArgs
      exact HctorArgs
    have hlhsRebuild := VExpr.mkApps_getAppFnArgs lhsBody
    rw [hrecursorSpine] at hlhsRebuild
    have hsourceParamLength : params.size = recInfo.numParams := by
      simp only [params, Array.size_extract, binders, Array.size_map,
        List.size_toArray, List.length_range, binderCount]
      omega
    have hsourceMotiveLength : motives.size = recInfo.numMotives := by
      simp [motives, binders, binderCount]
      omega
    have hsourceMinorLength : minors.size = recInfo.numMinors := by
      simp [minors, binders, binderCount]
      omega
    have hsourceFieldLength : fields.size = rule.nfields := by
      simp only [fields, Array.size_extract, binders, Array.size_map,
        List.size_toArray, List.length_range, binderCount]
      omega
    have Hleading' : List.Forall₂
        (TrExprS venv recInfo.levelParams
          (abstractForallContext domains []))
        (params.toList ++ (motives.toList ++ minors.toList ++
          plan.indices.toList))
        leadingArgs := by
      simpa only [List.append_assoc] using Hleading
    rcases checkPositivityStep.List.Forall₂.split_left Hleading' with
      ⟨leadingParams, leadingRest, hleadingSplit, HleadingParams,
        _HleadingRest⟩
    rcases checkPositivityStep.List.Forall₂.split_left HctorArgs' with
      ⟨ctorParams, ctorFields, hctorSplit, HctorParams, HctorFields⟩
    have hparamTargets : leadingParams = ctorParams :=
      Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
        HleadingParams HctorParams (by
          intro expression hexpression
          rcases List.mem_iff_getElem.mp hexpression with ⟨i, hi, rfl⟩
          simp [params, binders, binderCount] at hi ⊢
          trivial)
    have HcanonicalFields : List.Forall₂
        (TrExprS venv recInfo.levelParams
          (abstractForallContext domains []))
        fields.toList
        ((Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
          rule.nfields).map VExpr.bvar) := by
      have Hcanonical := TrExprS.canonicalBvars_of_abstractForallContext
        (env := venv) (Us := recInfo.levelParams) domains [] rule.nfields
        (by rw [hdomains]; omega)
      have hfieldsConcrete : fields.toList =
          List.ofFn (fun i : Fin rule.nfields =>
            Expr.bvar (rule.nfields - 1 - i)) := by
        apply List.ext_getElem
        · simp only [Array.length_toList, hsourceFieldLength,
            List.length_ofFn]
        · intro i hiLeft hiRight
          simp only [Array.getElem_toList, List.getElem_ofFn]
          simp [fields, binders, binderCount]
          omega
      rw [hfieldsConcrete]
      simpa only [
        Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars,
        List.map_ofFn, Function.comp_def] using Hcanonical
    have hfieldTargets : ctorFields =
        (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
          rule.nfields).map VExpr.bvar :=
      Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
        HctorFields HcanonicalFields (by
          intro expression hexpression
          rcases List.mem_iff_getElem.mp hexpression with ⟨i, hi, rfl⟩
          simp [fields, binders, binderCount] at hi ⊢
          trivial)
    have hrecursorLength := checkPositivityStep.List.mapM_some_length
      hrecursorLevels
    have hctorLength := checkPositivityStep.List.mapM_some_length hctorLevels
    refine ⟨{
      recursorLevels := recursorLevels
      leadingArgs := leadingParams ++ leadingRest
      ctorLevels := ctorLevels
      ctorArgs := ctorParams ++ ctorFields
      lhs_pattern := ?_
      recursor_levels := by simpa using hrecursorLength.symm
      ctor_levels := by simpa using hctorLength.symm
      leading_arity := ?_
      constructor_arity := ?_
      parameter_args := ?_
      field_args := ?_ }⟩
    · rw [← hleadingSplit, ← hctorSplit]
      have hmajorRebuild' := VExpr.mkApps_getAppFnArgs majorTarget
      rw [hctorSpine] at hmajorRebuild'
      rw [hmajorRebuild']
      exact hlhsRebuild.symm
    · have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
        Hleading
      rw [hleadingSplit] at hlen
      simp only [List.length_append, Array.length_toList] at hlen ⊢
      rw [hsourceParamLength, hsourceMotiveLength, hsourceMinorLength] at hlen
      omega
    · have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
        HctorArgs'
      rw [hctorSplit] at hlen
      simp only [List.length_append, Array.length_toList] at hlen ⊢
      rw [hsourceParamLength, hsourceFieldLength] at hlen
      omega
    · rw [hparamTargets]
      have hleadingParamsLength : leadingParams.length = recInfo.numParams := by
        have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
          HleadingParams
        simpa [hsourceParamLength] using hlen.symm
      have hctorParamsLength : ctorParams.length = recInfo.numParams := by
        rw [← hparamTargets]
        exact hleadingParamsLength
      simp [hleadingParamsLength, hctorParamsLength]
    · rw [hfieldTargets]
      have hctorParamsLength : ctorParams.length = recInfo.numParams := by
        have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
          HctorParams
        simpa [hsourceParamLength] using hlen.symm
      simp [hctorParamsLength]

theorem validateRestoredRecursorRules.dropHeadForalls_sound
    (H : Lean4Lean.validateRestoredRecursorRules.dropHeadForalls arity
      expression = some residual) :
    Expr.ForallTelescope expression arity residual := by
  induction arity generalizing expression with
  | zero =>
      cases expression <;>
        simp [Lean4Lean.validateRestoredRecursorRules.dropHeadForalls] at H <;>
        subst residual <;> exact Expr.ForallTelescope.nil _
  | succ arity ih =>
      cases expression with
      | forallE name domain body binderInfo => exact .cons (ih H)
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata |
          proj =>
          simp [Lean4Lean.validateRestoredRecursorRules.dropHeadForalls] at H

theorem validateRestoredRecursorRules.shiftEquationBody_eq
    (expression : Expr) (cutoff amount : Nat) :
    Lean4Lean.validateRestoredRecursorRules.shiftEquationBody expression
      cutoff amount = expression.liftLooseBVars' cutoff amount := by
  induction expression generalizing cutoff <;>
    simp [Lean4Lean.validateRestoredRecursorRules.shiftEquationBody,
      Expr.liftLooseBVars', *]

theorem validateRestoredRecursorRules.instantiate_shiftEquationBody
    (expression substitution : Expr) (cutoff : Nat := 0) :
    (Lean4Lean.validateRestoredRecursorRules.shiftEquationBody expression
      cutoff 1).instantiate1' substitution cutoff = expression := by
  rw [validateRestoredRecursorRules.shiftEquationBody_eq]
  exact Expr.instantiate1'_liftLooseBVars_0 expression substitution

theorem validateRestoredRecursorRules.instantiate_shiftEquationBody_succ
    (expression substitution : Expr) (amount : Nat) (cutoff : Nat := 0) :
    (Lean4Lean.validateRestoredRecursorRules.shiftEquationBody expression
      cutoff (amount + 1)).instantiate1' substitution cutoff =
        Lean4Lean.validateRestoredRecursorRules.shiftEquationBody expression
          cutoff amount := by
  rw [validateRestoredRecursorRules.shiftEquationBody_eq,
    validateRestoredRecursorRules.shiftEquationBody_eq]
  induction expression generalizing cutoff with
  | bvar index =>
      by_cases hindex : index < cutoff
      · simp [Expr.liftLooseBVars', Expr.instantiate1', hindex]
      · have hgt : cutoff < index + (amount + 1) := by omega
        simp [Expr.liftLooseBVars', Expr.instantiate1', hindex, hgt,
          Nat.ne_of_gt hgt]
        omega
  | _ => simp [Expr.liftLooseBVars', Expr.instantiate1', *]

/-- Successful construction of the shared witness exposes the exact source
telescope and its residual chain of checking lets. -/
theorem validateRestoredRecursorRules.buildEquationSharedWitness_success
    (H : Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness
      recInfo rule lhs lhsType equationLevel = .ok shared) :
    let arity := recInfo.numParams + recInfo.numMotives +
      recInfo.numMinors + rule.nfields
    ∃ lhsBody rhsBody bodyType,
      Expr.LambdaTelescope lhs arity lhsBody ∧
      Expr.LambdaTelescope rule.rhs arity rhsBody ∧
      Expr.ForallTelescope lhsType arity bodyType ∧
      Expr.LambdaTelescope shared arity
        (.letE `_equationType (.sort equationLevel) bodyType
          (.letE `_equationLhs (.bvar 0)
            (Lean4Lean.validateRestoredRecursorRules.shiftEquationBody
              lhsBody 0 1)
            (.letE `_equationRhs (.bvar 1)
              (Lean4Lean.validateRestoredRecursorRules.shiftEquationBody
                rhsBody 0 2) (.bvar 0) false)
            false)
          false) ∧
      Expr.SameLambdaPrefix arity rule.rhs shared := by
  dsimp only
  unfold Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness at H
  cases hlhs : Lean4Lean.validateRestoredRecursorRules.dropHeadLambdas
      (recInfo.numParams + recInfo.numMotives + recInfo.numMinors +
        rule.nfields) lhs with
  | none => simp [hlhs] at H
  | some lhsBody =>
    simp only [hlhs] at H
    cases hrhs : Lean4Lean.validateRestoredRecursorRules.dropHeadLambdas
        (recInfo.numParams + recInfo.numMotives + recInfo.numMinors +
          rule.nfields) rule.rhs with
    | none => simp [hrhs] at H
    | some rhsBody =>
      simp only [hrhs] at H
      cases htype : Lean4Lean.validateRestoredRecursorRules.dropHeadForalls
          (recInfo.numParams + recInfo.numMotives + recInfo.numMinors +
            rule.nfields) lhsType with
      | none => simp [htype] at H
      | some bodyType =>
        simp only [htype] at H
        rcases validateRestoredRecursorRules.replaceEquationBody_sound H with
          ⟨_residual, _Hsource, Hshared, Hsame⟩
        exact ⟨lhsBody, rhsBody, bodyType,
          validateRestoredRecursorRules.dropHeadLambdas_sound hlhs,
          validateRestoredRecursorRules.dropHeadLambdas_sound hrhs,
          validateRestoredRecursorRules.dropHeadForalls_sound htype,
          Hshared, Hsame⟩

theorem TrExprS.vletBVarZero_eq
    (H : TrExprS env Us ((none, .vlet type value) :: Delta)
      (.bvar 0) target) : target = value := by
  cases H with
  | bvar hfind =>
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value,
        VLocalDecl.type, VLocalDecl.depth] at hfind
      exact hfind.1.symm

theorem TrExprS.vletBVarOne_eq
    (H : TrExprS env Us
      ((none, .vlet innerType innerValue) ::
        (none, .vlet outerType outerValue) :: Delta)
      (.bvar 1) target) : target = outerValue := by
  cases H with
  | bvar hfind =>
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value,
        VLocalDecl.type, VLocalDecl.depth] at hfind
      exact hfind.1.symm

theorem validateRestoredRecursorRules.checkPrimaryRuleCondition_sound
    (H : Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleCondition
      condition message = .ok ()) : condition = true := by
  unfold Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleCondition at H
  split at H
  next h => exact h
  next => simp at H

theorem validateRestoredRecursorRules.primaryRuleMinorVar?_sound
    (H : Lean4Lean.validateRestoredRecursorRules.primaryRuleMinorVar?
      expression = some index) : expression.getAppFn = .bvar index := by
  unfold Lean4Lean.validateRestoredRecursorRules.primaryRuleMinorVar? at H
  cases hfn : expression.getAppFn <;> simp [hfn] at H
  rename_i actual
  simpa [H] using hfn

private theorem Expr.eqv_bvar_right_eq
    (H : ((expression == (.bvar index : Expr))) = true) :
    expression = .bvar index := by
  cases expression <;> simp [(· == ·), Expr.eqv'] at H
  rename_i actual
  subst actual
  rfl

private theorem List.exprBeq_bvars_eq
    {expressions : List Expr} {fields : List Nat}
    (H : (expressions == fields.map Expr.bvar) = true) :
    expressions = fields.map Expr.bvar := by
  induction fields generalizing expressions with
  | nil =>
      cases expressions <;> simp only [List.map_nil, BEq.beq, List.beq,
        Bool.false_eq_true] at H ⊢
  | cons field fields ih =>
      cases expressions with
      | nil => simp at H
      | cons expression expressions =>
          simp only [List.map_cons, BEq.beq, List.beq,
            Bool.and_eq_true] at H
          rw [Expr.eqv_bvar_right_eq H.1, ih H.2]
          rfl

set_option maxRecDepth 100000 in
/-- Soundness of the executable primary-rule shape pass. -/
theorem validateRestoredRecursorRules.primaryRuleShape_of_check
    (H : Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleShape
      recInfo sourceRecursors sourceRule restoredRule = .ok ()) :
    Nonempty (validateRestoredRecursorRules.PrimaryRuleShapeCertificate
      recInfo sourceRecursors sourceRule restoredRule) := by
  unfold Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleShape at H
  dsimp only at H
  rcases except_bind_success H with ⟨arityUnit, harityCheck, H⟩
  rcases arityUnit with ⟨⟩
  have hsourceArity :=
    validateRestoredRecursorRules.checkPrimaryRuleCondition_sound harityCheck
  cases hdrop : Lean4Lean.validateRestoredRecursorRules.dropHeadLambdas
      (recInfo.numParams + recInfo.numMotives + recInfo.numMinors +
        restoredRule.nfields) restoredRule.rhs with
  | none => simp [hdrop] at H
  | some residual =>
    simp only [hdrop] at H
    cases hminor :
        Lean4Lean.validateRestoredRecursorRules.primaryRuleMinorVar?
          residual with
    | none => simp [hminor] at H
    | some minorVar =>
      simp only [hminor] at H
      rcases except_bind_success H with
        ⟨minorUnit, hminorCheck, H⟩
      rcases minorUnit with ⟨⟩
      rcases except_bind_success H with
        ⟨fieldUnit, hfieldCheck, H⟩
      rcases fieldUnit with ⟨⟩
      rcases except_bind_success H with
        ⟨rangeUnit, hrangeCheck, H⟩
      rcases rangeUnit with ⟨⟩
      rcases except_bind_success H with
        ⟨positionsUnit, hpositionsCheck, H⟩
      rcases positionsUnit with ⟨⟩
      rcases except_bind_success H with
        ⟨sublistUnit, hsublistCheck, hresultsCheck⟩
      rcases sublistUnit with ⟨⟩
      have hminorScope :=
        validateRestoredRecursorRules.checkPrimaryRuleCondition_sound
          hminorCheck
      have hfieldPrefix :=
        validateRestoredRecursorRules.checkPrimaryRuleCondition_sound
          hfieldCheck
      have hrecursiveRange :=
        validateRestoredRecursorRules.checkPrimaryRuleCondition_sound
          hrangeCheck
      have hpositions :=
        validateRestoredRecursorRules.checkPrimaryRuleCondition_sound
          hpositionsCheck
      have hresults :=
        validateRestoredRecursorRules.checkPrimaryRuleCondition_sound
          hresultsCheck
      have hsublist :=
        validateRestoredRecursorRules.checkPrimaryRuleCondition_sound
          hsublistCheck
      refine ⟨{
        arity := recInfo.numParams + recInfo.numMotives + recInfo.numMinors +
          restoredRule.nfields
        arity_eq := rfl
        source_arity := by simpa using hsourceArity
        residual := residual
        telescope := validateRestoredRecursorRules.dropHeadLambdas_sound hdrop
        minorVar := minorVar
        minor_head :=
          validateRestoredRecursorRules.primaryRuleMinorVar?_sound hminor
        minor_in_scope := by simpa using hminorScope
        field_prefix := List.exprBeq_bvars_eq hfieldPrefix
        recursive_in_range := by simpa using hrecursiveRange
        positions_ordered := by simpa using hpositions
        recursive_args_sublist := by
          exact List.isSublist_iff_sublist.mp (by simpa using hsublist)
        recursive_results := by simpa using hresults }⟩

/-- Abstract RHS spine forced by the executable primary-rule shape check and
the strict translation of its exact residual. -/
structure validateRestoredRecursorRules.CanonicalPrimaryRhsSpine
    (shape : validateRestoredRecursorRules.PrimaryRuleShapeCertificate
      recInfo sourceRecursors sourceRule restoredRule)
    (domains : List VExpr) (rhsBody : VExpr) where
  rhsArgs : List VExpr
  rhs_spine : rhsBody.getAppFnArgs = (.bvar shape.minorVar, rhsArgs)
  field_args : rhsArgs.take restoredRule.nfields =
    (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
      restoredRule.nfields).map VExpr.bvar
  recursive_results : (rhsArgs.drop restoredRule.nfields).length =
    (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
      sourceRecursors sourceRule.rhs).length

/-- Translate the literal minor-headed RHS shape selected by the primary
checker.  Only canonical bound variables are compared, so this theorem needs
no general translation-uniqueness or projection-preservation premise. -/
theorem validateRestoredRecursorRules.canonicalPrimaryRhsSpine_of_translation
    (shape : validateRestoredRecursorRules.PrimaryRuleShapeCertificate
      recInfo sourceRecursors sourceRule restoredRule)
    (htranslation : TrExprS venv recInfo.levelParams
      (abstractForallContext domains []) shape.residual rhsBody)
    (hdomains : domains.length = shape.arity) :
    Nonempty (validateRestoredRecursorRules.CanonicalPrimaryRhsSpine shape
      domains rhsBody) := by
  rcases TrExprS.bvarAppSpine
      (ConcreteBVarIdentity.abstractForallContext domains) htranslation
      shape.minor_head with ⟨rhsArgs, hrhsSpine, Hargs⟩
  let sourceFields :=
    (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
      restoredRule.nfields).map Expr.bvar
  have hsourceSplit : shape.residual.getAppArgsList =
      sourceFields ++ shape.residual.getAppArgsList.drop restoredRule.nfields := by
    have hsplit := List.take_append_drop restoredRule.nfields
      shape.residual.getAppArgsList
    have hprefix : shape.residual.getAppArgsList.take restoredRule.nfields =
        sourceFields := by
      simpa only [sourceFields, Expr.getAppArgs_toList] using shape.field_prefix
    rw [hprefix] at hsplit
    exact hsplit.symm
  have Hargs' : List.Forall₂
      (TrExprS venv recInfo.levelParams (abstractForallContext domains []))
      (sourceFields ++ shape.residual.getAppArgsList.drop restoredRule.nfields)
      rhsArgs := by
    rw [← hsourceSplit]
    exact Hargs
  rcases checkPositivityStep.List.Forall₂.split_left Hargs' with
    ⟨rhsFields, rhsResults, hrhsArgs, Hfields, Hresults⟩
  have HcanonicalFields : List.Forall₂
      (TrExprS venv recInfo.levelParams (abstractForallContext domains []))
      sourceFields
      ((Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
        restoredRule.nfields).map VExpr.bvar) := by
    have Hcanonical := TrExprS.canonicalBvars_of_abstractForallContext
      (env := venv) (Us := recInfo.levelParams) domains [] restoredRule.nfields
      (by rw [hdomains, shape.arity_eq]; omega)
    simpa only [sourceFields,
      Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars,
      List.map_ofFn, Function.comp_def] using Hcanonical
  have hfields : rhsFields =
      (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
        restoredRule.nfields).map VExpr.bvar :=
    Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
      Hfields HcanonicalFields (by
        intro expression hexpression
        rcases List.mem_iff_getElem.mp hexpression with ⟨i, hi, rfl⟩
        simp [sourceFields,
          Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars] at hi ⊢
        trivial)
  have hfieldLength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
    Hfields
  have hresultLength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
    Hresults
  refine ⟨{
    rhsArgs := rhsFields ++ rhsResults
    rhs_spine := by rw [← hrhsArgs]; exact hrhsSpine
    field_args := ?_
    recursive_results := ?_ }⟩
  · rw [hfields]
    simp [Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars]
  · have hfieldsLength : rhsFields.length = restoredRule.nfields := by
      simpa [sourceFields,
        Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars]
        using hfieldLength.symm
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append]
    exact hresultLength.symm.trans (by
      simpa only [Expr.getAppArgs_toList] using shape.recursive_results)

/-- Assemble the declarative nested iota rule from the two checker-derived
canonical spines and the recursor/constructor metadata selected by the actual
restoration trace. -/
def validateRestoredRecursorRules.nestedIotaRule_of_canonicalSpines
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {abstractRule : VDefEq}
    (recursor : VConstVal)
    (hrecursorMem : recursor ∈ block.recursors)
    (hrecursorShape : decl.NestedRecursorShape owner recursor)
    (hrecursorName : recursor.name = recInfo.name)
    (hrecursorUvars : recursor.uvars = recInfo.levelParams.length)
    (hnparams : decl.nparams = recInfo.numParams)
    (hprefixCount : decl.nparams + hrecursorShape.motives.length +
      hrecursorShape.minors.length =
        recInfo.numParams + recInfo.numMotives + recInfo.numMinors)
    (hindices : owner.numIndices = plan.indices.size)
    (hdeclUvars : decl.uvars = plan.ctorLevels.length)
    (hctorName : ctor.name = restoredRule.ctor)
    (hdomains : domains.length = recInfo.numParams + recInfo.numMotives +
      recInfo.numMinors + restoredRule.nfields)
    (hlhsWrapped : abstractRule.lhs = VExpr.wrapLams domains lhsBody)
    (hrhsWrapped : abstractRule.rhs = VExpr.wrapLams domains rhsBody)
    (htypeWrapped : abstractRule.type = VExpr.wrapForalls domains typeBody)
    (hruleUvars : abstractRule.uvars = recInfo.levelParams.length)
    (Hlhs : validateRestoredRecursorRules.CanonicalPrimaryLhsSpine recInfo
      restoredRule plan domains lhsBody)
    (shape : validateRestoredRecursorRules.PrimaryRuleShapeCertificate recInfo
      sourceRecursors sourceRule restoredRule)
    (Hrhs : validateRestoredRecursorRules.CanonicalPrimaryRhsSpine shape
      domains rhsBody)
    (Hguard : rhsBody.GuardedIota (block.recursors.map (·.name))
      (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
        sourceRecursors sourceRule.rhs) 0) :
    decl.NestedIotaRule block owner ctor abstractRule := by
  let recursiveVars :=
    Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
      sourceRecursors sourceRule.rhs
  let recursiveFields : List VInductDecl.NestedIotaField :=
    recursiveVars.map fun field => {
      fieldIndex := restoredRule.nfields - 1 - field
      arg := .bvar field }
  let recursiveArgs := recursiveVars.map VExpr.bvar
  have hctorFields : Hlhs.ctorArgs.drop decl.nparams =
      (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars
        restoredRule.nfields).map VExpr.bvar := by
    simpa only [hnparams] using Hlhs.field_args
  have hfieldCount : Hlhs.ctorArgs.length - decl.nparams =
      restoredRule.nfields := by
    rw [Hlhs.constructor_arity, hnparams]
    simp
  refine {
    recursor := recursor
    recursor_mem := hrecursorMem
    recursor_shape := hrecursorShape
    rule_uvars := hruleUvars.trans hrecursorUvars.symm
    domains := domains
    lhsBody := lhsBody
    rhsBody := rhsBody
    typeBody := typeBody
    lhs_wrapped := hlhsWrapped
    rhs_wrapped := hrhsWrapped
    type_wrapped := htypeWrapped
    recursorLevels := Hlhs.recursorLevels
    leadingArgs := Hlhs.leadingArgs
    ctorLevels := Hlhs.ctorLevels
    ctorArgs := Hlhs.ctorArgs
    lhs_pattern := by simpa [hrecursorName, hctorName] using Hlhs.lhs_pattern
    recursor_levels := Hlhs.recursor_levels.trans hrecursorUvars.symm
    ctor_levels := Hlhs.ctor_levels.trans hdeclUvars.symm
    leading_arity := by
      rw [Hlhs.leading_arity, hprefixCount, hindices]
    constructor_arity := by
      rw [Hlhs.constructor_arity, hnparams]
      omega
    parameter_args := by simpa only [hnparams] using Hlhs.parameter_args
    domains_arity := by
      rw [hdomains, hfieldCount, hprefixCount]
    recursiveFields := recursiveFields
    fieldPositions := recursiveVars.map fun field =>
      restoredRule.nfields - 1 - field
    fieldPositions_eq := by simp [recursiveFields]
    fieldPositions_ordered := by simpa [recursiveVars] using
      shape.positions_ordered
    fields_at_positions := ?_
    recursiveArgs := recursiveArgs
    recursiveArgs_eq := by simp [recursiveArgs, recursiveFields]
    recursive_args := ?_
    fieldVars := recursiveVars
    fieldVars_eq := by
      dsimp only [recursiveArgs]
      induction recursiveVars with
      | nil => rfl
      | cons field rest ih =>
          simp only [List.map_cons, List.filterMap_cons]
          change field :: rest =
            field :: (rest.map VExpr.bvar).filterMap VExpr.bvarHead?
          exact congrArg (List.cons field) ih
    fields_in_scope := ?_
    minorVar := shape.minorVar
    minor_in_scope := by
      rw [hdomains, ← shape.arity_eq]
      exact shape.minor_in_scope
    rhsArgs := Hrhs.rhsArgs
    rhs_spine := Hrhs.rhs_spine
    field_args := by rw [hfieldCount, hctorFields]; exact Hrhs.field_args
    recursive_results := by
      rw [hfieldCount, Hrhs.recursive_results]
      simp [recursiveArgs, recursiveVars]
    rhs_guarded := Hguard }
  · intro nestedField hnestedField
    rcases List.mem_map.mp hnestedField with ⟨field, hfield, rfl⟩
    have hfieldRange : field < restoredRule.nfields :=
      shape.recursive_in_range field (by simpa [recursiveVars] using hfield)
    have hposition : restoredRule.nfields - 1 - field <
        restoredRule.nfields := by omega
    rw [hctorFields]
    refine ⟨by simpa [
      Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars] using
        hposition, ?_⟩
    simp [Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars,
      hposition]
    congr 1
    omega
  · rw [hctorFields]
    exact shape.recursive_args_sublist.map VExpr.bvar
  · intro field hfield
    have hfieldRange : field < restoredRule.nfields :=
      shape.recursive_in_range field (by simpa [recursiveVars] using hfield)
    rw [hdomains]
    omega

/-- Soundness of the explicit-field checker at the residual selected by an
exact lambda telescope.  This is the primary nested-equation bridge: unlike
`GuardedRuleRhs`, its conclusion does not existentially forget `fieldVars`.
-/
theorem validateRestoredRecursorRules.guardedResidual_of_checkGuardedWithFields
    (hcheck : Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFields
      recursors fieldVars expression = .ok ())
    (Htelescope : Expr.LambdaTelescope expression arity residual)
    (hresidual : residual.isLambda = false)
    (hdomains : domains.length = arity)
    (Htranslation : TrExprS env Us [] expression
      (VExpr.wrapLams domains targetBody)) :
    targetBody.GuardedIota recursors fieldVars 0 := by
  unfold Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFields at hcheck
  split at hcheck
  next hguarded =>
    have Hconcrete :=
      validateRestoredRecursorRules.guardedRuleCheck_residual_sound hguarded
        Htelescope hresidual
    have Hresidual := TrExprS.lambdaTelescope_exact_residual Htelescope
      hdomains Htranslation
    exact Hconcrete.translate
      (ConcreteBVarIdentity.abstractForallContext domains)
      Hresidual
  next => simp at hcheck

/-- End-to-end soundness of the executable guard pass for a closed strict
translation. -/
theorem validateRestoredRecursorRules.guarded_of_checkGuarded
    (hcheck : Lean4Lean.validateRestoredRecursorRules.checkGuarded recursors
      expression = .ok ())
    (Htranslation : TrExprS env Us [] expression target) :
    target.GuardedRuleRhs recursors := by
  unfold Lean4Lean.validateRestoredRecursorRules.checkGuarded
    Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFields at hcheck
  split at hcheck
  next hguarded =>
    exact (validateRestoredRecursorRules.guardedRuleCheck_sound hguarded).translate
      ConcreteBVarIdentity.nil Htranslation
  next => simp at hcheck

end VerifyInductive
end Lean4Lean
