import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.VDecl

namespace Lean4Lean

/-- The semantic output of compiling an inductive declaration. The staging is
significant: all inductive headers are available while checking constructors,
and all recursors are available while checking their reduction equations. -/
structure VInductBlock where
  types : List VConstVal
  ctors : List VConstVal
  recursors : List VConstVal
  rules : List VDefEq

namespace VEnv

/-- Add a list of constants from left to right, failing on the first name
collision. -/
def addConstVals : VEnv → List VConstVal → Option VEnv
  | env, [] => some env
  | env, ci :: cis => do
    let env ← env.addConst ci.name ci.toVConstant
    env.addConstVals cis

theorem addConstVal_mono
    {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂)
    (h₁ : env₁.addConst name ci = some env₁')
    (h₂ : env₂.addConst name ci = some env₂') :
    env₁' ≤ env₂' := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  constructor
  · intro n a ha
    simp at ha ⊢
    split at ha <;> split <;> simp_all
    exact H.constants ha
  · exact H.defeqs

theorem addConstVals_mono
    {env₁ env₂ env₁' env₂' : VEnv} {cis : List VConstVal}
    (H : env₁ ≤ env₂)
    (h₁ : env₁.addConstVals cis = some env₁')
    (h₂ : env₂.addConstVals cis = some env₂') :
    env₁' ≤ env₂' := by
  induction cis generalizing env₁ env₂ env₁' env₂' with
  | nil =>
    simp [VEnv.addConstVals] at h₁ h₂
    subst env₁'
    subst env₂'
    exact H
  | cons ci cis ih =>
    simp only [VEnv.addConstVals] at h₁ h₂
    cases hhead₁ : env₁.addConst ci.name ci.toVConstant with
    | none => simp [hhead₁] at h₁
    | some middle₁ =>
      cases hhead₂ : env₂.addConst ci.name ci.toVConstant with
      | none => simp [hhead₂] at h₂
      | some middle₂ =>
        simp [hhead₁] at h₁
        simp [hhead₂] at h₂
        exact ih (addConstVal_mono H hhead₁ hhead₂) h₁ h₂

/-- Reduction equations do not introduce names and therefore cannot fail. -/
def addDefEqRules : VEnv → List VDefEq → VEnv
  | env, [] => env
  | env, df :: dfs => addDefEqRules (env.addDefEq df) dfs

end VEnv

def VInductDecl.typeConstants (decl : VInductDecl) : List VConstVal :=
  decl.types.map VInductiveType.toVConstVal

def VInductDecl.constructorConstants (decl : VInductDecl) : List VConstVal :=
  decl.types.flatMap VInductiveType.ctors

def VInductDecl.sourceNames (decl : VInductDecl) : List Name :=
  decl.typeConstants.map VConstVal.name ++ decl.constructorConstants.map VConstVal.name

theorem VInductDecl.typeNames_nodup
    {decl : VInductDecl} (H : decl.sourceNames.Nodup) :
    (decl.types.map (·.name)).Nodup := by
  have hprefix := (List.nodup_append.mp H).1
  simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
    VInductiveType.toVConstVal, Function.comp_def] using hprefix

/-- Duplicate-free source names turn equality of family names back into
equality of their positions in the mutual block. -/
theorem VInductDecl.typeIndex_eq_of_name
    {decl : VInductDecl} (H : decl.sourceNames.Nodup)
    {left right : Nat} (hleft : left < decl.types.length)
    (hright : right < decl.types.length)
    (hname : decl.types[left].name = decl.types[right].name) :
    left = right := by
  have hleftMap : left < (decl.types.map (·.name)).length := by
    simpa using hleft
  have hrightMap : right < (decl.types.map (·.name)).length := by
    simpa using hright
  apply (List.getElem_inj (h₀ := hleftMap) (h₁ := hrightMap)
    (VInductDecl.typeNames_nodup H)).mp
  simpa using hname

/-- Split exactly `n` leading forall binders, retaining domains in outermost to
innermost order. -/
def VExpr.takeForalls : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE dom body => do
    let (doms, result) ← body.takeForalls n
    return (dom :: doms, result)
  | _ + 1, _ => none

theorem VExpr.takeForalls_domains_length
    {e : VExpr} {n : Nat} {domains : List VExpr} {result : VExpr}
    (H : e.takeForalls n = some (domains, result)) :
    domains.length = n := by
  induction n generalizing e domains result with
  | zero =>
    change some ([], e) = some (domains, result) at H
    cases Option.some.inj H
    rfl
  | succ n ih =>
    cases e <;> simp [VExpr.takeForalls] at H
    case forallE dom body =>
      rcases H with ⟨tailDomains, htail, hd⟩
      rw [← hd]
      simp [ih htail]

/-- Head and left-to-right arguments of an application spine. -/
def VExpr.getAppFnArgs (e : VExpr) : VExpr × List VExpr :=
  go e []
where
  go : VExpr → List VExpr → VExpr × List VExpr
    | .app fn arg, args => go fn (arg :: args)
    | fn, args => (fn, args)

@[simp] theorem VExpr.getAppFnArgs_const :
    getAppFnArgs (.const name levels) = (.const name levels, []) := rfl

private theorem VExpr.getAppFnArgs.go_append
    (e : VExpr) (pre suffix : List VExpr) :
    getAppFnArgs.go e (pre ++ suffix) =
      let (fn, args) := getAppFnArgs.go e pre
      (fn, args ++ suffix) := by
  induction e generalizing pre with
  | app fn arg ihFn _ =>
    simpa only [getAppFnArgs.go, List.cons_append] using
      ihFn (arg :: pre)
  | _ => simp [getAppFnArgs.go]

@[simp] theorem VExpr.getAppFnArgs_app :
    getAppFnArgs (.app fn arg) =
      let (head, args) := fn.getAppFnArgs
      (head, args ++ [arg]) := by
  change getAppFnArgs.go fn [arg] =
    let (head, args) := getAppFnArgs.go fn []
    (head, args ++ [arg])
  simpa using getAppFnArgs.go_append fn [] [arg]

/-- Universe substitution commutes with exposing an application spine. -/
@[simp] theorem VExpr.getAppFnArgs_instL (e : VExpr) (levels : List VLevel) :
    (e.instL levels).getAppFnArgs =
      let (fn, args) := e.getAppFnArgs
      (fn.instL levels, args.map (VExpr.instL levels)) := by
  induction e with
  | app fn arg ihFn _ =>
    simp only [VExpr.instL, VExpr.getAppFnArgs_app, ihFn]
    simp
  | bvar | sort | const | lam | forallE =>
    rfl

def VExpr.containsAnyConst (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const name _ => names.contains name
  | .app fn arg | .lam fn arg | .forallE fn arg =>
    fn.containsAnyConst names || arg.containsAnyConst names

/-- Universe substitution changes levels but not the constant-name support
of an expression. -/
@[simp] theorem VExpr.containsAnyConst_instL
    (e : VExpr) (levels : List VLevel) :
    (e.instL levels).containsAnyConst names = e.containsAnyConst names := by
  induction e <;> simp [VExpr.instL, VExpr.containsAnyConst, *]

/-- The common parameters as de Bruijn variables beneath `depth` additional
constructor-field binders. -/
def VInductDecl.paramVars (decl : VInductDecl) (depth : Nat) : List VExpr :=
  (List.range decl.nparams).reverse.map fun i => .bvar (depth + i)

def VInductDecl.ParamsDefEq (env : VEnv) (decl : VInductDecl)
    (params params' : List VExpr) : Prop :=
  VEnv.IsDefEqCtx env decl.uvars [] params.reverse params'.reverse

/-- The support-relevant shape of a primitive projection expansion.  The
arguments before the major and the generated minor are administrative: they
are reconstructed by the certified projection producer, but they were not
subterms of the source projection expression. -/
inductive VExpr.ProjectionSupportExpansion (major : VExpr) : VExpr → Prop
  | canonical (administrativeHead minor : VExpr) :
      ProjectionSupportExpansion major
        (.app (.app administrativeHead major) minor)

theorem VExpr.ProjectionSupportExpansion.liftN
    (H : VExpr.ProjectionSupportExpansion major target) (n k : Nat) :
    VExpr.ProjectionSupportExpansion (major.liftN n k)
      (target.liftN n k) := by
  cases H with
  | canonical administrativeHead minor =>
    simpa [VExpr.liftN] using
      VExpr.ProjectionSupportExpansion.canonical
        (administrativeHead.liftN n k) (minor.liftN n k)

/-- Constant support inherited from source syntax.  Ordinary nodes expose
the support of all source subterms.  A certified projection expansion exposes
only the support of its source major; the eliminator, motive, inferred
parameters, and generated minor are administrative elaboration artifacts.

This is intentionally distinct from raw `containsAnyConst`: canonical
projection expansion does not preserve that stronger property. -/
inductive VExpr.SourceConstFree (names : List Name) : VExpr → Prop
  | bvar (index : Nat) : SourceConstFree names (.bvar index)
  | sort (level : VLevel) : SourceConstFree names (.sort level)
  | const (name : Name) (levels : List VLevel) (fresh : name ∉ names) :
      SourceConstFree names (.const name levels)
  | app : SourceConstFree names fn → SourceConstFree names arg →
      SourceConstFree names (.app fn arg)
  | lam : SourceConstFree names domain → SourceConstFree names body →
      SourceConstFree names (.lam domain body)
  | forallE : SourceConstFree names domain →
      SourceConstFree names body → SourceConstFree names (.forallE domain body)
  | projection : ProjectionSupportExpansion major target →
      SourceConstFree names major → SourceConstFree names target

theorem VExpr.SourceConstFree.ofContainsAnyConst
    {expression : VExpr} {names : List Name}
    (H : expression.containsAnyConst names = false) :
    expression.SourceConstFree names := by
  induction expression with
  | bvar index => exact .bvar index
  | sort level => exact .sort level
  | const name levels =>
    apply SourceConstFree.const name levels
    intro hname
    simp [VExpr.containsAnyConst, hname] at H
  | app fn arg ihFn ihArg =>
    rcases Bool.or_eq_false_iff.mp H with ⟨hfn, harg⟩
    exact .app (ihFn hfn) (ihArg harg)
  | lam domain body ihDomain ihBody | forallE domain body ihDomain ihBody =>
    rcases Bool.or_eq_false_iff.mp H with ⟨hdomain, hbody⟩
    first | exact .lam (ihDomain hdomain) (ihBody hbody)
          | exact .forallE (ihDomain hdomain) (ihBody hbody)

/-- Universe instantiation preserves source support. -/
theorem VExpr.SourceConstFree.instL
    {expression : VExpr} {names : List Name}
    (H : expression.SourceConstFree names) (levels : List VLevel) :
    (expression.instL levels).SourceConstFree names := by
  induction H with
  | bvar index => exact .bvar index
  | sort level => exact .sort _
  | const name sourceLevels fresh => exact .const name _ fresh
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody
  | @projection major target expansion _ ihMajor =>
    cases expansion with
    | canonical administrativeHead minor =>
      apply SourceConstFree.projection
        (ProjectionSupportExpansion.canonical
          (administrativeHead.instL levels)
          (minor.instL levels))
      exact ihMajor

/-- Bound-variable weakening preserves source support. -/
theorem VExpr.SourceConstFree.liftN
    {expression : VExpr} {names : List Name}
    (H : expression.SourceConstFree names) (n k : Nat) :
    (expression.liftN n k).SourceConstFree names := by
  induction H generalizing k with
  | bvar index => exact .bvar _
  | sort level => exact .sort level
  | const name sourceLevels fresh => exact .const name sourceLevels fresh
  | app _ _ ihFn ihArg => exact .app (ihFn k) (ihArg k)
  | lam _ _ ihDomain ihBody => exact .lam (ihDomain k) (ihBody (k + 1))
  | forallE _ _ ihDomain ihBody =>
    exact .forallE (ihDomain k) (ihBody (k + 1))
  | @projection major target expansion _ ihMajor =>
    cases expansion with
    | canonical administrativeHead minor =>
      exact .projection
        (.canonical (administrativeHead.liftN n k) (minor.liftN n k))
        (ihMajor k)


/-- A fully applied occurrence of one of the simultaneously declared types.
Recursive occurrences use precisely the common parameter variables, and their
indices contain no recursive occurrence. -/
def VInductDecl.ValidIndAppAt (decl : VInductDecl) (target : Option Name)
    (depth : Nat) (e : VExpr) : Prop :=
  let (fn, args) := e.getAppFnArgs
  ∃ type ∈ decl.types, (target = none ∨ target = some type.name) ∧
    ∃ levels,
      fn = .const type.name levels ∧
      levels.length = decl.uvars ∧
      args.length = decl.nparams + type.numIndices ∧
      args.take decl.nparams = decl.paramVars depth ∧
      ∀ arg ∈ args.drop decl.nparams,
        arg.SourceConstFree (decl.types.map (·.name))

theorem VInductDecl.ValidIndAppAt.forgetTarget
    {decl : VInductDecl} {target : Option Name}
    {depth : Nat} {e : VExpr}
    (H : decl.ValidIndAppAt target depth e) :
    decl.ValidIndAppAt none depth e := by
  rcases H with ⟨type, htype, _htarget, levels, hfn, hlevels,
    hargs, hparams, hindices⟩
  exact ⟨type, htype, Or.inl rfl, levels, hfn, hlevels,
    hargs, hparams, hindices⟩

/-- Instantiating universes preserves the syntactic recursive-application
criterion.  In particular this lets a recursive domain checked under a fresh
recursor universe be specialized back to the declaration universe arity. -/
theorem VInductDecl.ValidIndAppAt.instL
    {decl : VInductDecl} {target : Option Name}
    {depth : Nat} {e : VExpr} (levels : List VLevel)
    (H : decl.ValidIndAppAt target depth e) :
    decl.ValidIndAppAt target depth (e.instL levels) := by
  unfold VInductDecl.ValidIndAppAt at H ⊢
  generalize hspine : e.getAppFnArgs = spine at H
  rcases spine with ⟨fn, args⟩
  rw [VExpr.getAppFnArgs_instL, hspine]
  rcases H with ⟨type, htype, htarget, sourceLevels, hfn,
    hlevelLength, hargLength, hparams, hindices⟩
  refine ⟨type, htype, htarget, sourceLevels.map (VLevel.inst levels),
    ?_, by simpa using hlevelLength, by simpa using hargLength, ?_, ?_⟩
  · simp [hfn, VExpr.instL]
  · rw [← List.map_take, hparams]
    simp [VInductDecl.paramVars, VExpr.instL]
  · intro arg harg
    rw [← List.map_drop] at harg
    rcases List.mem_map.mp harg with ⟨source, hsource, rfl⟩
    exact (hindices source hsource).instL levels

/-- A concrete application spine cannot name two different members of the
same inductive block.  Keeping this fact at the abstract boundary lets later
implementation proofs compare independently replayed classifier passes
without appealing to array indices or executable name lookup. -/
theorem VInductDecl.ValidIndAppAt.target_unique
    {decl : VInductDecl} {left right : Name}
    {depth : Nat} {e : VExpr}
    (Hleft : decl.ValidIndAppAt (some left) depth e)
    (Hright : decl.ValidIndAppAt (some right) depth e) :
    left = right := by
  rcases Hleft with ⟨leftType, _hleftType, hleftTarget,
    leftLevels, hleftHead, _⟩
  rcases Hright with ⟨rightType, _hrightType, hrightTarget,
    rightLevels, hrightHead, _⟩
  have htypeNames : leftType.name = rightType.name := by
    exact (VExpr.const.inj (hleftHead.symm.trans hrightHead)).1
  rcases hleftTarget with hnone | hleft
  · cases hnone
  rcases hrightTarget with hnone | hright
  · cases hnone
  exact Option.some.inj hleft |>.trans <|
    htypeNames.trans (Option.some.inj hright).symm

theorem VInductDecl.ValidIndAppAt.targetIndex_unique
    {decl : VInductDecl} (hnames : decl.sourceNames.Nodup)
    {left right : Nat} (hleft : left < decl.types.length)
    (hright : right < decl.types.length) {depth : Nat} {e : VExpr}
    (Hleft : decl.ValidIndAppAt
      (some (decl.types[left]'hleft).name) depth e)
    (Hright : decl.ValidIndAppAt
      (some (decl.types[right]'hright).name) depth e) :
    left = right := by
  apply VInductDecl.typeIndex_eq_of_name hnames hleft hright
  exact Hleft.target_unique Hright

/- Positivity is recursively modulo definitional equality: the executable
checker exposes every higher-order body to WHNF, not only the outermost field
type.  `SyntacticallyPositive` classifies one exposed head, while `Positive`
records the definitional-equality step and recurs under `forallE`. -/
namespace VInductDecl

mutual

/-- Positivity modulo one WHNF/definitional-equality step. -/
inductive Positive (env : VEnv) (decl : VInductDecl) :
    List VExpr → Nat → VExpr → Prop
  | unfold :
    env.IsDefEq decl.uvars ctx e exposed type →
    SyntacticallyPositive env decl ctx depth exposed →
    Positive env decl ctx depth e
/-- The exposed-head cases of strict positivity. -/
inductive SyntacticallyPositive (env : VEnv)
    (decl : VInductDecl) : List VExpr → Nat → VExpr → Prop
  | nonrecursive :
    e.SourceConstFree (decl.types.map (·.name)) →
    SyntacticallyPositive env decl ctx depth e
  | forallE :
    dom.SourceConstFree (decl.types.map (·.name)) →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    Positive env decl (checkedDom :: ctx) (depth + 1) checkedBody →
    SyntacticallyPositive env decl ctx depth (.forallE dom body)
  | recursive :
    decl.ValidIndAppAt none depth e →
    SyntacticallyPositive env decl ctx depth e

end

end VInductDecl

/-- A constructor field for which recursor generation must introduce an
induction hypothesis. Unlike positivity, this judgment follows higher-order
binders only to classify the field's eventual result; positivity of the whole
domain is checked separately by `Positive`. -/
inductive VInductDecl.RecursiveArg (env : VEnv) (decl : VInductDecl) :
    List VExpr → Nat → VExpr → Prop
  | direct :
    env.IsDefEq decl.uvars ctx e exposed type →
    decl.ValidIndAppAt none depth exposed →
    decl.RecursiveArg env ctx depth e
  | forallE :
    env.IsDefEq decl.uvars ctx e (.forallE dom body) type →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    decl.RecursiveArg env (checkedDom :: ctx) (depth + 1) checkedBody →
    decl.RecursiveArg env ctx depth e

/-- Universe-parametric form of `RecursiveArg`.  Constructor declarations are
checked at `decl.uvars`, but generated large-elimination recursors interpret
the same recursive-domain syntax after prepending a fresh universe parameter.
Keeping the universe arity explicit lets the implementation refinement state
that intermediate invariant without identifying those two contexts. -/
inductive VInductDecl.RecursiveArgAt (env : VEnv) (decl : VInductDecl)
    (uvars : Nat) : List VExpr → Nat → VExpr → Prop
  | direct :
    env.IsDefEq uvars ctx e exposed type →
    decl.ValidIndAppAt none depth exposed →
    decl.RecursiveArgAt env uvars ctx depth e
  | forallE :
    env.IsDefEq uvars ctx e (.forallE dom body) type →
    env.IsDefEq uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq uvars (dom :: ctx) body checkedBody bodyType →
    decl.RecursiveArgAt env uvars (checkedDom :: ctx) (depth + 1)
      checkedBody →
    decl.RecursiveArgAt env uvars ctx depth e

/-- Target-preserving recursive-argument classification.  The executable
classifier returns a mutual-family index; this judgment carries the matching
family name through every higher-order binder instead of forgetting it at the
direct application. -/
inductive VInductDecl.RecursiveArgAtTarget
    (env : VEnv) (decl : VInductDecl) (uvars : Nat) (target : Name) :
    List VExpr → Nat → VExpr → Prop
  | direct :
    env.IsDefEq uvars ctx e exposed type →
    decl.ValidIndAppAt (some target) depth exposed →
    decl.RecursiveArgAtTarget env uvars target ctx depth e
  | forallE :
    env.IsDefEq uvars ctx e (.forallE dom body) type →
    env.IsDefEq uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq uvars (dom :: ctx) body checkedBody bodyType →
    decl.RecursiveArgAtTarget env uvars target
      (checkedDom :: ctx) (depth + 1) checkedBody →
    decl.RecursiveArgAtTarget env uvars target ctx depth e

theorem VInductDecl.RecursiveArgAtTarget.forgetTarget
    {decl : VInductDecl} {env : VEnv} {uvars : Nat} {target : Name}
    {ctx : List VExpr} {depth : Nat} {e : VExpr}
    (H : decl.RecursiveArgAtTarget env uvars target ctx depth e) :
    decl.RecursiveArgAt env uvars ctx depth e := by
  induction H with
  | direct hdef happ => exact .direct hdef happ.forgetTarget
  | forallE he hdom hbody _ ih => exact .forallE he hdom hbody ih

/-- Recursive-argument classification is stable under arbitrary universe
specialization.  The context and classified domain are instantiated in
lockstep with every definitional-equality premise. -/
theorem VInductDecl.RecursiveArgAtTarget.instL
    {decl : VInductDecl} {env : VEnv} {uvars targetUvars : Nat}
    {target : Name} {ctx : List VExpr} {depth : Nat} {e : VExpr}
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF targetUvars)
    (H : decl.RecursiveArgAtTarget env uvars target ctx depth e) :
    decl.RecursiveArgAtTarget env targetUvars target
      (ctx.map (VExpr.instL levels)) depth (e.instL levels) := by
  induction H with
  | direct hdef happ =>
    exact .direct (hdef.instL hlevels) (happ.instL levels)
  | forallE he hdom hbody _ ih =>
    simpa [VExpr.instL] using
      VInductDecl.RecursiveArgAtTarget.forallE
        (he.instL hlevels) (hdom.instL hlevels)
        (hbody.instL hlevels) ih

theorem VInductDecl.RecursiveArg.toAt
    {decl : VInductDecl} {env : VEnv} {ctx : List VExpr}
    {depth : Nat} {e : VExpr}
    (H : decl.RecursiveArg env ctx depth e) :
    decl.RecursiveArgAt env decl.uvars ctx depth e := by
  induction H with
  | direct hdef happ => exact .direct hdef happ
  | forallE he hdom hbody _ ih => exact .forallE he hdom hbody ih

theorem VInductDecl.RecursiveArgAt.toRecursiveArg
    {decl : VInductDecl} {env : VEnv} {ctx : List VExpr}
    {depth : Nat} {e : VExpr}
    (H : decl.RecursiveArgAt env decl.uvars ctx depth e) :
    decl.RecursiveArg env ctx depth e := by
  induction H with
  | direct hdef happ => exact .direct hdef happ
  | forallE he hdom hbody _ ih => exact .forallE he hdom hbody ih

/-- Constructor fields followed by the constructor's target application. -/
inductive VInductDecl.CtorTailWF (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) : List VExpr → Nat → VExpr → Prop
  | result :
    decl.ValidIndAppAt (some target.name) depth result' →
    env.IsDefEq decl.uvars ctx result result' type →
    decl.CtorTailWF env target ctx depth result
  | field :
    env.HasType decl.uvars ctx dom (.sort fieldLevel) →
    (target.resultLevel ≈ .zero ∨ fieldLevel ≤ target.resultLevel) →
    (decl.isUnsafe = true ∨ decl.Positive env ctx depth dom) →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort checkedLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    decl.CtorTailWF env target (checkedDom :: ctx) (depth + 1) checkedBody →
    decl.CtorTailWF env target ctx depth (.forallE dom body)

theorem VInductDecl.ParamsDefEq.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.ParamsDefEq env params params') :
    decl.ParamsDefEq env' params params' :=
  VEnv.IsDefEqCtx.mono henv H

theorem VInductDecl.Positive.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.Positive env ctx depth e) :
    decl.Positive env' ctx depth e := by
  exact VInductDecl.Positive.rec
    (motive_1 := fun ctx depth e _ => decl.Positive env' ctx depth e)
    (motive_2 := fun ctx depth e _ =>
      decl.SyntacticallyPositive env' ctx depth e)
    (fun hdef _ ih => .unfold (hdef.mono henv) ih)
    (fun h => .nonrecursive h)
    (fun hcontains hdom hbody _ ih =>
      .forallE hcontains (hdom.mono henv) (hbody.mono henv) ih)
    (fun h => .recursive h) H

theorem VInductDecl.SyntacticallyPositive.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.SyntacticallyPositive env ctx depth e) :
    decl.SyntacticallyPositive env' ctx depth e := by
  exact VInductDecl.SyntacticallyPositive.rec
    (motive_1 := fun ctx depth e _ => decl.Positive env' ctx depth e)
    (motive_2 := fun ctx depth e _ =>
      decl.SyntacticallyPositive env' ctx depth e)
    (fun hdef _ ih => .unfold (hdef.mono henv) ih)
    (fun h => .nonrecursive h)
    (fun hcontains hdom hbody _ ih =>
      .forallE hcontains (hdom.mono henv) (hbody.mono henv) ih)
    (fun h => .recursive h) H

theorem VInductDecl.RecursiveArg.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.RecursiveArg env ctx depth e) :
    decl.RecursiveArg env' ctx depth e := by
  induction H with
  | direct hdef happ => exact .direct (hdef.mono henv) happ
  | forallE he hdom hbody _ ih =>
    exact .forallE (he.mono henv) (hdom.mono henv) (hbody.mono henv) ih

theorem VInductDecl.RecursiveArgAt.mono
    {env env' : VEnv} {decl : VInductDecl} {uvars : Nat}
    {ctx : List VExpr} {depth : Nat} {e : VExpr}
    (henv : env ≤ env')
    (H : decl.RecursiveArgAt env uvars ctx depth e) :
    decl.RecursiveArgAt env' uvars ctx depth e := by
  induction H with
  | direct hdef happ => exact .direct (hdef.mono henv) happ
  | forallE he hdom hbody _ ih =>
    exact .forallE (he.mono henv) (hdom.mono henv) (hbody.mono henv) ih

theorem VInductDecl.RecursiveArgAtTarget.mono
    {env env' : VEnv} {decl : VInductDecl} {uvars : Nat}
    {target : Name} {ctx : List VExpr} {depth : Nat} {e : VExpr}
    (henv : env ≤ env')
    (H : decl.RecursiveArgAtTarget env uvars target ctx depth e) :
    decl.RecursiveArgAtTarget env' uvars target ctx depth e := by
  induction H with
  | direct hdef happ => exact .direct (hdef.mono henv) happ
  | forallE he hdom hbody _ ih =>
    exact .forallE (he.mono henv) (hdom.mono henv) (hbody.mono henv) ih

theorem VInductDecl.CtorTailWF.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.CtorTailWF env target ctx depth e) :
    decl.CtorTailWF env' target ctx depth e := by
  induction H with
  | result happ hdef => exact .result happ (hdef.mono henv)
  | field htype hlevel hpositive hdom hbody _ ih =>
    exact .field (htype.mono henv) hlevel
      (hpositive.elim (fun h => .inl h)
        (fun h => .inr (h.mono henv)))
      (hdom.mono henv) (hbody.mono henv) ih

/-- Shape of one inductive type after normalization: common parameters,
exactly the recorded indices, and the recorded result sort. -/
def VInductDecl.TypeShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (type : VInductiveType) : Prop :=
  ∃ normalized ownParams afterParams indices result exprType,
    env.IsDefEq decl.uvars [] type.type normalized exprType ∧
    normalized.takeForalls decl.nparams = some (ownParams, afterParams) ∧
    afterParams.takeForalls type.numIndices = some (indices, result) ∧
    decl.ParamsDefEq env params ownParams ∧
    env.IsDefEq decl.uvars (indices.reverse ++ ownParams.reverse)
      result (.sort type.resultLevel) (.sort (.succ type.resultLevel))

def VInductDecl.CtorShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) (ctor : VConstVal) : Prop :=
  ∃ normalized ownParams tail exprType tailCtx,
    env.IsDefEq decl.uvars [] ctor.type normalized exprType ∧
    normalized.takeForalls decl.nparams = some (ownParams, tail) ∧
    decl.ParamsDefEq env params ownParams ∧
    env.IsDefEqCtx decl.uvars [] ownParams.reverse tailCtx ∧
    decl.CtorTailWF env target tailCtx 0 tail

/-- Raw common-parameter shape of one constructor before normalization.
This is separate from `CtorShape`: normalization may change the visible
forall prefix, while the executable checker compares the original prefix
directly with the mutual header parameters. -/
def VInductDecl.CtorParameterShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (ctor : VConstVal) : Prop :=
  ∃ ownParams tail,
    ctor.type.takeForalls decl.nparams = some (ownParams, tail) ∧
    decl.ParamsDefEq env params ownParams

/-- Source-facing common-parameter formation retained by both ordinary and
nested declarations.  The family headers identify the shared semantic
parameter telescope, while every original constructor retains its raw
pre-normalization prefix against that same telescope. -/
def VInductDecl.SourceParameterWF (env : VEnv)
    (decl : VInductDecl) : Prop :=
  ∃ params envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    (∀ type ∈ decl.types, decl.TypeShape env params type) ∧
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
      decl.CtorParameterShape envTypes params ctor

theorem VInductDecl.TypeShape.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.TypeShape env params type) :
    decl.TypeShape env' params type := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      htype, hparams, hindices, hparamsDefEq, hresult⟩
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    htype.mono henv, hparams, hindices, hparamsDefEq.mono henv,
    hresult.mono henv⟩

theorem VInductDecl.CtorShape.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.CtorShape env params target ctor) :
    decl.CtorShape env' params target ctor := by
  rcases H with
    ⟨normalized, ownParams, tail, exprType, tailCtx, htype, hparams,
      hparamsDefEq, hctx, htail⟩
  exact ⟨normalized, ownParams, tail, exprType, tailCtx, htype.mono henv,
    hparams, hparamsDefEq.mono henv, hctx.mono henv, htail.mono henv⟩

theorem VInductDecl.CtorParameterShape.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : decl.CtorParameterShape env params ctor) :
    decl.CtorParameterShape env' params ctor := by
  rcases H with ⟨ownParams, tail, htake, hparams⟩
  exact ⟨ownParams, tail, htake, hparams.mono henv⟩

/-! ## Abstract nested expansion

Nested lowering preserves the position of every constructor field, replacing
maximal nested applications by applications of fresh auxiliary families. The
relations below state that source-to-expanded correspondence independently of
the executable lowering state. They deliberately precede any change to
`VInductDecl.WF`: the implementation refinement must first prove that its
stateful `Expr` traversal projects to this small `VExpr` relation. -/

/-- Structural expression expansion with an explicit relation for maximal
nested-application hits. Binder depth is retained because direct inductive
applications use depth-indexed canonical parameters. -/
inductive VExpr.NestedExprExpansion
    (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → VExpr → VExpr → Prop
  | hit : leaf depth source target →
      NestedExprExpansion leaf depth source target
  | bvar : NestedExprExpansion leaf depth (.bvar index) (.bvar index)
  | sort : NestedExprExpansion leaf depth (.sort level) (.sort level)
  | const : NestedExprExpansion leaf depth (.const name levels)
      (.const name levels)
  | app : NestedExprExpansion leaf depth sourceFn targetFn →
      NestedExprExpansion leaf depth sourceArg targetArg →
      NestedExprExpansion leaf depth (.app sourceFn sourceArg)
        (.app targetFn targetArg)
  | lam : NestedExprExpansion leaf depth sourceDomain targetDomain →
      NestedExprExpansion leaf (depth + 1) sourceBody targetBody →
      NestedExprExpansion leaf depth (.lam sourceDomain sourceBody)
        (.lam targetDomain targetBody)
  | forallE : NestedExprExpansion leaf depth sourceDomain targetDomain →
      NestedExprExpansion leaf (depth + 1) sourceBody targetBody →
      NestedExprExpansion leaf depth (.forallE sourceDomain sourceBody)
        (.forallE targetDomain targetBody)
  | projection :
      ProjectionSupportExpansion sourceMajor sourceTarget →
      ProjectionSupportExpansion targetMajor targetTarget →
      NestedExprExpansion leaf depth sourceMajor targetMajor →
      NestedExprExpansion leaf depth sourceTarget targetTarget

/-- Change only the interpretation of successful leaves. -/
theorem VExpr.NestedExprExpansion.map
    (Hleaf : ∀ {depth source target}, leaf depth source target →
      leaf' depth source target)
    (H : VExpr.NestedExprExpansion leaf depth source target) :
    VExpr.NestedExprExpansion leaf' depth source target := by
  induction H with
  | hit h => exact .hit (Hleaf h)
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody
  | projection Hsource Htarget _ ihMajor =>
    exact .projection Hsource Htarget ihMajor

/-- Leaving an abstract expression unchanged is always an expansion. -/
theorem VExpr.NestedExprExpansion.refl
    (leaf : Nat → VExpr → VExpr → Prop)
    (depth : Nat) (e : VExpr) :
    VExpr.NestedExprExpansion leaf depth e e := by
  induction e generalizing depth with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihFn ihArg => exact .app (ihFn depth) (ihArg depth)
  | lam _ _ ihDomain ihBody =>
    exact .lam (ihDomain depth) (ihBody (depth + 1))
  | forallE _ _ ihDomain ihBody =>
    exact .forallE (ihDomain depth) (ihBody (depth + 1))

/-- The exact common-parameter prefix retained by nested lowering.  Unlike
`NestedExprExpansion` of the complete constructor, this records where each
of the first `arity` forall domains sits in the depth-indexed expansion. -/
inductive VExpr.NestedForallPrefixExpansion
    (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → Nat → VExpr → VExpr → Prop
  | nil
      (Hbody : VExpr.NestedExprExpansion leaf depth sourceBody targetBody) :
      VExpr.NestedForallPrefixExpansion leaf depth 0 sourceBody targetBody
  | cons
      (Hdomain : VExpr.NestedExprExpansion leaf depth
        sourceDomain targetDomain)
      (Hbody : VExpr.NestedForallPrefixExpansion leaf (depth + 1) arity
        sourceBody targetBody) :
      VExpr.NestedForallPrefixExpansion leaf depth (arity + 1)
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)

/-- One positionally corresponding source/expanded constructor.  The common
parameter prefix is retained separately from the complete structural body so
later semantic assembly never has to replay the executable parameter loop. -/
structure VInductDecl.NestedConstructorExpansion
    (leaf : Nat → VExpr → VExpr → Prop) (nparams : Nat)
    (source target : VConstVal) : Prop where
  name : target.name = source.name
  uvars : target.uvars = source.uvars
  parameters : VExpr.NestedForallPrefixExpansion leaf 0 nparams
    source.type target.type
  type : VExpr.NestedExprExpansion leaf 0 source.type target.type

/-- One original family and its positionally corresponding expanded family.
Headers are compared semantically; constructor bodies retain the structural
nested-expansion relation. -/
structure VInductDecl.NestedTypeExpansion
    (env : VEnv) (decl : VInductDecl)
    (leaf : Nat → VExpr → VExpr → Prop)
    (source target : VInductiveType) : Prop where
  name : target.name = source.name
  uvars : target.uvars = source.uvars
  type : env.IsDefEqU decl.uvars [] source.type target.type
  numIndices : target.numIndices = source.numIndices
  resultLevel : target.resultLevel = source.resultLevel
  constructors : List.Forall₂ (NestedConstructorExpansion leaf decl.nparams)
    source.ctors target.ctors

/-- Independent source-to-expanded declaration relation for nested lowering.
Original families occupy an exact prefix; generated leaves point to an
auxiliary family in the remaining suffix and replace an expression containing
an original-family occurrence. -/
structure VInductDecl.NestedExpansion
    (leaf : Nat → VExpr → VExpr → Prop)
    (env : VEnv) (source expanded : VInductDecl) : Prop where
  uvars : expanded.uvars = source.uvars
  nparams : expanded.nparams = source.nparams
  isUnsafe : expanded.isUnsafe = source.isUnsafe
  sourcePrefix : source.types.length ≤ expanded.types.length
  leafSource : ∀ {depth input output}, leaf depth input output →
    input.containsAnyConst (source.types.map (·.name)) = true
  leafTarget : ∀ {depth input output}, leaf depth input output →
    ∃ auxiliary ∈ expanded.types.drop source.types.length,
      ∃ levels args,
        output.getAppFnArgs = (.const auxiliary.name levels, args)
  originalTypes : List.Forall₂
    (NestedTypeExpansion env source leaf) source.types
      (expanded.types.take source.types.length)

theorem VInductDecl.NestedTypeExpansion.mono
    (henv : env ≤ env')
    (H : VInductDecl.NestedTypeExpansion env decl leaf source target) :
    VInductDecl.NestedTypeExpansion env' decl leaf source target where
  name := H.name
  uvars := H.uvars
  type := H.type.mono henv
  numIndices := H.numIndices
  resultLevel := H.resultLevel
  constructors := H.constructors

/-- Nested expansion is stable when the ambient abstract environment grows.
This is the relation-level ingredient needed by later block rebasing. -/
theorem VInductDecl.NestedExpansion.mono
    (henv : env ≤ env')
    (H : VInductDecl.NestedExpansion leaf env source expanded) :
    VInductDecl.NestedExpansion leaf env' source expanded where
  uvars := H.uvars
  nparams := H.nparams
  isUnsafe := H.isUnsafe
  sourcePrefix := H.sourcePrefix
  leafSource := H.leafSource
  leafTarget := H.leafTarget
  originalTypes := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => h.mono henv) H.originalTypes

/-- Rebase an expansion witness without changing either declaration or the
leaf correspondence. -/
theorem VInductDecl.NestedExpansion.rebase
    (H : VInductDecl.NestedExpansion leaf env source expanded)
    (henv : env ≤ env') :
    VInductDecl.NestedExpansion leaf env' source expanded :=
  H.mono henv

/-- Source-level obligations that cannot be erased by ordinary or nested
compilation. In particular constructor types are checked in an environment
containing all mutually declared headers, before any nested occurrence is
lowered. -/
def VInductDecl.SourceWF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.types ≠ [] ∧
  decl.sourceNames.Nodup ∧
  (∀ type ∈ decl.types, type.uvars = decl.uvars) ∧
  (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) ∧
  ∃ envTypes envCtors,
    env.addConstVals decl.typeConstants = some envTypes ∧
    envTypes.addConstVals decl.constructorConstants = some envCtors ∧
    (∀ type ∈ decl.types, type.toVConstant.WF env) ∧
    ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes

/-- Formation conditions for ordinary and mutually recursive inductive blocks.
Nested declarations use the same source judgment; their lowering must later
produce these conditions for the expanded mutual family. -/
def VInductDecl.FormationWF (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ params resultLevel envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    (∀ type ∈ decl.types,
      type.resultLevel ≈ resultLevel ∧ decl.TypeShape env params type) ∧
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
      decl.CtorParameterShape envTypes params ctor ∧
      decl.CtorShape envTypes params type ctor

theorem VInductDecl.FormationWF.sourceParameterWF
    {env : VEnv} {decl : VInductDecl}
    (H : VInductDecl.FormationWF env decl) :
    VInductDecl.SourceParameterWF env decl := by
  rcases H with
    ⟨params, _resultLevel, envTypes, htypes, Htypes, Hconstructors⟩
  exact ⟨params, envTypes, htypes,
    fun type htype => (Htypes type htype).2,
    fun type htype ctor hctor =>
      (Hconstructors type htype ctor hctor).1⟩

theorem VInductDecl.SourceWF.originalTypes
    {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) :
    ∀ type ∈ decl.types, type.toVConstant.WF env := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypes, hctors, hwf, _⟩
  exact hwf

/-- In particular, source constructor types are checked before nested lowering.
This is the abstract obligation whose absence exposed the erased-parameter
kernel bug: a proof about generated auxiliary constructors cannot discharge it. -/
theorem VInductDecl.SourceWF.originalConstructors
    {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) :
    ∃ envTypes,
      env.addConstVals decl.typeConstants = some envTypes ∧
      ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypes, hctors, _, hwf⟩
  exact ⟨envTypes, htypes, hwf⟩

/-- Install a compiled block in dependency order. -/
def VInductBlock.install (env : VEnv) (block : VInductBlock) : Option VEnv := do
  let env ← env.addConstVals block.types
  let env ← env.addConstVals block.ctors
  let env ← env.addConstVals block.recursors
  return env.addDefEqRules block.rules

/-- A compiled block is semantically well formed when every declaration is
well formed at the stage where it is installed, and installation succeeds. -/
def VInductBlock.WF (env : VEnv) (block : VInductBlock) : Prop :=
  ∃ envTypes envCtors envRecursors,
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    envCtors.addConstVals block.recursors = some envRecursors ∧
    (∀ ci ∈ block.types, ci.toVConstant.WF env) ∧
    (∀ ci ∈ block.ctors, ci.toVConstant.WF envTypes) ∧
    (∀ ci ∈ block.recursors, ci.toVConstant.WF envCtors) ∧
    ∀ df ∈ block.rules, df.WF envRecursors

theorem VInductBlock.WF.exists_install (H : VInductBlock.WF env block) :
    ∃ env', VInductBlock.install env block = some env' := by
  rcases H with ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs, _⟩
  exact ⟨envRecursors.addDefEqRules block.rules, by
    simp [VInductBlock.install, htypes, hctors, hrecs]⟩

def VExpr.mkApps (fn : VExpr) (args : List VExpr) : VExpr :=
  args.foldl .app fn

def VExpr.wrapLams (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .lam body

def VExpr.wrapForalls (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .forallE body

/-- Consume an exact forall prefix with the supplied arguments. Ill-shaped
inputs are left unchanged; formation witnesses rule that branch out. -/
def VExpr.instantiateForallPrefix : VExpr → List VExpr → VExpr
  | type, [] => type
  | .forallE _ body, arg :: args =>
    instantiateForallPrefix (body.inst arg) args
  | type, _ :: _ => type

@[simp] theorem VExpr.wrapLams_append
    (left right : List VExpr) (body : VExpr) :
    VExpr.wrapLams (left ++ right) body =
      VExpr.wrapLams left (VExpr.wrapLams right body) := by
  simp [wrapLams, List.foldr_append]

@[simp] theorem VExpr.wrapForalls_append
    (left right : List VExpr) (body : VExpr) :
    VExpr.wrapForalls (left ++ right) body =
      VExpr.wrapForalls left (VExpr.wrapForalls right body) := by
  simp [wrapForalls, List.foldr_append]

@[simp] theorem VExpr.takeForalls_wrapForalls_append
    (pre suff : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls (pre ++ suff) body).takeForalls pre.length =
      some (pre, VExpr.wrapForalls suff body) := by
  induction pre with
  | nil => rfl
  | cons dom pre ih =>
    change (do
      let (domains, result) ←
        (VExpr.wrapForalls (pre ++ suff) body).takeForalls pre.length
      return (dom :: domains, result)) = _
    rw [ih]
    rfl

@[simp] theorem VExpr.takeForalls_wrapForalls
    (domains : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls domains body).takeForalls domains.length =
      some (domains, body) := by
  simpa [wrapForalls] using
    VExpr.takeForalls_wrapForalls_append domains [] body

/-- `e` is an application of one of the constructor fields represented by its
de Bruijn index at the outside of the rule telescope. `depth` accounts for
binders introduced inside a higher-order recursive call. -/
def VExpr.IsFieldApp (fieldVars : List Nat) (depth : Nat) (e : VExpr) : Prop :=
  ∃ field ∈ fieldVars, ∃ args,
    e.getAppFnArgs = (.bvar (field + depth), args)

def VExpr.bvarHead? (e : VExpr) : Option Nat :=
  match e.getAppFnArgs.1 with
  | .bvar i => some i
  | _ => none

/-- Syntactic guard for an iota-rule right-hand side. A recursor constant may
only occur through `recCall`, and its major premise must be an application of
a designated constructor field. Ordinary applications cannot smuggle in a
recursor because the `const` constructor excludes their names. -/
inductive VExpr.GuardedIota (recursors : List Name) (fieldVars : List Nat) :
    Nat → VExpr → Prop
  | bvar : GuardedIota recursors fieldVars depth (.bvar n)
  | sort : GuardedIota recursors fieldVars depth (.sort u)
  | const : name ∉ recursors →
      GuardedIota recursors fieldVars depth (.const name levels)
  | app :
      GuardedIota recursors fieldVars depth fn →
      GuardedIota recursors fieldVars depth arg →
      GuardedIota recursors fieldVars depth (.app fn arg)
  | lam :
      GuardedIota recursors fieldVars depth dom →
      GuardedIota recursors fieldVars (depth + 1) body →
      GuardedIota recursors fieldVars depth (.lam dom body)
  | forallE :
      GuardedIota recursors fieldVars depth dom →
      GuardedIota recursors fieldVars (depth + 1) body →
      GuardedIota recursors fieldVars depth (.forallE dom body)
  | projection :
      ProjectionSupportExpansion major target →
      GuardedIota recursors fieldVars depth major →
      GuardedIota recursors fieldVars depth target
  | recCall :
      recursor ∈ recursors →
      (∀ arg ∈ init ++ [major],
        GuardedIota recursors fieldVars depth arg) →
      major.IsFieldApp fieldVars depth →
      GuardedIota recursors fieldVars depth
        (VExpr.mkApps (.const recursor levels) (init ++ [major]))

/-- Guardedness for the closed RHS stored in a definitional equation.
Top-level lambdas are the equation telescope, so their bound constructor
fields become the free field variables of the residual iota body.  Testing
the complete closed lambda with an increasing `GuardedIota` depth would
instead (and incorrectly) classify every bound field as non-recursive.

Binder domains are checked with an empty field set, which permits ordinary
types but no recursive call.  Once the telescope is peeled, the residual
body uses the ordinary guarded-iota judgment at depth zero. -/
inductive VExpr.GuardedRuleRhs (recursors : List Name) : VExpr → Prop
  | body (fieldVars : List Nat) :
      GuardedIota recursors fieldVars 0 expression →
      GuardedRuleRhs recursors expression
  | lam :
      GuardedIota recursors [] 0 domain →
      GuardedRuleRhs recursors body →
      GuardedRuleRhs recursors (.lam domain body)

/-- Guardedness depends on the recursor collection only through membership.
This permits an executable checker to use the concrete restoration order and
the abstract block proof to use its canonical recursor order, once those two
orders have been identified extensionally. -/
theorem VExpr.GuardedIota.congrRecursors
    {expression : VExpr} {recursors recursors' : List Name}
    {fieldVars : List Nat} {depth : Nat}
    (hsame : ∀ name, name ∈ recursors ↔ name ∈ recursors')
    (H : expression.GuardedIota recursors fieldVars depth) :
    expression.GuardedIota recursors' fieldVars depth := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const fresh =>
      exact .const (fun hmem => fresh ((hsame _).mpr hmem))
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody
  | projection expansion _ ihMajor => exact .projection expansion ihMajor
  | recCall recursorMem arguments majorField ihArguments =>
      exact .recCall ((hsame _).mp recursorMem) ihArguments majorField

theorem VExpr.GuardedRuleRhs.congrRecursors
    {expression : VExpr} {recursors recursors' : List Name}
    (hsame : ∀ name, name ∈ recursors ↔ name ∈ recursors')
    (H : expression.GuardedRuleRhs recursors) :
    expression.GuardedRuleRhs recursors' := by
  induction H with
  | body fieldVars guarded =>
      exact .body fieldVars (guarded.congrRecursors hsame)
  | lam domainGuarded _ ihBody =>
      exact .lam (domainGuarded.congrRecursors hsame) ihBody

def VInductDecl.ownedConstructors
    (decl : VInductDecl) : List (VInductiveType × VConstVal) :=
  decl.types.flatMap fun type => type.ctors.map (type, ·)

def VInductDecl.recursorName (_decl : VInductDecl) (type : VInductiveType) : Name :=
  .mkStr type.name "rec"

/-- A constructor argument selected for an induction hypothesis, together
with the independent recursive-result certificate produced for its domain. -/
structure VInductDecl.RecursiveField (env : VEnv) (decl : VInductDecl) where
  /-- Zero-based position among the constructor fields, after the common
  parameter prefix. -/
  fieldIndex : Nat
  arg : VExpr
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArg env ctx depth domain

def VInductDecl.RecursiveField.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env') (H : decl.RecursiveField env) :
    decl.RecursiveField env' where
  fieldIndex := H.fieldIndex
  arg := H.arg
  ctx := H.ctx
  depth := H.depth
  domain := H.domain
  recursive := H.recursive.mono henv

@[simp] theorem VInductDecl.RecursiveField.mono_fieldIndex
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env') (H : decl.RecursiveField env) :
    (H.mono henv).fieldIndex = H.fieldIndex := rfl

@[simp] theorem VInductDecl.RecursiveField.mono_arg
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env') (H : decl.RecursiveField env) :
    (H.mono henv).arg = H.arg := rfl

/-- Recursor result with an explicit motive count.  Ordinary compilation has
one motive per source family; nested compilation may append motives for
lowering-generated auxiliary families while retaining each source owner's
original position. -/
def VInductDecl.recursorResultWithCounts (_decl : VInductDecl)
    (ownerIdx numMotives numMinors : Nat) (owner : VInductiveType) : VExpr :=
  let motiveOffset :=
    1 + owner.numIndices + numMinors + (numMotives - 1 - ownerIdx)
  let indexVars := (List.range owner.numIndices).reverse.map fun i =>
    VExpr.bvar (i + 1)
  VExpr.mkApps (.bvar motiveOffset) (indexVars ++ [.bvar 0])

def VInductDecl.recursorResult (decl : VInductDecl)
    (ownerIdx numMinors : Nat) (owner : VInductiveType) : VExpr :=
  decl.recursorResultWithCounts ownerIdx decl.types.length numMinors owner

/-- Independent shape of a generated recursor. Besides its conventional name
and universe count, the leading telescope contains exactly the common
parameters, one motive per mutual type, one minor per constructor, the owner's
indices, and one major premise; its result applies the matching motive to the
indices and major premise. -/
structure VInductDecl.RecursorShape (decl : VInductDecl)
    (owner : VInductiveType) (recursor : VConstVal) where
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  owner_eq : decl.types[ownerIdx] = owner
  name : recursor.name = decl.recursorName owner
  uvars : recursor.uvars = decl.uvars ∨ recursor.uvars = decl.uvars + 1
  params : List VExpr
  motives : List VExpr
  minors : List VExpr
  indices : List VExpr
  major : List VExpr
  afterParams : VExpr
  afterMotives : VExpr
  afterMinors : VExpr
  afterIndices : VExpr
  result : VExpr
  params_take : recursor.type.takeForalls decl.nparams =
    some (params, afterParams)
  motives_take : afterParams.takeForalls decl.types.length =
    some (motives, afterMotives)
  minors_take : afterMotives.takeForalls decl.ownedConstructors.length =
    some (minors, afterMinors)
  indices_take : afterMinors.takeForalls owner.numIndices =
    some (indices, afterIndices)
  major_take : afterIndices.takeForalls 1 = some (major, result)
  result_eq : result = decl.recursorResult ownerIdx minors.length owner

/-- Canonical constructor for `RecursorShape` from the single wrapped
telescope produced by recursor generation. -/
def VInductDecl.RecursorShape.ofWrapped
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    {ownerIdx : Nat} {params motives minors indices major : List VExpr}
    {result : VExpr}
    (owner_lt : ownerIdx < decl.types.length)
    (owner_eq : decl.types[ownerIdx] = owner)
    (name : recursor.name = decl.recursorName owner)
    (uvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1)
    (hparams : params.length = decl.nparams)
    (hmotives : motives.length = decl.types.length)
    (hminors : minors.length = decl.ownedConstructors.length)
    (hindices : indices.length = owner.numIndices)
    (hmajor : major.length = 1)
    (htype : recursor.type = VExpr.wrapForalls
      (params ++ motives ++ minors ++ indices ++ major) result)
    (hresult : result = decl.recursorResult ownerIdx minors.length owner) :
    decl.RecursorShape owner recursor := by
  refine {
    ownerIdx, owner_lt, owner_eq, name, uvars, params, motives, minors, indices,
    major
    afterParams := VExpr.wrapForalls (motives ++ minors ++ indices ++ major) result
    afterMotives := VExpr.wrapForalls (minors ++ indices ++ major) result
    afterMinors := VExpr.wrapForalls (indices ++ major) result
    afterIndices := VExpr.wrapForalls major result
    result
    params_take := ?_
    motives_take := ?_
    minors_take := ?_
    indices_take := ?_
    major_take := ?_
    result_eq := hresult }
  · rw [← hparams]
    rw [htype]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append params
        (motives ++ minors ++ indices ++ major) result
  · rw [← hmotives]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append motives
        (minors ++ indices ++ major) result
  · rw [← hminors]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append minors (indices ++ major) result
  · rw [← hindices]
    exact VExpr.takeForalls_wrapForalls_append indices major result
  · rw [← hmajor]
    exact VExpr.takeForalls_wrapForalls major result

/-- Shape of a restored primary recursor for a nested declaration.  Lowering
appends auxiliary families and constructors to the mutual block, so their
motives and minors remain in the restored primary telescope.  The original
source families and constructors form prefixes of those two groups; the
source owner keeps its original motive position. -/
structure VInductDecl.NestedRecursorShape (decl : VInductDecl)
    (owner : VInductiveType) (recursor : VConstVal) where
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  owner_eq : decl.types[ownerIdx] = owner
  name : recursor.name = decl.recursorName owner
  uvars : recursor.uvars = decl.uvars ∨ recursor.uvars = decl.uvars + 1
  params : List VExpr
  motives : List VExpr
  minors : List VExpr
  indices : List VExpr
  major : List VExpr
  source_motives : decl.types.length ≤ motives.length
  source_minors : decl.ownedConstructors.length ≤ minors.length
  afterParams : VExpr
  afterMotives : VExpr
  afterMinors : VExpr
  afterIndices : VExpr
  result : VExpr
  params_take : recursor.type.takeForalls decl.nparams =
    some (params, afterParams)
  motives_take : afterParams.takeForalls motives.length =
    some (motives, afterMotives)
  minors_take : afterMotives.takeForalls minors.length =
    some (minors, afterMinors)
  indices_take : afterMinors.takeForalls owner.numIndices =
    some (indices, afterIndices)
  major_take : afterIndices.takeForalls 1 = some (major, result)
  result_eq : result = decl.recursorResultWithCounts ownerIdx
    motives.length minors.length owner

/-- Canonical constructor for the nested recursor shape from its complete
restored telescope. -/
def VInductDecl.NestedRecursorShape.ofWrapped
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    {ownerIdx : Nat} {params motives minors indices major : List VExpr}
    {result : VExpr}
    (owner_lt : ownerIdx < decl.types.length)
    (owner_eq : decl.types[ownerIdx] = owner)
    (name : recursor.name = decl.recursorName owner)
    (uvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1)
    (hparams : params.length = decl.nparams)
    (hsourceMotives : decl.types.length ≤ motives.length)
    (hsourceMinors : decl.ownedConstructors.length ≤ minors.length)
    (hindices : indices.length = owner.numIndices)
    (hmajor : major.length = 1)
    (htype : recursor.type = VExpr.wrapForalls
      (params ++ motives ++ minors ++ indices ++ major) result)
    (hresult : result = decl.recursorResultWithCounts ownerIdx
      motives.length minors.length owner) :
    decl.NestedRecursorShape owner recursor := by
  refine {
    ownerIdx, owner_lt, owner_eq, name, uvars, params, motives, minors, indices,
    major, source_motives := hsourceMotives, source_minors := hsourceMinors
    afterParams := VExpr.wrapForalls (motives ++ minors ++ indices ++ major) result
    afterMotives := VExpr.wrapForalls (minors ++ indices ++ major) result
    afterMinors := VExpr.wrapForalls (indices ++ major) result
    afterIndices := VExpr.wrapForalls major result
    result
    params_take := ?_
    motives_take := ?_
    minors_take := ?_
    indices_take := ?_
    major_take := ?_
    result_eq := hresult }
  · rw [← hparams, htype]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append params
        (motives ++ minors ++ indices ++ major) result
  · simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append motives
        (minors ++ indices ++ major) result
  · simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append minors
        (indices ++ major) result
  · rw [← hindices]
    exact VExpr.takeForalls_wrapForalls_append indices major result
  · rw [← hmajor]
    exact VExpr.takeForalls_wrapForalls major result

/-- Ordinary recursors are the zero-auxiliary special case of nested
recursors. -/
def VInductDecl.RecursorShape.toNested
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    (H : decl.RecursorShape owner recursor) :
    decl.NestedRecursorShape owner recursor where
  ownerIdx := H.ownerIdx
  owner_lt := H.owner_lt
  owner_eq := H.owner_eq
  name := H.name
  uvars := H.uvars
  params := H.params
  motives := H.motives
  minors := H.minors
  indices := H.indices
  major := H.major
  source_motives := Nat.le_of_eq
    (VExpr.takeForalls_domains_length H.motives_take).symm
  source_minors := Nat.le_of_eq
    (VExpr.takeForalls_domains_length H.minors_take).symm
  afterParams := H.afterParams
  afterMotives := H.afterMotives
  afterMinors := H.afterMinors
  afterIndices := H.afterIndices
  result := H.result
  params_take := H.params_take
  motives_take := by
    rw [VExpr.takeForalls_domains_length H.motives_take]
    exact H.motives_take
  minors_take := by
    rw [VExpr.takeForalls_domains_length H.minors_take]
    exact H.minors_take
  indices_take := H.indices_take
  major_take := H.major_take
  result_eq := by
    rw [VExpr.takeForalls_domains_length H.motives_take]
    simpa [VInductDecl.recursorResult] using H.result_eq

/-- Reinterpret an expanded nested-recursor telescope at a compatible source
declaration.  This is the declarative lowering boundary: auxiliary motives
and minors remain in the telescope, while the source declaration supplies
the original family prefix, universe/parameter metadata, and owner. -/
def VInductDecl.NestedRecursorShape.ofCompatible
    {loweredDecl sourceDecl : VInductDecl}
    {loweredOwner sourceOwner : VInductiveType} {recursor : VConstVal}
    (H : loweredDecl.NestedRecursorShape loweredOwner recursor)
    (howner : H.ownerIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[H.ownerIdx] = sourceOwner)
    (hname : recursor.name = sourceDecl.recursorName sourceOwner)
    (huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (hnparams : sourceDecl.nparams = loweredDecl.nparams)
    (hmotives : sourceDecl.types.length ≤ H.motives.length)
    (hminors : sourceDecl.ownedConstructors.length ≤ H.minors.length)
    (hindices : sourceOwner.numIndices = loweredOwner.numIndices) :
    sourceDecl.NestedRecursorShape sourceOwner recursor where
  ownerIdx := H.ownerIdx
  owner_lt := howner
  owner_eq := hownerEq
  name := hname
  uvars := huvars
  params := H.params
  motives := H.motives
  minors := H.minors
  indices := H.indices
  major := H.major
  source_motives := hmotives
  source_minors := hminors
  afterParams := H.afterParams
  afterMotives := H.afterMotives
  afterMinors := H.afterMinors
  afterIndices := H.afterIndices
  result := H.result
  params_take := by simpa [hnparams] using H.params_take
  motives_take := H.motives_take
  minors_take := H.minors_take
  indices_take := by simpa [hindices] using H.indices_take
  major_take := H.major_take
  result_eq := by
    rw [H.result_eq]
    simp only [VInductDecl.recursorResultWithCounts]
    rw [hindices]

/-- One declarative iota equation. The left-hand side is a recursor whose final
argument is the matching constructor application. The right-hand side may call
any sibling recursor in a mutual block, but only on explicitly identified
constructor fields. Typing of the complete equation is supplied separately by
`VInductBlock.WF`. -/
structure VInductDecl.IotaRule (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_name : recursor.name = decl.recursorName owner
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + (ctorArgs.length - decl.nparams)
  recursiveFields : List (decl.RecursiveField env)
  fieldPositions : List Nat
  fieldPositions_eq : fieldPositions = recursiveFields.map (·.fieldIndex)
  fieldPositions_ordered : fieldPositions.Pairwise (· < ·)
  fields_at_positions : ∀ field ∈ recursiveFields,
    ∃ h : field.fieldIndex < (ctorArgs.drop decl.nparams).length,
      field.arg = (ctorArgs.drop decl.nparams)[field.fieldIndex]'h
  recursiveArgs : List VExpr
  recursiveArgs_eq : recursiveArgs = recursiveFields.map (·.arg)
  recursive_args : List.Sublist recursiveArgs (ctorArgs.drop decl.nparams)
  fieldVars : List Nat
  fieldVars_eq : fieldVars =
    recursiveArgs.filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  minorVar : Nat
  minor_in_scope : minorVar < domains.length
  rhsArgs : List VExpr
  rhs_spine : rhsBody.getAppFnArgs = (.bvar minorVar, rhsArgs)
  field_args : rhsArgs.take (ctorArgs.length - decl.nparams) =
    ctorArgs.drop decl.nparams
  recursive_results :
    (rhsArgs.drop (ctorArgs.length - decl.nparams)).length = recursiveArgs.length
  rhs_guarded : rhsBody.GuardedIota (block.recursors.map (·.name)) fieldVars 0

/-- A constructor field selected by a restored nested equation.  Unlike
`RecursiveField`, this record does not claim that the source field has a
direct mutual-family head: a genuinely nested field may instead be consumed
by one of the restored auxiliary recursors. -/
structure VInductDecl.NestedIotaField where
  fieldIndex : Nat
  arg : VExpr

/-- Declarative iota equation for a restored primary nested recursor.

Lowering-generated motives and minors remain in the restored primary
recursor telescope, so their exact counts come from the same
`NestedRecursorShape` witness as the recursor itself.  Recursive arguments are
recorded by their ordered constructor-field positions rather than by
`RecursiveArg`: the latter deliberately recognizes only direct mutual-family
heads and therefore cannot classify fields such as `List Tree`.

Typing of the equation remains an independent obligation of
`VInductBlock.WF`; together with `rhs_guarded`, it ensures that every selected
field is used only by a well-typed restored recursor call. -/
structure VInductDecl.NestedIotaRule
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_shape : decl.NestedRecursorShape owner recursor
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams +
    recursor_shape.motives.length + recursor_shape.minors.length +
      owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams +
    recursor_shape.motives.length + recursor_shape.minors.length +
      (ctorArgs.length - decl.nparams)
  recursiveFields : List NestedIotaField
  fieldPositions : List Nat
  fieldPositions_eq : fieldPositions = recursiveFields.map (·.fieldIndex)
  fieldPositions_ordered : fieldPositions.Pairwise (· < ·)
  fields_at_positions : ∀ field ∈ recursiveFields,
    ∃ h : field.fieldIndex < (ctorArgs.drop decl.nparams).length,
      field.arg = (ctorArgs.drop decl.nparams)[field.fieldIndex]'h
  recursiveArgs : List VExpr
  recursiveArgs_eq : recursiveArgs = recursiveFields.map (·.arg)
  recursive_args : List.Sublist recursiveArgs (ctorArgs.drop decl.nparams)
  fieldVars : List Nat
  fieldVars_eq : fieldVars = recursiveArgs.filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  minorVar : Nat
  minor_in_scope : minorVar < domains.length
  rhsArgs : List VExpr
  rhs_spine : rhsBody.getAppFnArgs = (.bvar minorVar, rhsArgs)
  field_args : rhsArgs.take (ctorArgs.length - decl.nparams) =
    ctorArgs.drop decl.nparams
  recursive_results :
    (rhsArgs.drop (ctorArgs.length - decl.nparams)).length =
      recursiveArgs.length
  rhs_guarded : rhsBody.GuardedIota
    (block.recursors.map (·.name)) fieldVars 0

/-- Reinterpret an ordinary equation from an expanded lowering declaration as
one source nested equation.  The source nested-recursor shape fixes the
retained auxiliary telescope; constructor identity is needed only at the
constant-name boundary because the restored source constructor may have a
different abstract type. -/
def VInductDecl.IotaRule.toNestedOfCompatible
    {env : VEnv} {loweredDecl sourceDecl : VInductDecl}
    {loweredBlock sourceBlock : VInductBlock}
    {loweredOwner sourceOwner : VInductiveType}
    {loweredCtor sourceCtor : VConstVal} {rule : VDefEq}
    (H : loweredDecl.IotaRule env loweredBlock loweredOwner loweredCtor rule)
    (sourceRecursor : VConstVal)
    (Hshape : sourceDecl.NestedRecursorShape sourceOwner sourceRecursor)
    (hrecursorMem : sourceRecursor ∈ sourceBlock.recursors)
    (hrecursorNames : sourceBlock.recursors.map (·.name) =
      loweredBlock.recursors.map (·.name))
    (hrecursorName : sourceRecursor.name = H.recursor.name)
    (hrecursorUvars : sourceRecursor.uvars = H.recursor.uvars)
    (huvars : sourceDecl.uvars = loweredDecl.uvars)
    (hnparams : sourceDecl.nparams = loweredDecl.nparams)
    (hindices : sourceOwner.numIndices = loweredOwner.numIndices)
    (hmotives : Hshape.motives.length = loweredDecl.types.length)
    (hminors : Hshape.minors.length =
      loweredDecl.ownedConstructors.length)
    (hctorName : sourceCtor.name = loweredCtor.name) :
    sourceDecl.NestedIotaRule sourceBlock sourceOwner sourceCtor rule := by
  let fields : List VInductDecl.NestedIotaField :=
    H.recursiveFields.map fun field =>
      { fieldIndex := field.fieldIndex, arg := field.arg }
  refine {
    recursor := sourceRecursor
    recursor_mem := hrecursorMem
    recursor_shape := Hshape
    rule_uvars := H.rule_uvars.trans hrecursorUvars.symm
    domains := H.domains
    lhsBody := H.lhsBody
    rhsBody := H.rhsBody
    typeBody := H.typeBody
    lhs_wrapped := H.lhs_wrapped
    rhs_wrapped := H.rhs_wrapped
    type_wrapped := H.type_wrapped
    recursorLevels := H.recursorLevels
    leadingArgs := H.leadingArgs
    ctorLevels := H.ctorLevels
    ctorArgs := H.ctorArgs
    lhs_pattern := ?_
    recursor_levels := H.recursor_levels.trans hrecursorUvars.symm
    ctor_levels := by simpa [huvars] using H.ctor_levels
    leading_arity := by
      simpa [hnparams, hmotives, hminors, hindices] using H.leading_arity
    constructor_arity := by simpa [hnparams] using H.constructor_arity
    parameter_args := by simpa [hnparams] using H.parameter_args
    domains_arity := by
      simpa [hnparams, hmotives, hminors] using H.domains_arity
    recursiveFields := fields
    fieldPositions := H.fieldPositions
    fieldPositions_eq := ?_
    fieldPositions_ordered := H.fieldPositions_ordered
    fields_at_positions := ?_
    recursiveArgs := H.recursiveArgs
    recursiveArgs_eq := ?_
    recursive_args := by simpa [hnparams] using H.recursive_args
    fieldVars := H.fieldVars
    fieldVars_eq := H.fieldVars_eq
    fields_in_scope := H.fields_in_scope
    minorVar := H.minorVar
    minor_in_scope := H.minor_in_scope
    rhsArgs := H.rhsArgs
    rhs_spine := H.rhs_spine
    field_args := by simpa [hnparams] using H.field_args
    recursive_results := by simpa [hnparams] using H.recursive_results
    rhs_guarded := by simpa [hrecursorNames] using H.rhs_guarded }
  · simpa [hrecursorName, hctorName] using H.lhs_pattern
  · simpa [fields, Function.comp_def] using H.fieldPositions_eq
  · intro field hfield
    rcases List.mem_map.mp hfield with ⟨source, hsource, rfl⟩
    simpa [hnparams] using H.fields_at_positions source hsource
  · simpa [fields, Function.comp_def] using H.recursiveArgs_eq

def VInductDecl.IotaRule.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env')
    (H : decl.IotaRule env block owner ctor rule) :
    decl.IotaRule env' block owner ctor rule := by
  let fields := H.recursiveFields.map fun field => field.mono henv
  refine { H with
    recursiveFields := fields
    fieldPositions_eq := ?_
    fields_at_positions := ?_
    recursiveArgs_eq := ?_ }
  · rw [H.fieldPositions_eq]
    simp [fields, VInductDecl.RecursiveField.mono]
  · intro field hfield
    rcases List.mem_map.mp hfield with ⟨source, hsource, rfl⟩
    rcases H.fields_at_positions source hsource with ⟨hindex, harg⟩
    exact ⟨hindex, harg⟩
  · rw [H.recursiveArgs_eq]
    simp [fields, VInductDecl.RecursiveField.mono]

/-- Independent ordinary/mutual compilation interface. It is deliberately
stronger than mere well-typedness: source constants are preserved exactly,
recursor names and arities are constrained, and constructor/rule coverage is
total and ordered. -/
structure VInductDecl.OrdinaryCompilation
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  recursors : List.Forall₂ (fun type recursor =>
    Nonempty (decl.RecursorShape type recursor))
    decl.types block.recursors
  rules : ∃ envTypes envCtors,
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.IotaRule envCtors block owned.1 owned.2 rule))
      decl.ownedConstructors block.rules
  names : List.Nodup ((block.types ++ block.ctors ++ block.recursors).map (·.name))

/-- Compilation interface for a source declaration containing nested
occurrences. Restoration keeps the source type and constructor constants
exactly, retains the ordinary primary recursors/rules, and may add a sequence
of guarded auxiliary recursors under deterministic `main.recN` names. -/
structure VInductDecl.NestedCompilation
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) where
  main : VInductiveType
  rest : List VInductiveType
  types_source : decl.types = main :: rest
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  primaryRecursors : List VConstVal
  auxiliaryRecursors : List VConstVal
  recursors_eq : block.recursors = primaryRecursors ++ auxiliaryRecursors
  primary_recursors : List.Forall₂ (fun type recursor =>
    Nonempty (decl.NestedRecursorShape type recursor))
    decl.types primaryRecursors
  primaryRules : List VDefEq
  auxiliaryRules : List VDefEq
  rules_eq : block.rules = primaryRules ++ auxiliaryRules
  primary_rules : ∃ envTypes envCtors,
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.NestedIotaRule block owned.1 owned.2 rule))
      decl.ownedConstructors primaryRules
  auxiliary_guarded : ∀ rule ∈ auxiliaryRules,
    rule.rhs.GuardedRuleRhs (block.recursors.map (·.name))
  names : List.Nodup ((block.types ++ block.ctors ++ block.recursors).map (·.name))

/-- Pure abstract compilation, kept separate from the executable
`AddInductive` implementation. Nested compilation will enter through a second
constructor after proving that lowering yields an ordinary compilation. -/
inductive VInductDecl.CompilesTo (env : VEnv) : VInductDecl → VInductBlock → Prop
  | ordinary : VInductDecl.OrdinaryCompilation env decl block →
      VInductDecl.CompilesTo env decl block
  | nested : VInductDecl.NestedCompilation env decl block →
      VInductDecl.CompilesTo env decl block

theorem VInductDecl.OrdinaryCompilation.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env')
    (Hblock : block.WF env')
    (H : decl.OrdinaryCompilation env block) :
    decl.OrdinaryCompilation env' block := by
  rcases H.rules with
    ⟨oldTypes, oldCtors, holdTypes, holdCtors, holdRules⟩
  rcases Hblock with
    ⟨envTypes, envCtors, _envRecursors, htypes, hctors, _hrecs, _⟩
  have htypesLE := VEnv.addConstVals_mono henv holdTypes htypes
  have hctorsLE := VEnv.addConstVals_mono htypesLE holdCtors hctors
  exact { H with
    rules := ⟨envTypes, envCtors, htypes, hctors,
      Lean4Lean.List.Forall₂.imp
      (fun _ _ h => let ⟨rule⟩ := h; ⟨rule.mono hctorsLE⟩)
      holdRules⟩ }

theorem VInductDecl.CompilesTo.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env')
    (Hblock : block.WF env')
    (H : decl.CompilesTo env block) : decl.CompilesTo env' block := by
  cases H with
  | ordinary H => exact .ordinary (H.mono henv Hblock)
  | nested H =>
    rcases H.primary_rules with
      ⟨_oldTypes, _oldCtors, _holdTypes, _holdCtors, holdRules⟩
    rcases Hblock with
      ⟨envTypes, envCtors, _envRecursors, htypes, hctors, _hrecs, _⟩
    exact .nested { H with
      primary_rules := ⟨envTypes, envCtors, htypes, hctors,
        holdRules⟩ }

theorem VInductDecl.CompilesTo.types
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    block.types = decl.typeConstants := by
  cases H with
  | ordinary H => exact H.types
  | nested H => exact H.types

theorem VInductDecl.CompilesTo.ctors
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    block.ctors = decl.constructorConstants := by
  cases H with
  | ordinary H => exact H.ctors
  | nested H => exact H.ctors

/-! ## Ordinary-or-nested formation derivations

Nested formation refers only to prior, finitely derived installed inductive
blocks. Keeping installation provenance in the same mutual derivation as
formation avoids both an uncheckable environment lookup and a definitional
cycle through `AddInduct`. -/

/-- Exact construction of one direct auxiliary constructor before its own
body is recursively lowered. -/
structure VInductDecl.DirectAuxConstructor
    (env : VEnv) (U : Nat)
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (containerFamily auxiliaryFamily : VInductiveType)
    (source target : VConstVal) : Prop where
  name : target.name = source.name.replacePrefix containerFamily.name
    auxiliaryFamily.name
  uvars : target.uvars = auxiliaryFamily.uvars
  type : env.IsDefEqU U [] target.type
    (VExpr.wrapForalls sourceParams
      (VExpr.instantiateForallPrefix (source.type.instL levels) baseArgs))

/-- A rigid head used to package two corresponding argument lists as one
expression relation.  Unlike a bound variable, it is stable when the
surrounding constructor telescope is lifted. -/
def VInductDecl.nestedTrailingMarker : VExpr :=
  .const `_nested.trailing []

mutual

/-- Formation evidence is either the ordinary judgment or a finite nested
expansion into an independently ordinary well-formed declaration. -/
inductive VInductDecl.FormationEvidence : VEnv → VInductDecl → Prop
  | ordinary {env decl} : VInductDecl.FormationWF env decl →
      VInductDecl.FormationEvidence env decl
  | nested {base env decl} : VInductDecl.NestedFormationWF base decl →
      base ≤ env →
      VInductDecl.FormationEvidence env decl

/-- Cycle-free provenance for a prior container block. The prior declaration
has its own finite source/formation derivation, compiles to the exact block,
and that well-formed block occurs below the ambient environment. -/
inductive VEnv.InstalledInductCertificate : VEnv → VInductDecl → Prop
  | intro {env container base block installed} :
      VInductDecl.SourceWF base container →
      VInductDecl.FormationEvidence base container →
      container.CompilesTo base block →
      block.WF base →
      VInductBlock.install base block = some installed →
      installed ≤ env →
      VEnv.InstalledInductCertificate env container

/-- One legal maximal nested-application replacement. The generated family
is an exact parameter specialization of a family in a previously installed
container block, and its direct constructors are the corresponding exact
specializations with deterministic production names.  The executable
lowering certificate separately retains that some concrete parameter syntax
mentions the finite lowering queue.  That occurrence is intentionally not a
premise here: `TrExprS` erases metadata and let types/values and interprets
projections opaquely, so a concrete occurrence need not survive in `VExpr`.
Such an erased-only occurrence may generate a semantically unused auxiliary;
this remains sound because the prior-container specialization is exact and
ordinary formation checks the complete expanded finite block. -/
inductive VInductDecl.NestedAuxiliarySource :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | intro {env sourceTypesEnv source generated depth input output container
      containerFamily auxiliaryFamily sourceParams baseArgs levels
      auxiliaryLevels inputBaseArgs sourceTrailing targetTrailing} :
      env.addConstVals source.typeConstants = some sourceTypesEnv →
      VEnv.InstalledInductCertificate sourceTypesEnv container →
      containerFamily ∈ container.types →
      auxiliaryFamily ∈ generated →
      sourceParams.length = source.nparams →
      baseArgs.length = container.nparams →
      (∀ arg ∈ baseArgs, arg.ClosedN source.nparams) →
      levels.length = container.uvars →
      (∀ level ∈ levels, level.WF source.uvars) →
      auxiliaryFamily.uvars = source.uvars →
      sourceTypesEnv.IsDefEqU source.uvars [] auxiliaryFamily.type
        (VExpr.wrapForalls sourceParams
          (VExpr.instantiateForallPrefix
            (containerFamily.type.instL levels) baseArgs)) →
      List.Forall₂
        (VInductDecl.DirectAuxConstructor sourceTypesEnv source.uvars sourceParams
          baseArgs levels containerFamily auxiliaryFamily)
        containerFamily.ctors auxiliaryFamily.ctors →
      auxiliaryLevels.length = source.uvars →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker
          (baseArgs.map (fun arg => arg.liftN depth 0)))
        (VExpr.mkApps VInductDecl.nestedTrailingMarker inputBaseArgs) →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceTrailing)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker targetTrailing) →
      input = VExpr.mkApps (.const containerFamily.name levels)
        (inputBaseArgs ++ sourceTrailing) →
      output = VExpr.mkApps (.const auxiliaryFamily.name auxiliaryLevels)
        (source.paramVars depth ++ targetTrailing) →
      VInductDecl.NestedAuxiliarySource env source generated depth input output

/-- Specialized structural expansion used inside the mutual formation
derivation. It has a forgetful map to `VExpr.NestedExprExpansion`; spelling it
out here is required by Lean's strict-positivity checker for the mutual leaf. -/
inductive VInductDecl.NestedExprWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | hit {env source generated depth relativeDepth input output} :
      depth = source.nparams + relativeDepth →
      VInductDecl.NestedAuxiliarySource env source generated relativeDepth
        input output →
      VInductDecl.NestedExprWFExpansion env source generated depth input output
  | bvar {env source generated index depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.bvar index) (.bvar index)
  | sort {env source generated level depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.sort level) (.sort level)
  | const {env source generated name levels depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.const name levels) (.const name levels)
  | app {env source generated depth sourceFn targetFn sourceArg targetArg} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceFn targetFn →
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceArg targetArg →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.app sourceFn sourceArg) (.app targetFn targetArg)
  | lam {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.lam sourceDomain sourceBody) (.lam targetDomain targetBody)
  | forallE {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)
  | projection {env source generated depth sourceMajor targetMajor
      sourceTarget targetTarget} :
      VExpr.ProjectionSupportExpansion sourceMajor sourceTarget →
      VExpr.ProjectionSupportExpansion targetMajor targetTarget →
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceMajor targetMajor →
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceTarget targetTarget

/-- Strictly-positive counterpart of `NestedForallPrefixExpansion` for the
mutually defined nested-formation leaf. -/
inductive VInductDecl.NestedForallPrefixWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → Nat → VExpr → VExpr → Prop
  | nil
      (Hbody : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth 0
        sourceBody targetBody
  | cons
      (Hdomain : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain)
      (Hbody : VInductDecl.NestedForallPrefixWFExpansion env source generated
        (depth + 1) arity sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth
        (arity + 1) (.forallE sourceDomain sourceBody)
          (.forallE targetDomain targetBody)

/-- Ordered constructor expansion without nesting the mutually defined leaf
inside an external `List.Forall₂`. -/
inductive VInductDecl.NestedConstructorWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VConstVal → List VConstVal → Prop
  | nil {env source generated} :
      VInductDecl.NestedConstructorWFExpansions env source generated [] []
  | cons {env source generated sourceCtor targetCtor sourceCtors targetCtors} :
      targetCtor.name = sourceCtor.name →
      targetCtor.uvars = sourceCtor.uvars →
      VInductDecl.NestedForallPrefixWFExpansion env source generated 0
        source.nparams sourceCtor.type targetCtor.type →
      VInductDecl.NestedExprWFExpansion env source generated 0 sourceCtor.type
        targetCtor.type →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceCtors targetCtors →
      VInductDecl.NestedConstructorWFExpansions env source generated
        (sourceCtor :: sourceCtors) (targetCtor :: targetCtors)

/-- Ordered family expansion for the initial mutual block followed by the
direct, unlowered auxiliary queue. -/
inductive VInductDecl.NestedTypeWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VInductiveType → List VInductiveType → Prop
  | nil {env source generated} :
      VInductDecl.NestedTypeWFExpansions env source generated [] []
  | cons {env source generated sourceType targetType sourceTypes targetTypes} :
      targetType.name = sourceType.name →
      targetType.uvars = sourceType.uvars →
      env.IsDefEqU source.uvars [] sourceType.type targetType.type →
      targetType.numIndices = sourceType.numIndices →
      targetType.resultLevel = sourceType.resultLevel →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceType.ctors targetType.ctors →
      VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
        targetTypes →
      VInductDecl.NestedTypeWFExpansions env source generated
        (sourceType :: sourceTypes) (targetType :: targetTypes)

/-- A nested declaration is formed by expanding the original families and a
finite queue of direct auxiliary sources into a declaration satisfying the
ordinary source and formation judgments. -/
inductive VInductDecl.NestedFormationWF : VEnv → VInductDecl → Prop
  | intro {env source expanded generated} :
      VInductDecl.SourceWF env expanded →
      VInductDecl.FormationWF env expanded →
      VInductDecl.SourceParameterWF env source →
      expanded.uvars = source.uvars →
      expanded.nparams = source.nparams →
      expanded.isUnsafe = source.isUnsafe →
      VInductDecl.NestedTypeWFExpansions env source generated
        (source.types ++ generated) expanded.types →
      VInductDecl.NestedFormationWF env source

end

/-- Constructor expressions count every enclosing forall binder, whereas
`NestedAuxiliarySource` counts only constructor-field binders below the common
parameter prefix.  This wrapper is the explicit boundary between those two
depth conventions. -/
def VInductDecl.NestedAuxiliarySourceAbsolute
    (env : VEnv) (source : VInductDecl)
    (generated : List VInductiveType) (depth : Nat)
    (input output : VExpr) : Prop :=
  ∃ relativeDepth,
    depth = source.nparams + relativeDepth ∧
    VInductDecl.NestedAuxiliarySource env source generated relativeDepth
      input output


/-- Abstract well-formedness always retains the original source judgment;
formation is a finite ordinary-or-nested derivation. -/
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.SourceWF env ∧ decl.FormationEvidence env

theorem VInductDecl.WF.originalConstructors
    {env : VEnv} {decl : VInductDecl}
    (H : decl.WF env) :
    ∃ envTypes,
      env.addConstVals decl.typeConstants = some envTypes ∧
      ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes :=
  H.1.originalConstructors

/-- Forget the mutual positivity encoding and recover the reusable generic
expression carrier. -/
theorem VInductDecl.NestedExprWFExpansion.toNestedExprExpansion
    {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {depth : Nat} {input output : VExpr}
    (H : VInductDecl.NestedExprWFExpansion env source generated depth input
      output) :
    VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      depth input output := by
  exact VInductDecl.NestedExprWFExpansion.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun env source generated depth input output _ =>
      VExpr.NestedExprExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth input output)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun hdepth Hleaf _ => .hit ⟨_, hdepth, Hleaf⟩)
    (by exact .bvar)
    (by exact .sort)
    (by exact .const)
    (fun _ _ ihFn ihArg => .app ihFn ihArg)
    (fun _ _ ihDomain ihBody => .lam ihDomain ihBody)
    (fun _ _ ihDomain ihBody => .forallE ihDomain ihBody)
    (fun Hsource Htarget _ ihMajor =>
      .projection Hsource Htarget ihMajor)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    H

/-- Forget the specialized constructor-list encoding. -/
theorem VInductDecl.NestedConstructorWFExpansions.toForall₂
    {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {sourceCtors targetCtors : List VConstVal}
    (H : VInductDecl.NestedConstructorWFExpansions env source generated
      sourceCtors targetCtors) :
    List.Forall₂
      (VInductDecl.NestedConstructorExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        source.nparams)
      sourceCtors targetCtors := by
  exact VInductDecl.NestedConstructorWFExpansions.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun env source generated depth input output _ =>
      VExpr.NestedExprExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth input output)
    (motive_5 := fun env source generated depth arity input output _ =>
      VExpr.NestedForallPrefixExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth arity input output)
    (motive_6 := fun env source generated sourceCtors targetCtors _ =>
      List.Forall₂
        (VInductDecl.NestedConstructorExpansion
          (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
          source.nparams)
        sourceCtors targetCtors)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun hdepth Hleaf _ => .hit ⟨_, hdepth, Hleaf⟩)
    (by exact .bvar)
    (by exact .sort)
    (by exact .const)
    (fun _ _ ihFn ihArg => .app ihFn ihArg)
    (fun _ _ ihDomain ihBody => .lam ihDomain ihBody)
    (fun _ _ ihDomain ihBody => .forallE ihDomain ihBody)
    (fun Hsource Htarget _ ihMajor =>
      .projection Hsource Htarget ihMajor)
    (fun _ ihBody => .nil ihBody)
    (fun _ _ ihDomain ihBody => .cons ihDomain ihBody)
    (by exact .nil)
    (fun hname huvars _ _ _ ihParams ihType ihTail =>
      .cons ⟨hname, huvars, ihParams, ihType⟩ ihTail)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    H

/-- Forget the specialized family-list encoding. -/
theorem VInductDecl.NestedTypeWFExpansions.toForall₂
    {env : VEnv} {source : VInductDecl}
    {generated sourceTypes targetTypes : List VInductiveType}
    (H : VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
      targetTypes) :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
      sourceTypes targetTypes := by
  exact VInductDecl.NestedTypeWFExpansions.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun env source generated depth input output _ =>
      VExpr.NestedExprExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth input output)
    (motive_5 := fun env source generated depth arity input output _ =>
      VExpr.NestedForallPrefixExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth arity input output)
    (motive_6 := fun env source generated sourceCtors targetCtors _ =>
      List.Forall₂
        (VInductDecl.NestedConstructorExpansion
          (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
          source.nparams)
        sourceCtors targetCtors)
    (motive_7 := fun env source generated sourceTypes targetTypes _ =>
      List.Forall₂
        (VInductDecl.NestedTypeExpansion env source
          (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
        sourceTypes targetTypes)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun hdepth Hleaf _ => .hit ⟨_, hdepth, Hleaf⟩)
    (by exact .bvar)
    (by exact .sort)
    (by exact .const)
    (fun _ _ ihFn ihArg => .app ihFn ihArg)
    (fun _ _ ihDomain ihBody => .lam ihDomain ihBody)
    (fun _ _ ihDomain ihBody => .forallE ihDomain ihBody)
    (fun Hsource Htarget _ ihMajor =>
      .projection Hsource Htarget ihMajor)
    (fun _ ihBody => .nil ihBody)
    (fun _ _ ihDomain ihBody => .cons ihDomain ihBody)
    (by exact .nil)
    (fun hname huvars _ _ _ ihParams ihType ihTail =>
      .cons ⟨hname, huvars, ihParams, ihType⟩ ihTail)
    (by exact .nil)
    (fun hname huvars htype hindices hlevel _ _ ihCtors ihTail =>
      .cons ⟨hname, huvars, htype, hindices, hlevel, ihCtors⟩ ihTail)
    (by intros; trivial)
    H

theorem VEnv.InstalledInductCertificate.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : VEnv.InstalledInductCertificate env decl) :
    VEnv.InstalledInductCertificate env' decl := by
  cases H with
  | intro hsource hformation hcompile hblock hinstall hle =>
    exact .intro hsource hformation hcompile hblock hinstall (hle.trans henv)


/-- Relational abstract environment extension for inductive declarations.
Unlike the old placeholder function, this exposes the compiled block witness
needed by the implementation-refinement proof. -/
inductive VEnv.AddInduct (env : VEnv) (decl : VInductDecl) : VEnv → Prop where
  | intro :
    decl.WF env →
    VInductDecl.CompilesTo env decl block →
    VInductBlock.WF env block →
    VInductBlock.install env block = some env' →
    VEnv.AddInduct env decl env'
