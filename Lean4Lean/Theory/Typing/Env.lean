import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

/-- Add a block of constants, without their defining equations. -/
def VEnv.addConsts (env : VEnv) (cis : List VDefVal) : Option VEnv :=
  cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env

/-- Add the defining equations of a block, after all of its constants. -/
def VEnv.addDefEqs (env : VEnv) (cis : List VDefVal) : VEnv :=
  cis.foldl (fun env ci => env.addDefEq ci.toDefEq) env

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  | mutualDef :
    (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' →
    (∀ ci ∈ cis, ci.WF env') →
    VDecl.WF env (.mutualDef cis) (env'.addDefEqs cis)
  | opaque :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct :
    decl.WF env →
    env.addInduct decl = some env' →
    VDecl.WF env (.induct decl) env'

/-- The constructor-and-projection prefix of an inductive declaration: `env'` is `env` extended
by the type formers and constructors of `decl` as fresh constants and by the projection entries
of its structures (`VInductDecl.addTypesCtorsProjs`), and `decl` satisfies in `env` the source
and formation judgments of `VInductDecl.WF`: headers and constructors typed, distinct names,
strict positivity (unless `decl.isUnsafe`) and the universe bound, for an ordinary declaration
or through a finite nested expansion. The recursors of `decl` play no role: neither the
judgments nor `addTypesCtorsProjs` read `decl.recs`. -/
structure VInductDecl.ProjectionStage (env : VEnv) (decl : VInductDecl) (env' : VEnv) :
    Prop where
  /-- The source judgment, as in `VInductDecl.WF.source`. -/
  source : decl.SourceWF env
  /-- The formation judgment, as in `VInductDecl.WF.formation`. -/
  formation : decl.FormationWF env
  /-- Stages 0 to 2 of `VEnv.addInduct`, from `env`. -/
  install : decl.addTypesCtorsProjs env = some env'

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)
  /-- The constructor-and-projection prefix of an inductive declaration
  (`VInductDecl.ProjectionStage`) extends a well-formed environment to a well-formed
  environment. The executable checks the generated recursors of a declaration in this
  environment, before `VInductDecl.WF` is known, and every checker theorem requires a
  well-formed environment. The stage introduces its own type formers and constructors and
  imposes the source and formation conditions of the full declaration, so it is the full
  declaration step `VDecl.WF.induct` without the recursor and ι-rule stages, and the history
  records it as `.induct decl`: an entry `.induct decl` of a history stands for the whole
  declaration or for this prefix of it. -/
  | inductProjections {env} {decl : VInductDecl} :
    decl.ProjectionStage env env' → env.WF' ds → env'.WF' (.induct decl :: ds)

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env

/-- The constructor-and-projection prefix of an inductive declaration over a well-formed
environment is well formed. -/
theorem VEnv.WF.inductProjections {env env' : VEnv} {decl : VInductDecl}
    (henv : env.WF) (hstage : decl.ProjectionStage env env') : env'.WF :=
  let ⟨_, henv⟩ := henv; ⟨_, .inductProjections hstage henv⟩

/-- `env₀` is the environment reached by a prefix of `env`'s declaration list: `env` extends
`env₀` by a run of well-formed declarations. The environments the strengthening argument
walks through (`VEnv.WF.strong`) are these and their extensions by constants alone. -/
inductive VEnv.WFPrefix : VEnv → VEnv → Prop where
  | rfl : VEnv.WFPrefix env env
  | decl {d} : VDecl.WF env d env' → VEnv.WFPrefix env env₀ → VEnv.WFPrefix env' env₀
  /-- The constructor-and-projection prefix of an inductive declaration
  (`VEnv.WF'.inductProjections`) is a step of the history too. -/
  | inductProjections {decl : VInductDecl} :
    decl.ProjectionStage env env' → VEnv.WFPrefix env env₀ → VEnv.WFPrefix env' env₀

/-- A prefix of a prefix is a prefix. -/
theorem VEnv.WFPrefix.trans {env env₁ env₂ : VEnv}
    (h₁ : env.WFPrefix env₁) (h₂ : env₁.WFPrefix env₂) : env.WFPrefix env₂ := by
  induction h₁ with
  | rfl => exact h₂
  | decl hd _ ih => exact .decl hd (ih h₂)
  | inductProjections hs _ ih => exact .inductProjections hs (ih h₂)
