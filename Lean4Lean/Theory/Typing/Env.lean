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
    VEnv.AddInduct env decl env' →
    VDecl.WF env (.induct decl) env'

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)
  | inductProjections {base envTypes envCtors : VEnv}
      {decl : VInductDecl} {block : VInductBlock} :
    VEnv.WF' baseDecls base →
    VEnv.WF' ds envCtors →
    decl.sourceNames.Nodup →
    (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) →
    block.types = decl.typeConstants →
    block.ctors = decl.constructorConstants →
    block.projections = decl.projectionEntries →
    base.addConstVals block.types = some envTypes →
    envTypes.addConstVals block.ctors = some envCtors →
    VEnv.WF' ds (envCtors.addProjections block.projections)

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env

/-- Register the projection table of one exact inductive prefix before its
recursors are installed.  Both the source base and the constructor-complete
environment retain independent declaration traces; the remaining premises
tie the new metadata to that precise prefix. -/
theorem VEnv.WF.inductProjections
    {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock}
    (hbase : base.WF) (hctorsWF : envCtors.WF)
    (hsource : decl.sourceNames.Nodup)
    (hconstructorUvars :
      ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    (envCtors.addProjections block.projections).WF := by
  rcases hbase with ⟨baseDecls, hbase⟩
  rcases hctorsWF with ⟨decls, hctorsWF⟩
  exact ⟨decls, .inductProjections hbase hctorsWF hsource
    hconstructorUvars htypesSource hctorsSource hprojections htypes hctors⟩
