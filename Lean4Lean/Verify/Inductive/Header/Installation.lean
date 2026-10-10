import Lean4Lean.Verify.Inductive.Header.Check

/-! # Header installation: `declareInductiveTypes`

After the header traversal, `AddInductive.declareInductiveTypes` adds the kernel headers
(`inductiveTypeInfos`) to the environment, one checked name at a time. `HeaderEnvironment` is
the frozen interface of the resulting environment, indexed by the abstract declaration `decl`
the constructor phase will select (only its header data is constrained here);
`AddInductive.declareInductiveTypes.WF` is the boundary theorem.

Wave 2 scaffold: owned by the `Header/`+`Context/`+`Formation` agent (source branch:
`Header/{Declaration,Installation}.lean`, `Install/Headers.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The environment after `declareInductiveTypes`: the kernel headers are installed over the
source environment (`map_eq`, `fresh`), each translating to the abstract type former of `decl`
(`trHeaders`, the header half of `TrIndType`); the abstract header environment is the source
model with `decl`'s type constants (`typesAdded`); the parameters are still declared in the
context (`parameters`). -/
structure HeaderEnvironment (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  numNested : Nat
  /-- The kernel headers, exactly the executable's `inductiveTypeInfos`. -/
  infos : List InductiveVal
  infos_eq : infos = (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
    isUnsafe c.lparams).toList
  map_eq : outEnv.constants = insertConsts c.env.constants (infos.map .inductInfo)
  quotInit_eq : outEnv.quotInit = c.env.quotInit
  fresh : ∀ info ∈ infos, c.env.find? info.name = none
  uvars : decl.uvars = c.lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  /-- The source context and the context over the header environment share the main local
  context (the parameters). -/
  sourceContext : ContextWF c
  sourceContextVEnv : sourceContext.venv = sourceEnv
  context : ContextWF { c with env := outEnv }
  contextMLCtx : context.mlctx = sourceContext.mlctx
  typesAdded : sourceEnv.addConstVals decl.typeConstants = some context.venv
  headers : HeaderCertificate sourceEnv decl
  /-- Each kernel header translates to the abstract type former and lists the declaration's
  constructor names (the header half of `TrIndType`). -/
  trHeaders : List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
      TrConstVal c.safety sourceEnv (.inductInfo info) t.toVConstVal ∧
      info.ctors = t.ctors.map (·.name))
    infos decl.types
  /-- The source family types translate to the abstract type formers. -/
  trSources : List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
      TrSourceConst sourceEnv c.lparams source.name source.type t.toVConstVal ∧
      source.ctors.map (·.name) = t.ctors.map (·.name))
    indTypes.toList decl.types
  parameters : HeaderParameterContext context stats headers.params depth
  sourceParameters : HeaderParameterContext sourceContext stats headers.params depth
  /-- Every constructor a header of the source environment lists is present there. -/
  sourcePresent : ListedConstructorsPresent c.env

/-- The boundary theorem of header installation: in the context of a completed header phase,
`declareInductiveTypes` yields a header environment for every declaration the checked headers
describe. -/
theorem AddInductive.declareInductiveTypes.WF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c'.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe c'.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested isUnsafe c').WF
      fun headerEnv => ∀ decl : VInductDecl, P.headers.Describes decl →
        Nonempty (HeaderEnvironment c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes
          headerEnv) := by
  -- WAVE 2 STUB (Header/Context/Formation): the source branch's
  -- `HeaderDeclaration.toHeaderEnvironment` (`Install/Headers.lean`) and
  -- `declareInductiveTypes.installsHeadersAtomicWF`.
  have := hpresent; sorry

end VerifyInductive
end Lean4Lean
