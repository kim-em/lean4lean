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

open private Lean.Kernel.Environment.add from Lean.Environment

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

/-- The constructor names of a declaration are absent from an environment. The header
environment is a checking environment (`CheckingEnv.Valid`: a header lists only absent names or
its own constructors) only once the constructor names are known to be absent from it; the
executable checks this only when it declares the constructors, after checking their types, so
the constructor phase reads it off a successful `declareConstructors`
(`AddInductive.declareConstructors.namesAbsent`). -/
def ConstructorNamesAbsent (indTypes : Array InductiveType) (env : Environment) : Prop :=
  ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors, env.find? ctor.name = none

/-- The constructor fold of `declareConstructors` succeeds only on names absent from every
environment it extends. -/
theorem AddInductive.declareConstructors.ctorFoldAbsent
    (allowPrimitive : Bool) (mk : Nat → Constructor → ConstantInfo)
    (hmk : ∀ i ctor, (mk i ctor).name = ctor.name) (base : Environment) :
    ∀ (ctors : List Constructor) (cidx : Nat) (env : Environment), env.constants.WF →
      (∀ {n x}, base.find? n = some x → env.find? n = some x) →
      (ctors.foldlM (init := (cidx, env)) fun (state : Nat × Environment)
          (ctor : Constructor) => do
        let (cidx, env) := state
        env.checkName ctor.name allowPrimitive
        pure (cidx + 1, env.add (mk cidx ctor))).WF fun r =>
        r.2.constants.WF ∧ (∀ {n x}, base.find? n = some x → r.2.find? n = some x) ∧
        ∀ ctor ∈ ctors, base.find? ctor.name = none
  | [], _, _, hwf, hsub => Except.WF.pure ⟨hwf, hsub, by simp⟩
  | ctor :: ctors, cidx, env, hwf, hsub => by
    rw [List.foldlM_cons]
    refine Except.WF.bind (Q := fun r => r.2.constants.WF ∧
        (∀ {n x}, base.find? n = some x → r.2.find? n = some x) ∧
        base.find? ctor.name = none) ?_ fun r ⟨hwf', hsub', habs⟩ => ?_
    · refine (checkName.WF hwf ctor.name allowPrimitive).bind fun _ ⟨hn, _⟩ => ?_
      have hn' : env.find? (mk cidx ctor).name = none := by rw [hmk]; exact hn
      have hnMap : env.constants.find? (mk cidx ctor).name = none := by
        rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn'
      refine Except.WF.pure ⟨?_, ?_, ?_⟩
      · change (env.constants.insert (mk cidx ctor).name (mk cidx ctor)).WF
        exact hwf.insert _ _ hnMap
      · intro n x h
        exact findAddFresh_of_find hwf _ hn' (hsub h)
      · cases hb : base.find? ctor.name with
        | none => rfl
        | some x => rw [hsub hb] at hn; cases hn
    · exact (ctorFoldAbsent allowPrimitive mk hmk base ctors r.1 r.2 hwf' hsub').mono
        fun r' ⟨h1, h2, h3⟩ => ⟨h1, h2, by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact habs
          · exact h3 c hc⟩

/-- `declareConstructors` succeeds only when every constructor name is absent from the
environment it starts from. -/
theorem AddInductive.declareConstructors.namesAbsent
    {c : AddInductive.Context} (hwf : c.env.constants.WF) :
    (AddInductive.declareConstructors stats indTypes isUnsafe c).WF fun _ =>
      ConstructorNamesAbsent indTypes c.env := by
  let mk := fun (owner : InductiveType) (cidx : Nat) (ctor : Constructor) =>
    ConstantInfo.ctorInfo (AddInductive.constructorInfo stats c.lparams isUnsafe owner cidx ctor)
  have outer : ∀ (owners : List InductiveType) (env : Environment), env.constants.WF →
      (∀ {n x}, c.env.find? n = some x → env.find? n = some x) →
      (owners.foldlM (init := env) fun (env : Environment) (owner : InductiveType) => do
        let (_, env) ← owner.ctors.foldlM (init := (0, env)) fun
            (state : Nat × Environment) (ctor : Constructor) => do
          let (cidx, env) := state
          env.checkName ctor.name c.allowPrimitive
          pure (cidx + 1, env.add (mk owner cidx ctor))
        pure env).WF fun _ =>
        ∀ owner ∈ owners, ∀ ctor ∈ owner.ctors, c.env.find? ctor.name = none := by
    intro owners
    induction owners with
    | nil => intro _ _ _; exact Except.WF.pure (by simp)
    | cons owner owners ih =>
      intro env hwf hsub
      rw [List.foldlM_cons]
      refine Except.WF.bind (Q := fun env' : Environment => env'.constants.WF ∧
            (∀ {n x}, c.env.find? n = some x → env'.find? n = some x) ∧
            ∀ ctor ∈ owner.ctors, c.env.find? ctor.name = none) ?_ fun env' h => ?_
      · exact Except.WF.bind (AddInductive.declareConstructors.ctorFoldAbsent
          c.allowPrimitive (mk owner) (by intros; rfl) c.env owner.ctors 0 env hwf hsub)
          fun ⟨_, _⟩ h => Except.WF.pure h
      · rcases h with ⟨hwf', hsub', habs⟩
        exact (ih env' hwf' hsub').mono fun _ h o ho ctor hctor => by
          simp only [List.mem_cons] at ho
          rcases ho with rfl | ho
          · exact habs ctor hctor
          · exact h o ho ctor hctor
  rw [AddInductive.declareConstructors, ← Array.foldlM_toList]
  exact outer indTypes.toList c.env hwf id

/-- The boundary theorem of header installation: in the context of a completed header phase,
`declareInductiveTypes` yields a well-formed constant map and, once the constructor names are
absent from it, a header environment for every declaration the checked headers describe. -/
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
      fun headerEnv => headerEnv.constants.WF ∧
        (ConstructorNamesAbsent indTypes headerEnv → ∀ decl : VInductDecl,
          P.headers.Describes decl →
          Nonempty (HeaderEnvironment c' stats decl nparams isUnsafe P.depth Hc'.venv indTypes
            headerEnv)) := by
  -- WAVE 2 STUB (Header/Context/Formation): the source branch's
  -- `HeaderDeclaration.toHeaderEnvironment` (`Install/Headers.lean`) and
  -- `declareInductiveTypes.installsHeadersAtomicWF`.
  have := hpresent; sorry

end VerifyInductive
end Lean4Lean
