import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal

/-! # The recursor phase

After the constructors, the executable computes the elimination level, the K flag and the
recursor infos (`mkRecInfos`: motives, minors, rule templates), checks the recursive fields and
declares the recursors (`declareRecursors`, which type-checks every generated recursor type and
instantiates the rule templates). `RecursorCheck` is the frozen interface of the resulting
environment: the kernel recursors `rvals`, the model recursors `recs` they translate to
(PR #43's `TrRecursor`, with the rules' reducts translated in the recursor-stage environment),
the recursor-stage environment `outVEnv`, the shape clauses of `VInductDecl.WF`, and the
signature generator (`signature`, `generation`) whose recursors the `recs` are. The rules'
typing and their identification with the generated equations are the rule phase's
(`Rules/RuleTranslations.lean`). `ConstructorCheck.recursorPhasesWF` is the boundary theorem.

Wave 2 scaffold: owned by the `Recursor/**` agent (source branch: `Recursor/{Check,
Construction,Metadata,RecInfoCheck,InstanceAlignment}.lean`, `Recursor/{Binders,Context,
Elimination,Entries,Signature}/**`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The recursor check: the recursors are installed over the constructor environment, typed in
the projection stage, and translate to the generated recursors of a signature instance that
models the declaration. -/
structure RecursorCheck
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (outEnv : Environment) where
  elimLevel : Level
  elimLevelChecked : AddInductive.getElimLevel stats indTypes { c with env := ctorEnv } =
    .ok elimLevel
  kTarget : Bool
  /-- The kernel recursors, one per family, in family order. -/
  rvals : List RecursorVal
  rvals_names : rvals.map (·.name) = indTypes.toList.map (Lean.mkRecName ·.name)
  /-- The model recursors with their ι rules. -/
  recs : List VRecursor
  /-- The recursor-stage environment: the projection stage with the recursors added. -/
  outVEnv : VEnv
  recsAdded : (decl.withRecs recs).addRecs R.envP = some outVEnv
  /-- Each kernel recursor translates to its model recursor (PR #43's `TrRecursor`): type in
  the constructor stage, telescope split and K flag copied, rules matched one to one with
  reducts translated in the recursor stage and constructor parameter counts read off the
  output map. -/
  trRecs : List.Forall₂ (TrRecursor c.safety R.ctorVEnv outVEnv outEnv.constants) rvals recs
  map_eq : outEnv.constants = insertConsts ctorEnv.constants (rvals.map .recInfo)
  quotInit_eq : outEnv.quotInit = ctorEnv.quotInit
  fresh : ∀ rval ∈ rvals, ctorEnv.find? rval.name = none
  /-- The recursor-stage environment is a valid checking environment of the output. -/
  checking : CheckingEnv.Valid c.safety outEnv outVEnv
  /-- `VInductDecl.WF.recs_wf`: the recursors are typed in the projection stage. -/
  recsWF : ∀ r ∈ recs, r.toVConstVal.toVConstant.WF R.envP
  /-- `VInductDecl.WF.rec_shape`. -/
  rec_shape : ∀ r ∈ recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  /-- `VInductDecl.WF.rules_nodup`. -/
  rules_nodup : ∀ r ∈ recs, (r.rules.map (·.ctor)).Nodup
  /-- `VInductDecl.WF.rules_ctor`, in the constructor stage. -/
  rules_ctor : ∀ r ∈ recs, ∀ ru ∈ r.rules,
    ∃ ci, R.ctorVEnv.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields)
  /-- `VInductDecl.WF.rule_shape`. -/
  rule_shape : ∀ r ∈ recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
    r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
    ru.nfields ≤ A.piArity ∧
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j
  /-- Every reduct is closed, so `addRules` (hence `addInduct`) succeeds. -/
  rules_closed : ∀ r ∈ recs, ∀ ru ∈ r.rules, ru.rhs.Closed
  /-- The K clause of every new recursor (`InstalledBlocks.addInduct`'s `hrecK`). -/
  kLike : ∀ rval ∈ rvals, KLikeRecursor outEnv.constants outVEnv rval
  /-- The signature generator: a signature modelling the declaration and an admissible
  instance of it whose induction hypotheses and family applications are typed in the
  projection stage (the clauses of `InductiveSignature.Compiles`). -/
  signature : InductiveSignature
  generation : InductiveSignature.Instance signature
  models : signature.Models sourceEnv decl
  admissible : generation.Admissible R.headerVEnv
  ihsWellTyped : generation.GeneratedIHsWellTyped R.envP
  familyTypesWF : signature.FamilyTypesWF R.envP decl.uvars
  recursorNames : ∀ owner, generation.recursorName owner = signature.families[owner].name.str "rec"
  /-- The model recursors are the generated ones. -/
  recursors_eq : recs.map (·.toVConstVal) = generation.recursors
  /-- Each kernel recursor has the generated metadata of its owner. -/
  metadata : List.Forall₂ (fun (owner : Fin signature.families.size) rval =>
      InductiveSignature.RecursorMetadata generation outVEnv owner rval)
    (List.finRange signature.families.size) rvals
  closed : MutualInductivesClosed outEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants outEnv.constants decl
  constructorParameterAlignment : ∀ {safety},
    ConstructorParameterAlignment safety c.env sourceEnv →
    ConstructorParameterAlignment safety outEnv outVEnv

namespace RecursorCheck

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The declaration with the generated recursors: the declaration `addInduct` installs. -/
abbrev decl' (H : RecursorCheck R outEnv) : VInductDecl := decl.withRecs H.recs

theorem rvals_length (H : RecursorCheck R outEnv) : H.rvals.length = indTypes.size := by
  have := congrArg List.length H.rvals_names; simpa using this

theorem recs_length (H : RecursorCheck R outEnv) : H.recs.length = H.rvals.length :=
  (List.Forall₂.length_eq H.trRecs).symm

theorem addTypesCtorsProjsRecs (H : RecursorCheck R outEnv) :
    H.decl'.addTypesCtorsProjsRecs sourceEnv = some H.outVEnv := by
  rw [VInductDecl.addTypesCtorsProjsRecs]
  have h : H.decl'.addTypesCtorsProjs sourceEnv = some R.envP := R.addTypesCtorsProjs
  rw [h]; exact H.recsAdded

theorem outVEnv_wf (H : RecursorCheck R outEnv) : H.outVEnv.WF := H.checking.tr.wf

end RecursorCheck

/-- The boundary theorem of the recursor phase: the recursor suffix of `runWithStats`
(elimination level, K flag, recursor infos, recursive-field check, `declareRecursors`), run in
the constructor environment, yields a recursor check. -/
theorem ConstructorCheck.recursorPhasesWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hsourceSafety : isUnsafe = (c.safety != .safe))
    (hnotPartial : c.safety ≠ .partial)
    (hnprim : c.allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains (Lean.mkRecName indTypes[owner]!.name))
    (hpositivity : positivity = R.classes) :
    ((AddInductive.getElimLevel stats indTypes >>= fun elimLevel =>
      AddInductive.withTypeCheckerLParams
        (AddInductive.getRecLevelParams elimLevel c.lparams) do
        let kTarget ← AddInductive.isKTarget stats indTypes
        AddInductive.mkRecInfos stats indTypes elimLevel fun recInfos => do
          AddInductive.checkRecursiveFields isUnsafe positivity recInfos
          AddInductive.declareRecursors stats indTypes elimLevel recInfos
            kTarget c.lparams)
      { c with env := ctorEnv }).WF fun outEnv =>
        Nonempty (RecursorCheck R outEnv) := by
  -- WAVE 2 STUB (Recursor/**): the source branch's `ConstructorCheck.recursorPhasesWF`
  -- (`Recursor/Check.lean`), with `TrRecursorVal` replaced by `TrRecursor` and the shape
  -- clauses of `VInductDecl.WF`.
  have := hlparams; have := hsourceSafety; have := hnotPartial; have := hnprim
  have := hpositivity; sorry

end VerifyInductive
end Lean4Lean
