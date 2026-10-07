import Lean4Lean.Theory.Typing.ShapeModel.EnvTablesRegistration

/-!
# Environment tables built along a declaration history

`HistTables env T`: the tables `T` are those built step by step along a `VEnv.WF'` history of
`env` (one constructor per step, with the step's premises and the explicit table update). Every
such `T` satisfies the history invariant `Tables.Inv env` (`HistTables.inv`), and every
well-formed environment has such tables (`VEnv.WF'.histTables`).

The environment tables of the shape model (`envTables`, `EnvTables.lean`) are chosen among these:
the validity of the computation rules (milestone M4c) is proved by induction along the history
that built the tables, so that every table entry is justified by derivations in an earlier
environment of the same history, where soundness is already established.
-/

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature

/-- Tables built along a well-formed history. -/
inductive HistTables : VEnv → Tables → Prop
  | empty : HistTables .empty Tables.empty
  | «axiom» {env env' : VEnv} {T : Tables} {ci : VConstVal} :
    HistTables env T → env.WF → ci.WF env → env.addConst ci.name ci.toVConstant = some env' →
    HistTables env' T
  | «opaque» {env env' : VEnv} {T : Tables} {ci : VDefVal} :
    HistTables env T → env.WF → ci.WF env → env.addConst ci.name ci.toVConstant = some env' →
    HistTables env' T
  | «def» {env env' : VEnv} {T : Tables} {ci : VDefVal} :
    HistTables env T → env.WF → ci.WF env → env.addConst ci.name ci.toVConstant = some env' →
    HistTables (env'.addDefEq ci.toDefEq) (T.addDefs [ci])
  | mutualDef {env env' : VEnv} {T : Tables} {cis : List VDefVal} :
    HistTables env T → env.WF → (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' → (∀ ci ∈ cis, ci.WF env') →
    HistTables (env'.addDefEqs cis) (T.addDefs cis)
  | quot {env env' : VEnv} {T : Tables} :
    HistTables env T → env.WF → env.QuotReady → env.addQuot = some env' →
    HistTables env' T.addQuot
  | induct {env env' cbase : VEnv} {T : Tables} {decl expanded : VInductDecl}
      {block : VInductBlock} {s : InductiveSignature} {g : Instance s}
      {aux : List ContainerSpecialization} :
    HistTables env T → env.WF → decl.WF env → decl.CompilesTo env block →
    VInductBlock.WF env block → block.install env = some env' →
    cbase ≤ env → CompilationData cbase decl expanded s g aux block →
    CertifiedSpecializations cbase aux →
    HistTables env' (T.addNative decl (NativeRecursorData.compilationEntries default decl s aux g))
  | elim {base env : VEnv} {T : Tables} {source : VInductDecl} {block : VInductBlock}
      {schema : CaseSchema} {key : Name} :
    HistTables env T → base.WF → env.WF → base ≤ env →
    schema.Certified base source block →
    source.types.head?.map (·.name) = some key →
    ((∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant) ∧ env.defeqs = base.defeqs ∧
      schema.ProjNamesRegistered env key) →
    schema.Fresh env key → schema.StructCompat env →
    HistTables (env.addEliminator key schema) (T.addSchema env source)
  | proj {base envTypes envCtors : VEnv} {T : Tables} {decl : VInductDecl}
      {block : VInductBlock} :
    HistTables envCtors T → base.WF → envCtors.WF →
    decl.sourceNames.Nodup →
    (∀ type ∈ decl.types, type.toVConstant.WF base) →
    (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) →
    (∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes) →
    decl.SourceParameterWF base →
    (∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor) →
    block.types = decl.typeConstants →
    block.ctors = decl.constructorConstants →
    block.projections = decl.projectionEntries →
    base.addConstVals block.types = some envTypes →
    envTypes.addConstVals block.ctors = some envCtors →
    HistTables (envCtors.addProjections block.projections)
      (T.addViews (viewFams decl selStruct) (viewCtors decl selStruct))

variable {env env' : VEnv} {T : Tables}

theorem Tables.Inv.extends_addDefs (H : T.Inv env) {cis : List VDefVal} {env1 : VEnv}
    (hadd : env.addConsts cis = some env1) : T.Extends (T.addDefs cis) := by
  obtain ⟨hfresh, hnd⟩ := addConsts_fresh hadd
  have hold : ∀ n, (∃ ci, env.constants n = some ci) → ∀ ci ∈ cis, ci.name ≠ n := by
    rintro n ⟨x, hx⟩ ci hci rfl
    rw [hfresh ci hci] at hx
    cases hx
  refine ⟨fun {n v} h => ?_, id, id, id, id⟩
  exact (Tables.addDefs_defs hnd).mpr (.inr ⟨hold n (H.defs_const (by simp [h])), h⟩)

theorem Tables.extends_addQuot (T : Tables) : T.Extends T.addQuot :=
  ⟨id, id, fun _ => rfl, addView_of_old, addView_of_old⟩

/-- Tables built along a history satisfy the history invariant, in a well-formed environment. -/
theorem HistTables.inv (H : HistTables env T) : T.Inv env ∧ env.WF := by
  induction H with
  | empty => exact ⟨Tables.empty_inv, ⟨[], .empty⟩⟩
  | «axiom» _ henv hci hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
      (VEnv.addConst_projections hadd), ⟨_, .decl (.axiom hci hadd) hds⟩⟩
  | «opaque» _ henv hci hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
      (VEnv.addConst_projections hadd), ⟨_, .decl (.opaque hci hadd) hds⟩⟩
  | @«def» env env' T ci _ henv hci hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.addDefinitions (cis := [ci]) (by simpa [VEnv.addConsts] using hadd),
      ⟨_, .decl (.def hci hadd) hds⟩⟩
  | mutualDef _ henv h1 hadd h2 ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨ih.1.addDefinitions hadd, ⟨_, .decl (.mutualDef h1 hadd h2) hds⟩⟩
  | quot _ henv hready hadd ih =>
    obtain ⟨ds, hds⟩ := henv
    have henv' : VEnv.WF _ := ⟨_, .decl (.quot hready hadd) hds⟩
    exact ⟨ih.1.addQuot ⟨ds, hds⟩ henv' hadd, henv'⟩
  | induct _ henv hdecl hcomp hblock hinstall hcle hdata hprior ih =>
    obtain ⟨ds, hds⟩ := henv
    exact ⟨(ih.1.install' ⟨ds, hds⟩ hcomp hblock hinstall hcle hdata hprior).2,
      ⟨_, .decl (.induct hdecl (.intro hdecl hcomp hblock hinstall)) hds⟩⟩
  | elim _ hbase henv hle hcert hkey hconsts hfresh hcompat ih =>
    exact ⟨(ih.1.eliminator hbase hle hcert hconsts.1 hconsts.2.1).2,
      VEnv.WF.inductEliminators hbase henv hle hcert hkey hconsts.1 hconsts.2.1 hconsts.2.2
        hfresh hcompat⟩
  | proj _ hbase hctorsWF hsource htypesWF hconstructorUvars hctorsWF' hparams hshape
      htypesSource hctorsSource hprojections htypes hctors ih =>
    have henv' := VEnv.WF.inductProjections hbase hctorsWF hsource htypesWF hconstructorUvars
      hctorsWF' hparams hshape htypesSource hctorsSource hprojections htypes hctors
    exact ⟨(ih.1.registerProjections hbase henv' hsource hconstructorUvars hparams hshape
      htypesSource hctorsSource hprojections htypes hctors).2, henv'⟩

/-- Every well-formed history builds tables. -/
theorem VEnv.WF'.histTables {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    ∃ T : Tables, HistTables env T := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | @decl d env' ds env hdecl hprev ih =>
    obtain ⟨T, hT⟩ := ih
    have henv : env.WF := ⟨ds, hprev⟩
    cases hdecl with
    | «axiom» hci hadd => exact ⟨T, .axiom hT henv hci hadd⟩
    | «opaque» hci hadd => exact ⟨T, .opaque hT henv hci hadd⟩
    | «example» => exact ⟨T, hT⟩
    | «def» hci hadd => exact ⟨_, .def hT henv hci hadd⟩
    | mutualDef h1 hadd h2 => exact ⟨_, .mutualDef hT henv h1 hadd h2⟩
    | quot hready hadd => exact ⟨_, .quot hT henv hready hadd⟩
    | induct hdecl hadd =>
      cases hadd with
      | intro _ hcompile hblock hinstall =>
        obtain ⟨cbase, expanded, s, g, aux, hcle, hdata, hprior⟩ :=
          hcompile.compiled.compilationOrigin
        exact ⟨_, .induct hT henv hdecl hcompile hblock hinstall hcle hdata hprior⟩
  | inductEliminators hbase hprev hle hcert hkey hconsts hfresh hcompat _ ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨_, .elim hT ⟨_, hbase⟩ ⟨_, hprev⟩ hle hcert hkey hconsts hfresh hcompat⟩
  | inductProjections hbase hctorsWF hsource htypesWF hconstructorUvars hctorsWF' hparams
      hshape htypesSource hctorsSource hprojections htypes hctors _ ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨_, .proj hT ⟨_, hbase⟩ ⟨_, hctorsWF⟩ hsource htypesWF hconstructorUvars hctorsWF'
      hparams hshape htypesSource hctorsSource hprojections htypes hctors⟩

end Lean4Lean.ShapeModel
