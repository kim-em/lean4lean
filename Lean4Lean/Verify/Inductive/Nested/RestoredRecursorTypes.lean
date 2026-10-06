import Lean4Lean.Verify.Inductive.Nested.RestorationAgreement

/-! Restored recursor types of an exact validated nested run, with the
parameter telescope of the lowered recursor type discharged from the
restoration step and the canonical recursor type. -/

namespace Lean4Lean
namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- A restoration telescope of an expression translating to a forall
telescope whose body is neither a binder is a forall telescope: a `lam`
binder would translate to a `lam`. -/
theorem RestoreTelescope.forallTelescope_of_tr {env : VEnv} {Us : List Name}
    {X : VExpr} (hXlam : ∀ a b, X ≠ .lam a b) (hXforall : ∀ a b, X ≠ .forallE a b) :
    ∀ {e : Expr} {n : Nat} {Δ : VLCtx} {D : List VExpr},
      RestoreTelescope e n → TrExprS env Us Δ e (VExpr.wrapForalls D X) →
      ∃ suffix, Expr.ForallTelescope e n suffix := by
  intro e n Δ D H
  induction H generalizing Δ D with
  | done => intro _; exact ⟨_, .nil _⟩
  | @forallE body n name dom bi _ ih =>
    intro Ht
    generalize hv : VExpr.wrapForalls D X = v at Ht
    cases Ht with
    | forallE _ _ _ hbody =>
      cases D with
      | nil =>
        simp only [VExpr.wrapForalls, List.foldr_nil] at hv
        exact absurd hv (hXforall _ _)
      | cons d D =>
        simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.forallE.injEq] at hv
        rcases hv with ⟨rfl, hv⟩
        rw [← hv] at hbody
        rcases ih hbody with ⟨suffix, hs⟩
        exact ⟨suffix, .cons hs⟩
  | lam _ _ =>
    intro Ht
    generalize hv : VExpr.wrapForalls D X = v at Ht
    cases Ht with
    | lam _ _ _ =>
      cases D with
      | nil =>
        simp only [VExpr.wrapForalls, List.foldr_nil] at hv
        exact absurd hv (hXlam _ _)
      | cons d D =>
        simp [VExpr.wrapForalls] at hv

theorem VExpr.mkApps_append_singleton (f a : VExpr) (l : List VExpr) :
    VExpr.mkApps f (l ++ [a]) = .app (VExpr.mkApps f l) a := by
  simp [VExpr.mkApps, List.foldl_append]

open _root_.Lean4Lean.InductiveSignature in
/-- The parameter telescope of a lowered recursor type whose translation is
a canonical generated recursor type. -/
theorem RestoreTelescope.forallTelescope_of_recursorType
    {s : InductiveSignature} {g : Instance s} {owner : Fin s.families.size}
    {env : VEnv} {Us : List Name} {e : Expr} {n : Nat}
    (H : RestoreTelescope e n) (Ht : TrExprS env Us [] e (g.recursorType owner)) :
    ∃ suffix, Expr.ForallTelescope e n suffix := by
  simp only [Instance.recursorType] at Ht
  refine H.forallTelescope_of_tr ?_ ?_ Ht <;>
  · intro a b h
    simp only [VExpr.mkApps_append_singleton] at h
    cases h


/-- The lowered recursor type of a restoration step at a generated owner's
recursor name translates to the owner's canonical generated recursor type. -/
theorem NestedValidatedRunResult.loweredRecursorTypeTranslation
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    TrExprS E.production.production.completed.outVEnv Hstep.oldInfo.levelParams []
      Hstep.oldInfo.type
      (E.production.production.completed.canonicalGeneration.recursorType owner) := by
  rcases E.production.production.completed.metadataRealization owner with
    ⟨rec, hrec, _, M⟩
  have hlen : owner.val < E.production.production.entries.length := by
    rw [show E.production.production.entries =
      E.production.production.completed.entries from rfl,
      E.production.production.completed.entries_length_eq]
    exact owner.isLt
  have hmem := List.getElem_mem (l := E.production.production.entries)
    (n := owner.val) hlen
  have hfind := E.production.production.findRecursorOfMem
    (info := (E.production.production.entries[owner.val]'hlen).1) hmem
  have hrec' : (E.production.production.entries[owner.val]'hlen).1 = .recInfo rec := hrec
  rw [hrec'] at hfind
  change E.loweredEnv.find? rec.name = some (.recInfo rec) at hfind
  have h2 : some (ConstantInfo.recInfo rec) = some (.recInfo Hstep.oldInfo) := by
    rw [← hfind, M.name]
    exact Hstep.lookup
  have heq : rec = Hstep.oldInfo := by
    injection h2 with h
    injection h
  rw [heq] at M
  exact M.type

/-- The parameter telescope of the lowered recursor type of a restoration
step at a generated owner's recursor name. -/
theorem NestedValidatedRunResult.loweredRecursorParameterTelescope
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    ∃ suffix, Expr.ForallTelescope Hstep.oldInfo.type result.nparams suffix :=
  Hstep.typeTelescope.forallTelescope_of_recursorType
    (E.loweredRecursorTypeTranslation owner Hstep)

/-- Every generated recursor name of the installed lowered production is the
canonical recursor name of a generated owner. -/
theorem NestedValidatedRunResult.recursorOwnerOfGenerated
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {name : Name}
    (hname : name ∈ (E.production.production.entries.map Prod.snd).map (·.name)) :
    ∃ owner : Fin E.production.production.completed.generationSignature.families.size,
      name = E.production.production.completed.canonicalGeneration.recursorName owner := by
  rcases List.mem_map.mp hname with ⟨value, hvalue, rfl⟩
  rcases List.mem_iff_getElem.mp hvalue with ⟨i, hi, hget⟩
  have hi' : i < E.production.production.completed.generationSignature.families.size := by
    have : i < E.production.production.entries.length := by simpa using hi
    rw [← E.production.production.completed.entries_length_eq]
    exact this
  refine ⟨⟨i, hi'⟩, ?_⟩
  rcases E.production.production.completed.metadataRealization ⟨i, hi'⟩ with
    ⟨_, _, hvalueEq, _⟩
  rw [← hget, List.getElem_map]
  exact congrArg VConstVal.name hvalueEq


open _root_.Lean4Lean.InductiveSignature in
/-- **Restored recursor types of an exact validated nested run**, with the
parameter telescope of the lowered recursor type discharged. For every
generated owner and every executable restoration step at the owner's
lowered recursor name, any translation `t` of the restored recursor type is
exactly the abstract restoration of the owner's canonical generated recursor
type, given the closed-form readiness of the lowered type's parameter
residual and the readiness of its parameter domains. -/
theorem NestedValidatedRunResult.restoredRecursorTypes'
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ (envTypes : VEnv) (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      auxiliaries.map (·.auxiliary) =
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (·.name) ∧
      CertifiedSpecializations (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      ∀ (owner : Fin E.production.production.completed.generationSignature.families.size)
        {stepSource stepTarget : Environment}
        (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.production.production.completed.canonicalGeneration.recursorName owner)
          stepSource stepTarget),
        (∀ suffix, Expr.ForallTelescope Hstep.oldInfo.type result.nparams suffix →
          LoweredRestoreReady (auxiliaries.flatMap (·.headNames)) result.nparams
            (compilationRestoration sourceDecl auxiliaries).restorableNames
            (lparams.map Level.param) 0 suffix) →
        ForallDomainsReady (compilationRestoration sourceDecl auxiliaries).restorableNames
          result.nparams Hstep.oldInfo.type →
        ∀ (targetEnv : VEnv) (t : VExpr),
          TrExprS targetEnv Hstep.restored.newInfo.levelParams []
            Hstep.restored.newInfo.type t →
          (compilationRestoration sourceDecl auxiliaries).expr
            (E.production.production.completed.canonicalGeneration.recursorType owner) =
              some t := by
  rcases E.restorationMapAgreement wf Hsources with
    ⟨envTypes, auxiliaries, hadded, _, hnames, _, hcertified, _, hscoped, _,
      hparamsSize, D, A⟩
  refine ⟨envTypes, auxiliaries, hadded, hnames, hcertified, hscoped, ?_⟩
  intro owner stepSource stepTarget Hstep Hlowered Hdomains targetEnv t Ht
  have Hs := E.loweredRecursorTypeTranslation owner Hstep
  rcases E.loweredRecursorParameterTelescope owner Hstep with ⟨suffix, Htel⟩
  have hclosed : Closed Hstep.oldInfo.type := by
    simpa [VLCtx.bvars] using Hs.closed
  have Hinput : Hstep.oldInfo.type.FVarsIn fun _ => False :=
    Hs.fvarsIn.mono fun _ h => by simp [VLCtx.fvars] at h
  have Hready : ∀ Hopen : NestedRestorationOpening result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      Hstep.oldInfo.type Hstep.restored.newInfo.type,
      RestoreReady result E.loweredEnv Hopen.params
        (compilationRestoration sourceDecl auxiliaries).restorableNames
        (lparams.map Level.param) Hopen.body ∧ Closed Hopen.restoredBody := by
    intro Hopen
    refine ⟨Hopen.restoreReady_of_lowered (A targetEnv Hstep.oldInfo.levelParams) Htel
      ?_, Hopen.restoredBody_closed D Htel hclosed⟩
    rw [compilationRestoration_heads_auxiliary]
    exact Hlowered suffix Htel
  exact Hstep.restored.restoration.typeRestorationCommutes hparamsSize
    (A targetEnv _) Hready Htel Hdomains Hinput hclosed Hs Ht

/-- The executable recursor name of a generated entry, as recorded by
`RestoredAuxiliaryGeneratedStepAlignment.oldRecName_eq`, is the canonical
recursor name of the generated owner at the same position. -/
theorem NestedValidatedRunResult.recursorOwnerOfEntry
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {ownerIdx : Nat} (hentry : ownerIdx < E.production.production.entries.length) :
    ∃ owner : Fin E.production.production.completed.generationSignature.families.size,
      owner.val = ownerIdx ∧
      Lean.mkRecName E.production.indTypes[ownerIdx]!.name =
        E.production.production.completed.canonicalGeneration.recursorName owner := by
  have hi : ownerIdx < E.production.production.completed.generationSignature.families.size := by
    rw [← E.production.production.completed.entries_length_eq]
    exact hentry
  refine ⟨⟨ownerIdx, hi⟩, rfl, ?_⟩
  rcases E.production.production.completed.metadataRealization ⟨ownerIdx, hi⟩ with
    ⟨rec, hrec, _, M⟩
  let G := E.production.production.generated.entry ownerIdx hentry
  have h : ConstantInfo.recInfo rec = .recInfo G.info := hrec.symm.trans G.source_eq
  injection h with h
  rw [← G.name, ← h, M.name]

/-- A recursor visible in a checking environment translates its type to the
type of its abstract constant. -/
theorem _root_.Lean4Lean.CheckingEnv.recursorConstant {safety : DefinitionSafety}
    {env : Environment} {venv : VEnv} (Htr : CheckingEnv safety env venv)
    {rec : RecursorVal} (hfind : env.find? rec.name = some (.recInfo rec))
    (hsafety : safety ≤ (ConstantInfo.recInfo rec).safety) :
    ∃ type, venv.constants rec.name = some ⟨rec.levelParams.length, type⟩ ∧
      TrExprS venv rec.levelParams [] rec.type type := by
  rcases Htr.find? hfind hsafety with ⟨ci', hci', _, huvars, htr⟩
  refine ⟨ci'.type, ?_, htr⟩
  rw [hci']
  congr 1
  cases ci'
  simp only at huvars ⊢
  rw [← huvars]
  rfl


open _root_.Lean4Lean.InductiveSignature in
/-- The `type` clause of `RestoredRecursorShapeInputs` for every recursor
visible in a checking environment whose name, universe parameters and type
are those of an executable restoration step at a generated owner's lowered
recursor name (for instance the rule-stripped copy of the restored recursor
in `finalValidOfStaged_of_shapes`), modulo the two syntactic readiness
conditions on the lowered recursor type. -/
theorem NestedValidatedRunResult.restoredRecursorTypeConstants
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∃ (envTypes : VEnv) (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      auxiliaries.map (·.auxiliary) =
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (·.name) ∧
      CertifiedSpecializations (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      ∀ (owner : Fin E.production.production.completed.generationSignature.families.size)
        {stepSource stepTarget : Environment}
        (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.production.production.completed.canonicalGeneration.recursorName owner)
          stepSource stepTarget),
        (∀ suffix, Expr.ForallTelescope Hstep.oldInfo.type result.nparams suffix →
          LoweredRestoreReady (auxiliaries.flatMap (·.headNames)) result.nparams
            (compilationRestoration sourceDecl auxiliaries).restorableNames
            (lparams.map Level.param) 0 suffix) →
        ForallDomainsReady (compilationRestoration sourceDecl auxiliaries).restorableNames
          result.nparams Hstep.oldInfo.type →
        ∀ {checkSafety : DefinitionSafety} {env : Environment} {venv : VEnv},
          CheckingEnv checkSafety env venv →
          ∀ (rec : RecursorVal), env.find? rec.name = some (.recInfo rec) →
          rec.levelParams = Hstep.restored.newInfo.levelParams →
          rec.type = Hstep.restored.newInfo.type →
          checkSafety ≤ (ConstantInfo.recInfo rec).safety →
          ∃ type, (compilationRestoration sourceDecl auxiliaries).expr
              (E.production.production.completed.canonicalGeneration.recursorType owner) =
                some type ∧
            venv.constants rec.name = some ⟨rec.levelParams.length, type⟩ := by
  rcases E.restoredRecursorTypes' wf Hsources with
    ⟨envTypes, auxiliaries, hadded, hnames, hcertified, hscoped, H⟩
  refine ⟨envTypes, auxiliaries, hadded, hnames, hcertified, hscoped, ?_⟩
  intro owner stepSource stepTarget Hstep Hlowered Hdomains checkSafety env venv
    Htr rec hfind hlevels htype hsafety
  rcases Htr.recursorConstant hfind hsafety with ⟨type, hconst, Ht⟩
  rw [hlevels, htype] at Ht
  exact ⟨type, H owner Hstep Hlowered Hdomains venv type Ht, hconst⟩

end VerifyInductive
end Lean4Lean
