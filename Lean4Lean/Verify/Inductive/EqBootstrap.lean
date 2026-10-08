import Lean4Lean.Verify.Inductive.Run.SemanticFinalEnvironment
import Lean4Lean.Verify.Inductive.Run.SemanticSpecification
import Lean4Lean.Verify.Inductive.EqCanonicalForms

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

private theorem forall₂_leftSingleton
    (H : List.Forall₂ R [a] bs) :
    ∃ b, bs = [b] ∧ R a b := by
  cases H with
  | cons hab Htail =>
    cases Htail
    exact ⟨_, rfl, hab⟩

private theorem vconstant_eq_of_fields {a b : VConstant}
    (huvars : a.uvars = b.uvars) (htype : a.type = b.type) : a = b := by
  cases a
  cases b
  simp_all

/-- Exact production syntax of Lean's ordinary (non-primitive) `Eq`
bootstrap declaration, modulo binder and universe-parameter names.  As
submitted by `Init.Prelude`, `Eq` has two parameters (`α` and the left
endpoint `a`) and one index (the right endpoint), so `nparams = 2`. -/
def EqBootstrapShape (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  ∃ u alphaName lhsName rhsName reflAlphaName reflValueName,
    lparams = [u] ∧ nparams = 2 ∧ isUnsafe = false ∧
    types = [{
      name := ``Eq
      type := eqBootstrapType u alphaName lhsName rhsName
      ctors := [{
        name := ``Eq.refl
        type := eqBootstrapReflType u reflAlphaName reflValueName }] }]

/-- The concrete `Eq` family arity has the canonical abstract type stored in
`eqConst`. This proof is environment-independent: the arity contains only
sorts and bound variables. -/
theorem eqBootstrapType_translation
    (env : VEnv) (u alphaName lhsName rhsName : Name) :
    TrExprS env [u] [] (eqBootstrapType u alphaName lhsName rhsName)
      eqConst.type := by
  unfold eqBootstrapType eqConst
  change TrExprS env [u] []
    (.forallE alphaName (.sort (.param u))
      (.forallE lhsName (.bvar 0)
        (.forallE rhsName (.bvar 1) (.sort .zero) .default) .default)
      .implicit)
    (.forallE (.sort (.param 0))
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
  apply TrExprS.forallE
  · refine ⟨_, VEnv.HasType.sort ?_⟩
    change VLevel.WF 1 (.param 0)
    trivial
  · apply VEnv.IsType.forallE
    · refine ⟨.param 0, ?_⟩
      type_tac
    · apply VEnv.IsType.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
  · exact .sort (by simp [VLevel.ofLevel])
  · apply TrExprS.forallE
    · refine ⟨.param 0, ?_⟩
      type_tac
    · apply VEnv.IsType.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
    · exact .bvar rfl
    · apply TrExprS.forallE
      · refine ⟨.param 0, ?_⟩
        type_tac
      · exact ⟨_, VEnv.HasType.sort (by trivial)⟩
      · exact .bvar rfl
      · exact .sort rfl

/-- Header translation of the exact production `Eq` declaration determines
the abstract family constant uniquely. -/
theorem TrInductDeclHeaders.eqBootstrapConstant
    (H : TrInductDeclHeaders env lparams nparams types isUnsafe decl envTypes)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe) :
    ∃ target : VInductiveType,
      decl.types = [target] ∧ target.name = ``Eq ∧
      target.toVConstant = eqConst := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      hlparams, _hnparams, _hunsafe, htypes⟩
  subst lparams
  subst types
  rcases forall₂_leftSingleton H.types with ⟨target, hdecl, Htarget⟩
  refine ⟨target, hdecl, Htarget.header.name, ?_⟩
  apply vconstant_eq_of_fields
  · simpa [eqConst] using Htarget.header.uvars
  · apply TrExprS.unique (by trivial) Htarget.header.type
    exact eqBootstrapType_translation env u alphaName lhsName rhsName

/-- An exact bootstrap header certificate identifies one installed production
`Eq` entry and the corresponding canonical abstract value. -/
theorem DeclaredHeadersResult.eqBootstrapEntry
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (Hshape : EqBootstrapShape c.lparams nparams indTypes.toList isUnsafe) :
    ∃ (info : InductiveVal) (target : VInductiveType),
      (.inductInfo info, target.toVConstVal) ∈ H.entries ∧
      info.name = ``Eq ∧ target.name = ``Eq ∧
      target.toVConstant = eqConst := by
  rcases TrInductDeclHeaders.eqBootstrapConstant H.translation Hshape with
    ⟨target, htypes, htargetName, htargetConstant⟩
  have htargetMem : target.toVConstVal ∈ H.entries.map Prod.snd := by
    rw [H.values, VInductDecl.typeConstants, htypes]
    simp
  rcases List.mem_map.mp htargetMem with
    ⟨entry, hentry, hentryValue⟩
  rcases H.sourceAligned with ⟨_numNested, Haligned⟩
  rcases Haligned.originInfo hentry with
    ⟨info, _hinfo, hentryInfo⟩
  have hnames := H.installed.entryNames hentry
  have hinfoName : info.name = ``Eq := by
    rw [hentryInfo] at hnames
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal, hentryValue,
      htargetName] using hnames
  have hentryEq : entry = (.inductInfo info, target.toVConstVal) := by
    apply Prod.ext
    · exact hentryInfo
    · exact hentryValue
  exact ⟨info, target, hentryEq ▸ hentry, hinfoName,
    htargetName, htargetConstant⟩

/-- The source translation of the exact bootstrap declaration fixes the
abstract declaration: one family `Eq` with the stored type of `Eq`, one
constructor `Eq.refl` with the stored type of `Eq.refl`, two parameters. -/
theorem TrInductDeclCore.eqBootstrapDecl
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl envTypes envCtors)
    (Hshape : EqBootstrapShape lparams nparams types isUnsafe) :
    ∃ family refl, decl.types = [family] ∧ family.name = ``Eq ∧
      family.toVConstant = ⟨1, canonicalEqType⟩ ∧ family.ctors = [refl] ∧
      refl.name = ``Eq.refl ∧ refl.toVConstant = ⟨1, canonicalEqReflType⟩ ∧
      decl.nparams = 2 := by
  rcases Hshape with
    ⟨u, alphaName, lhsName, rhsName, reflAlphaName, reflValueName,
      rfl, rfl, rfl, rfl⟩
  rcases forall₂_leftSingleton H.types with ⟨family, hdecl, Hfamily⟩
  rcases forall₂_leftSingleton Hfamily.ctors with ⟨refl, hctors, Hrefl⟩
  refine ⟨family, refl, hdecl, Hfamily.header.name, ?_, hctors, Hrefl.name, ?_,
    H.nparams⟩
  · apply vconstant_eq_of_fields
    · simpa using Hfamily.header.uvars
    · exact TrExprS.eq_canonicalEqType Hfamily.header.type
  · apply vconstant_eq_of_fields
    · simpa using Hrefl.uvars
    · exact TrExprS.eq_canonicalEqReflType Hrefl.type

/-- Installation of a block exposes each of its recursors at its exact value. -/
theorem VInductBlock.install_recursorConstant {base env' : VEnv} {block : VInductBlock}
    (H : block.install base = some env') {recursor : VConstVal}
    (hrecursor : recursor ∈ block.recursors) :
    env'.constants recursor.name = some recursor.toVConstant := by
  unfold VInductBlock.install at H
  cases htypes : base.addConstVals block.types with
  | none => simp [htypes] at H
  | some envTypes =>
    cases hctors : envTypes.addConstVals block.ctors with
    | none => simp [htypes, hctors] at H
    | some envCtors =>
      cases hrecursors : ((envCtors.addEliminators block.eliminators).addProjections
          block.projections).addConstVals block.recursors with
      | none => simp [htypes, hctors, hrecursors] at H
      | some envRecursors =>
        simp [htypes, hctors, hrecursors] at H
        subst env'
        simpa using VEnv.addConstVals_get hrecursors hrecursor

/-- Installation of a block stores each of its rules. -/
theorem VInductBlock.install_rule {base env' : VEnv} {block : VInductBlock}
    (H : block.install base = some env') {rule : VDefEq} (hrule : rule ∈ block.rules) :
    env'.defeqs rule := by
  unfold VInductBlock.install at H
  cases htypes : base.addConstVals block.types with
  | none => simp [htypes] at H
  | some envTypes =>
    cases hctors : envTypes.addConstVals block.ctors with
    | none => simp [htypes, hctors] at H
    | some envCtors =>
      cases hrecursors : ((envCtors.addEliminators block.eliminators).addProjections
          block.projections).addConstVals block.recursors with
      | none => simp [htypes, hctors, hrecursors] at H
      | some envRecursors =>
        simp [htypes, hctors, hrecursors] at H
        subst env'
        exact VEnv.addDefEqRules_defeqs_iff.mpr (.inr hrule)

/-- The completed safe ordinary run for Lean's bootstrap declaration of `Eq`
creates the canonical abstract equality constant at every observer safety.
Unlike later ordinary declarations, this theorem assumes only that production
`Eq` is absent at the source; canonical equality is obtained from the actual
header translation and staged installation of this block. -/
theorem SemanticRunWithStatsResult.extendSafeEqBootstrap
    {ves : VEnvs}
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WFCore c.env) (hcorner : ∀ safety, ProjectionCorner safety c.env (ves.venv safety))
    (_hAbsent : c.env.constants.find? ``Eq = none)
    (hsafety : c.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (Hshape : EqBootstrapShape c.lparams nparams indTypes.toList isUnsafe) :
    ∃ ves' : VEnvs, ves'.WFCore outEnv ∧ CanonicalEqEnvs ves' ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (InductiveSpecificationResult (ves.venv .safe) c.lparams
        nparams indTypes.toList isUnsafe (ves'.venv .safe)) ∧
      (∀ ci, outEnv.find? ``Eq.rec = some ci → IsProductionEqRec ci →
        ∀ safety, (ves'.venv safety).HasCanonicalEq) := by
  subst sourceEnv
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.canonicalCompletedRuleTranslation with ⟨T⟩
  let B0 := Hrecursors.declaredBlockCertificate T.rules T.rulesWF
  let B := B0.sf_mono (safety := .safe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  rcases Hheaders.eqBootstrapEntry Hshape with
    ⟨eqInfo, target, hentry, hinfoName, htargetName, htargetConstant⟩
  have hnonempty : indTypes.toList ≠ [] := by
    intro hempty
    rcases Hshape with ⟨u, alphaName, lhsName, rhsName,
      reflAlphaName, reflValueName, _hlparams, _hnparams, _hunsafe, htypes⟩
    rw [hempty] at htypes
    contradiction
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .safe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .safe) B.block :=
    by simpa [B, B0, BlockCertificate.sf_mono, StagedBlock.sf_mono, BlockCertificate.block] using
      (show OrdinaryCompilationCertificate _ decl B0.block from
        T.compilation hnonempty).compilesTo
  have hconstructors :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (Hrecursors.outVEnv.addDefEqRules T.rules) := by
    exact Hrecursors.completedConstructorSemantics
      (wf.constructorSemantics (safety := .safe)) T.rules
  have horigins :
      ProductionInductiveOrigins c.env.constants outEnv.constants decl :=
    Hrecursors.productionInductiveOrigins
  have htypeValue : target.toVConstVal ∈ Hheaders.entries.map Prod.snd :=
    List.mem_map.mpr ⟨(.inductInfo eqInfo, target.toVConstVal), hentry, rfl⟩
  have htypesEq : B.staged.venvTypes.constants ``Eq = some eqConst := by
    have hlookup := VEnv.addConstVals_get B.staged.abstract_types htypeValue
    simpa [htargetName, htargetConstant] using hlookup
  have houtEq :
      (Hrecursors.outVEnv.addDefEqRules T.rules).constants ``Eq = some eqConst := by
    apply VEnv.addDefEqRules_le.constants
    apply (VEnv.addConstVals_le B.staged.abstract_recursors).constants
    apply VEnv.addEliminators_addProjections_le.constants
    apply (VEnv.addConstVals_le B.staged.abstract_ctors).constants
    exact htypesEq
  rcases B.extendSafeExact wf hcorner hdecl hcompile horigins T.recursorProvenance Hrecursors.closed
      (Hrecursors.constructorOwnersPresent wf.constructorOwners)
      hconstructors
      (fun safety => Hrecursors.declaredBlockEliminatorsReplay T.rules T.rulesWF
        (wf.mono (DefinitionSafety.le_safe (a := safety)))) with
      ⟨ves', wf', hle, hadd, hsafeReplay⟩
  have hsafeEq : (ves'.venv .safe).constants ``Eq = some eqConst :=
    hsafeReplay.constants houtEq
  have hcanonical : CanonicalEqEnvs ves' := by
    intro safety
    exact (wf'.mono DefinitionSafety.le_safe).constants hsafeEq
  have hHasCanonical : ∀ ci, outEnv.find? ``Eq.rec = some ci → IsProductionEqRec ci →
      ∀ safety, (ves'.venv safety).HasCanonicalEq := by
    intro ci hfind ⟨hciSafe, u, v, names, huv, hlps, htype⟩ safety
    refine VEnv.HasCanonicalEq.mono (wf'.mono DefinitionSafety.le_safe) ?_
    -- `Eq.rec`: the production type translates to the stored type.
    rcases (wf'.tr (safety := .safe)).find? hfind
        (by rw [hciSafe]; exact DefinitionSafety.le_rfl) with
      ⟨recConst, hrecConst, -, hrecUvars, hrecType⟩
    rw [hlps, htype] at hrecType
    have hrecEq : (ves'.venv .safe).constants ``Eq.rec = some ⟨2, canonicalEqRecType⟩ := by
      rw [hrecConst]
      congr 1
      apply vconstant_eq_of_fields
      · simpa [hlps] using hrecUvars.symm
      · exact TrExprS.eq_canonicalEqRecType huv hrecType
    -- The abstract declaration is the canonical one.
    rcases VerifyInductive.TrInductDeclCore.eqBootstrapDecl R.core Hshape with
      ⟨family, refl, hdeclTypes, hfamilyName, hfamilyConst, hfamilyCtors, hreflName,
        hreflConst, hdeclParams⟩
    -- The generated rule is the stored rule.
    have hinstall : B.block.install (ves.venv .safe) = some B.finalVEnv := B.install
    have hrules : B.block.rules = [canonicalEqRecRule] := by
      have Hcompiles : InductiveSignature.Compiles (ves.venv .safe) decl B.block := by
        simpa [B, B0, BlockCertificate.sf_mono, StagedBlock.sf_mono, BlockCertificate.block] using
          (show OrdinaryCompilationCertificate _ decl B0.block from
            T.compilation hnonempty).canonical
      refine Hcompiles.eqRecRules hdeclTypes hfamilyName (by simp [hfamilyCtors])
        hdeclParams ?_
      intro recursor hrecursor hname
      have hinstalled := hsafeReplay.constants
        (VInductBlock.install_recursorConstant hinstall hrecursor)
      rw [hname, hrecEq] at hinstalled
      have h := Option.some.inj hinstalled
      exact ⟨(congrArg VConstant.uvars h).symm, (congrArg VConstant.type h).symm⟩
    have hrule : (ves'.venv .safe).defeqs canonicalEqRecRule :=
      hsafeReplay.defeqs (VInductBlock.install_rule hinstall (by simp [hrules]))
    -- `Eq.refl` is installed with the translated constructor type.
    have hcert : VEnv.InstalledInductCertificate (ves'.venv .safe) decl := by
      cases hadd with
      | intro hdecl' hcompile' hblock' _helim' hinstall' =>
        exact .intro hdecl'.1 hdecl'.2 hcompile' hblock' hinstall' VEnv.LE.rfl
    have hreflEq : (ves'.venv .safe).constants ``Eq.refl =
        some ⟨1, canonicalEqReflType⟩ := by
      have hfamily : 0 < decl.types.length := by simp [hdeclTypes]
      have hctor : 0 < decl.types[0].ctors.length := by
        simp [hdeclTypes, hfamilyCtors]
      have := hcert.constructorConstant 0 0 hfamily hctor
      simp only [hdeclTypes, hfamilyCtors, List.getElem_cons_zero] at this
      rw [hreflName, hreflConst] at this
      exact this
    exact ⟨hsafeEq, hreflEq, hrecEq, hrule⟩
  exact ⟨ves', wf', hcanonical, hle, ⟨{
    decl := decl
    envTypes := Hheaders.context.venv
    envCtors := R.declared.venvCtors
    source := R.core
    extension := hadd
  }⟩, hHasCanonical⟩

end VerifyInductive
end Lean4Lean
