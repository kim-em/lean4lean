import Lean4Lean.Verify.Inductive.Run.SemanticFinalEnvironment

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

/-- The concrete family type submitted by Lean's bootstrap declaration of
`Eq`. Binder names are operationally retained by `Expr`, although abstract
translation erases them. -/
def eqBootstrapType (u alphaName lhsName rhsName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE lhsName (.bvar 0)
      (.forallE rhsName (.bvar 1) (.sort .zero) .default) .default)
    .implicit

/-- The concrete constructor type submitted for `Eq.refl`. -/
def eqBootstrapReflType (u alphaName valueName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE valueName (.bvar 0)
      (.app (.app (.app (.const ``Eq [.param u]) (.bvar 1)) (.bvar 0))
        (.bvar 0)) .default)
    .implicit

/-- Exact production syntax of Lean's ordinary (non-primitive) `Eq`
bootstrap declaration, modulo binder and universe-parameter names. -/
def EqBootstrapShape (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  ∃ u alphaName lhsName rhsName reflAlphaName reflValueName,
    lparams = [u] ∧ nparams = 1 ∧ isUnsafe = false ∧
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

/-- The completed safe ordinary run for Lean's bootstrap declaration of `Eq`
creates the canonical abstract equality constant at every observer safety.
Unlike later ordinary declarations, this theorem assumes only that production
`Eq` is absent at the source; canonical equality is obtained from the actual
header translation and staged installation of this block. -/
theorem SemanticRunWithStatsResult.extendSafeEqBootstrap
    {ves : VEnvs}
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (_hAbsent : c.env.constants.find? ``Eq = none)
    (hsafety : c.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (Hshape : EqBootstrapShape c.lparams nparams indTypes.toList isUnsafe)
    (hproj : ProjectionConstPreservation) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  subst sourceEnv
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.canonicalOrdinaryRuleTranslation hproj with ⟨T⟩
  let B := Hrecursors.blockCertificate T.rules T.rulesWF
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
    T.compilation.compilesTo
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
  have houtEq : (Hrecursors.outVEnv.addDefEqRules T.rules).constants ``Eq =
      some eqConst := by
    apply VEnv.addDefEqRules_le.constants
    apply (VEnv.addConstVals_le B.staged.abstract_recursors).constants
    apply (VEnv.addConstVals_le B.staged.abstract_ctors).constants
    exact htypesEq
  rw [hsafety] at B
  rcases B.extendSafeExact wf hdecl hcompile horigins Hrecursors.closed
      hconstructors with ⟨ves', wf', hle, hsafeReplay⟩
  have hsafeEq : (ves'.venv .safe).constants ``Eq = some eqConst :=
    hsafeReplay.constants houtEq
  have hcanonical : CanonicalEqEnvs ves' := by
    intro safety
    exact (wf'.mono DefinitionSafety.le_safe).constants hsafeEq
  exact ⟨ves', wf', hcanonical, hle⟩

end VerifyInductive
end Lean4Lean
