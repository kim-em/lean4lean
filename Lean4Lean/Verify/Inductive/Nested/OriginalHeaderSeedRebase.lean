import Lean4Lean.Verify.Inductive.Recursor.Origins
import Lean4Lean.Verify.Inductive.Recursor.TelescopeRestriction

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Adding constants changes no definitional-equality rules.  This exact
equality is the missing reverse-facing companion to `VEnv.addConstVals_le`:
the latter is sufficient for monotone typing transport, while nested header
restoration compares two different constant batches installed over the same
rule environment. -/
theorem VEnv.addConstVals_defeqs_eq
    {base out : VEnv} {constants : List VConstVal}
    (H : base.addConstVals constants = some out) :
    out.defeqs = base.defeqs := by
  induction constants generalizing base with
  | nil =>
      simp [VEnv.addConstVals] at H
      subst out
      rfl
  | cons ci constants ih =>
      simp only [VEnv.addConstVals] at H
      cases hadd : base.addConst ci.name ci.toVConstant with
      | none => simp [hadd] at H
      | some next =>
          rw [hadd] at H
          rw [ih H]
          unfold VEnv.addConst at hadd
          split at hadd <;> cases hadd
          rfl

/-- Two successful constant batches over the same base agree away from the
names installed by the source batch.  This is the environment relation used
to move a lowered header's family-independent prefix into the independently
rebuilt source block: no equality between the batches themselves is needed. -/
theorem VEnv.addConstVals_LEExcept
    {base source target : VEnv} {sourceConstants targetConstants : List VConstVal}
    {changed : Name -> Prop}
    (Hsource : base.addConstVals sourceConstants = some source)
    (Htarget : base.addConstVals targetConstants = some target)
    (Hchanged : forall ci, ci ∈ sourceConstants -> changed ci.name) :
    VEnv.LEExcept changed source target where
  constants := by
    intro name ci hlookup hunchanged
    have hne : forall value, value ∈ sourceConstants -> value.name ≠ name := by
      intro value hvalue hname
      apply hunchanged
      rw [← hname]
      exact Hchanged value hvalue
    have hbase : base.constants name = some ci := by
      rw [VEnv.addConstVals_constants_of_forall_ne Hsource hne] at hlookup
      exact hlookup
    exact (VEnv.addConstVals_le Htarget).constants hbase
  defeqs := by
    intro df hdf
    rw [VEnv.addConstVals_defeqs_eq Hsource] at hdf
    rw [VEnv.addConstVals_defeqs_eq Htarget]
    exact hdf

/-- Constructor environments produced from two independently translated
inductive blocks over the same base agree away from the first block's own
header and constructor names.  In the nested application the first block is
the lowered declaration and the second is the original source declaration. -/
theorem TrInductDeclCore.ctorEnvsLEExcept
    (Hfrom : TrInductDeclCore base fromLparams fromNparams fromTypes
      fromUnsafe fromDecl fromEnvTypes fromEnvCtors)
    (Hto : TrInductDeclCore base toLparams toNparams toTypes
      toUnsafe toDecl toEnvTypes toEnvCtors) :
    VEnv.LEExcept (fun name => name ∈ fromDecl.sourceNames)
      fromEnvCtors toEnvCtors := by
  have HfromAdded : base.addConstVals
      (fromDecl.typeConstants ++ fromDecl.constructorConstants) =
      some fromEnvCtors :=
    VEnv.addConstVals_append Hfrom.typesAdded Hfrom.ctorsAdded
  have HtoAdded : base.addConstVals
      (toDecl.typeConstants ++ toDecl.constructorConstants) =
      some toEnvCtors :=
    VEnv.addConstVals_append Hto.typesAdded Hto.ctorsAdded
  apply VEnv.addConstVals_LEExcept HfromAdded HtoAdded
  intro ci hci
  simp only [List.mem_append] at hci
  rcases hci with htype | hctor
  · unfold VInductDecl.sourceNames
    exact List.mem_append_left _ (List.mem_map.mpr ⟨ci, htype, rfl⟩)
  · unfold VInductDecl.sourceNames
    exact List.mem_append_right _ (List.mem_map.mpr ⟨ci, hctor, rfl⟩)

/-- Every source-block name is absent from the independent environment in
which its headers were checked.  This follows from successful abstract
installation, rather than from a separate freshness premise. -/
theorem TrInductDeclCore.baseAvoidsSourceNames
    (H : TrInductDeclCore base lparams nparams types isUnsafe decl
      envTypes envCtors)
    {name : Name} {ci : VConstant}
    (hlookup : base.constants name = some ci) :
    name ∉ decl.sourceNames := by
  intro hname
  have Hadd : base.addConstVals
      (decl.typeConstants ++ decl.constructorConstants) = some envCtors :=
    VEnv.addConstVals_append H.typesAdded H.ctorsAdded
  have Hfresh := (VEnv.addConstVals_names_fresh Hadd).2
  unfold VInductDecl.sourceNames at hname
  simp only [List.mem_append] at hname
  rcases hname with htype | hctor
  · rcases List.mem_map.mp htype with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_left _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction
  · rcases List.mem_map.mp hctor with ⟨value, hvalue, hvalueName⟩
    have habsent := Hfresh value (List.mem_append_right _ hvalue)
    rw [hvalueName, hlookup] at habsent
    contradiction

/-- A normalized telescope built in the pre-block checking environment
retains canonical restriction evidence after monotonic transport into any
later phase.  This is the producer-facing way to discharge the nested
header-prefix side condition: retain the original derivation, not an
assumption about every constant in the larger constructor environment. -/
theorem Expr.ForallTelescopeTypeTranslation.prefixUsesOnlyOfCoreBase
    (Hcore : TrInductDeclCore base lparams nparams types isUnsafe decl
      envTypes envCtors)
    (Hbase : Expr.ForallTelescopeTypeTranslation base levelParams ctx
      source arity target)
    (henv : base ≤ current) :
    (Hbase.mono henv).PrefixUsesOnly
      (fun name => name ∈ decl.sourceNames) :=
  (Expr.ForallTelescopeTypeTranslation.PrefixUsesOnly.of_constants Hbase
    (fun hlookup =>
      Lean4Lean.VerifyInductive.TrInductDeclCore.baseAvoidsSourceNames
        Hcore hlookup)).mono henv

/-- Exact source/target form of the retained normalized header telescope.
Keeping the witnesses definitionally visible lets later splitting recover
that the index suffix still ends in the harmless `Sort 0` residual. -/
theorem checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope.closedSortPrefixUsesOnlyExact
    (H : checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope
      base levelParams commonParams nparams nindices)
    (Hcore : TrInductDeclCore base lparams declNParams types isUnsafe decl
      envTypes envCtors)
    (hbase : base.WF) (henv : base ≤ current) :
    ∃ Hprefix : Expr.ForallTelescopeTypeTranslation current levelParams []
        (H.source.sources.closeSource (.sort (.zero : Level)))
        H.sourceScope.length
        (VExpr.wrapForalls H.sourceScope.toCtx.reverse
          (.sort (.zero : VLevel))),
      Hprefix.PrefixUsesOnly (fun name => name ∈ decl.sourceNames) := by
  have hzero : VLevel.ofLevel levelParams (.zero : Level) =
      some (.zero : VLevel) := rfl
  have Hsort : TrExprS base levelParams H.sourceScope
      (.sort (.zero : Level)) (.sort (.zero : VLevel)) :=
    .sort hzero
  have HsortType : base.IsType levelParams.length H.sourceScope.toCtx
      (.sort (.zero : VLevel)) :=
    ⟨.succ .zero, VEnv.HasType.sort (.of_ofLevel hzero)⟩
  let Hclosed := H.source.closeTypedTelescope hbase Hsort HsortType
  let Htransported := Hclosed.mono henv
  exact ⟨Htransported, Hclosed.prefixUsesOnlyOfCoreBase Hcore henv⟩

/-- A retained normalized header telescope produces a complete literal
pre-block source prefix whose transported derivation is certified not to use
the subsequently installed inductive block.  The residual is a harmless
`Sort 0`; nested restoration later replaces it with the family-specific
major/result suffix. -/
theorem checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope.closedSortPrefixUsesOnly
    (H : checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope
      base levelParams commonParams nparams nindices)
    (Hcore : TrInductDeclCore base lparams declNParams types isUnsafe decl
      envTypes envCtors)
    (hbase : base.WF) (henv : base ≤ current) :
    ∃ source target,
      ∃ Hprefix : Expr.ForallTelescopeTypeTranslation current levelParams []
        source H.sourceScope.length target,
        Hprefix.PrefixUsesOnly (fun name => name ∈ decl.sourceNames) := by
  rcases H.closedSortPrefixUsesOnlyExact Hcore hbase henv with
    ⟨Hprefix, HprefixUses⟩
  exact ⟨_, _, Hprefix, HprefixUses⟩

/-- Drop the common parameter portion of a retained normalized source header
and expose exactly its index telescope.  The executable header fold supplies
the full arity equation; `PrefixUsesOnly.dropPrefix` then preserves the
pre-block restriction evidence on the surviving index domains. -/
theorem checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope.closedIndexSuffixUsesOnly
    (H : checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope
      base levelParams commonParams nparams nindices)
    (Hcore : TrInductDeclCore base lparams declNParams types isUnsafe decl
      envTypes envCtors)
    (hbase : base.WF) (henv : base ≤ current) :
    ∃ source target parameterDomains indexSource indexTarget,
      parameterDomains.length = nparams ∧
      Expr.ForallTelescope source nparams indexSource ∧
      target = VExpr.wrapForalls parameterDomains indexTarget ∧
      Expr.ForallTelescope indexSource nindices
        (.sort (.zero : Level)) ∧
      ∃ Hindices : Expr.ForallTelescopeTypeTranslation current levelParams
          (abstractForallContext parameterDomains [])
          indexSource nindices indexTarget,
        Hindices.PrefixUsesOnly
          (fun name => name ∈ decl.sourceNames) := by
  rcases H.closedSortPrefixUsesOnlyExact Hcore hbase henv with
    ⟨Hprefix, HprefixUses⟩
  let source := H.source.sources.closeSource (.sort (.zero : Level))
  let target := VExpr.wrapForalls H.sourceScope.toCtx.reverse
    (.sort (.zero : VLevel))
  have harity : H.sourceScope.length = nindices + nparams := by
    calc
      H.sourceScope.length = nparams + nindices := H.sourceLength
      _ = nindices + nparams := Nat.add_comm _ _
  have Hpacked :
      ∃ Hfull : Expr.ForallTelescopeTypeTranslation current levelParams []
          source H.sourceScope.length target,
        Hfull.PrefixUsesOnly
          (fun name => name ∈ decl.sourceNames) :=
    ⟨Hprefix, HprefixUses⟩
  have Hpacked' :
      ∃ Hfull : Expr.ForallTelescopeTypeTranslation current levelParams []
          source (nindices + nparams) target,
        Hfull.PrefixUsesOnly
          (fun name => name ∈ decl.sourceNames) :=
    harity ▸ Hpacked
  rcases Hpacked' with ⟨Hfull, HfullUses⟩
  rcases Expr.ForallTelescopeTypeTranslation.PrefixUsesOnly.dropPrefix
      Hfull HfullUses with
    ⟨parameterDomains, indexSource, indexTarget, hparameters,
      Hsource, htarget, Hindices, HindicesUses⟩
  rcases Hindices.telescope with ⟨indexResidual, HindexSource⟩
  have Hcomplete := H.source.sources.closeSource_telescope
    (H.source.scopeWF hbase).fvars_nodup (.sort (.zero : Level))
  have hsortAbstract : ∀ fvars : List FVarId,
      (Expr.sort (.zero : Level)).abstractList fvars =
        .sort (.zero : Level) := by
    intro fvars
    induction fvars with
    | nil => rfl
    | cons fv fvars ih =>
      simp only [Expr.abstractList]
      rw [show (Expr.sort (.zero : Level)).abstract1 fv =
        .sort (.zero : Level) by rfl]
      exact ih
  rw [hsortAbstract] at Hcomplete
  have Hcombined : Expr.ForallTelescope source
      (nparams + nindices) indexResidual :=
    Hsource.trans HindexSource
  have Hcomplete' : Expr.ForallTelescope source
      (nparams + nindices) (.sort (.zero : Level)) := by
    simpa [source, H.sourceLength] using Hcomplete
  have hresidual : indexResidual = .sort (.zero : Level) :=
    Hcombined.residual_eq Hcomplete'
  subst indexResidual
  exact ⟨source, target, parameterDomains, indexSource, indexTarget,
    hparameters, Hsource, htarget, HindexSource, Hindices, HindicesUses⟩

/-- Rebuild the exact normalized index telescope in an independently
installed block environment.  Only the index domains are transported; the
dummy `Sort 0` residual is reconstructed directly in the target environment.
This is the producer-derived nested-restoration bridge, so callers need no
blanket assumption that the original motive translation survives replacing
the lowered family constants. -/
theorem checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope.closedIndexSuffixRebased
    (H : checkInductiveTypes.loopType.NormalizedHeaderSourceTelescope
      base levelParams commonParams nparams nindices)
    (Hcore : TrInductDeclCore base lparams declNParams types isUnsafe decl
      envTypes envCtors)
    (hbase : base.WF) (henv : base ≤ current)
    (E : VEnv.LEExcept (fun name => name ∈ decl.sourceNames)
      current targetEnv) :
    ∃ source target parameterDomains indexSource indexTarget,
      parameterDomains.length = nparams ∧
      Expr.ForallTelescope source nparams indexSource ∧
      target = VExpr.wrapForalls parameterDomains indexTarget ∧
      Expr.ForallTelescope indexSource nindices
        (.sort (.zero : Level)) ∧
      ∃ target', Expr.ForallTelescopeTypeTranslation targetEnv levelParams
        (abstractForallContext parameterDomains [])
        indexSource nindices target' := by
  rcases H.closedIndexSuffixUsesOnly Hcore hbase henv with
    ⟨source, target, parameterDomains, indexSource, indexTarget,
      hparameters, Hsource, htarget, HindexSource, Hindices,
      HindicesUses⟩
  have Hresidual :
      Expr.ForallTelescopeTypeTranslation.ResidualReplacement targetEnv
        Hindices :=
    Expr.ForallTelescopeTypeTranslation.ResidualReplacement.sortZero
      Hindices HindexSource
  rcases Hindices.rebasePrefixReplaceResidual E HindicesUses Hresidual with
    ⟨target', Htarget'⟩
  exact ⟨source, target, parameterDomains, indexSource, indexTarget,
    hparameters, Hsource, htarget, HindexSource, target', Htarget'⟩

/-- Family-indexed producer form of `closedIndexSuffixRebased`.  A completed
header traversal already retains the normalized source telescope for every
member of the mutual block, so nested restoration can select the owner row
directly and transport its exact index prefix into the independently
installed source block. -/
theorem checkInductiveTypes.loopInd.MaterializedHeaderResult.normalizedIndexSuffixRebasedAt
    {headerLparams : List Name}
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      base headerLparams ctx stats decl depth)
    (Hcore : TrInductDeclCore base lparams declNParams types isUnsafe decl
      envTypes envCtors)
    (hbase : base.WF)
    (i : Nat) (hi : i < decl.types.length)
    (E : VEnv.LEExcept (fun name => name ∈ decl.sourceNames)
      base targetEnv) :
    ∃ source target parameterDomains indexSource indexTarget,
      parameterDomains.length = decl.nparams ∧
      Expr.ForallTelescope source decl.nparams indexSource ∧
      target = VExpr.wrapForalls parameterDomains indexTarget ∧
      Expr.ForallTelescope indexSource decl.types[i].numIndices
        (.sort (.zero : Level)) ∧
      ∃ target', Expr.ForallTelescopeTypeTranslation targetEnv headerLparams
        (abstractForallContext parameterDomains [])
        indexSource decl.types[i].numIndices target' := by
  rcases H.normalizedSources i hi with ⟨Hsource⟩
  exact Hsource.closedIndexSuffixRebased Hcore hbase VEnv.LE.rfl E

/-- View the first-pass closed motive as a typed translation of precisely its
normalized index prefix.  The residual is the closed major-domain/result
telescope; it is intentionally left opaque because restoration reconstructs
that current-family portion in a different environment. -/
theorem RecursorMotiveTelescopeSeed.indexPrefixTranslation
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (H : RecursorMotiveTelescopeSeed Rroot stats decl target info elimLevel) :
    Expr.ForallTelescopeTypeTranslation Rroot.venv recLparams
      H.motiveClosedScope
      (root.lctx.mkForall info.indices
        (root.lctx.mkForall #[info.major] (.sort elimLevel)))
      info.indices.size H.motiveClosedTarget := by
  have Htelescope := H.indicesBound.mkForall_forallTelescope
    Rroot.toBindingContextWF
    (root.lctx.mkForall #[info.major] (.sort elimLevel))
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS Htelescope
    H.motiveClosedTr H.motiveClosedType

/-- Exact boundary data for transporting only an original header's
normalized index prefix.  No claim is made that the whole first-pass motive
is rebasable: its residual mentions the current family, whose installed
constant changes under nested restoration. -/
structure OriginalHeaderSeedRebaseAt
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (H : RecursorMotiveTelescopeSeed Rroot stats decl target info elimLevel)
    (targetEnv : VEnv) (changed : Name → Prop) : Prop where
  agreement : VEnv.LEExcept changed Rroot.venv targetEnv
  prefixUses :
    H.indexPrefixTranslation.PrefixUsesOnly changed

/-- Build the environment-agreement half of an original-header rebase from
the two independently translated blocks.  The only remaining datum is the
derivation-local fact that the normalized index prefix did not consult the
lowered block's own constants. -/
theorem OriginalHeaderSeedRebaseAt.ofCoreTranslations
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {H : RecursorMotiveTelescopeSeed Rroot stats fromDecl target info
      elimLevel}
    (Hfrom : TrInductDeclCore base fromLparams fromNparams fromTypes
      fromUnsafe fromDecl fromEnvTypes fromEnvCtors)
    (Hto : TrInductDeclCore base toLparams toNparams toTypes
      toUnsafe toDecl toEnvTypes toEnvCtors)
    (henv : Rroot.venv = fromEnvCtors)
    (Hprefix : H.indexPrefixTranslation.PrefixUsesOnly
      (fun name => name ∈ fromDecl.sourceNames)) :
    OriginalHeaderSeedRebaseAt H toEnvCtors
      (fun name => name ∈ fromDecl.sourceNames) where
  agreement := by
    rw [henv]
    exact Lean4Lean.VerifyInductive.TrInductDeclCore.ctorEnvsLEExcept
      Hfrom Hto
  prefixUses := Hprefix

/-- Splice a typed restored current-family residual beneath the transported
normalized index prefix.  The resulting abstract target is existential and
may differ definitionally from the lowered seed target. -/
theorem OriginalHeaderSeedRebaseAt.rebaseIndexPrefix
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {H : RecursorMotiveTelescopeSeed Rroot stats decl target info elimLevel}
    (C : OriginalHeaderSeedRebaseAt H targetEnv changed)
    (Hresidual : H.indexPrefixTranslation.ResidualReplacement targetEnv) :
    ∃ target', Expr.ForallTelescopeTypeTranslation targetEnv recLparams
      H.motiveClosedScope
      (root.lctx.mkForall info.indices
        (root.lctx.mkForall #[info.major] (.sort elimLevel)))
      info.indices.size target' :=
  H.indexPrefixTranslation.rebasePrefixReplaceResidual
    C.agreement C.prefixUses Hresidual

end VerifyInductive
end Lean4Lean
