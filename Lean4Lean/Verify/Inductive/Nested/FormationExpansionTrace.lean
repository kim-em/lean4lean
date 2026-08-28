import Lean4Lean.Verify.Inductive.Nested.EndToEnd
import Lean4Lean.Verify.Inductive.Nested.FormationEvidence
import Lean4Lean.Verify.Inductive.Nested.GeneratedQueueOrigins
import Lean4Lean.Verify.Inductive.Nested.GeneratedFamilyConstruction

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Projection of the concrete nested-lowering trace to formation

The ordinary expression translation erases concrete lets by interpreting
their bodies in a `vlet` context.  Consequently the projection induction must
relate those contexts by nested expansion, rather than by literal equality.
-/

/-- The metadata-prefix certificate preserves the result universe as well as
the index count.  `MaterializedInductivePrefix.numIndices` exposes the first
projection; formation needs this second projection at the same exact source
position. -/
theorem VInductDeclSkeleton.materializePrefix_resultLevel
    (skeleton : VInductDeclSkeleton) (expanded source : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length)
    (Hmaterialize : skeleton.materialize
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel)) = some source)
    (i : Nat) (hi : i < skeleton.types.length)
    (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).resultLevel =
      (expanded.types[i]'hexpanded).resultLevel := by
  rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize hi with
    ⟨data, hdata, hsourceLookup⟩
  have hmetadata :
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel))[i]? =
        some (expanded.types[i].numIndices,
          expanded.types[i].resultLevel) := by
    simp [hi, hle]
  have hdataEq : data =
      (expanded.types[i].numIndices, expanded.types[i].resultLevel) := by
    rw [hmetadata] at hdata
    exact Option.some.inj hdata.symm
  subst data
  have hsourceEq : source.types[i] =
      skeleton.types[i].toVInductiveType expanded.types[i].numIndices
        expanded.types[i].resultLevel := by
    rw [List.getElem?_eq_getElem hsource] at hsourceLookup
    exact Option.some.inj hsourceLookup
  have hresult := congrArg VInductiveType.resultLevel hsourceEq
  simpa [VInductiveTypeSkeleton.toVInductiveType] using hresult

theorem MaterializedInductivePrefix.resultLevel
    (H : MaterializedInductivePrefix source expanded)
    (hle : source.types.length ≤ expanded.types.length)
    (i : Nat) (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).resultLevel =
      (expanded.types[i]'hexpanded).resultLevel := by
  rcases H with ⟨skeleton, Hmaterialize⟩
  have hskeleton : skeleton.types.length = source.types.length :=
    (VInductDeclSkeleton.materialize_fields Hmaterialize).2.2.2.symm
  apply VInductDeclSkeleton.materializePrefix_resultLevel skeleton expanded
    source
  · simpa [hskeleton] using hle
  · exact Hmaterialize
  · simpa [hskeleton] using hsource

/-- Compatibility of a leaf relation with entering one additional concrete
binder.  The cutoff records binders internal to the abstract expression. -/
def NestedExpansionLeafLiftCompat
    (leaf : Nat → VExpr → VExpr → Prop) : Prop :=
  ∀ {depth source target} (cutoff : Nat),
    cutoff ≤ depth →
    leaf depth source target →
    leaf (depth + 1) (source.liftN 1 cutoff) (target.liftN 1 cutoff)

/-- The formation leaf is stable under precisely the binder lift exercised by
the structural projection.  Its two trailing application spines are lifted
pointwise, while retaining their recursively nested correspondence. -/
theorem VInductDecl.NestedAuxiliarySource.liftDepth
    (H : VInductDecl.NestedAuxiliarySource env source generated depth input
      output)
    (cutoff : Nat) (Hcutoff : cutoff ≤ depth) :
    VInductDecl.NestedAuxiliarySource env source generated (depth + 1)
      (input.liftN 1 cutoff) (output.liftN 1 cutoff) := by
  exact VInductDecl.NestedAuxiliarySource.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun env source generated depth input output _ =>
      ∀ cutoff, cutoff ≤ depth →
        VInductDecl.NestedAuxiliarySource env source generated (depth + 1)
          (input.liftN 1 cutoff) (output.liftN 1 cutoff))
    (motive_4 := fun env source generated absoluteDepth input output _ =>
      ∀ relativeDepth, absoluteDepth = source.nparams + relativeDepth →
        ∀ cutoff, cutoff ≤ relativeDepth →
          VInductDecl.NestedExprWFExpansion env source generated
            (source.nparams + (relativeDepth + 1))
            (input.liftN 1 cutoff) (output.liftN 1 cutoff))
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun {env source generated depth input output container containerFamily
        auxiliaryFamily sourceParams baseArgs levels auxiliaryLevels
        sourceTrailing targetTrailing} Hinstalled HcontainerFamily
        HauxiliaryFamily HsourceParams HbaseArgs HbaseClosed Hlevels HlevelsWF
        HauxiliaryLevels HauxiliaryType Hconstructors HoutputLevels Htrailing
        Hinput Houtput _ihInstalled ihTrailing cutoff Hcutoff => by
      subst input
      subst output
      have Htrailing' := ihTrailing depth rfl cutoff Hcutoff
      have Htrailing'' :
          VInductDecl.NestedExprWFExpansion env source generated
            (source.nparams + (depth + 1))
            (VExpr.mkApps VInductDecl.nestedTrailingMarker
              (sourceTrailing.map fun arg => arg.liftN 1 cutoff))
            (VExpr.mkApps VInductDecl.nestedTrailingMarker
              (targetTrailing.map fun arg => arg.liftN 1 cutoff)) := by
        simpa [VInductDecl.nestedTrailingMarker, VExpr.liftN_mkApps,
          VExpr.liftN] using Htrailing'
      refine .intro
        (sourceTrailing := sourceTrailing.map fun arg => arg.liftN 1 cutoff)
        (targetTrailing := targetTrailing.map fun arg => arg.liftN 1 cutoff)
        Hinstalled HcontainerFamily HauxiliaryFamily HsourceParams HbaseArgs
        HbaseClosed Hlevels HlevelsWF HauxiliaryLevels HauxiliaryType
        Hconstructors HoutputLevels Htrailing'' ?_ ?_
      · simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append,
          List.map_map]
        congr 2
        apply List.map_congr_left
        intro arg _
        exact VExpr.liftN'_liftN' (Nat.zero_le cutoff) Hcutoff
      · simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append]
        congr 2
        simp only [VInductDecl.paramVars, List.map_map]
        apply List.map_congr_left
        intro index _
        have Hge : cutoff ≤ depth + index :=
          Nat.le_trans Hcutoff (Nat.le_add_right depth index)
        simp [VExpr.liftN, liftVar, Nat.not_lt_of_ge Hge]
        omega)
    (fun {env source generated depth relativeDepth input output} hdepth
        _Hleaf ihLeaf requestedDepth habsolute cutoff Hcutoff => by
      have hrelative : requestedDepth = relativeDepth := by omega
      subst requestedDepth
      exact .hit (by omega) (ihLeaf cutoff Hcutoff))
    (fun relativeDepth _ cutoff _ => .bvar)
    (fun relativeDepth _ cutoff _ => .sort)
    (fun relativeDepth _ cutoff _ => .const)
    (fun _ _ ihFn ihArg relativeDepth habsolute cutoff Hcutoff =>
      .app (ihFn relativeDepth habsolute cutoff Hcutoff)
        (ihArg relativeDepth habsolute cutoff Hcutoff))
    (fun _ _ ihDomain ihBody relativeDepth habsolute cutoff Hcutoff =>
      .lam (ihDomain relativeDepth habsolute cutoff Hcutoff)
        (ihBody (relativeDepth + 1) (by omega) (cutoff + 1) (by omega)))
    (fun _ _ ihDomain ihBody relativeDepth habsolute cutoff Hcutoff =>
      .forallE (ihDomain relativeDepth habsolute cutoff Hcutoff)
        (ihBody (relativeDepth + 1) (by omega) (cutoff + 1) (by omega)))
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    H cutoff Hcutoff

theorem nestedAuxiliarySource_leafLiftCompat :
    NestedExpansionLeafLiftCompat
      (VInductDecl.NestedAuxiliarySource env source generated) :=
  fun cutoff Hcutoff Hleaf =>
    Lean4Lean.VerifyInductive.VInductDecl.NestedAuxiliarySource.liftDepth
      Hleaf cutoff Hcutoff

/-- Embed a relative constructor-field leaf at the absolute depth obtained by
placing it below the declaration's common-parameter prefix. -/
theorem VInductDecl.NestedAuxiliarySource.toAbsolute
    (H : VInductDecl.NestedAuxiliarySource env source generated depth input
      output) :
    VInductDecl.NestedAuxiliarySourceAbsolute env source generated
      (source.nparams + depth) input output :=
  ⟨depth, rfl, H⟩

/-- Recover the relative leaf at one exact absolute constructor depth. -/
theorem VInductDecl.NestedAuxiliarySourceAbsolute.toRelative
    (H : VInductDecl.NestedAuxiliarySourceAbsolute env source generated
      (source.nparams + depth) input output) :
    VInductDecl.NestedAuxiliarySource env source generated depth input
      output := by
  rcases H with ⟨relativeDepth, hdepth, Hrelative⟩
  have : depth = relativeDepth := Nat.add_left_cancel hdepth
  simpa [this] using Hrelative

/-- The absolute wrapper is stable under a binder inserted among the
constructor fields.  The arithmetic premise says exactly that the cutoff is
below the common-parameter prefix, ruling out the semantically invalid lift
that would insert a binder inside that prefix. -/
theorem VInductDecl.NestedAuxiliarySourceAbsolute.liftFieldDepth
    (H : VInductDecl.NestedAuxiliarySourceAbsolute env source generated
      depth input output)
    (cutoff : Nat) (Hcutoff : source.nparams + cutoff ≤ depth) :
    VInductDecl.NestedAuxiliarySourceAbsolute env source generated
      (depth + 1) (input.liftN 1 cutoff) (output.liftN 1 cutoff) := by
  rcases H with ⟨relativeDepth, hdepth, Hrelative⟩
  have hrelative : cutoff ≤ relativeDepth := by omega
  refine ⟨relativeDepth + 1, by omega, ?_⟩
  exact
    Lean4Lean.VerifyInductive.VInductDecl.NestedAuxiliarySource.liftDepth
      Hrelative cutoff hrelative

/-- Reindex a relative constructor-body expansion below the fixed common
parameter prefix.  Expressions are unchanged; only the leaf-depth convention
changes. -/
theorem VExpr.NestedExprExpansion.toAbsoluteConstructorDepth
    (H : VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySource env source generated)
      depth input output) :
    VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      (source.nparams + depth) input output := by
  induction H with
  | hit Hleaf =>
    exact .hit
      (Lean4Lean.VerifyInductive.VInductDecl.NestedAuxiliarySource.toAbsolute
        Hleaf)
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody =>
    exact .lam ihDomain (by simpa [Nat.add_assoc] using ihBody)
  | forallE _ _ ihDomain ihBody =>
    exact .forallE ihDomain (by simpa [Nat.add_assoc] using ihBody)

/-- General inverse reindexing theorem, with the absolute-depth equality
kept explicit so dependent induction can move beneath binders. -/
theorem VExpr.NestedExprExpansion.toRelativeConstructorDepthAux
    (H : VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      absoluteDepth input output)
    (hdepth : absoluteDepth = source.nparams + depth) :
    VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySource env source generated)
      depth input output := by
  induction H generalizing depth with
  | hit Hleaf =>
    rcases Hleaf with ⟨relativeDepth, habsolute, Hrelative⟩
    have heq : depth = relativeDepth := by omega
    simpa [heq] using VExpr.NestedExprExpansion.hit Hrelative
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihFn ihArg => exact .app (ihFn hdepth) (ihArg hdepth)
  | lam _ _ ihDomain ihBody =>
    exact .lam (ihDomain hdepth) (ihBody (by omega))
  | forallE _ _ ihDomain ihBody =>
    exact .forallE (ihDomain hdepth) (ihBody (by omega))

/-- Inverse of `toAbsoluteConstructorDepth` at an exact offset. -/
theorem VExpr.NestedExprExpansion.toRelativeConstructorDepth
    (H : VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      (source.nparams + depth) input output) :
    VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySource env source generated)
      depth input output :=
  VExpr.NestedExprExpansion.toRelativeConstructorDepthAux H rfl

/-- Structural nested expansion is stable under entering one surrounding
binder whenever its successful leaves are. -/
theorem VExpr.NestedExprExpansion.liftDepth
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (H : VExpr.NestedExprExpansion leaf depth source target) (cutoff : Nat)
    (Hcutoff : cutoff ≤ depth) :
    VExpr.NestedExprExpansion leaf (depth + 1)
      (source.liftN 1 cutoff) (target.liftN 1 cutoff) := by
  induction H generalizing cutoff with
  | hit Hleaf => exact .hit (Hlift cutoff Hcutoff Hleaf)
  | bvar => exact VExpr.NestedExprExpansion.refl leaf _ _
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihFn ihArg =>
    simpa [VExpr.liftN] using
      .app (ihFn cutoff Hcutoff) (ihArg cutoff Hcutoff)
  | lam _ _ ihDomain ihBody =>
    simpa [VExpr.liftN, Nat.add_assoc] using
      .lam (ihDomain cutoff Hcutoff)
        (ihBody (cutoff + 1) (Nat.add_le_add_right Hcutoff 1))
  | forallE _ _ ihDomain ihBody =>
    simpa [VExpr.liftN, Nat.add_assoc] using
      .forallE (ihDomain cutoff Hcutoff)
        (ihBody (cutoff + 1) (Nat.add_le_add_right Hcutoff 1))

/-- Binder-indexed expansion of two abstract forall telescopes.  The body is
compared beneath every accumulated binder, exactly matching
`NestedExprExpansion.forallE`. -/
inductive VExpr.NestedForallExpansion
    (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → List VExpr → VExpr → List VExpr → VExpr → Prop
  | nil
      (Hbody : VExpr.NestedExprExpansion leaf depth sourceBody targetBody) :
      VExpr.NestedForallExpansion leaf depth [] sourceBody [] targetBody
  | cons
      (Hdomain : VExpr.NestedExprExpansion leaf depth
        sourceDomain targetDomain)
      (Htail : VExpr.NestedForallExpansion leaf (depth + 1)
        sourceDomains sourceBody targetDomains targetBody) :
      VExpr.NestedForallExpansion leaf depth
        (sourceDomain :: sourceDomains) sourceBody
        (targetDomain :: targetDomains) targetBody

/-- Closing a binder-indexed expansion produces expansion of the complete
abstract forall types. -/
theorem VExpr.NestedForallExpansion.wrapForalls
    (H : VExpr.NestedForallExpansion leaf depth sourceDomains sourceBody
      targetDomains targetBody) :
    VExpr.NestedExprExpansion leaf depth
      (VExpr.wrapForalls sourceDomains sourceBody)
      (VExpr.wrapForalls targetDomains targetBody) := by
  induction H with
  | nil Hbody => simpa [VExpr.wrapForalls] using Hbody
  | cons Hdomain _ ih =>
    simpa [VExpr.wrapForalls] using
      VExpr.NestedExprExpansion.forallE Hdomain ih

/-- Translation contexts related by nested expansion.  Lambda declarations
advance concrete binder depth; let declarations retain it and relate the
stored values structurally. -/
inductive NestedExpansionCtx
    (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → VLCtx → VLCtx → Prop
  | nil : NestedExpansionCtx leaf depth [] []
  | vlam
      (Hctx : NestedExpansionCtx leaf depth source target)
      (Htype : VExpr.NestedExprExpansion leaf depth sourceType targetType) :
      NestedExpansionCtx leaf (depth + 1)
        ((ofv, .vlam sourceType) :: source)
        ((ofv, .vlam targetType) :: target)
  | vlet
      (Hctx : NestedExpansionCtx leaf depth source target)
      (Htype : VExpr.NestedExprExpansion leaf depth sourceType targetType)
      (Hvalue : VExpr.NestedExprExpansion leaf depth sourceValue targetValue) :
      NestedExpansionCtx leaf depth
        ((ofv, .vlet sourceType sourceValue) :: source)
        ((ofv, .vlet targetType targetValue) :: target)

/-- Reindex a relative constructor-body context below the fixed common
parameter prefix.  Every stored domain/value expansion is reindexed by the
same offset, so concrete translation lookups are unchanged. -/
theorem NestedExpansionCtx.toAbsoluteConstructorDepth
    (Hctx : NestedExpansionCtx
      (VInductDecl.NestedAuxiliarySource env source generated)
      depth sourceCtx targetCtx) :
    NestedExpansionCtx
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      (source.nparams + depth) sourceCtx targetCtx := by
  induction Hctx with
  | nil => exact .nil
  | vlam _ Htype ih =>
    exact .vlam ih (by
      exact VExpr.NestedExprExpansion.toAbsoluteConstructorDepth Htype)
  | vlet _ Htype Hvalue ih =>
    exact .vlet ih
      (VExpr.NestedExprExpansion.toAbsoluteConstructorDepth Htype)
      (VExpr.NestedExprExpansion.toAbsoluteConstructorDepth Hvalue)

/-- Corresponding variable lookups in expansion-related contexts return
expansion-related values. -/
theorem NestedExpansionCtx.find?_expansion
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hsource : sourceCtx.find? var = some (sourceValue, sourceType))
    (Htarget : targetCtx.find? var = some (targetValue, targetType)) :
    VExpr.NestedExprExpansion leaf depth sourceValue targetValue := by
  induction Hctx generalizing var sourceValue sourceType targetValue targetType with
  | nil => simp [VLCtx.find?] at Hsource
  | @vlam depth source target sourceType' targetType' ofv Hctx Htype ih =>
    simp only [VLCtx.find?] at Hsource Htarget
    cases hnext : VLCtx.next ofv var with
    | none =>
      simp only [hnext] at Hsource Htarget
      have hs : (.bvar 0 : VExpr) = sourceValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Hsource)
      have ht : (.bvar 0 : VExpr) = targetValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Htarget)
      rw [← hs, ← ht]
      exact .bvar
    | some next =>
      simp [hnext] at Hsource Htarget
      rcases Hsource with ⟨sourceValue', sourceType', Hsource', rfl, rfl⟩
      rcases Htarget with ⟨targetValue', targetType', Htarget', rfl, rfl⟩
      simpa [VLocalDecl.depth] using
        VExpr.NestedExprExpansion.liftDepth Hlift
          (ih Hsource' Htarget') 0 (Nat.zero_le _)
  | @vlet depth source target sourceType' targetType' sourceValue'
      targetValue' ofv Hctx Htype Hvalue ih =>
    simp only [VLCtx.find?] at Hsource Htarget
    cases hnext : VLCtx.next ofv var with
    | none =>
      simp only [hnext] at Hsource Htarget
      have hs : sourceValue' = sourceValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Hsource)
      have ht : targetValue' = targetValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Htarget)
      rwa [← hs, ← ht]
    | some next =>
      simp [hnext] at Hsource Htarget
      rcases Hsource with ⟨sourceValue'', sourceType'', Hsource', rfl, rfl⟩
      rcases Htarget with ⟨targetValue'', targetType'', Htarget', rfl, rfl⟩
      simpa [VLocalDecl.depth] using ih Hsource' Htarget'

/-- The exact compatibility required at the opaque `TrProj` boundary. -/
def NestedProjectionExpansionCompat
    (leaf : Nat → VExpr → VExpr → Prop) : Prop :=
  ∀ {depth sourceBody targetBody sourceTarget targetTarget
      structName index} {sourceCtx targetCtx : VLCtx},
    VExpr.NestedExprExpansion leaf depth sourceBody targetBody →
    TrProj sourceCtx.toCtx structName index sourceBody sourceTarget →
    TrProj targetCtx.toCtx structName index targetBody targetTarget →
    VExpr.NestedExprExpansion leaf depth sourceTarget targetTarget

/-- An absolute-depth projection theorem induces the relative theorem used
inside the opened constructor residual.  Both directions are exact depth
reindexings; no projection behavior is assumed here. -/
theorem NestedProjectionExpansionCompat.toRelativeConstructorDepth
    (Hproj : NestedProjectionExpansionCompat
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)) :
    NestedProjectionExpansionCompat
      (VInductDecl.NestedAuxiliarySource env source generated) := by
  intro depth sourceBody targetBody sourceTarget targetTarget structName index
    sourceCtx targetCtx Hbody Hsource Htarget
  have Habsolute := Hproj
    (VExpr.NestedExprExpansion.toAbsoluteConstructorDepth Hbody)
      Hsource Htarget
  exact VExpr.NestedExprExpansion.toRelativeConstructorDepth Habsolute

/-- Expressions whose translation cannot inspect local declarations.  This
is deliberately smaller than `TrExprS.IsUnique`: it excludes variables, so
translations are unique even when their source and target contexts differ. -/
inductive TrExprS.ContextFree : Expr → Prop
  | sort : ContextFree (.sort level)
  | const : ContextFree (.const name levels)
  | app : ContextFree fn → ContextFree arg → ContextFree (.app fn arg)
  | lit : ContextFree literal.toConstructor → ContextFree (.lit literal)
  | mdata : ContextFree body → ContextFree (.mdata data body)

/-- Translation of a context-free expression is independent of the local
context. -/
theorem TrExprS.ContextFree.translation_unique
    (Hfree : ContextFree expr)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx expr sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx expr targetTarget) :
    sourceTarget = targetTarget := by
  induction Hfree generalizing sourceCtx targetCtx sourceTarget targetTarget with
  | sort =>
    cases Hsource with
    | sort HsourceLevel =>
      cases Htarget with
      | sort HtargetLevel =>
        cases Option.some.inj (HsourceLevel.symm.trans HtargetLevel)
        rfl
  | const =>
    cases Hsource with
    | const _ HsourceLevels _ =>
      cases Htarget with
      | const _ HtargetLevels _ =>
        cases Option.some.inj (HsourceLevels.symm.trans HtargetLevels)
        rfl
  | app _ _ ihFn ihArg =>
    cases Hsource with
    | app _ _ HsourceFn HsourceArg =>
      cases Htarget with
      | app _ _ HtargetFn HtargetArg =>
        rw [ihFn HsourceFn HtargetFn, ihArg HsourceArg HtargetArg]
  | lit _ ih =>
    cases Hsource with
    | lit _ HsourceConstructor =>
      cases Htarget with
      | lit _ HtargetConstructor =>
        exact ih HsourceConstructor HtargetConstructor
  | mdata _ ih =>
    cases Hsource with
    | mdata HsourceBody =>
      cases Htarget with
      | mdata HtargetBody => exact ih HsourceBody HtargetBody

theorem TrExprS.ContextFree.natLitToConstructor :
    ∀ n, ContextFree (.natLitToConstructor n)
  | 0 => by
    simp [Expr.natLitToConstructor, Expr.natZero]
    exact .const
  | n + 1 => by
    simp [Expr.natLitToConstructor, Expr.natSucc]
    exact .app .const (.lit (natLitToConstructor n))

theorem TrExprS.ContextFree.strLitToConstructor (string : String) :
    ContextFree (.strLitToConstructor string) := by
  simp only [Expr.strLitToConstructor]
  apply ContextFree.app ContextFree.const
  induction string.toList with
  | nil =>
    simp
    exact .app .const .const
  | cons char chars ih =>
    simp only [List.foldr_cons]
    exact .app
      (.app
        (.app .const .const)
        (.app .const (.lit (natLitToConstructor char.toNat))))
      ih

theorem TrExprS.ContextFree.literal (literal : Literal) :
    ContextFree (.lit literal) := by
  apply ContextFree.lit
  cases literal with
  | natVal n => exact .natLitToConstructor n
  | strVal string => exact .strLitToConstructor string

/-- Two translations of the same concrete expression in expansion-related
contexts are themselves structurally expansion-related.  This is the
identity half of formation projection: it handles unchanged common-parameter
domains, including concrete lets, and delegates only opaque projections. -/
theorem TrExprS.abstractExpansionRelational
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hproj : NestedProjectionExpansionCompat leaf)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx expr sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx expr targetTarget) :
    VExpr.NestedExprExpansion leaf depth sourceTarget targetTarget := by
  induction Hsource generalizing targetCtx targetTarget depth with
  | bvar HsourceLookup =>
    cases Htarget with
    | bvar HtargetLookup =>
      exact Hctx.find?_expansion Hlift HsourceLookup HtargetLookup
  | fvar HsourceLookup =>
    cases Htarget with
    | fvar HtargetLookup =>
      exact Hctx.find?_expansion Hlift HsourceLookup HtargetLookup
  | sort HsourceLevel =>
    cases Htarget with
    | sort HtargetLevel =>
      cases Option.some.inj (HsourceLevel.symm.trans HtargetLevel)
      exact .sort
  | const _ HsourceLevels _ =>
    cases Htarget with
    | const _ HtargetLevels _ =>
      cases Option.some.inj (HsourceLevels.symm.trans HtargetLevels)
      exact .const
  | app _ _ HsourceFn HsourceArg ihFn ihArg =>
    cases Htarget with
    | app _ _ HtargetFn HtargetArg =>
      exact .app (ihFn Hctx HtargetFn) (ihArg Hctx HtargetArg)
  | lam _ HsourceDomain HsourceBody ihDomain ihBody =>
    cases Htarget with
    | lam _ HtargetDomain HtargetBody =>
      have Hdomain := ihDomain Hctx HtargetDomain
      exact .lam Hdomain
        (ihBody (.vlam Hctx Hdomain) HtargetBody)
  | forallE _ _ HsourceDomain HsourceBody ihDomain ihBody =>
    cases Htarget with
    | forallE _ _ HtargetDomain HtargetBody =>
      have Hdomain := ihDomain Hctx HtargetDomain
      exact .forallE Hdomain
        (ihBody (.vlam Hctx Hdomain) HtargetBody)
  | letE _ HsourceType HsourceValue HsourceBody ihType ihValue ihBody =>
    cases Htarget with
    | letE _ HtargetType HtargetValue HtargetBody =>
      have Htype := ihType Hctx HtargetType
      have Hvalue := ihValue Hctx HtargetValue
      exact ihBody (.vlet Hctx Htype Hvalue) HtargetBody
  | lit _ _ ih =>
    cases Htarget with
    | lit _ HtargetConstructor => exact ih Hctx HtargetConstructor
  | mdata _ ih =>
    cases Htarget with
    | mdata HtargetBody => exact ih Hctx HtargetBody
  | proj HsourceBody HsourceProj ih =>
    cases Htarget with
    | proj HtargetBody HtargetProj =>
      exact Hproj (ih Hctx HtargetBody) HsourceProj HtargetProj

/-- Pointwise form of relational translation projection for one unchanged
concrete application spine.  Source and target abstract arguments need not be
syntactically equal: preceding let declarations may translate to structurally
expanded values. -/
theorem TrExprS.forall₂_abstractExpansionRelational
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hproj : NestedProjectionExpansionCompat leaf)
    (Hsource : List.Forall₂ (TrExprS sourceVEnv lparams sourceCtx)
      concrete sourceTargets)
    (Htarget : List.Forall₂ (TrExprS targetVEnv lparams targetCtx)
      concrete targetTargets) :
    List.Forall₂ (VExpr.NestedExprExpansion leaf depth)
      sourceTargets targetTargets := by
  induction Hsource generalizing targetTargets with
  | nil =>
    cases Htarget
    exact .nil
  | cons HsourceHead _ ih =>
    cases Htarget with
    | cons HtargetHead HtargetTail =>
      exact .cons
        (TrExprS.abstractExpansionRelational Hctx Hlift Hproj HsourceHead
          HtargetHead)
        (ih HtargetTail)

/-- Pointwise expansion of an application spine lifts to expansion of the
whole application.  The accumulator-general form follows the actual
left-fold definition of `mkApps`. -/
theorem forall₂_mkApps_nestedExprExpansion
    (Hfn : VExpr.NestedExprExpansion leaf depth sourceFn targetFn)
    (Hargs : List.Forall₂ (VExpr.NestedExprExpansion leaf depth)
      sourceArgs targetArgs) :
    VExpr.NestedExprExpansion leaf depth
      (VExpr.mkApps sourceFn sourceArgs) (VExpr.mkApps targetFn targetArgs) := by
  induction Hargs generalizing sourceFn targetFn with
  | nil => simpa [VExpr.mkApps] using Hfn
  | cons Hhead _ ih =>
    simpa [VExpr.mkApps] using ih (.app Hfn Hhead)

/-- Package a structurally related trailing spine under the rigid marker used
by the mutually positive abstract formation judgment. -/
theorem forall₂_nestedTrailingExpansion
    (Hargs : List.Forall₂
      (VExpr.NestedExprExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth)
      sourceArgs targetArgs) :
    VInductDecl.NestedExprWFExpansion env source generated depth
      (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceArgs)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker targetArgs) :=
  nestedExprExpansion_toNestedExprWFExpansion
    (forall₂_mkApps_nestedExprExpansion (.const) Hargs)

/-- Add one selected concrete free variable as an abstract forall binder. -/
def pushSelectedForall (ctx : VLCtx) (binding : FVarId × VExpr) : VLCtx :=
  (some (binding.1, []), .vlam binding.2) :: ctx

@[simp] theorem pushSelectedForall_find_self
    (ctx : VLCtx) (binding : FVarId × VExpr) :
    (pushSelectedForall ctx binding).find? (.inr binding.1) =
      some (.bvar 0, binding.2.lift) := by
  simp [pushSelectedForall, VLCtx.find?, VLCtx.next, VLocalDecl.value,
    VLocalDecl.type]

theorem pushSelectedForall_find_ne
    (hne : binding.1 ≠ fv) :
    (pushSelectedForall ctx binding).find? (.inr fv) =
      (ctx.find? (.inr fv)).map fun value =>
        (value.1.liftN 1 0, value.2.liftN 1 0) := by
  cases hfind : ctx.find? (.inr fv) <;>
    simp [pushSelectedForall, VLCtx.find?, VLCtx.next, hne,
      VLocalDecl.depth, hfind]

/-- Folding fresh selected binders over an existing bound-variable lookup
increments that variable by exactly the number of new forall binders. -/
theorem foldl_pushSelectedForall_find_bvar
    {base : VLCtx} {fv : FVarId} {k : Nat} {type : VExpr}
    (bindings : List (FVarId × VExpr))
    (Hbase : base.find? (.inr fv) = some (.bvar k, type))
    (Hfresh : ∀ binding ∈ bindings, binding.1 ≠ fv) :
    ∃ finalType,
      (bindings.foldl pushSelectedForall base).find? (.inr fv) =
        some (.bvar (k + bindings.length), finalType) := by
  induction bindings generalizing base k type with
  | nil => exact ⟨type, by simpa using Hbase⟩
  | cons binding bindings ih =>
      have hne : binding.1 ≠ fv := Hfresh binding (by simp)
      have Hnext : (pushSelectedForall base binding).find? (.inr fv) =
          some (.bvar (k + 1), type.liftN 1 0) := by
        rw [pushSelectedForall_find_ne hne, Hbase]
        simp [VExpr.liftN]
      rcases ih Hnext (fun next hnext => Hfresh next (by simp [hnext])) with
        ⟨finalType, Hfinal⟩
      exact ⟨finalType, by
        change
          (bindings.foldl pushSelectedForall
            (pushSelectedForall base binding)).find? (.inr fv) =
            some (.bvar (k + (bindings.length + 1)), finalType)
        rw [← show k + 1 + bindings.length =
          k + (bindings.length + 1) by omega]
        exact Hfinal⟩

/-- A selected binder can be recovered at its exact de Bruijn position after
the complete duplicate-free prefix is folded into the translation context. -/
theorem foldl_pushSelectedForall_find_getElem
    (bindings : List (FVarId × VExpr))
    (hnodup : (bindings.map Prod.fst).Nodup)
    (i : Nat) (hi : i < bindings.length) :
    ∃ finalType,
      (bindings.foldl pushSelectedForall base).find?
          (.inr bindings[i].1) =
        some (.bvar (bindings.length - 1 - i), finalType) := by
  induction bindings generalizing base i with
  | nil => simp at hi
  | cons binding bindings ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hhead, htail⟩
      cases i with
      | zero =>
          have Hfresh : ∀ next ∈ bindings, next.1 ≠ binding.1 := by
            intro next hnext heq
            exact hhead (List.mem_map.mpr ⟨next, hnext, heq⟩)
          rcases foldl_pushSelectedForall_find_bvar bindings
              (pushSelectedForall_find_self base binding) Hfresh with
            ⟨finalType, Hfinal⟩
          exact ⟨finalType, by simpa using Hfinal⟩
      | succ i =>
          have hiTail : i < bindings.length := by simpa using hi
          rcases ih htail i hiTail (base := pushSelectedForall base binding)
              with ⟨finalType, Hfinal⟩
          exact ⟨finalType, by
            change
              (bindings.foldl pushSelectedForall
                (pushSelectedForall base binding)).find?
                  (.inr bindings[i].1) =
                some (.bvar (bindings.length - (i + 1)), finalType)
            rw [show bindings.length - (i + 1) =
              bindings.length - 1 - i by omega]
            exact Hfinal⟩

/-- Exact residual view of two translated concrete forall prefixes after
opening them with the same fresh free variables.  The `close` field is the
structural induction that reattaches all translated binder domains. -/
structure NestedOpenedForallProjection
    (sourceVEnv targetVEnv : VEnv) (lparams : List Name)
    (leaf : Nat → VExpr → VExpr → Prop)
    (depth arity : Nat) (source target : Expr) (fvars : List FVarId)
    (sourceBaseCtx targetBaseCtx : VLCtx)
    (sourceTarget targetTarget : VExpr) where
  sourceResidual : Expr
  targetResidual : Expr
  sourceCtx : VLCtx
  targetCtx : VLCtx
  sourceResidualTarget : VExpr
  targetResidualTarget : VExpr
  contexts : NestedExpansionCtx leaf (depth + arity) sourceCtx targetCtx
  sourceTranslation : TrExprS sourceVEnv lparams sourceCtx sourceResidual
    sourceResidualTarget
  targetTranslation : TrExprS targetVEnv lparams targetCtx targetResidual
    targetResidualTarget
  sourceResidualData : ∃ residual,
    Expr.ForallTelescope source arity residual ∧
    sourceResidual = residual.instantiateRevList (fvars.map Expr.fvar)
  targetResidualData : ∃ residual,
    Expr.ForallTelescope target arity residual ∧
    targetResidual = residual.instantiateRevList (fvars.map Expr.fvar)
  sourceBindings : List (FVarId × VExpr)
  sourceBindingFVars : sourceBindings.map Prod.fst = fvars
  sourceContext_eq : sourceCtx =
    sourceBindings.foldl pushSelectedForall sourceBaseCtx
  targetBindings : List (FVarId × VExpr)
  targetBindingFVars : targetBindings.map Prod.fst = fvars
  targetContext_eq : targetCtx =
    targetBindings.foldl pushSelectedForall targetBaseCtx
  parameterPrefix :
    VExpr.NestedExprExpansion leaf (depth + arity)
        sourceResidualTarget targetResidualTarget →
      VExpr.NestedForallPrefixExpansion leaf depth arity
        sourceTarget targetTarget
  close : VExpr.NestedExprExpansion leaf (depth + arity)
      sourceResidualTarget targetResidualTarget →
    VExpr.NestedExprExpansion leaf depth sourceTarget targetTarget

/-- The retained source-prefix equation exposes every selected concrete
parameter as its canonical de Bruijn variable. -/
theorem NestedOpenedForallProjection.sourceParameterLookup
    (H : NestedOpenedForallProjection sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length) :
    ∃ type,
      H.sourceCtx.find? (.inr fvars[i]) =
        some (.bvar (fvars.length - 1 - i), type) := by
  have hbindingsLength : H.sourceBindings.length = fvars.length := by
    simpa using congrArg List.length H.sourceBindingFVars
  have hiBindings : i < H.sourceBindings.length := by
    simpa [hbindingsLength] using hi
  have hnodupBindings : (H.sourceBindings.map Prod.fst).Nodup := by
    simpa [H.sourceBindingFVars] using hnodup
  rcases foldl_pushSelectedForall_find_getElem H.sourceBindings
      hnodupBindings i hiBindings (base := sourceBaseCtx) with
    ⟨type, Hlookup⟩
  have hname : H.sourceBindings[i].1 = fvars[i] := by
    have hiMap : i < (H.sourceBindings.map Prod.fst).length := by
      simpa using hiBindings
    have hgets := congrArg (fun names : List FVarId => names[i]?)
      H.sourceBindingFVars
    rw [List.getElem?_eq_getElem hiMap, List.getElem?_eq_getElem hi] at hgets
    simpa using hgets
  rw [H.sourceContext_eq, ← hname]
  exact ⟨type, by simpa [hbindingsLength] using Hlookup⟩

/-- The retained target-prefix equation exposes every selected concrete
parameter as its canonical de Bruijn variable. -/
theorem NestedOpenedForallProjection.targetParameterLookup
    (H : NestedOpenedForallProjection sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length) :
    ∃ type,
      H.targetCtx.find? (.inr fvars[i]) =
        some (.bvar (fvars.length - 1 - i), type) := by
  have hbindingsLength : H.targetBindings.length = fvars.length := by
    simpa using congrArg List.length H.targetBindingFVars
  have hiBindings : i < H.targetBindings.length := by
    simpa [hbindingsLength] using hi
  have hnodupBindings : (H.targetBindings.map Prod.fst).Nodup := by
    simpa [H.targetBindingFVars] using hnodup
  rcases foldl_pushSelectedForall_find_getElem H.targetBindings
      hnodupBindings i hiBindings (base := targetBaseCtx) with
    ⟨type, Hlookup⟩
  have hname : H.targetBindings[i].1 = fvars[i] := by
    have hiMap : i < (H.targetBindings.map Prod.fst).length := by
      simpa using hiBindings
    have hgets := congrArg (fun names : List FVarId => names[i]?)
      H.targetBindingFVars
    rw [List.getElem?_eq_getElem hiMap, List.getElem?_eq_getElem hi] at hgets
    simpa using hgets
  rw [H.targetContext_eq, ← hname]
  exact ⟨type, by simpa [hbindingsLength] using Hlookup⟩

/-- Exact lookup invariant for the constructor's common parameters while
the residual lowering traversal enters additional field binders. -/
def SelectedParameterTargets
    (fvars : List FVarId) (fieldDepth : Nat) (targetCtx : VLCtx) : Prop :=
  ∀ (i : Nat) (hi : i < fvars.length), ∃ type,
    targetCtx.find? (.inr fvars[i]) =
      some (.bvar (fieldDepth + (fvars.length - 1 - i)), type)

theorem NestedOpenedForallProjection.selectedParameterTargets
    (H : NestedOpenedForallProjection sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup) :
    SelectedParameterTargets fvars 0 H.targetCtx := by
  intro i hi
  simpa using H.targetParameterLookup hnodup i hi

theorem NestedOpenedForallProjection.selectedParameterSources
    (H : NestedOpenedForallProjection sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup) :
    SelectedParameterTargets fvars 0 H.sourceCtx := by
  intro i hi
  simpa using H.sourceParameterLookup hnodup i hi

theorem SelectedParameterTargets.vlam
    (H : SelectedParameterTargets fvars fieldDepth targetCtx) :
    SelectedParameterTargets fvars (fieldDepth + 1)
      ((none, .vlam targetType) :: targetCtx) := by
  intro i hi
  rcases H i hi with ⟨type, Hlookup⟩
  refine ⟨type.liftN 1 0, ?_⟩
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.depth, Hlookup, VExpr.liftN]
  omega

theorem SelectedParameterTargets.vlet
    (H : SelectedParameterTargets fvars fieldDepth targetCtx) :
    SelectedParameterTargets fvars fieldDepth
      ((none, .vlet targetType targetValue) :: targetCtx) := by
  intro i hi
  rcases H i hi with ⟨type, Hlookup⟩
  refine ⟨type, ?_⟩
  simpa [VLCtx.find?, VLCtx.next, VLocalDecl.depth, Hlookup]

/-- The executable opening selection, together with the retained target
context lookups, determines the abstract translation of the complete selected
parameter array.  This is the exact bridge from concrete `As` to the
de-Bruijn prefix required by `NestedAuxiliarySource`. -/
theorem SelectedParameterTargets.translatedSelection
    {sourceDecl : VInductDecl}
    (Hselection : LocalForallSelection lctx As)
    (Hparams : SelectedParameterTargets Hselection.fvars fieldDepth targetCtx)
    (Htargets : List.Forall₂ (TrExprS targetVEnv lparams targetCtx)
      As.toList targets)
    (harity : As.size = sourceDecl.nparams) :
    targets = sourceDecl.paramVars fieldDepth := by
  have hfvarsLength : Hselection.fvars.length = As.size := by
    have hsize := congrArg Array.size Hselection.expressions
    simpa using hsize.symm
  have htargetsLength : targets.length = As.size := by
    simpa using (Lean4Lean.List.Forall₂.length_eq Htargets).symm
  apply List.ext_getElem
  · simpa [VInductDecl.paramVars, htargetsLength, ← harity]
  · intro i hiTarget hiParam
    have hiAs : i < As.toList.length := by simpa [htargetsLength] using hiTarget
    have hiFVars : i < Hselection.fvars.length := by
      simpa [hfvarsLength] using hiAs
    have Htranslated := Lean4Lean.VerifyInductive.List.Forall₂.getElem
      Htargets i hiAs hiTarget
    have hsource : As.toList[i] = .fvar Hselection.fvars[i] := by
      have harr : As.toList = Hselection.fvars.map Expr.fvar := by
        simpa using congrArg Array.toList Hselection.expressions
      have hiMap : i < (Hselection.fvars.map Expr.fvar).length := by
        simpa using hiFVars
      have hget := congrArg (fun xs : List Expr => xs[i]?) harr
      rw [List.getElem?_eq_getElem hiAs,
        List.getElem?_eq_getElem hiMap] at hget
      simpa using hget
    rw [hsource] at Htranslated
    cases Htranslated with
    | fvar Hlookup =>
      rcases Hparams i hiFVars with ⟨type, Hcanonical⟩
      have hvalue := congrArg Prod.fst <|
        Option.some.inj (Hlookup.symm.trans Hcanonical)
      simpa [VInductDecl.paramVars, List.getElem_reverse, hfvarsLength,
        harity] using hvalue

/-- Exact abstract output spine selected by one successful replacement.  The
concrete trace fixes the auxiliary name and universe arguments; the anchored
constructor context fixes the translated common-parameter prefix. -/
structure NestedReplacementTargetSpine
    (Htrace : NestedReplacementFinalTrace prodEnv lctx result.params As input
      state output nextState result finalState)
    (Hselection : LocalForallSelection lctx As)
    (Htarget : TrExprS targetVEnv lparams targetCtx output targetValue)
    (sourceDecl : VInductDecl) (fieldDepth : Nat) where
  value : InductiveVal
  targetName : Name
  levels : List Level
  auxName : Name
  concreteAuxLevels : List Level
  nested : Expr
  candidate : NestedAppCandidate prodEnv state input value
  inputHead : input.getAppFn = .const targetName levels
  replacement : output = mkAppRange
    (mkAppN (.const auxName concreteAuxLevels) As)
    value.numParams input.getAppArgs.size input.getAppArgs
  nested_eq : (nested ==
    ((mkAppRange (.const targetName levels) 0 value.numParams
      input.getAppArgs).abstract As).instantiateRev result.params) = true
  resultLookup : result.aux2nested.find? auxName = some nested
  auxiliaryLevels : List VLevel
  trailing : List VExpr
  auxiliaryLevelsTranslation :
    concreteAuxLevels.mapM (VLevel.ofLevel lparams) = some auxiliaryLevels
  targetValue_eq : targetValue = VExpr.mkApps (.const auxName auxiliaryLevels)
    (sourceDecl.paramVars fieldDepth ++ trailing)
  trailingTranslation : List.Forall₂ (TrExprS targetVEnv lparams targetCtx)
    (input.getAppArgsList.drop value.numParams) trailing

theorem NestedReplacementFinalTrace.targetSpine
    (Htrace : NestedReplacementFinalTrace prodEnv lctx result.params As input
      state output nextState result finalState)
    (Hselection : LocalForallSelection lctx As)
    (Harity : As.size = result.params.size)
    (Hparams : SelectedParameterTargets Hselection.fvars fieldDepth targetCtx)
    (hsourceParams : result.params.size = sourceDecl.nparams)
    (Htarget : TrExprS targetVEnv lparams targetCtx output targetValue) :
    Nonempty (NestedReplacementTargetSpine Htrace Hselection Htarget sourceDecl
      fieldDepth) := by
  rcases Htrace.mapping with
    ⟨value, targetName, levels, auxName, concreteAuxLevels, nested,
      Hcandidate, hhead, hreplacement, hnested, hlookup⟩
  have houtput : output = Expr.mkAppList (.const auxName concreteAuxLevels)
      (As.toList ++ input.getAppArgsList.drop value.numParams) := by
    rw [hreplacement]
    rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
    rw [Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
    simp only [Expr.getAppArgs_toList]
  rw [houtput] at Htarget
  rcases Lean4Lean.VerifyInductive.checkPositivityStep.TrExprS.mkAppList_append_inv
      Htarget with
    ⟨headTarget, parameterTargets, trailing, HheadTarget,
      HparameterTargets, Htrailing, htarget⟩
  cases HheadTarget with
  | const _ HauxLevels _ =>
    have hparameters := Hparams.translatedSelection Hselection
      HparameterTargets (Harity.trans hsourceParams)
    exact ⟨{
      value := value
      targetName := targetName
      levels := levels
      auxName := auxName
      concreteAuxLevels := concreteAuxLevels
      nested := nested
      candidate := Hcandidate
      inputHead := hhead
      replacement := hreplacement
      nested_eq := hnested
      resultLookup := hlookup
      auxiliaryLevels := _
      trailing := trailing
      auxiliaryLevelsTranslation := HauxLevels
      targetValue_eq := by simpa [hparameters] using htarget
      trailingTranslation := Htrailing }⟩

/-- Source-side application spine at the same exact successful hit.  This is
obtained solely by splitting the original application at the recognized
container's common-parameter arity. -/
structure NestedReplacementSourceSpine
    (targetName : Name) (levels : List Level) (value : InductiveVal)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx input sourceValue) where
  sourceLevels : List VLevel
  baseArgsAtDepth : List VExpr
  trailing : List VExpr
  sourceLevelsTranslation :
    levels.mapM (VLevel.ofLevel lparams) = some sourceLevels
  baseArgsTranslation : List.Forall₂ (TrExprS sourceVEnv lparams sourceCtx)
    (input.getAppArgsList.take value.numParams) baseArgsAtDepth
  trailingTranslation : List.Forall₂ (TrExprS sourceVEnv lparams sourceCtx)
    (input.getAppArgsList.drop value.numParams) trailing
  sourceValue_eq : sourceValue =
    VExpr.mkApps (.const targetName sourceLevels)
      (baseArgsAtDepth ++ trailing)

theorem NestedReplacementTargetSpine.sourceSpine
    {prodEnv : Environment} {lctx : LocalContext}
    {result : Lean4Lean.ElimNestedInductive.Result} {As : Array Expr}
    {input output : Expr} {state nextState finalState :
      Lean4Lean.ElimNestedInductive.State}
    {Htrace : NestedReplacementFinalTrace prodEnv lctx result.params As input
      state output nextState result finalState}
    {Hselection : LocalForallSelection lctx As}
    {targetVEnv : VEnv} {lparams : List Name} {targetCtx : VLCtx}
    {targetValue : VExpr}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    {sourceDecl : VInductDecl} {fieldDepth : Nat}
    (T : NestedReplacementTargetSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx input sourceValue) :
    Nonempty (NestedReplacementSourceSpine
      (sourceVEnv := sourceVEnv) (sourceCtx := sourceCtx)
      (sourceValue := sourceValue) (lparams := lparams) (input := input)
      T.targetName T.levels T.value Hsource) := by
  have hinput : input = Expr.mkAppList (.const T.targetName T.levels)
      (input.getAppArgsList.take T.value.numParams ++
        input.getAppArgsList.drop T.value.numParams) := by
    rw [List.take_append_drop]
    exact (Expr.mkAppList_getAppArgsList input).symm.trans (by
      rw [T.inputHead])
  rw [hinput] at Hsource
  rcases Lean4Lean.VerifyInductive.checkPositivityStep.TrExprS.mkAppList_append_inv
      Hsource with
    ⟨headTarget, baseArgsAtDepth, trailing, Hhead, Hbase, Htrailing,
      hsource⟩
  cases Hhead with
  | const _ Hlevels _ =>
    exact ⟨{
      sourceLevels := _
      baseArgsAtDepth := baseArgsAtDepth
      trailing := trailing
      sourceLevelsTranslation := Hlevels
      baseArgsTranslation := Hbase
      trailingTranslation := Htrailing
      sourceValue_eq := hsource }⟩

/-- The exact auxiliary name selected by the translated target spine rejoins
the append-only generated-family queue without any name/equality heuristic. -/
theorem NestedReplacementTargetSpine.finalGeneratedFamilyOrigin
    {prodEnv : Environment} {lctx : LocalContext}
    {result : Lean4Lean.ElimNestedInductive.Result} {As : Array Expr}
    {input output : Expr} {state nextState finalState :
      Lean4Lean.ElimNestedInductive.State}
    {Htrace : NestedReplacementFinalTrace prodEnv lctx result.params As input
      state output nextState result finalState}
    {Hselection : LocalForallSelection lctx As}
    {targetVEnv : VEnv} {lparams : List Name} {targetCtx : VLCtx}
    {targetValue : VExpr}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    {sourceDecl : VInductDecl} {fieldDepth : Nat}
    (T : NestedReplacementTargetSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (Hrun : NestedLoweringRun prodEnv fuel nparams sourceTypes initialState
      (result, runFinalState))
    (Henv : EnvironmentTypesClosed prodEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hinitialTypes : initialState.newTypes = sourceTypes.toArray)
    (hempty : initialState.nestedAux = #[]) :
    Nonempty (FinalCachedGeneratedFamilyOrigin prodEnv result.params nparams
      initialState.newTypes.size runFinalState T.nested T.auxName) :=
  Hrun.finalCachedGeneratedFamilyOriginOfLookup Henv Hsources hinitialTypes
    hempty T.resultLookup

/-- The generated queue origin selected by this exact hit carries finite
installed-inductive provenance for the container family. -/
theorem NestedReplacementTargetSpine.generatedInstalledContainer
    {prodEnv : Environment} {lctx : LocalContext}
    {result : Lean4Lean.ElimNestedInductive.Result} {As : Array Expr}
    {input output : Expr} {state nextState finalState :
      Lean4Lean.ElimNestedInductive.State}
    {Htrace : NestedReplacementFinalTrace prodEnv lctx result.params As input
      state output nextState result finalState}
    {Hselection : LocalForallSelection lctx As}
    {targetVEnv : VEnv} {lparams : List Name} {targetCtx : VLCtx}
    {targetValue : VExpr}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    {sourceDecl : VInductDecl} {fieldDepth : Nat} {ves : VEnvs}
    (T : NestedReplacementTargetSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (Hrun : NestedLoweringRun prodEnv fuel nparams sourceTypes initialState
      (result, runFinalState))
    (Henv : EnvironmentTypesClosed prodEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hinitialTypes : initialState.newTypes = sourceTypes.toArray)
    (hempty : initialState.nestedAux = #[])
    (wf : ves.WF prodEnv) :
    ∃ O : FinalCachedGeneratedFamilyOrigin prodEnv result.params nparams
        initialState.newTypes.size runFinalState T.nested T.auxName,
      Nonempty (GeneratedFamilyInstalledContainer prodEnv (ves.venv .unsafe)
        result.params runFinalState.nestedAux O.origin.source
        O.origin.generated) := by
  rcases T.finalGeneratedFamilyOrigin Hrun Henv Hsources hinitialTypes hempty
      with ⟨O⟩
  exact ⟨O, O.origin.generated.installedContainer wf⟩

/-- Complete local spine projection for one hit.  The unchanged concrete
trailing arguments project to a structural expansion, not in general to
literal equality: translated let-bound values may already differ because of
earlier lowering. -/
theorem NestedReplacementFinalTrace.translatedSpines
    (Htrace : NestedReplacementFinalTrace prodEnv lctx result.params As input
      state output nextState result finalState)
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hselection : LocalForallSelection lctx As)
    (Harity : As.size = result.params.size)
    (HtargetParams : SelectedParameterTargets Hselection.fvars fieldDepth
      targetCtx)
    (hsourceParams : result.params.size = sourceDecl.nparams)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx input sourceValue)
    (Htarget : TrExprS targetVEnv lparams targetCtx output targetValue)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hproj : NestedProjectionExpansionCompat leaf) :
    ∃ (T : NestedReplacementTargetSpine Htrace Hselection Htarget sourceDecl
        fieldDepth)
      (S : NestedReplacementSourceSpine T.targetName T.levels T.value Hsource),
      List.Forall₂ (VExpr.NestedExprExpansion leaf depth)
        S.trailing T.trailing := by
  rcases Htrace.targetSpine Hselection Harity HtargetParams hsourceParams
      Htarget with ⟨T⟩
  rcases T.sourceSpine Hsource with ⟨S⟩
  exact ⟨T, S,
    TrExprS.forall₂_abstractExpansionRelational Hctx Hlift Hproj
      S.trailingTranslation T.trailingTranslation⟩

/-- Translate a shared concrete forall prefix while replacing its anonymous
de Bruijn binders by one exact duplicate-free list of opening fvars.  This is
the closed/opened bridge needed by constructor lowering: the returned
residual translations live in contexts where `NestedExprMapping`'s opened
tail can be projected directly. -/
theorem Expr.SameForallPrefix.openedAbstractProjection
    (Hsame : Expr.SameForallPrefix arity source target)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (HsourceCtxWF : sourceCtx.WF sourceVEnv lparams.length)
    (HtargetCtxWF : targetCtx.WF targetVEnv lparams.length)
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hproj : NestedProjectionExpansionCompat leaf)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx source sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx target targetTarget)
    (fvars : List FVarId) (hfvars : fvars.length = arity)
    (hnodup : fvars.Nodup)
    (HsourceFresh : ∀ fv ∈ fvars, fv ∉ sourceCtx.fvars)
    (HtargetFresh : ∀ fv ∈ fvars, fv ∉ targetCtx.fvars) :
    Nonempty (NestedOpenedForallProjection sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceCtx targetCtx sourceTarget
      targetTarget) := by
  induction arity generalizing source target depth sourceCtx targetCtx
      sourceTarget targetTarget fvars with
  | zero =>
    cases Hsame with
    | nil =>
    have hfvarsNil : fvars = [] := List.eq_nil_of_length_eq_zero hfvars
    subst fvars
    exact ⟨{
      sourceResidual := source
      targetResidual := target
      sourceCtx := sourceCtx
      targetCtx := targetCtx
      sourceResidualTarget := sourceTarget
      targetResidualTarget := targetTarget
      contexts := by simpa using Hctx
      sourceTranslation := Hsource
      targetTranslation := Htarget
      sourceResidualData := ⟨source, .nil source, by simp⟩
      targetResidualData := ⟨target, .nil target, by simp⟩
      sourceBindings := []
      sourceBindingFVars := rfl
      sourceContext_eq := rfl
      targetBindings := []
      targetBindingFVars := rfl
      targetContext_eq := rfl
      parameterPrefix := fun Htail => by simpa using
        VExpr.NestedForallPrefixExpansion.nil Htail
      close := fun Htail => by simpa using Htail }⟩
  | succ arity ih =>
    cases Hsame with
    | @cons _ sourceBody targetBody name domain bi Htail =>
    cases fvars with
    | nil => simp at hfvars
    | cons fv fvars =>
      cases Hsource with
      | @forallE sourceDomainTarget sourceBodyTarget _ _ _ _ _
          HsourceDomainType HsourceBodyType HsourceDomain HsourceBody =>
        cases Htarget with
        | @forallE targetDomainTarget targetBodyTarget _ _ _ _ _
            HtargetDomainType HtargetBodyType HtargetDomain HtargetBody =>
          have htailLength : fvars.length = arity := by simpa using hfvars
          have htailNodup : fvars.Nodup := (List.nodup_cons.mp hnodup).2
          have hsourceFv : fv ∉ sourceCtx.fvars :=
            HsourceFresh fv (by simp)
          have htargetFv : fv ∉ targetCtx.fvars :=
            HtargetFresh fv (by simp)
          let sourceCtx' : VLCtx :=
            (some (fv, []), .vlam sourceDomainTarget) :: sourceCtx
          let targetCtx' : VLCtx :=
            (some (fv, []), .vlam targetDomainTarget) :: targetCtx
          have HsourceCtxWF' : sourceCtx'.WF sourceVEnv lparams.length := by
            refine ⟨HsourceCtxWF, ?_, HsourceDomainType⟩
            intro other deps heq
            simp at heq
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨hsourceFv, by simp⟩
          have HtargetCtxWF' : targetCtx'.WF targetVEnv lparams.length := by
            refine ⟨HtargetCtxWF, ?_, HtargetDomainType⟩
            intro other deps heq
            simp at heq
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨htargetFv, by simp⟩
          have Hdomain : VExpr.NestedExprExpansion leaf depth
              sourceDomainTarget targetDomainTarget :=
            TrExprS.abstractExpansionRelational Hctx Hlift Hproj
              HsourceDomain HtargetDomain
          have Hctx' : NestedExpansionCtx leaf (depth + 1)
              sourceCtx' targetCtx' := by
            exact NestedExpansionCtx.vlam (ofv := some (fv, [])) Hctx Hdomain
          have HsourceBody' : TrExprS sourceVEnv lparams sourceCtx'
              (sourceBody.instantiate1' (.fvar fv)) sourceBodyTarget := by
            exact HsourceBody.inst_fvar HsourceEnvWF.ordered HsourceCtxWF'
          have HtargetBody' : TrExprS targetVEnv lparams targetCtx'
              (targetBody.instantiate1' (.fvar fv)) targetBodyTarget := by
            exact HtargetBody.inst_fvar HtargetEnvWF.ordered HtargetCtxWF'
          have Hsame' : Expr.SameForallPrefix arity
              (sourceBody.instantiate1' (.fvar fv))
              (targetBody.instantiate1' (.fvar fv)) :=
            Htail.instantiate1' (.fvar fv)
          have HsourceFresh' : ∀ other ∈ fvars,
              other ∉ sourceCtx'.fvars := by
            intro other hother
            have hne : other ≠ fv := fun heq =>
              (List.nodup_cons.mp hnodup).1 (heq ▸ hother)
            have hold : other ∉ sourceCtx.fvars :=
              HsourceFresh other (by simp [hother])
            change other ∉ fv :: sourceCtx.fvars
            simp [hne, hold]
          have HtargetFresh' : ∀ other ∈ fvars,
              other ∉ targetCtx'.fvars := by
            intro other hother
            have hne : other ≠ fv := fun heq =>
              (List.nodup_cons.mp hnodup).1 (heq ▸ hother)
            have hold : other ∉ targetCtx.fvars :=
              HtargetFresh other (by simp [hother])
            change other ∉ fv :: targetCtx.fvars
            simp [hne, hold]
          rcases ih Hsame' HsourceCtxWF' HtargetCtxWF'
            Hctx' HsourceBody' HtargetBody' fvars htailLength htailNodup
            HsourceFresh' HtargetFresh' with ⟨Hopened⟩
          rcases Hopened.sourceResidualData with
            ⟨sourceResidual, HsourceTelescope, hsourceResidual⟩
          rcases HsourceTelescope.reflect_instantiate1'_fvar with
            ⟨sourceResidual', HsourceTelescope'⟩
          have HsourceInstantiated :=
            HsourceTelescope'.instantiate1' (.fvar fv) 0
          have hsourceResidual' : sourceResidual =
              sourceResidual'.instantiate1' (.fvar fv) arity :=
            HsourceTelescope.residual_eq (by
              simpa using HsourceInstantiated)
          rcases Hopened.targetResidualData with
            ⟨targetResidual, HtargetTelescope, htargetResidual⟩
          rcases HtargetTelescope.reflect_instantiate1'_fvar with
            ⟨targetResidual', HtargetTelescope'⟩
          have HtargetInstantiated :=
            HtargetTelescope'.instantiate1' (.fvar fv) 0
          have htargetResidual' : targetResidual =
              targetResidual'.instantiate1' (.fvar fv) arity :=
            HtargetTelescope.residual_eq (by
              simpa using HtargetInstantiated)
          exact ⟨{
            sourceResidual := Hopened.sourceResidual
            targetResidual := Hopened.targetResidual
            sourceCtx := Hopened.sourceCtx
            targetCtx := Hopened.targetCtx
            sourceResidualTarget := Hopened.sourceResidualTarget
            targetResidualTarget := Hopened.targetResidualTarget
            contexts := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                Hopened.contexts
            sourceTranslation := Hopened.sourceTranslation
            targetTranslation := Hopened.targetTranslation
            sourceResidualData := ⟨sourceResidual', .cons HsourceTelescope', by
              rw [hsourceResidual, hsourceResidual']
              have hcomm := Expr.instantiateRevList_instantiate1'_fvars
                sourceResidual' fv fvars 0 0
              simp only [Nat.zero_add, Nat.add_zero] at hcomm
              rw [htailLength] at hcomm
              simpa using hcomm⟩
            targetResidualData := ⟨targetResidual', .cons HtargetTelescope', by
              rw [htargetResidual, htargetResidual']
              have hcomm := Expr.instantiateRevList_instantiate1'_fvars
                targetResidual' fv fvars 0 0
              simp only [Nat.zero_add, Nat.add_zero] at hcomm
              rw [htailLength] at hcomm
              simpa using hcomm⟩
            sourceBindings := (fv, sourceDomainTarget) ::
              Hopened.sourceBindings
            sourceBindingFVars := by
              simp [Hopened.sourceBindingFVars]
            sourceContext_eq := by
              simpa [sourceCtx', pushSelectedForall] using
                Hopened.sourceContext_eq
            targetBindings := (fv, targetDomainTarget) ::
              Hopened.targetBindings
            targetBindingFVars := by
              simp [Hopened.targetBindingFVars]
            targetContext_eq := by
              simpa [targetCtx', pushSelectedForall] using
                Hopened.targetContext_eq
            parameterPrefix := fun Hresidual =>
              VExpr.NestedForallPrefixExpansion.cons Hdomain
                (Hopened.parameterPrefix (by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hresidual))
            close := fun Hresidual =>
              VExpr.NestedExprExpansion.forallE Hdomain
                (Hopened.close (by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hresidual)) }⟩

/-- Expansion-aware projection of an expression mapping.  Unlike
`NestedExprMapping.abstractExpansion`, this induction derives the let case:
the translated type and value extend `NestedExpansionCtx`, after which the
body induction hypothesis applies directly. -/
theorem NestedExprMapping.abstractExpansionRelational
    (H : NestedExprMapping prodEnv lctx params As result input state out)
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hselection : LocalForallSelection lctx As)
    (Harity : As.size = params.size)
    (HsourceParams : SelectedParameterTargets Hselection.fvars fieldDepth
      sourceCtx)
    (Hparams : SelectedParameterTargets Hselection.fvars fieldDepth targetCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hhit : ∀ {input state output nextState finalState depth fieldDepth
        sourceTarget targetTarget sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionCtx leaf depth sourceCtx targetCtx →
      (selection : LocalForallSelection lctx As) →
      As.size = params.size →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      TrExprS sourceVEnv lparams sourceCtx input sourceTarget →
      TrExprS targetVEnv lparams targetCtx output targetTarget →
      leaf depth sourceTarget targetTarget)
    (Hproj : NestedProjectionExpansionCompat leaf)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx input sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx out.1 targetTarget) :
    VExpr.NestedExprExpansion leaf depth sourceTarget targetTarget := by
  induction H generalizing sourceCtx targetCtx sourceTarget targetTarget depth
      fieldDepth with
  | hit Hnode =>
      exact .hit
        (Hhit Hnode Hctx Hselection Harity HsourceParams Hparams Hsource Htarget)
  | bvar =>
    cases Hsource with
    | bvar HsourceLookup =>
      cases Htarget with
      | bvar HtargetLookup =>
        exact Hctx.find?_expansion Hlift HsourceLookup HtargetLookup
  | fvar =>
    cases Hsource with
    | fvar HsourceLookup =>
      cases Htarget with
      | fvar HtargetLookup =>
        exact Hctx.find?_expansion Hlift HsourceLookup HtargetLookup
  | mvar => cases Hsource
  | sort =>
    cases Hsource with
    | sort HsourceLevel =>
      cases Htarget with
      | sort HtargetLevel =>
        have heq := Option.some.inj (HsourceLevel.symm.trans HtargetLevel)
        cases heq
        exact .sort
  | const =>
    cases Hsource with
    | const _ HsourceLevels _ =>
      cases Htarget with
      | const _ HtargetLevels _ =>
        have heq := Option.some.inj (HsourceLevels.symm.trans HtargetLevels)
        cases heq
        exact .const
  | lit =>
    have heq : sourceTarget = targetTarget :=
      (TrExprS.ContextFree.literal _).translation_unique Hsource Htarget
    subst targetTarget
    exact VExpr.NestedExprExpansion.refl leaf depth sourceTarget
  | @app fn arg state fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx (.app fn' arg')
        targetTarget := by
      simpa [Expr.updateApp!] using Htarget
    cases Hsource with
    | app _ _ HsourceFn HsourceArg =>
      cases Htarget' with
      | app _ _ HtargetFn HtargetArg =>
        exact .app (ihFn Hctx HsourceParams Hparams HsourceFn HtargetFn)
          (ihArg Hctx HsourceParams Hparams HsourceArg HtargetArg)
  | @lam name dom body bi state dom' domState body' outState Hnode Hdom
      Hbody ihDom ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.lam name dom' body' bi) targetTarget := by
      simpa [Expr.updateLambdaE!] using Htarget
    cases Hsource with
    | lam _ HsourceDom HsourceBody =>
      cases Htarget' with
      | lam _ HtargetDom HtargetBody =>
        have HdomExpansion := ihDom Hctx HsourceParams Hparams HsourceDom
          HtargetDom
        exact .lam HdomExpansion
          (ihBody (.vlam Hctx HdomExpansion) HsourceParams.vlam Hparams.vlam
            HsourceBody HtargetBody)
  | @forallE name dom body bi state dom' domState body' outState Hnode Hdom
      Hbody ihDom ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.forallE name dom' body' bi) targetTarget := by
      simpa [Expr.updateForallE!] using Htarget
    cases Hsource with
    | forallE _ _ HsourceDom HsourceBody =>
      cases Htarget' with
      | forallE _ _ HtargetDom HtargetBody =>
        have HdomExpansion := ihDom Hctx HsourceParams Hparams HsourceDom
          HtargetDom
        exact .forallE HdomExpansion
          (ihBody (.vlam Hctx HdomExpansion) HsourceParams.vlam Hparams.vlam
            HsourceBody HtargetBody)
  | @letE name type value body nondep state type' typeState value'
      valueState body' outState Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.letE name type' value' body' nondep) targetTarget := by
      simpa [Expr.updateLet!] using Htarget
    cases Hsource with
    | letE _ HsourceType HsourceValue HsourceBody =>
      cases Htarget' with
      | letE _ HtargetType HtargetValue HtargetBody =>
        have HtypeExpansion := ihType Hctx HsourceParams Hparams HsourceType
          HtargetType
        have HvalueExpansion := ihValue Hctx HsourceParams Hparams HsourceValue
          HtargetValue
        exact ihBody (.vlet Hctx HtypeExpansion HvalueExpansion)
          HsourceParams.vlet Hparams.vlet HsourceBody HtargetBody
  | @mdata data body state body' outState Hnode Hbody ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx (.mdata data body')
        targetTarget := by
      simpa [Expr.updateMData!] using Htarget
    cases Hsource with
    | mdata HsourceBody =>
      cases Htarget' with
      | mdata HtargetBody =>
        exact ihBody Hctx HsourceParams Hparams HsourceBody HtargetBody
  | @proj structName index body state body' outState Hnode Hbody ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.proj structName index body') targetTarget := by
      simpa [Expr.updateProj!] using Htarget
    cases Hsource with
    | proj HsourceBody HsourceProj =>
      cases Htarget' with
      | proj HtargetBody HtargetProj =>
        exact Hproj
          (ihBody Hctx HsourceParams Hparams HsourceBody HtargetBody)
          HsourceProj HtargetProj

/-- Closing and reopening with the same duplicate-free fvar list is the
identity.  This is the transparent list-facing cancellation theorem needed
for the exact constructor body rebuilt by `LocalContext.mkForall`. -/
theorem _root_.Lean.Expr.reopenFVarsAt_self
    (hnodup : fvars.Nodup) (e : Expr) (k : Nat) :
    Expr.reopenFVarsAt e fvars fvars k = e := by
  induction e generalizing k with
  | bvar i => exact Expr.reopenFVarsAt_bvar rfl i k
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      exact Expr.reopenFVarsAt_selected hnodup rfl i hi k
    · apply Expr.reopenFVarsAt_eq_self_of_abstract
        (fun depth => Expr.abstractList_fvar_of_not_mem hfv)
        (by simp [Expr.looseBVarRange']) k
  | mvar id | sort id | const id _ | lit id =>
    apply Expr.reopenFVarsAt_of_abstract1_eq_self
      (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange'])
  | app fn arg ihFn ihArg =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_app,
      Expr.instantiateRevList_app]
    change Expr.app (Expr.reopenFVarsAt fn fvars fvars k)
        (Expr.reopenFVarsAt arg fvars fvars k) = Expr.app fn arg
    rw [ihFn k, ihArg k]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_lam,
      Expr.instantiateRevList_lam]
    change Expr.lam name (Expr.reopenFVarsAt dom fvars fvars k)
        (Expr.reopenFVarsAt body fvars fvars (k + 1)) bi =
      Expr.lam name dom body bi
    rw [ihDom k, ihBody (k + 1)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_forallE,
      Expr.instantiateRevList_forallE]
    change Expr.forallE name (Expr.reopenFVarsAt dom fvars fvars k)
        (Expr.reopenFVarsAt body fvars fvars (k + 1)) bi =
      Expr.forallE name dom body bi
    rw [ihDom k, ihBody (k + 1)]
  | letE name type value body nondep ihType ihValue ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_letE,
      Expr.instantiateRevList_letE]
    change Expr.letE name (Expr.reopenFVarsAt type fvars fvars k)
        (Expr.reopenFVarsAt value fvars fvars k)
        (Expr.reopenFVarsAt body fvars fvars (k + 1)) nondep =
      Expr.letE name type value body nondep
    rw [ihType k, ihValue k, ihBody (k + 1)]
  | mdata data body ihBody =>
    simpa [Expr.reopenFVarsAt, Expr.abstractList_mdata,
      Expr.instantiateRevList_mdata] using congrArg (Expr.mdata data) (ihBody k)
  | proj name index body ihBody =>
    simpa [Expr.reopenFVarsAt, Expr.abstractList_proj,
      Expr.instantiateRevList_proj] using
      congrArg (Expr.proj name index) (ihBody k)

/-- Pointwise structural projection of one constructor lowering.  The exact
source opening, the rebuilt target telescope, and the shared translated
forall prefix determine the same opened residuals used by the operational
mapping; the expression traversal can therefore be projected without an
additional constructor-level semantic premise. -/
theorem LoweredConstructorMapping.abstractExpansion
    (Hmapping : LoweredConstructorMapping prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (Hsource : TrSourceConstRaw sourceVEnv lparams sourceConcrete.name
      sourceConcrete.type sourceTarget)
    (Htarget : TrSourceConst targetVEnv lparams targetConcrete.name
      targetConcrete.type targetTarget)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (hparamsSize : params.size = nparams)
    (HsourceClosed : sourceConcrete.type.FVarsIn fun _ => False)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionCtx leaf depth sourceCtx targetCtx →
      (selection : LocalForallSelection lctx As) →
      As.size = params.size →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      TrExprS sourceVEnv lparams sourceCtx input sourceValue →
      TrExprS targetVEnv lparams targetCtx output targetValue →
      leaf depth sourceValue targetValue)
    (Hproj : NestedProjectionExpansionCompat leaf) :
    VInductDecl.NestedConstructorExpansion leaf nparams sourceTarget
      targetTarget := by
  rcases Hmapping.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      hnodup, _hopenedTypes, _hopenedAux, _hopenedNext, hsize, Hbody,
      htargetType⟩
  have Hsame := Hmapping.sourceTargetSameForallPrefix HsourceClosed
  rcases Hsame.openedAbstractProjection (depth := 0) HsourceEnvWF HtargetEnvWF
      (by trivial) (by trivial)
      (.nil : NestedExpansionCtx leaf 0 [] []) Hlift
      Hproj Hsource.type Htarget.type Hselection.fvars
      (by simpa [Hselection.expressions] using hsize) hnodup
      (by simp) (by simp) with ⟨Hopened⟩
  rcases Hopened.sourceResidualData with
    ⟨sourceResidual, HsourceTelescope, hsourceResidual⟩
  rcases Hopening.forallTelescope with
    ⟨openingResidual, HopeningTelescope⟩
  have hsourceTelescopeResidual : sourceResidual = openingResidual :=
    HsourceTelescope.residual_eq HopeningTelescope
  have htail : tail =
      openingResidual.instantiateRevList
        (Hselection.fvars.map Expr.fvar) := by
    have htail' := Hopening.toRestoreParamOpening.forallResidual
      HopeningTelescope
    rw [Hselection.expressions, Expr.instantiateRev_eq,
      Expr.instantiate_eq] at htail'
    simpa [Expr.instantiateList_reverse] using htail'
  have hsourceOpened : Hopened.sourceResidual = tail := by
    rw [hsourceResidual, hsourceTelescopeResidual, htail]
  have HtargetTelescope : Expr.ForallTelescope targetConcrete.type nparams
      (lowered.abstractList Hselection.fvars) := by
    rw [htargetType, ← hsize]
    exact Hselection.forallTelescope lowered
  rcases Hopened.targetResidualData with
    ⟨targetResidual, HtargetTelescope', htargetResidual⟩
  have htargetTelescopeResidual : targetResidual =
      lowered.abstractList Hselection.fvars :=
    HtargetTelescope'.residual_eq HtargetTelescope
  have htargetOpened : Hopened.targetResidual = lowered := by
    rw [htargetResidual, htargetTelescopeResidual]
    exact Expr.reopenFVarsAt_self hnodup lowered 0
  have Hresidual : VExpr.NestedExprExpansion leaf nparams
      Hopened.sourceResidualTarget Hopened.targetResidualTarget := by
    have HsourceResidualTranslation : TrExprS sourceVEnv lparams
        Hopened.sourceCtx tail Hopened.sourceResidualTarget := by
      simpa [hsourceOpened] using Hopened.sourceTranslation
    have HtargetResidualTranslation : TrExprS targetVEnv lparams
        Hopened.targetCtx lowered Hopened.targetResidualTarget := by
      simpa [htargetOpened] using Hopened.targetTranslation
    have Hresidual' := Hbody.abstractExpansionRelational
      (sourceTarget := Hopened.sourceResidualTarget)
      (targetTarget := Hopened.targetResidualTarget)
      Hopened.contexts Hselection (hsize.trans hparamsSize.symm)
      (Hopened.selectedParameterSources hnodup)
      (Hopened.selectedParameterTargets hnodup) Hlift Hhit Hproj
      HsourceResidualTranslation HtargetResidualTranslation
    simpa using Hresidual'
  exact {
    name := by
      calc
        targetTarget.name = targetConcrete.name := Htarget.name
        _ = sourceConcrete.name := Hmapping.name
        _ = sourceTarget.name := Hsource.name.symm
    uvars := Htarget.uvars.trans Hsource.uvars.symm
    parameters := Hopened.parameterPrefix (by simpa using Hresidual)
    type := Hopened.close (by simpa using Hresidual) }

/-- State threading is irrelevant after every exact constructor step has
been projected: source and lowered translation lists become an ordered
constructor expansion. -/
theorem LoweredConstructorMappings.abstractExpansions
    (Hmapping : LoweredConstructorMappings prodEnv params nparams result
      sources state out)
    (Hsource : List.Forall₂ (fun source target =>
      TrSourceConstRaw sourceVEnv lparams source.name source.type target)
      sources sourceTargets)
    (Htarget : List.Forall₂ (fun source target =>
      TrSourceConst targetVEnv lparams source.name source.type target)
      out.1 targetTargets)
    (Hclosed : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (hparamsSize : params.size = nparams)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionCtx leaf depth sourceCtx targetCtx →
      (selection : LocalForallSelection lctx As) →
      As.size = params.size →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      TrExprS sourceVEnv lparams sourceCtx input sourceValue →
      TrExprS targetVEnv lparams targetCtx output targetValue →
      leaf depth sourceValue targetValue)
    (Hproj : NestedProjectionExpansionCompat leaf) :
    List.Forall₂ (VInductDecl.NestedConstructorExpansion leaf nparams)
      sourceTargets targetTargets := by
  induction Hmapping generalizing sourceTargets targetTargets with
  | nil =>
    cases Hsource
    cases Htarget
    exact .nil
  | cons Hhead Htail ih =>
    cases Hsource with
    | cons HsourceHead HsourceTail =>
      cases Htarget with
      | cons HtargetHead HtargetTail =>
        exact .cons
          (Hhead.abstractExpansion HsourceHead HtargetHead HsourceEnvWF
            HtargetEnvWF hparamsSize (Hclosed _ (by simp)) Hlift Hhit Hproj)
          (ih HsourceTail HtargetTail (fun source hsource =>
            Hclosed source (by simp [hsource])))

/-- The constructor-independent fields of one nested family expansion.  This
small carrier lets the exact lowering provenance discharge family metadata
without obscuring the sole remaining constructor-expression join. -/
structure NestedTypeExpansionHeader
    (env : VEnv) (decl : VInductDecl)
    (source target : VInductiveType) : Prop where
  name : target.name = source.name
  uvars : target.uvars = source.uvars
  type : env.IsDefEqU decl.uvars [] source.type target.type
  numIndices : target.numIndices = source.numIndices
  resultLevel : target.resultLevel = source.resultLevel

/-- Two abstract headers translated from the exact source/lowered concrete
family pair inherit all family-level expansion fields from lowering. -/
theorem LoweredInductiveMapping.abstractHeaderExpansion
    (Hmapping : LoweredInductiveMapping prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (Hsource : TrInductiveTypeHeaders env envTypes lparams sourceConcrete source)
    (Htarget : TrInductiveType env targetEnvTypes lparams targetConcrete target)
    (henv : env.WF)
    (huvars : decl.uvars = lparams.length)
    (hnumIndices : target.numIndices = source.numIndices)
    (hresultLevel : target.resultLevel = source.resultLevel) :
    NestedTypeExpansionHeader env decl source target where
  name := by
    calc
      target.name = targetConcrete.name := Htarget.header.name
      _ = sourceConcrete.name := Hmapping.name
      _ = source.name := Hsource.header.name.symm
  uvars := by
    calc
      target.uvars = lparams.length := Htarget.header.uvars
      _ = source.uvars := Hsource.header.uvars.symm
  type := by
    rw [huvars]
    exact Hsource.header.type.uniq henv (.refl henv (by trivial)) (by
      rw [← Hmapping.type]
      exact Htarget.header.type)
  numIndices := hnumIndices
  resultLevel := hresultLevel

/-- Family-level projection packages the exact header with the ordered
constructor traversal. -/
theorem LoweredInductiveMapping.abstractExpansion
    (Hmapping : LoweredInductiveMapping prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (Hsource : TrInductiveTypeHeaders headerVEnv sourceVEnv lparams sourceConcrete
      sourceTarget)
    (Htarget : TrInductiveType headerVEnv targetVEnv lparams targetConcrete
      targetTarget)
    (Hheader : NestedTypeExpansionHeader headerVEnv decl sourceTarget
      targetTarget)
    (Hclosed : InductiveConstructorsClosed sourceConcrete)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = decl.nparams)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionCtx leaf depth sourceCtx targetCtx →
      (selection : LocalForallSelection lctx As) →
      As.size = params.size →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      TrExprS sourceVEnv lparams sourceCtx input sourceValue →
      TrExprS targetVEnv lparams targetCtx output targetValue →
      leaf depth sourceValue targetValue)
    (Hproj : NestedProjectionExpansionCompat leaf) :
    VInductDecl.NestedTypeExpansion headerVEnv decl leaf sourceTarget
      targetTarget where
  name := Hheader.name
  uvars := Hheader.uvars
  type := Hheader.type
  numIndices := Hheader.numIndices
  resultLevel := Hheader.resultLevel
  constructors := by
    simpa only [hnparams] using
      Hmapping.constructors.abstractExpansions Hsource.ctors Htarget.ctors
        Hclosed HsourceEnvWF HtargetEnvWF hparamsSize Hlift Hhit Hproj

/-- Exact original-prefix specialization.  The source family remains at its
original queue position; the independent source and production translations,
together with metadata materialization, determine the complete abstract
header expansion at that position. -/
theorem NestedLoweringResultClosed.originalHeaderExpansionAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    ∃ hsourceDecl : familyIdx < sourceDecl.types.length,
      ∃ htargetDecl : familyIdx < loweredDecl.types.length,
      NestedTypeExpansionHeader sourceVEnv sourceDecl
        (sourceDecl.types[familyIdx]'hsourceDecl)
        (loweredDecl.types[familyIdx]'htargetDecl) := by
  have hresult : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hfamily H.toResult.sourceTypes_length_le
  have hsourceDecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have htargetDecl : familyIdx < loweredDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget]
    exact hresult
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, targetConcrete, nextState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨_hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hsourceDecl
  have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Htarget familyIdx hresult htargetDecl
  rw [htargetEq] at HtargetType
  refine ⟨hsourceDecl, htargetDecl, Hmapping.abstractHeaderExpansion
    (Lean4Lean.VerifyInductive.TrInductiveType.headers HsourceType)
      HtargetType henv Hsource.uvars ?_ ?_⟩
  · exact (Hmetadata.numIndices hdeclLength familyIdx hsourceDecl
      htargetDecl).symm
  · exact (Hmetadata.resultLevel hdeclLength familyIdx hsourceDecl
      htargetDecl).symm

/-- Header staging alone yields a well-formed mutual-family environment;
constructor staging is not needed by the structural expansion proof. -/
theorem TrInductDeclCore.envTypesWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (henv : env.WF) : envTypes.WF := by
  apply VEnv.WF.addConstVals henv _ H.typesAdded
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types target htarget with
    ⟨_source, _hsource, Htarget⟩
  exact Htarget.header.wf

/-- Exact interpretation of successful replacement leaves for one closed
lowering result and one independently translated source/expanded block.  In
contrast to a generic expression provider, every quantified replacement is
an actual `NestedReplacementHasFinalMapping` into this exact final result,
and both translations use the exact mutual-header environments. -/
def NestedFormationReplacementCompat
    (prodEnv : Environment) (result : Lean4Lean.ElimNestedInductive.Result)
    (baseVEnv sourceVEnv targetVEnv : VEnv) (lparams : List Name)
    (sourceDecl : VInductDecl) (generated : List VInductiveType) : Prop :=
  ∀ {lctx : LocalContext} {As : Array Expr}
      {input state output nextState finalState depth fieldDepth sourceValue targetValue
        sourceCtx targetCtx},
    NestedReplacementFinalTrace prodEnv lctx result.params As input state output
      nextState result finalState →
    NestedExpansionCtx
      (VInductDecl.NestedAuxiliarySource baseVEnv sourceDecl generated)
      depth sourceCtx targetCtx →
    (selection : LocalForallSelection lctx As) →
    As.size = result.params.size →
    SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
    SelectedParameterTargets selection.fvars fieldDepth targetCtx →
    TrExprS sourceVEnv lparams sourceCtx input sourceValue →
    TrExprS targetVEnv lparams targetCtx output targetValue →
    VInductDecl.NestedAuxiliarySource baseVEnv sourceDecl generated depth
      sourceValue targetValue

/-- Complete leaf judgment for the canonical direct family.  The premises
are only the translated application spine and its scope facts; installed
declaration provenance and every constructor specialization are derived from
the exact generated-family container certificate. -/
theorem GeneratedFamilyInstalledContainer.directAuxiliarySource
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H)
    (sourceDecl : VInductDecl) (generated : List VInductiveType)
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (numIndices : Nat) (resultLevel : VLevel)
    (auxiliaryLevels : List VLevel) (trailing : List VExpr)
    (hfamily : VInductiveType.directAuxiliary sourceParams baseArgs levels
      (C.container.types[C.familyIdx]'C.familyIdx_lt) H.auxName
        sourceDecl.uvars numIndices resultLevel ∈ generated)
    (hsourceParams : sourceParams.length = sourceDecl.nparams)
    (hbaseArgs : baseArgs.length = C.container.nparams)
    (hbaseClosed : ∀ arg ∈ baseArgs, arg.ClosedN sourceDecl.nparams)
    (hlevels : levels.length = C.container.uvars)
    (hlevelsWF : ∀ level ∈ levels, level.WF sourceDecl.uvars)
    (hfamilyType : venv.IsDefEqU sourceDecl.uvars []
      (VInductiveType.directAuxiliary sourceParams baseArgs levels
        (C.container.types[C.familyIdx]'C.familyIdx_lt) H.auxName
          sourceDecl.uvars numIndices resultLevel).type
      (VExpr.wrapForalls sourceParams
        (VExpr.instantiateForallPrefix
          ((C.container.types[C.familyIdx]'C.familyIdx_lt).type.instL levels)
          baseArgs)))
    (hconstructorTypes : ∀ source ∈
      (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors,
      (VConstVal.directAuxiliary sourceParams baseArgs levels
        (C.container.types[C.familyIdx]'C.familyIdx_lt) H.auxName
          sourceDecl.uvars source).type.WF venv sourceDecl.uvars [])
    (hauxiliaryLevels : auxiliaryLevels.length = sourceDecl.uvars)
    (hinput : input = VExpr.mkApps
      (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name levels)
      (baseArgs.map (fun arg => arg.liftN depth 0) ++ trailing))
    (houtput : output = VExpr.mkApps (.const H.auxName auxiliaryLevels)
      (sourceDecl.paramVars depth ++ trailing)) :
    VInductDecl.NestedAuxiliarySource venv sourceDecl generated depth input
      output := by
  let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
  let auxiliaryFamily := VInductiveType.directAuxiliary sourceParams
    baseArgs levels containerFamily H.auxName sourceDecl.uvars numIndices
      resultLevel
  have Hdirect := C.directAuxiliaryEvidence sourceParams baseArgs levels
    sourceDecl.uvars numIndices resultLevel hconstructorTypes
  have Htrailing :
      VInductDecl.NestedExprWFExpansion venv sourceDecl generated
        (sourceDecl.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker trailing)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker trailing) :=
    nestedExprExpansion_toNestedExprWFExpansion
      (VExpr.NestedExprExpansion.refl
        (VInductDecl.NestedAuxiliarySourceAbsolute venv sourceDecl generated)
        (sourceDecl.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker trailing))
  exact .intro Hdirect.1 Hdirect.2.1 (by
      simpa only [containerFamily, auxiliaryFamily] using hfamily)
    hsourceParams hbaseArgs hbaseClosed hlevels hlevelsWF rfl hfamilyType
    Hdirect.2.2 hauxiliaryLevels Htrailing (by
      simpa only [containerFamily] using hinput) (by
      simpa only [auxiliaryFamily, VInductiveType.directAuxiliary] using
        houtput)

/-- Complete leaf judgment when the unchanged concrete trailing spine has
already been projected to a structural nested expansion.  This is the form
used by an exact replacement trace: source and target translations of the
same concrete trailing arguments need not be literally equal because local
let values may themselves have been lowered, but their marker applications
are related by the retained expansion context. -/
theorem GeneratedFamilyInstalledContainer.directAuxiliarySourceOfTrailingExpansion
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H)
    (sourceDecl : VInductDecl) (generated : List VInductiveType)
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (numIndices : Nat) (resultLevel : VLevel)
    (auxiliaryLevels : List VLevel)
    (sourceTrailing targetTrailing : List VExpr)
    (hfamily : VInductiveType.directAuxiliary sourceParams baseArgs levels
      (C.container.types[C.familyIdx]'C.familyIdx_lt) H.auxName
        sourceDecl.uvars numIndices resultLevel ∈ generated)
    (hsourceParams : sourceParams.length = sourceDecl.nparams)
    (hbaseArgs : baseArgs.length = C.container.nparams)
    (hbaseClosed : ∀ arg ∈ baseArgs, arg.ClosedN sourceDecl.nparams)
    (hlevels : levels.length = C.container.uvars)
    (hlevelsWF : ∀ level ∈ levels, level.WF sourceDecl.uvars)
    (hfamilyType : venv.IsDefEqU sourceDecl.uvars []
      (VInductiveType.directAuxiliary sourceParams baseArgs levels
        (C.container.types[C.familyIdx]'C.familyIdx_lt) H.auxName
          sourceDecl.uvars numIndices resultLevel).type
      (VExpr.wrapForalls sourceParams
        (VExpr.instantiateForallPrefix
          ((C.container.types[C.familyIdx]'C.familyIdx_lt).type.instL levels)
          baseArgs)))
    (hconstructorTypes : ∀ source ∈
      (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors,
      (VConstVal.directAuxiliary sourceParams baseArgs levels
        (C.container.types[C.familyIdx]'C.familyIdx_lt) H.auxName
          sourceDecl.uvars source).type.WF venv sourceDecl.uvars [])
    (hauxiliaryLevels : auxiliaryLevels.length = sourceDecl.uvars)
    (Htrailing : VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute venv sourceDecl generated)
      (sourceDecl.nparams + depth)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceTrailing)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker targetTrailing))
    (hinput : input = VExpr.mkApps
      (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name levels)
      (baseArgs.map (fun arg => arg.liftN depth 0) ++ sourceTrailing))
    (houtput : output = VExpr.mkApps (.const H.auxName auxiliaryLevels)
      (sourceDecl.paramVars depth ++ targetTrailing)) :
    VInductDecl.NestedAuxiliarySource venv sourceDecl generated depth input
      output := by
  let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
  let auxiliaryFamily := VInductiveType.directAuxiliary sourceParams
    baseArgs levels containerFamily H.auxName sourceDecl.uvars numIndices
      resultLevel
  have Hdirect := C.directAuxiliaryEvidence sourceParams baseArgs levels
    sourceDecl.uvars numIndices resultLevel hconstructorTypes
  exact .intro Hdirect.1 Hdirect.2.1 (by
      simpa only [containerFamily, auxiliaryFamily] using hfamily)
    hsourceParams hbaseArgs hbaseClosed hlevels hlevelsWF rfl hfamilyType
    Hdirect.2.2 hauxiliaryLevels
    (nestedExprExpansion_toNestedExprWFExpansion Htrailing) (by
      simpa only [containerFamily] using hinput) (by
      simpa only [auxiliaryFamily, VInductiveType.directAuxiliary] using
        houtput)

/-- Closure of the concrete pre-lowering generated constructors follows
directly from the exact builder once its retained local selection is known to
be a genuine lowering closing context. -/
theorem GeneratedFamilyWitness.constructorsClosedOfClosing
    (H : GeneratedFamilyWitness prodEnv params nestedAux family)
    (Henv : EnvironmentTypesClosed prodEnv)
    (Hclosing : NestedClosingContext H.lctx H.As ngen) :
    InductiveConstructorsClosed family := by
  rw [H.family_eq]
  have hfvars : H.selection.fvars = Hclosing.selection.fvars := by
    have harrays : (H.selection.fvars.map Expr.fvar).toArray =
        (Hclosing.selection.fvars.map Expr.fvar).toArray := by
      exact H.selection.expressions.symm.trans Hclosing.selection.expressions
    have hlists : H.selection.fvars.map Expr.fvar =
        Hclosing.selection.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList harrays
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists
  exact H.built.constructors.closed Henv Hclosing H.levelsNoMVars (by
    intro arg harg
    simpa only [← hfvars] using H.argsFVars arg harg)

/-- An exact family translation at the empty source context already proves
concrete constructor closure; retaining a second closure callback would
duplicate information in `TrInductiveType`. -/
theorem TrInductiveTypeHeaders.constructorsClosed
    (H : TrInductiveTypeHeaders env envTypes lparams concrete abstract) :
    InductiveConstructorsClosed concrete := by
  intro ctor hctor
  rcases Lean4Lean.List.Forall₂.forall_exists_l H.ctors ctor hctor with
    ⟨_target, _htarget, Hctor⟩
  simpa [Lean4Lean.FVarsIn] using Hctor.type.fvarsIn

/-- Narrow source-side payload still needed for one dynamically generated
queue family.  It contains no final expansion judgment: only the independent
translation of the exact pre-lowering family, its executable closure fact,
and the two metadata fields not represented by `TrInductiveType`.

This is the intended output of the `BuiltAuxiliary`/installed-container
projection, before the ordinary lowering mapping is interpreted. -/
structure FinalLoweredGeneratedFamilySource
    (H : FinalLoweredGeneratedFamilyOrigin prodEnv params nparams finalState
      targetConcrete)
    (baseVEnv sourceTypesVEnv : VEnv) (lparams : List Name)
    (target : VInductiveType) where
  source : VInductiveType
  translation : TrInductiveTypeHeaders baseVEnv sourceTypesVEnv lparams H.source
    source
  numIndices : target.numIndices = source.numIndices
  resultLevel : target.resultLevel = source.resultLevel

/-- Once the narrow pre-lowering source payload is available, the exact final
queue mapping yields the complete abstract generated-family expansion. -/
theorem FinalLoweredGeneratedFamilyOrigin.abstractExpansion
    (H : FinalLoweredGeneratedFamilyOrigin prodEnv params nparams finalState
      targetConcrete)
    (Hsource : FinalLoweredGeneratedFamilySource H baseVEnv sourceTypesVEnv
      lparams target)
    (Htarget : TrInductiveType baseVEnv targetTypesVEnv lparams targetConcrete
      target)
    (Hmap : NestedAuxMapModels result finalState)
    (henv : baseVEnv.WF)
    (huvars : decl.uvars = lparams.length)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (HtargetTypesWF : targetTypesVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = decl.nparams)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionCtx leaf depth sourceCtx targetCtx →
      (selection : LocalForallSelection lctx As) →
      As.size = params.size →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      TrExprS sourceTypesVEnv lparams sourceCtx input sourceValue →
      TrExprS targetTypesVEnv lparams targetCtx output targetValue →
      leaf depth sourceValue targetValue)
    (Hproj : NestedProjectionExpansionCompat leaf) :
    VInductDecl.NestedTypeExpansion baseVEnv decl leaf Hsource.source target := by
  have Hmapping := H.finalMapping Hmap
  have Hheader : NestedTypeExpansionHeader baseVEnv decl Hsource.source target :=
    Hmapping.abstractHeaderExpansion Hsource.translation Htarget henv huvars
      Hsource.numIndices Hsource.resultLevel
  exact Hmapping.abstractExpansion Hsource.translation Htarget Hheader
    (Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.constructorsClosed
      Hsource.translation)
    HsourceTypesWF HtargetTypesWF hparamsSize hnparams Hlift Hhit Hproj

/-- Complete original-prefix specialization.  All family and constructor
ordering is now obtained from exact positional translations and the
state-threaded lowering mapping. -/
theorem NestedLoweringResultClosed.originalExpansionAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hsyntax : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NestedReplacementFinalTrace prodEnv lctx result.params As input state
        output nextState result finalState →
      NestedExpansionCtx leaf depth sourceCtx targetCtx →
      (selection : LocalForallSelection lctx As) →
      As.size = result.params.size →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      TrExprS sourceEnvTypes lparams sourceCtx input sourceValue →
      TrExprS targetEnvTypes lparams targetCtx output targetValue →
      leaf depth sourceValue targetValue)
    (Hproj : NestedProjectionExpansionCompat leaf)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    ∃ hsourceDecl : familyIdx < sourceDecl.types.length,
      ∃ htargetDecl : familyIdx < loweredDecl.types.length,
      VInductDecl.NestedTypeExpansion sourceVEnv sourceDecl leaf
        (sourceDecl.types[familyIdx]'hsourceDecl)
        (loweredDecl.types[familyIdx]'htargetDecl) := by
  rcases H.originalHeaderExpansionAtFresh Hsource Htarget Hmetadata hempty henv
      familyIdx hfamily with ⟨hsourceDecl, htargetDecl, Hheader⟩
  have hresult : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hfamily H.toResult.sourceTypes_length_le
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, stepState, targetConcrete, loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨_hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hsourceDecl
  have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Htarget familyIdx hresult htargetDecl
  rw [htargetEq] at HtargetType
  have HsourceTypesWF : sourceEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource henv
  have HtargetTypesWF : targetEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Htarget henv
  have hparamsSize : result.params.size = nparams := by
    rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultParamsSize
  exact ⟨hsourceDecl, htargetDecl,
    Hmapping.abstractExpansion
      (Lean4Lean.VerifyInductive.TrInductiveType.headers HsourceType)
      HtargetType Hheader
      (Hsyntax.getElem familyIdx hfamily).constructors.closed
      HsourceTypesWF HtargetTypesWF hparamsSize Hsource.nparams.symm Hlift
      Hhit Hproj⟩

/-- Ordered expansion of the complete original source prefix.  This is the
list-valued formation payload for the initial queue; no positional choice is
left to the caller. -/
theorem NestedLoweringResultClosed.originalExpansions
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hsyntax : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (generated : List VInductiveType)
    (Hhit : NestedFormationReplacementCompat prodEnv result sourceVEnv
      sourceEnvTypes targetEnvTypes lparams sourceDecl generated)
    (Hproj : NestedProjectionExpansionCompat
      (VInductDecl.NestedAuxiliarySource sourceVEnv sourceDecl generated)) :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion sourceVEnv sourceDecl
        (VInductDecl.NestedAuxiliarySource sourceVEnv sourceDecl generated))
      sourceDecl.types (loweredDecl.types.take sourceDecl.types.length) := by
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
  have htargetLength : loweredDecl.types.length = result.types.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget).symm
  have hprefix : sourceDecl.types.length ≤ loweredDecl.types.length := by
    rw [hsourceLength, htargetLength]
    exact H.toResult.sourceTypes_length_le
  apply List.forall₂_of_getElem (by simp [hprefix])
  intro familyIdx hsourceDecl htargetDecl
  have hfamily : familyIdx < sourceTypes.length := by
    simpa [hsourceLength] using hsourceDecl
  have htargetFull : familyIdx < loweredDecl.types.length :=
    Nat.lt_of_lt_of_le hsourceDecl hprefix
  have htargetEq :
      (loweredDecl.types.take sourceDecl.types.length)[familyIdx] =
        loweredDecl.types[familyIdx] := by
    simp only [List.getElem_take]
  rcases H.originalExpansionAtFresh Hsource Htarget Hmetadata Hsyntax hempty
      henv nestedAuxiliarySource_leafLiftCompat Hhit Hproj familyIdx hfamily
      with ⟨hsourceDecl', htargetDecl', Hfamily⟩
  have hsourceProof : hsourceDecl' = hsourceDecl := Subsingleton.elim _ _
  have htargetProof : htargetDecl' = htargetFull := Subsingleton.elim _ _
  subst hsourceDecl'
  subst htargetDecl'
  simpa only [htargetEq] using Hfamily

/-- The trace-local source translation retained for the dynamically generated
suffix.  This is deliberately weaker than a formation provider: at each exact
queue position it supplies only the independently translated pre-lowering
family selected by that position's generated origin.  Lowering projection,
constructor expansion, and list ordering are derived below. -/
structure NestedGeneratedFamilySourceTranslations
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLoweringRun prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (sourceTypesVEnv : VEnv) (generated : List VInductiveType) : Prop where
  length : generated.length + sourceTypes.length = result.types.length
  sourceAt : ∀ (i : Nat) (hi : i < generated.length)
      (hresult : sourceTypes.length + i < result.types.length)
      (htarget : sourceTypes.length + i < loweredDecl.types.length)
      (Horigin : FinalLoweredGeneratedFamilyOrigin prodEnv result.params
        nparams finalState result.types[sourceTypes.length + i]),
    Nonempty (FinalLoweredGeneratedFamilySource Horigin baseVEnv
      sourceTypesVEnv lparams loweredDecl.types[sourceTypes.length + i]) ∧
    (∀ Hsource : FinalLoweredGeneratedFamilySource Horigin baseVEnv
        sourceTypesVEnv lparams loweredDecl.types[sourceTypes.length + i],
      Hsource.source = generated[i])

/-- Every exact translated generated-source suffix projects, in queue order,
to the corresponding suffix of the final lowered declaration.  The theorem
does not assume a family expansion judgment and does not reorder by names. -/
theorem NestedLoweringRun.generatedExpansions
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLoweringRun prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Henv : EnvironmentTypesClosed prodEnv)
    (henv : baseVEnv.WF)
    (HtargetTypesWF : targetEnvTypes.WF)
    (hempty : initialState.nestedAux = #[])
    (generated : List VInductiveType)
    (Hgenerated : NestedGeneratedFamilySourceTranslations Hrun Htarget
      sourceTypesVEnv generated)
    (HsourceTypesWF : sourceTypesVEnv.WF)
    (Hhit : NestedFormationReplacementCompat prodEnv result baseVEnv
      sourceTypesVEnv targetEnvTypes lparams sourceDecl generated)
    (Hproj : NestedProjectionExpansionCompat
      (VInductDecl.NestedAuxiliarySource baseVEnv sourceDecl generated))
    (huvars : sourceDecl.uvars = lparams.length)
    (hnparams : sourceDecl.nparams = nparams) :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion baseVEnv sourceDecl
        (VInductDecl.NestedAuxiliarySource baseVEnv sourceDecl generated))
      generated (loweredDecl.types.drop sourceTypes.length) := by
  have hloweredLength : loweredDecl.types.length = result.types.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget).symm
  have hdropLength : (loweredDecl.types.drop sourceTypes.length).length =
      generated.length := by
    rw [List.length_drop, hloweredLength]
    have hlength := Hgenerated.length
    omega
  apply List.forall₂_of_getElem (by omega)
  intro i hgenerated htargetDrop
  have hresult : sourceTypes.length + i < result.types.length := by
    have := htargetDrop
    simp only [List.length_drop, hloweredLength] at this
    omega
  have htarget : sourceTypes.length + i < loweredDecl.types.length := by
    simpa [hloweredLength] using hresult
  rcases Hrun.finalGeneratedFamilyOriginAt Henv Hsources (by simp)
      (by simp) hresult with ⟨Horigin⟩
  rcases (Hgenerated.sourceAt i hgenerated hresult htarget Horigin).1 with
    ⟨Hsource⟩
  have hsourceEq :=
    (Hgenerated.sourceAt i hgenerated hresult htarget Horigin).2 Hsource
  have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Htarget (sourceTypes.length + i) hresult htarget
  have Hmap := Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  have Hexpansion := Horigin.abstractExpansion Hsource HtargetType Hmap henv
    huvars HsourceTypesWF HtargetTypesWF Hrun.resultParamsSize hnparams.symm
      nestedAuxiliarySource_leafLiftCompat Hhit Hproj
  have hdropGet :
      (loweredDecl.types.drop sourceTypes.length)[i] =
        loweredDecl.types[sourceTypes.length + i] := by
    simp only [List.getElem_drop]
  rw [hsourceEq] at Hexpansion
  rw [hdropGet]
  exact Hexpansion

/-- Join the independently proved original prefix and generated suffix at the
exact queue boundary.  This is the complete ordered `Htypes` payload expected
by `NestedFinalCanonicalEvidence.ofProduction`; its temporary replacement-hit
premise is trace-indexed and is narrowed further below. -/
theorem NestedLoweringRun.allExpansions
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hrun : NestedLoweringRun prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray }
      (result, finalState))
    (Hcache : NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState)
    (Hparams : NestedResultParamsNodup result)
    (Hsource : TrInductDeclCore baseVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore baseVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Henv : EnvironmentTypesClosed prodEnv)
    (henv : baseVEnv.WF)
    (hempty : initialState.nestedAux = #[])
    (generated : List VInductiveType)
    (Hgenerated : NestedGeneratedFamilySourceTranslations Hrun Htarget
      sourceEnvTypes generated)
    (Hhit : NestedFormationReplacementCompat prodEnv result baseVEnv
      sourceEnvTypes targetEnvTypes lparams sourceDecl generated)
    (Hproj : NestedProjectionExpansionCompat
      (VInductDecl.NestedAuxiliarySource baseVEnv sourceDecl generated)) :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion baseVEnv sourceDecl
        (VInductDecl.NestedAuxiliarySource baseVEnv sourceDecl generated))
      (sourceDecl.types ++ generated) loweredDecl.types := by
  let Hclosed : NestedLoweringResultClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  have Horiginal := Hclosed.originalExpansions Hsource Htarget Hmetadata
    Hsources (by simpa using hempty) henv generated Hhit Hproj
  have HsourceTypesWF : sourceEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource henv
  have HtargetTypesWF : targetEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Htarget henv
  have HgeneratedExpansions := Hrun.generatedExpansions Htarget Hsources Henv
    henv HtargetTypesWF hempty generated Hgenerated HsourceTypesWF Hhit Hproj
      Hsource.uvars Hsource.nparams
  have Hall := Lean4Lean.VerifyInductive.List.Forall₂.append' Horiginal
    HgeneratedExpansions
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
  have htargetSplit :
      loweredDecl.types.take sourceDecl.types.length ++
          loweredDecl.types.drop sourceTypes.length = loweredDecl.types := by
    rw [hsourceLength]
    exact List.take_append_drop sourceTypes.length loweredDecl.types
  simpa only [htargetSplit] using Hall

end VerifyInductive
end Lean4Lean
