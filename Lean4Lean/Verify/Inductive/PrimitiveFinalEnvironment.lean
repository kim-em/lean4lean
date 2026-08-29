import Lean4Lean.Verify.Inductive.PrimitiveSemanticAddInduct
import Lean4Lean.Verify.Inductive.Run.EqCanonical

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Canonical equality is inherited by a completed block from its abstract
source.  The result is independent of whether formation used ordinary or
atomic installation. -/
theorem CompletedBlockCertificate.eqCanonicalOfBase
    (H : CompletedBlockCertificate safety prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hEq : venv.QuotReady) :
    forall info, outEnv.constants.find? ``Eq = some (.inductInfo info) ->
      (outVEnv.addDefEqRules rules).constants ``Eq = some eqConst := by
  intro _info _hfind
  exact (VInductBlock.install_le H.install).constants hEq

/-- Constructor semantics for a replayed completed safe block. Old families
come from the observer's source model; a newly installed family is safe and
therefore transports from the original completed safe model. -/
theorem CompletedBlockCertificate.replaySafeConstructorSemantics
    (H : CompletedBlockCertificate .safe prodEnv base types ctors recursors
      rules outEnv outBase)
    (Hreplay : CompletedBlockCertificate observer prodEnv observerBase types
      ctors recursors rules outEnv replayBase)
    (hwf : prodEnv.constants.WF)
    (Hsource : InductiveConstructorsSemanticallyCoherent observer prodEnv
      observerBase)
    (Hcompleted : InductiveConstructorsSemanticallyCoherent .safe outEnv
      (outBase.addDefEqRules rules))
    (hreplay : outBase.addDefEqRules rules <=
      replayBase.addDefEqRules rules) :
    InductiveConstructorsSemanticallyCoherent observer outEnv
      (replayBase.addDefEqRules rules) := by
  intro familyName familyInfo hfamily hvisible i hi
  let Hinstall := Hreplay.staged.combinedAtomic
  rcases Hinstall.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    have hlookup := Hinstall.preservesSourceFind hwf C.lookup
    have hle : observerBase <= replayBase.addDefEqRules rules :=
      Hinstall.le.trans VEnv.addDefEqRules_le
    exact ⟨C.rebaseProduction hlookup hle⟩
  · rcases hnew with ⟨entry, hentry, _hname, hinfo⟩
    have hsafe : .safe <= (ConstantInfo.inductInfo familyInfo).safety := by
      rw [hinfo]
      exact H.staged.combinedAtomic.entrySafety hentry
    have hsafe' : DefinitionSafety.safe <=
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hsafe
    have hfamilySafe : familyInfo.isUnsafe = false := by
      cases h : familyInfo.isUnsafe
      · rfl
      · have hsafeUnsafe : DefinitionSafety.safe <=
            DefinitionSafety.unsafe := by simpa [h] using hsafe'
        have heq : DefinitionSafety.safe = DefinitionSafety.unsafe :=
          DefinitionSafety.le_antisymm hsafeUnsafe DefinitionSafety.unsafe_le
        contradiction
    have hsafeVisible : DefinitionSafety.safe <=
        (if familyInfo.isUnsafe then DefinitionSafety.unsafe
          else DefinitionSafety.safe) := by
      simp [hfamilySafe, DefinitionSafety.le_rfl]
    rcases Hcompleted familyName familyInfo hfamily hsafeVisible i hi with ⟨C⟩
    exact ⟨C.mono hreplay⟩

/-- An exact primitive Bool/Nat block cannot manufacture the unrelated
bootstrap equality name.  Formation is identified by its finite canonical
abstract batch; recursor names are discharged separately by their generated
owner certificate. -/
theorem CompletedBlockCertificate.preservesEqAbsentPrimitive
    (H : CompletedBlockCertificate safety prodEnv base types ctors recursors
      rules outEnv outBase)
    (hwf : prodEnv.constants.WF)
    (hsource : prodEnv.find? ``Eq = none)
    (hconstants : types.map Prod.snd ++ ctors.map Prod.snd =
        primitiveBoolConstants \/
      types.map Prod.snd ++ ctors.map Prod.snd = primitiveNatConstants)
    (hrecursors : ∀ entry ∈ recursors, entry.1.name ≠ ``Eq) :
    outEnv.find? ``Eq = none := by
  apply H.staged.combinedAtomic.preservesFindNone hwf hsource
  intro entry hentry
  rcases List.mem_append.mp hentry with hformation | hrecursors'
  · rcases List.mem_append.mp hformation with htype | hctor
    · have hprefix : entry ∈ types ++ ctors := by simp [htype]
      have hvalue : entry.2.name ∈
          ((types.map Prod.snd ++ ctors.map Prod.snd).map (·.name)) := by
        simp only [List.map_append, List.mem_append, List.mem_map]
        exact Or.inl ⟨entry.2, ⟨entry, htype, rfl⟩, rfl⟩
      have hname := H.staged.combinedAtomic.entryNames
        (List.mem_append_left recursors hprefix)
      rcases hconstants with hbool | hnat
      · rw [hbool, primitiveBoolConstants_names] at hvalue
        rw [hname]
        intro heq
        have hor : entry.2.name = ``Bool \/
            entry.2.name = ``Bool.false \/ entry.2.name = ``Bool.true := by
          simpa using hvalue
        exact hor.elim
          (fun h => (by native_decide : ``Bool ≠ ``Eq)
            (h.symm.trans heq))
          (fun hs => hs.elim
            (fun h => (by native_decide : ``Bool.false ≠ ``Eq)
              (h.symm.trans heq))
            (fun h => (by native_decide : ``Bool.true ≠ ``Eq)
              (h.symm.trans heq)))
      · rw [hnat, primitiveNatConstants_names] at hvalue
        rw [hname]
        intro heq
        have hor : entry.2.name = ``Nat \/
            entry.2.name = ``Nat.zero \/ entry.2.name = ``Nat.succ := by
          simpa using hvalue
        exact hor.elim
          (fun h => (by native_decide : ``Nat ≠ ``Eq)
            (h.symm.trans heq))
          (fun hs => hs.elim
            (fun h => (by native_decide : ``Nat.zero ≠ ``Eq)
              (h.symm.trans heq))
            (fun h => (by native_decide : ``Nat.succ ≠ ``Eq)
              (h.symm.trans heq)))
    · have hprefix : entry ∈ types ++ ctors := by simp [hctor]
      have hvalue : entry.2.name ∈
          ((types.map Prod.snd ++ ctors.map Prod.snd).map (·.name)) := by
        simp only [List.map_append, List.mem_append, List.mem_map]
        exact Or.inr ⟨entry.2, ⟨entry, hctor, rfl⟩, rfl⟩
      have hname := H.staged.combinedAtomic.entryNames
        (List.mem_append_left recursors hprefix)
      rcases hconstants with hbool | hnat
      · rw [hbool, primitiveBoolConstants_names] at hvalue
        rw [hname]
        intro heq
        have hor : entry.2.name = ``Bool \/
            entry.2.name = ``Bool.false \/ entry.2.name = ``Bool.true := by
          simpa using hvalue
        exact hor.elim
          (fun h => (by native_decide : ``Bool ≠ ``Eq)
            (h.symm.trans heq))
          (fun hs => hs.elim
            (fun h => (by native_decide : ``Bool.false ≠ ``Eq)
              (h.symm.trans heq))
            (fun h => (by native_decide : ``Bool.true ≠ ``Eq)
              (h.symm.trans heq)))
      · rw [hnat, primitiveNatConstants_names] at hvalue
        rw [hname]
        intro heq
        have hor : entry.2.name = ``Nat \/
            entry.2.name = ``Nat.zero \/ entry.2.name = ``Nat.succ := by
          simpa using hvalue
        exact hor.elim
          (fun h => (by native_decide : ``Nat ≠ ``Eq)
            (h.symm.trans heq))
          (fun hs => hs.elim
            (fun h => (by native_decide : ``Nat.zero ≠ ``Eq)
              (h.symm.trans heq))
            (fun h => (by native_decide : ``Nat.succ ≠ ``Eq)
              (h.symm.trans heq)))
  · exact hrecursors entry hrecursors'

/-- A safe completed canonical primitive block extends all three abstract
safety models.  Header and constructor replay remains merely staged; the
`HasPrimitives` invariant is restored only at their complete Bool/Nat batch. -/
theorem CompletedBlockCertificate.extendSafePrimitive
    {ves : VEnvs} {decl : VInductDecl}
    (H : CompletedBlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hconstants : types.map Prod.snd ++ ctors.map Prod.snd =
        primitiveBoolConstants \/
      types.map Prod.snd ++ ctors.map Prod.snd = primitiveNatConstants)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsafePrimitives : forall {n ci}, outEnv.find? n = some ci ->
      Environment.primitives.contains n ->
      ci.safety = .safe /\ ci.levelParams = [])
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (outBase.addDefEqRules rules)) :
    exists ves' : VEnvs, ves'.WF outEnv /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  have valid (safety : DefinitionSafety) :
      CheckingEnv.Valid safety prodEnv (ves.venv safety) :=
    (wf.tr (safety := safety)).toCheckingValid
      (wf.hasPrimitives (safety := safety)) wf.safePrimitives
      wf.typeAnnotationWrappers
  rcases H.rebaseAddInductSafe (valid .unsafe)
      (wf.mono DefinitionSafety.unsafe_le) hdecl hcompile horigins with
    ⟨unsafeBase, ⟨Hunsafe⟩, HunsafeAdd, hunsafeLE⟩
  rcases H.rebaseAddInductSafe (valid .partial)
      (wf.mono DefinitionSafety.le_safe) hdecl hcompile horigins with
    ⟨partialBase, ⟨Hpartial⟩, HpartialAdd, hpartialLE⟩
  rcases H.rebaseAddInductSafe (valid .safe) VEnv.LE.rfl hdecl hcompile
      horigins with
    ⟨safeBase, ⟨Hsafe⟩, HsafeAdd, hsafeLE⟩
  let pre : DefinitionSafety -> VEnv
    | .unsafe => unsafeBase
    | .partial => partialBase
    | .safe => safeBase
  let next (safety : DefinitionSafety) := (pre safety).addDefEqRules rules
  let cert : forall safety,
      CompletedBlockCertificate safety prodEnv (ves.venv safety) types ctors
        recursors rules outEnv (pre safety)
    | .unsafe => Hunsafe
    | .partial => Hpartial
    | .safe => Hsafe
  let adds : forall safety,
      AddInduct safety prodEnv.constants (ves.venv safety) decl
        outEnv.constants (next safety)
    | .unsafe => HunsafeAdd
    | .partial => HpartialAdd
    | .safe => HsafeAdd
  let outputLE : forall safety,
      outBase.addDefEqRules rules <= (pre safety).addDefEqRules rules
    | .unsafe => hunsafeLE
    | .partial => hpartialLE
    | .safe => hsafeLE
  have formationPrimitives (safety : DefinitionSafety) :
      (cert safety).staged.venvCtors.HasPrimitives := by
    rcases hconstants with hbool | hnat
    · apply VEnv.HasPrimitives.addBoolBootstrap
        (wf.hasPrimitives (safety := safety))
      rw [← hbool]
      exact VEnv.addConstVals_append
        (cert safety).staged.abstract_types
        (cert safety).staged.abstract_ctors
    · apply VEnv.HasPrimitives.addNatBootstrap
        (wf.hasPrimitives (safety := safety))
      rw [← hnat]
      exact VEnv.addConstVals_append
        (cert safety).staged.abstract_types
        (cert safety).staged.abstract_ctors
  rcases wf.extendInduct decl next adds H.staged.quotInit_eq
      (fun safety => hasPrimitives_addDefEqs
        ((cert safety).staged.recursorsAdded.hasPrimitives
          (formationPrimitives safety)) rules)
      hsafePrimitives hclosed hconstructorOwners
      (fun safety => H.replaySafeConstructorSemantics (cert safety)
        (wf.tr (safety := safety)).map_wf
        (wf.constructorSemantics (safety := safety)) hconstructorSemantics
        (outputLE safety))
      (fun {safety safety'} hle =>
        VInductBlock.install_mono (wf.mono hle)
          (cert safety').install (cert safety).install) with
    ⟨ves', wf', hle⟩
  exact ⟨ves', wf', hle⟩

/-- Canonical-Eq compatibility adapter for declarations processed after the
bootstrap equality family has already been established. -/
theorem CompletedBlockCertificate.extendSafePrimitiveOfQuotReady
    {ves : VEnvs} {decl : VInductDecl}
    (H : CompletedBlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hEq : CanonicalEqEnvs ves)
    (hconstants : types.map Prod.snd ++ ctors.map Prod.snd =
        primitiveBoolConstants \/
      types.map Prod.snd ++ ctors.map Prod.snd = primitiveNatConstants)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsafePrimitives : forall {n ci}, outEnv.find? n = some ci ->
      Environment.primitives.contains n ->
      ci.safety = .safe /\ ci.levelParams = [])
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (outBase.addDefEqRules rules)) :
    exists ves' : VEnvs, ves'.WF outEnv /\ CanonicalEqEnvs ves' /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases H.extendSafePrimitive wf hconstants hdecl hcompile horigins
      hsafePrimitives hclosed
      hconstructorOwners hconstructorSemantics with ⟨ves', wf', hle⟩
  exact ⟨ves', wf', hEq.mono hle, hle⟩

/-- Primitive installation preserves the bootstrap phase invariant: before
`Eq`, the exact Bool/Nat batch leaves it absent; after `Eq`, monotonicity
preserves its canonical interpretation. -/
theorem CompletedBlockCertificate.extendSafePrimitiveEqReadyOrAbsent
    {ves : VEnvs} {decl : VInductDecl}
    (H : CompletedBlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WF prodEnv)
    (hEq : EqReadyOrAbsent prodEnv ves)
    (hpreserveAbsent : prodEnv.constants.find? ``Eq = none →
      outEnv.constants.find? ``Eq = none)
    (hconstants : types.map Prod.snd ++ ctors.map Prod.snd =
        primitiveBoolConstants \/
      types.map Prod.snd ++ ctors.map Prod.snd = primitiveNatConstants)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hsafePrimitives : forall {n ci}, outEnv.find? n = some ci ->
      Environment.primitives.contains n ->
      ci.safety = .safe /\ ci.levelParams = [])
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (outBase.addDefEqRules rules)) :
    exists ves' : VEnvs, ves'.WF outEnv /\ EqReadyOrAbsent outEnv ves' /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases hEq with habsent | hcanonical
  · have houtAbsent := hpreserveAbsent habsent
    rcases H.extendSafePrimitive wf hconstants hdecl hcompile horigins
        hsafePrimitives hclosed hconstructorOwners hconstructorSemantics with
      ⟨ves', wf', hle⟩
    exact ⟨ves', wf', Or.inl houtAbsent, hle⟩
  · rcases H.extendSafePrimitiveOfQuotReady wf hcanonical hconstants hdecl
        hcompile horigins hsafePrimitives hclosed hconstructorOwners
        hconstructorSemantics with
      ⟨ves', wf', hcanonical', hle⟩
    exact ⟨ves', wf', Or.inr hcanonical', hle⟩

/-- The shared completed-constructor boundary still determines the exact
canonical primitive constant batch from its source translation. -/
theorem CompletedConstructorPhases.primitiveAbstractConstants
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe) :
    R.headerEntries.map Prod.snd ++ R.constructorEntries.map Prod.snd =
        primitiveBoolConstants \/
      R.headerEntries.map Prod.snd ++ R.constructorEntries.map Prod.snd =
        primitiveNatConstants := by
  rw [R.headerValues, R.constructorValues]
  exact Lean4Lean.TrInductDeclHeaders.primitiveAbstractConstants
    (Lean4Lean.VerifyInductive.TrInductDeclCore.headers R.core) Hshape

/-- Every generated recursor has a `.rec` suffix, hence is distinct from the
root bootstrap name `Eq`. -/
theorem GeneratedRecursors.entryNamesNeEq
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries) :
    ∀ entry ∈ entries, entry.1.name ≠ ``Eq := by
  intro entry hentry
  rcases List.mem_iff_getElem.mp hentry with ⟨i, hi, heq⟩
  let E := H.entry i hi
  have hname : entries[i].1.name = Lean.mkRecName indTypes[i]!.name := by
    rw [E.source_eq]
    exact E.name
  rw [heq] at hname
  rw [hname]
  simp [Lean.mkRecName]

/-- The completed recursor suffix preserves the valid checking context that
was restored at the full primitive constructor boundary. -/
theorem CompletedRecursorPhasesResult.outValid
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    CheckingEnv.Valid H.localContext.safety outEnv H.outVEnv := by
  apply H.installed.valid
  rw [H.localExtends.safety_eq, H.localExtends.env_eq]
  exact R.context.checking

/-- A successful primitive Bool/Nat run extends the complete environment
model without any premise about the bootstrap state of `Eq`. -/
theorem SemanticPrimitiveRunWithStatsResult.extendSafe
    {ves : VEnvs}
    (Hrun : SemanticPrimitiveRunWithStatsResult c stats nparams depth
      (ves.venv .safe) indTypes (c.safety != .safe) outEnv)
    (wf : ves.WF c.env)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      (c.safety != .safe)) :
    exists decl : VInductDecl, exists ves' : VEnvs,
      ves'.WF outEnv /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases Hrun with ⟨decl, _ctorEnv, R, ⟨Hrecursors⟩⟩
  have hsafety : c.safety = .safe := by
    have hnotUnsafe : (c.safety != .safe) = false := Hshape.2.2.1
    simpa using hnotUnsafe
  have hnonempty : indTypes.toList ≠ [] := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  rcases Hrecursors.canonicalCompletedRuleTranslation with ⟨T⟩
  let Hcert0 := Hrecursors.blockCertificate T.rules T.rulesWF
  have Hcert : CompletedBlockCertificate .safe c.env (ves.venv .safe)
      R.headerEntries R.constructorEntries Hrecursors.entries T.rules
      outEnv Hrecursors.outVEnv := by
    simpa [Hcert0, hsafety] using Hcert0
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .safe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .safe) Hcert.block := by
    simpa only [CompletedBlockCertificate.block] using
      T.compilation.compilesTo
  have hconstants := R.primitiveAbstractConstants Hshape
  have HvalidOut := Hrecursors.outValid
  have hlocalSafety : Hrecursors.localContext.safety = .safe :=
    Hrecursors.localExtends.safety_eq.trans hsafety
  rw [hlocalSafety] at HvalidOut
  have Hsemantics : InductiveConstructorsSemanticallyCoherent .safe outEnv
      (Hrecursors.outVEnv.addDefEqRules T.rules) :=
    Hrecursors.completedConstructorSemantics
      (wf.constructorSemantics (safety := .safe)) T.rules
  rcases Hcert.extendSafePrimitive wf hconstants hdecl hcompile
      Hrecursors.productionInductiveOrigins HvalidOut.safePrimitives
      Hrecursors.closed
      (Hrecursors.constructorOwnersPresent wf.constructorOwners) Hsemantics with
    ⟨ves', wf', hle⟩
  exact ⟨decl, ves', wf', hle⟩

/-- A skeleton-free semantic primitive run now reaches the final
safety-indexed environment boundary, not merely a single abstract
`VEnv.AddInduct` witness. -/
theorem SemanticPrimitiveRunWithStatsResult.extendSafeEqReadyOrAbsent
    (Hrun : SemanticPrimitiveRunWithStatsResult c stats nparams depth
      (ves.venv .safe) indTypes (c.safety != .safe) outEnv)
    (wf : ves.WF c.env)
    (hEq : EqReadyOrAbsent c.env ves)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      (c.safety != .safe)) :
    exists decl : VInductDecl, exists ves' : VEnvs,
      ves'.WF outEnv /\ EqReadyOrAbsent outEnv ves' /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases Hrun with ⟨decl, _ctorEnv, R, ⟨Hrecursors⟩⟩
  have hsafety : c.safety = .safe := by
    have hnotUnsafe : (c.safety != .safe) = false := Hshape.2.2.1
    simpa using hnotUnsafe
  have hnonempty : indTypes.toList ≠ [] := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  rcases Hrecursors.canonicalCompletedRuleTranslation with ⟨T⟩
  let Hcert0 := Hrecursors.blockCertificate T.rules T.rulesWF
  have Hcert : CompletedBlockCertificate .safe c.env (ves.venv .safe)
      R.headerEntries R.constructorEntries Hrecursors.entries T.rules
      outEnv Hrecursors.outVEnv := by
    simpa [Hcert0, hsafety] using Hcert0
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .safe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .safe) Hcert.block := by
    simpa only [CompletedBlockCertificate.block] using
      T.compilation.compilesTo
  have hconstants := R.primitiveAbstractConstants Hshape
  have HvalidOut := Hrecursors.outValid
  have hlocalSafety : Hrecursors.localContext.safety = .safe :=
    Hrecursors.localExtends.safety_eq.trans hsafety
  rw [hlocalSafety] at HvalidOut
  have Hsemantics : InductiveConstructorsSemanticallyCoherent .safe outEnv
      (Hrecursors.outVEnv.addDefEqRules T.rules) :=
    Hrecursors.completedConstructorSemantics
      (wf.constructorSemantics (safety := .safe)) T.rules
  have hpreserveAbsent : c.env.constants.find? ``Eq = none →
      outEnv.constants.find? ``Eq = none := by
    intro hsource
    have hsource' : c.env.find? ``Eq = none := by
      rw [Lean.Kernel.Environment.find?,
        (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
      exact hsource
    have hout := Hcert.preservesEqAbsentPrimitive
      (wf.tr (safety := .safe)).map_wf hsource' hconstants
      Hrecursors.generated.entryNamesNeEq
    have houtWF := Hcert.staged.combinedAtomic.targetMapWF
      (wf.tr (safety := .safe)).map_wf
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hout
    exact hout
  rcases Hcert.extendSafePrimitiveEqReadyOrAbsent wf hEq hpreserveAbsent
      hconstants hdecl hcompile Hrecursors.productionInductiveOrigins
      HvalidOut.safePrimitives Hrecursors.closed
      (Hrecursors.constructorOwnersPresent wf.constructorOwners) Hsemantics with
    ⟨ves', wf', hEq', hle⟩
  exact ⟨decl, ves', wf', hEq', hle⟩

/-- Compatibility adapter for callers already past the canonical `Eq`
bootstrap declaration. -/
theorem SemanticPrimitiveRunWithStatsResult.extendSafeOfQuotReady
    (Hrun : SemanticPrimitiveRunWithStatsResult c stats nparams depth
      (ves.venv .safe) indTypes (c.safety != .safe) outEnv)
    (wf : ves.WF c.env)
    (hEq : CanonicalEqEnvs ves)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      (c.safety != .safe)) :
    exists decl : VInductDecl, exists ves' : VEnvs,
      ves'.WF outEnv /\ CanonicalEqEnvs ves' /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases Hrun.extendSafeEqReadyOrAbsent wf (Or.inr hEq) Hshape with
    ⟨decl, ves', wf', _hEq', hle⟩
  exact ⟨decl, ves', wf', hEq.mono hle, hle⟩

/-- Declaration-facing source alignment lets the completed semantic result
consume the caller's exact safety-indexed source model. -/
theorem VerifiedSemanticPrimitiveInductiveRunResultSourceAligned.extendSafeEqReadyOrAbsent
    (Hrun : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned source
      (ves.venv .safe) nparams types numNested outEnv)
    (wf : ves.WF source.env)
    (hEq : EqReadyOrAbsent source.env ves) :
    exists decl : VInductDecl, exists ves' : VEnvs,
      ves'.WF outEnv /\ EqReadyOrAbsent outEnv ves' /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases Hrun with
    ⟨c', stats, depth, _commonParams, _commonLevel, Hc', henv, hsafety,
      _hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hshape,
      Hphases⟩
  have wf' : ves.WF c'.env := by simpa [henv] using wf
  have Hshape' : PrimitiveInductiveShape c'.lparams nparams
      types.toArray.toList (c'.safety != .safe) := by
    simpa [hsafety] using Hshape
  have Hphases' : SemanticPrimitiveRunWithStatsResult c' stats nparams depth
      (ves.venv .safe) types.toArray (c'.safety != .safe) outEnv := by
    simpa [hvenv, hsafety] using Hphases
  have hEq' : EqReadyOrAbsent c'.env ves := by simpa [henv] using hEq
  exact Hphases'.extendSafeEqReadyOrAbsent wf' hEq' Hshape'

/-- Source-aligned primitive refinement without an equality-bootstrap
premise. -/
theorem VerifiedSemanticPrimitiveInductiveRunResultSourceAligned.extendSafe
    {ves : VEnvs}
    (Hrun : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned source
      (ves.venv .safe) nparams types numNested outEnv)
    (wf : ves.WF source.env) :
    exists decl : VInductDecl, exists ves' : VEnvs,
      ves'.WF outEnv /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases Hrun with
    ⟨c', stats, depth, _commonParams, _commonLevel, Hc', henv, hsafety,
      _hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hshape,
      Hphases⟩
  have wf' : ves.WF c'.env := by simpa [henv] using wf
  have Hshape' : PrimitiveInductiveShape c'.lparams nparams
      types.toArray.toList (c'.safety != .safe) := by
    simpa [hsafety] using Hshape
  have Hphases' : SemanticPrimitiveRunWithStatsResult c' stats nparams depth
      (ves.venv .safe) types.toArray (c'.safety != .safe) outEnv := by
    simpa [hvenv, hsafety] using Hphases
  exact SemanticPrimitiveRunWithStatsResult.extendSafe Hphases' wf' Hshape'

/-- Compatibility adapter for source-aligned callers already past `Eq`. -/
theorem VerifiedSemanticPrimitiveInductiveRunResultSourceAligned.extendSafeOfQuotReady
    (Hrun : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned source
      (ves.venv .safe) nparams types numNested outEnv)
    (wf : ves.WF source.env)
    (hEq : CanonicalEqEnvs ves) :
    exists decl : VInductDecl, exists ves' : VEnvs,
      ves'.WF outEnv /\ CanonicalEqEnvs ves' /\
      forall safety, ves.venv safety <= ves'.venv safety := by
  rcases Hrun.extendSafeEqReadyOrAbsent wf (Or.inr hEq) with
    ⟨decl, ves', wf', _hEq', hle⟩
  exact ⟨decl, ves', wf', hEq.mono hle, hle⟩

/-- The executable primitive checker reaches the final safety-indexed model
whenever its verified checking context is the caller's safe source model. -/
theorem AddInductive.run.primitiveFinalEnvironmentEqReadyOrAbsentWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hsource : Hc.venv = ves.venv .safe)
    (hEq : EqReadyOrAbsent c.env ves)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      exists decl : VInductDecl, exists ves' : VEnvs,
        ves'.WF outEnv /\ EqReadyOrAbsent outEnv ves' /\
        forall safety, ves.venv safety <= ves'.venv safety := by
  have Hrun := AddInductive.run.primitiveSemanticSourceAlignedWF
    nparams numNested Hc wf.inductivesClosed Hshape hctx hnonempty HnotPartial
  exact Hrun.mono fun outEnv Hresult => by
    have Hresult' : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned
        c (ves.venv .safe) nparams types numNested outEnv := by
      simpa [hsource] using Hresult
    exact Hresult'.extendSafeEqReadyOrAbsent wf hEq

/-- The executable primitive checker reaches the final safety-indexed model
without an equality-bootstrap premise. -/
theorem AddInductive.run.primitiveFinalEnvironmentModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hsource : Hc.venv = ves.venv .safe)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      exists decl : VInductDecl, exists ves' : VEnvs,
        ves'.WF outEnv /\
        forall safety, ves.venv safety <= ves'.venv safety := by
  have Hrun := AddInductive.run.primitiveSemanticSourceAlignedWF
    nparams numNested Hc wf.inductivesClosed Hshape hctx hnonempty HnotPartial
  exact Hrun.mono fun outEnv Hresult => by
    have Hresult' : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned
        c (ves.venv .safe) nparams types numNested outEnv := by
      simpa [hsource] using Hresult
    exact
      VerifiedSemanticPrimitiveInductiveRunResultSourceAligned.extendSafe
        Hresult' wf

/-- Compatibility adapter for executable primitive runs after canonical
equality is available. -/
theorem AddInductive.run.primitiveFinalEnvironmentWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hsource : Hc.venv = ves.venv .safe)
    (hEq : CanonicalEqEnvs ves)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      exists decl : VInductDecl, exists ves' : VEnvs,
        ves'.WF outEnv /\ CanonicalEqEnvs ves' /\
        forall safety, ves.venv safety <= ves'.venv safety := by
  have Hrun := AddInductive.run.primitiveFinalEnvironmentEqReadyOrAbsentWF
    nparams numNested Hc wf hsource (Or.inr hEq) Hshape hctx
    hnonempty HnotPartial
  exact Hrun.mono fun _ ⟨decl, ves', wf', _hEq', hle⟩ =>
    ⟨decl, ves', wf', hEq.mono hle, hle⟩

end VerifyInductive
end Lean4Lean
