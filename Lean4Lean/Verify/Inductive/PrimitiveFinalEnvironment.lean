import Lean4Lean.Verify.Inductive.PrimitiveSemanticAddInduct

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

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
      H.finalVEnv)
    (hreplay : H.finalVEnv <= Hreplay.finalVEnv) :
    InductiveConstructorsSemanticallyCoherent observer outEnv
      Hreplay.finalVEnv := by
  intro familyName familyInfo hfamily hvisible i hi
  let Hinstall := Hreplay.staged.combinedAtomic
  rcases Hinstall.entryOrigin hwf hfamily with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible i hi with ⟨C⟩
    have hlookup := Hinstall.preservesSourceFind hwf C.lookup
    have hle : observerBase <= Hreplay.finalVEnv :=
      VEnv.addEliminators_addProjections_le.trans (Hinstall.le.trans VEnv.addDefEqRules_le)
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

/-- A safe completed canonical primitive block extends all three abstract
safety models.  Header and constructor replay remains merely staged; the
`HasPrimitives` invariant is restored only at their complete Bool/Nat batch. -/
theorem CompletedBlockCertificate.extendSafePrimitiveExact
    {ves : VEnvs} {decl : VInductDecl}
    (H : CompletedBlockCertificate .safe prodEnv (ves.venv .safe) types ctors
      recursors rules outEnv outBase)
    (wf : ves.WFCore prodEnv) (hcorner : ∀ safety, ProjectionCorner safety prodEnv (ves.venv safety))
    (hconstants : types.map Prod.snd ++ ctors.map Prod.snd =
        primitiveBoolConstants \/
      types.map Prod.snd ++ ctors.map Prod.snd = primitiveNatConstants)
    (hdecl : decl.WF (ves.venv .safe))
    (hcompile : decl.CompilesTo (ves.venv .safe) H.block)
    (horigins : ProductionInductiveOrigins prodEnv.constants outEnv.constants
      decl)
    (hprovenance : InductiveRecursorProvenance .unsafe prodEnv.constants
      (ves.venv .safe) outEnv.constants H.finalVEnv)
    (hsafePrimitives : forall {n ci}, outEnv.find? n = some ci ->
      Environment.primitives.contains n ->
      ci.safety = .safe /\ ci.levelParams = [])
    (hclosed : MutualInductivesClosed outEnv)
    (hconstructorOwners : ConstructorOwnersPresent outEnv)
    (hconstructorSemantics :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        H.finalVEnv)
    (Hreplay : ∀ safety, VInductBlock.EliminatorsReplay (ves.venv safety) decl H.block) :
    exists ves' : VEnvs, ves'.WFCore outEnv /\
      (forall safety, ves.venv safety <= ves'.venv safety) /\
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) /\
      H.finalVEnv <= ves'.venv .safe := by
  have valid (safety : DefinitionSafety) :
      CheckingEnv.Valid safety prodEnv (ves.venv safety) :=
    (wf.tr (safety := safety)).toCheckingValid
      (wf.hasPrimitives (safety := safety)) wf.safePrimitives
      wf.constructorOwners wf.projectionRegistryCoherent ((hcorner _))
  rcases H.rebaseAddInductSafe (valid .unsafe)
      (wf.mono DefinitionSafety.unsafe_le) hdecl hcompile horigins hprovenance
      (Hreplay .unsafe) with
    ⟨unsafeBase, Hunsafe, HunsafeAdd, hunsafeLE, hunsafeProjections, hunsafeElim⟩
  rcases H.rebaseAddInductSafe (valid .partial)
      (wf.mono DefinitionSafety.le_safe) hdecl hcompile horigins hprovenance
      (Hreplay .partial) with
    ⟨partialBase, Hpartial, HpartialAdd, hpartialLE,
      hpartialProjections, hpartialElim⟩
  rcases H.rebaseAddInductSafe (valid .safe) VEnv.LE.rfl hdecl hcompile
      horigins hprovenance (Hreplay .safe) with
    ⟨safeBase, Hsafe, HsafeAdd, hsafeLE, hsafeProjections, hsafeElim⟩
  let pre : DefinitionSafety -> VEnv
    | .unsafe => unsafeBase
    | .partial => partialBase
    | .safe => safeBase
  let cert : forall safety,
      CompletedBlockCertificate safety prodEnv (ves.venv safety) types ctors
        recursors rules outEnv (pre safety)
    | .unsafe => Hunsafe
    | .partial => Hpartial
    | .safe => Hsafe
  let next (safety : DefinitionSafety) := (cert safety).finalVEnv
  let adds : forall safety,
      AddInduct safety prodEnv.constants (ves.venv safety) decl
        outEnv.constants (next safety)
    | .unsafe => by
        simpa [next, cert, CompletedBlockCertificate.finalVEnv,
          hunsafeProjections] using HunsafeAdd
    | .partial => by
        simpa [next, cert, CompletedBlockCertificate.finalVEnv,
          hpartialProjections] using HpartialAdd
    | .safe => by
        simpa [next, cert, CompletedBlockCertificate.finalVEnv,
          hsafeProjections] using HsafeAdd
  let outputLE : forall safety,
      H.finalVEnv <= (cert safety).finalVEnv
    | .unsafe => by
        simpa [cert, CompletedBlockCertificate.finalVEnv,
          hunsafeProjections] using hunsafeLE
    | .partial => by
        simpa [cert, CompletedBlockCertificate.finalVEnv,
          hpartialProjections] using hpartialLE
    | .safe => by
        simpa [cert, CompletedBlockCertificate.finalVEnv,
          hsafeProjections] using hsafeLE
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
  rcases wf.extendInductExact decl next adds H.staged.quotInit_eq
      (fun safety =>
        hasPrimitives_addDefEqs
          ((cert safety).staged.recursorsAdded.hasPrimitives
            (formationPrimitives safety).addEliminators.addProjections)
          rules)
      hsafePrimitives hclosed hconstructorOwners
      (fun safety => H.replaySafeConstructorSemantics (cert safety)
        (wf.tr (safety := safety)).map_wf
        (wf.constructorSemantics (safety := safety)) hconstructorSemantics
        (outputLE safety))
      (fun {safety safety'} hle => by
        have hprojections : (cert safety').projections =
            (cert safety).projections := by
          cases safety <;> cases safety' <;>
            simp only [cert, hunsafeProjections, hpartialProjections,
              hsafeProjections]
        have heliminators : (cert safety').staged.eliminators =
            (cert safety).staged.eliminators := by
          cases safety <;> cases safety' <;>
            simp only [cert, hunsafeElim, hpartialElim, hsafeElim]
        have hblock : (cert safety').block = (cert safety).block :=
          (cert safety').block_eq_of_projections_eq (cert safety) hprojections heliminators
        have hinstall := (cert safety').install
        rw [hblock] at hinstall
        exact VInductBlock.install_mono (wf.mono hle)
          hinstall (cert safety).install) with
    ⟨ves', wf', hle, hexact⟩
  refine ⟨ves', wf', hle, ?_, ?_⟩
  · rw [hexact .safe]
    exact (adds .safe).toVEnv
  · rw [hexact .safe]
    exact outputLE .safe

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

/-- The completed recursor suffix preserves the local checking invariants that
were restored at the full primitive constructor boundary. (The full invariant
is regained only once the iota rules are installed, see `VEnvs.WFCore`.) -/
theorem CompletedRecursorPhasesResult.outValid
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    CheckingEnv.ValidCore H.localContext.safety outEnv H.outVEnv := by
  apply H.installed.validCore
  rw [H.localExtends.safety_eq, H.localExtends.env_eq]
  exact R.context.checking.toValidCore

/-- A successful primitive Bool/Nat run extends the complete environment
model without any premise about the bootstrap state of `Eq`. -/
theorem SemanticPrimitiveRunWithStatsResult.extendSafeExact
    {ves : VEnvs}
    (Hrun : SemanticPrimitiveRunWithStatsResult c stats nparams depth
      (ves.venv .safe) indTypes (c.safety != .safe) outEnv)
    (wf : ves.WFCore c.env) (hcorner : ∀ safety, ProjectionCorner safety c.env (ves.venv safety))
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      (c.safety != .safe)) :
    exists ves' : VEnvs, exists decl : VInductDecl,
      exists envTypes envCtors : VEnv,
      ves'.WFCore outEnv /\
      (forall safety, ves.venv safety <= ves'.venv safety) /\
      TrInductDeclCore (ves.venv .safe) c.lparams nparams indTypes.toList
        (c.safety != .safe) decl envTypes envCtors /\
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) /\
      VEnvs.CertPres c.env outEnv ves ves' := by
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
  let Hcert := Hcert0.sf_mono (safety := .safe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .safe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .safe) Hcert.block := by
    simpa [Hcert, Hcert0, CompletedBlockCertificate.sf_mono, CompletedStagedBlock.sf_mono,
      CompletedBlockCertificate.block] using
      (T.compilation hnonempty).compilesTo
  have hconstants := R.primitiveAbstractConstants Hshape
  have HvalidOut := Hrecursors.outValid
  have hlocalSafety : Hrecursors.localContext.safety = .safe :=
    Hrecursors.localExtends.safety_eq.trans hsafety
  rw [hlocalSafety] at HvalidOut
  have Hsemantics : InductiveConstructorsSemanticallyCoherent .safe outEnv
      Hcert.finalVEnv := by
    simpa [Hcert, Hcert0, CompletedBlockCertificate.sf_mono, CompletedStagedBlock.sf_mono,
      CompletedBlockCertificate.finalVEnv] using
    Hrecursors.completedConstructorSemantics
      (wf.constructorSemantics (safety := .safe)) T.rules
  rcases Hcert.extendSafePrimitiveExact wf hcorner hconstants hdecl hcompile
      Hrecursors.productionInductiveOrigins T.recursorProvenance HvalidOut.safePrimitives
      Hrecursors.closed
      (Hrecursors.constructorOwnersPresent wf.constructorOwners) Hsemantics
      (fun safety => Hrecursors.blockEliminatorsReplay T.rules T.rulesWF
        (wf.mono (DefinitionSafety.le_safe (a := safety)))) with
    ⟨ves', wf', hle, hadd, hfinal⟩
  have hH : R.headerVEnv ≤ ves'.venv (if false then .unsafe else .safe) := by
    refine (Hcert.typesLe ?_).trans hfinal
    rw [R.headerValues]
    exact R.core.typesAdded
  refine ⟨ves', decl, R.headerVEnv, R.ctorVEnv, wf', hle, R.core, hadd,
    VEnvs.CertPres.ofOrigin (isUnsafe := false) hle wf'.mono hH fun hfind => ?_⟩
  rcases Hrecursors.ctorOrigin hfind with h | ⟨hu, hc⟩
  · exact .inl h
  · refine .inr ⟨?_, hc⟩
    rw [hu, hsafety]; rfl

/-- The executable primitive checker reaches the final safety-indexed model
without an equality-bootstrap premise. -/
theorem AddInductive.run.primitiveFinalEnvironmentModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WFCore c.env) (hcorner : ∀ safety, ProjectionCorner safety c.env (ves.venv safety))
    (hsource : Hc.venv = ves.venv .safe)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      exists decl : VInductDecl, exists ves' : VEnvs,
        ves'.WFCore outEnv /\
        forall safety, ves.venv safety <= ves'.venv safety := by
  have Hrun := AddInductive.run.primitiveSemanticSourceAlignedWF
    nparams numNested Hc wf.inductivesClosed Hshape hctx hnonempty HnotPartial
  exact Hrun.mono fun outEnv Hresult => by
    have Hresult' : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned
        c (ves.venv .safe) nparams types numNested outEnv := by
      simpa [hsource] using Hresult
    rcases Hresult' with
      ⟨c', stats, depth, _commonParams, _commonLevel, _Hc', henv, hsafety,
        _hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hshape',
        Hphases⟩
    have wf' : ves.WFCore c'.env := by simpa [henv] using wf
    have hcorner' : ∀ safety, ProjectionCorner safety c'.env (ves.venv safety) := by
      rw [henv]; exact hcorner
    have Hshape'' : PrimitiveInductiveShape c'.lparams nparams
        types.toArray.toList (c'.safety != .safe) := by
      simpa [hsafety] using Hshape'
    have Hphases' : SemanticPrimitiveRunWithStatsResult c' stats nparams depth
        (ves.venv .safe) types.toArray (c'.safety != .safe) outEnv := by
      simpa [hvenv, hsafety] using Hphases
    rcases Hphases'.extendSafeExact wf' hcorner' Hshape'' with
      ⟨ves', decl, _envTypes, _envCtors, wf'', hle, _source, _hadd⟩
    exact ⟨decl, ves', wf'', hle⟩

end VerifyInductive
end Lean4Lean
