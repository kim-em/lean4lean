import Lean4Lean.Verify.Inductive.Rules.Lhs
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Verify.Inductive.Recursor.InstanceAlignment
import Lean4Lean.Verify.Inductive.Recursor.Check

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Owner-prefix accumulation of reconstructed equations and their typing
proofs.  Keeping the equation traversal independent of the final block lets
this invariant grow in exactly the order used by `declareRecursors`. -/
structure CompletedRecursorPhasesResult.GeneratedEquationBuild
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (Us : List Name)
    (owner : Nat) (rules : List VDefEq) : Prop where
  equations : H.GeneratedIotaEquationTranslations Us [] owner rules
  rulesWF : ∀ rule ∈ rules, rule.WF H.outVEnv

def CompletedRecursorPhasesResult.GeneratedEquationBuild.empty
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (Us : List Name) :
    H.GeneratedEquationBuild Us 0 [] where
  equations := .nil
  rulesWF _ h := by simp at h

/-- The installed rule list of an ordinary recursor run and its typing in the
environment with the recursors. The compilation realization of
`CompletedRuleTranslationResult` fixes the list as the canonical equations. -/
structure CompletedRuleTranslationShape
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) where
  rules : List VDefEq
  rulesWF : ∀ df ∈ rules, df.WF H.outVEnv

structure CompletedRuleTranslationResult
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) extends CompletedRuleTranslationShape H where
  realization : InductiveSignature.CompilationRealization sourceEnv decl
    (H.blockCertificate rules rulesWF).block H.outVEnv H.entries

/-- Source nonemptiness comes from the existing declaration entry guard.
The completed run supplies formation and block typing, so the finite
derivation is constructed here without an additional caller proof. -/
theorem CompletedRuleTranslationResult.compilation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    (T : CompletedRuleTranslationResult H)
    (hnonempty : indTypes.toList ≠ []) :
    OrdinaryCompilationCertificate sourceEnv decl
      (H.blockCertificate T.rules T.rulesWF).block := by
  let B := H.blockCertificate T.rules T.rulesWF
  have htypes : B.block.types = decl.typeConstants := R.headerValues
  have hctors : B.block.ctors = decl.constructorConstants := R.constructorValues
  have hprojections : B.block.projections = decl.projectionEntries := by
    simp [B, CompletedBlockCertificate.block]
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  exact {
    types := htypes
    ctors := hctors
    projections := hprojections
    names := B.names
    canonical := T.realization.compiles
    finite := CompiledInductive.ordinary
      (Lean4Lean.TrInductDecl.sourceWF Htranslated) R.formation.formationWF
      T.realization.compiles B.wf htypes hctors hprojections B.names }

/-- Every newly stored equation is headed by a recursor from the same joint
generation witness, with that exact concrete entry present after installation. -/
theorem CompletedRuleTranslationResult.equationProvenance
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    (T : CompletedRuleTranslationResult H) :
    ∀ df, (H.outVEnv.addDefEqRules T.rules).defeqs df → sourceEnv.defeqs df ∨
      ∃ head ls rec, df.lhs.stripLams.getAppFnArgs.1 = .const head ls ∧
        outEnv.constants.find? head = some (.recInfo rec) := by
  let B := H.blockCertificate T.rules T.rulesWF
  have Hatomic := B.staged.combinedAtomic
  have hmapWF : c.env.constants.WF := R.sourceContext.checking.tr.map_wf
  have houtMapWF : outEnv.constants.WF := Hatomic.targetMapWF hmapWF
  intro df hdf
  rcases VEnv.addDefEqRules_defeqs_iff.mp hdf with hold | hnew
  · exact .inl (by simpa only [VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs] using Hatomic.defeqs df hold)
  · right
    rcases T.realization.generated with ⟨s, g, envTypes, hm, ht, ha, _, hn, hr, he, hentries⟩
    change T.rules = g.equations at he
    rw [he] at hnew
    rcases List.mem_map.mp hnew with ⟨index, _, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_l hentries
      s.constructors[index].owner (List.mem_finRange _) with ⟨entry, hentry, rec, hc, hv, hrec⟩
    have hlookup := Hatomic.findEntry hmapWF (info := entry.1) (value := entry.2) (by
      change entry ∈ R.headerEntries ++ R.constructorEntries ++ H.entries
      simp [hentry])
    rw [Lean.Kernel.Environment.find?, houtMapWF.find?'_eq_find?] at hlookup
    rw [hc] at hlookup
    refine ⟨rec.name, VLevel.params g.uvars, rec, ?_, hlookup⟩
    rw [hrec.name]
    exact g.equation_head index

/-- Formation headers and constructors cannot introduce a concrete recursor;
every new recursor lookup comes from the exact generated entry list. -/
theorem CompletedRuleTranslationResult.recursorEntryOrigin
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    (T : CompletedRuleTranslationResult H)
    {name : Name} {rec : RecursorVal}
    (hfind : outEnv.constants.find? name = some (.recInfo rec)) :
    c.env.constants.find? name = some (.recInfo rec) ∨
      ∃ entry ∈ H.entries, name = entry.1.name ∧ .recInfo rec = entry.1 := by
  let B := H.blockCertificate T.rules T.rulesWF
  have Hatomic := B.staged.combinedAtomic
  have hmapWF : c.env.constants.WF := R.sourceContext.checking.tr.map_wf
  have houtMapWF : outEnv.constants.WF := Hatomic.targetMapWF hmapWF
  have hfind' : outEnv.find? name = some (.recInfo rec) := by
    simpa only [Lean.Kernel.Environment.find?, houtMapWF.find?'_eq_find?] using hfind
  rcases Hatomic.entryOrigin hmapWF hfind' with hold | ⟨entry, hentry, hname, hinfo⟩
  · left
    simpa only [Lean.Kernel.Environment.find?, hmapWF.find?'_eq_find?] using hold
  · change entry ∈ R.headerEntries ++ R.constructorEntries ++ H.entries at hentry
    rcases List.mem_append.mp hentry with hformation | hrec
    · rcases List.mem_append.mp hformation with hheader | hctor
      · rcases R.headerSourceAligned with ⟨_, hheaders⟩
        rcases hheaders.originInfo hheader with ⟨info, _, heq⟩
        rw [heq] at hinfo
        cases hinfo
      · rcases R.constructorSourceAligned.ownerOfEntry hctor with ⟨_, _, info, heq, _⟩
        rw [heq] at hinfo
        cases hinfo
    · exact .inr ⟨entry, hrec, hname, hinfo⟩

/-- Recursor provenance is produced from the completed constructor/recursor
run and its joint generation/metadata witness. It cannot be recovered from a
generic block of translated constant types. The unsafe observer clause covers
all new entries, so the evidence can be replayed at every observer safety. -/
theorem CompletedRuleTranslationResult.recursorProvenance
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    (T : CompletedRuleTranslationResult H) :
    NewRecursorsAligned .unsafe c.env.constants sourceEnv
      outEnv.constants (H.outVEnv.addDefEqRules T.rules) := by
  refine { defeq := T.equationProvenance, recursor := ?_ }
  intro name rec hfind
  rcases T.recursorEntryOrigin hfind with hold | ⟨entry, hentry, hname, hinfo⟩
  · exact .inl hold
  · right
    intro _hsafety
    rcases T.realization.generated with ⟨s, g, envTypes, hm, ht, ha, _, hn, hr, he, hentries⟩
    change T.rules = g.equations at he
    have hrecursors : ∀ owner, H.outVEnv.constants (g.recursorName owner) =
        some (g.recursor owner).toVConstant := by
      intro owner
      rcases Lean4Lean.List.Forall₂.forall_exists_l hentries owner (List.mem_finRange _) with
        ⟨recEntry, hrecEntry, recInfo, hsource, habstract, hrec⟩
      have hlookup := VEnv.addConstVals_get H.installed.abstract
        (List.mem_map.mpr ⟨recEntry, hrecEntry, rfl⟩)
      rw [habstract] at hlookup
      exact hlookup
    have hrules : ∀ index, (g.equation index).WF H.outVEnv := by
      intro index
      apply T.rulesWF
      rw [he]
      exact List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r hentries entry hentry with
      ⟨owner, howner, recInfo, hsource, habstract, hrec⟩
    have hrecEq : rec = recInfo := ConstantInfo.recInfo.inj (hinfo.trans hsource)
    subst recInfo
    rw [he]
    exact ⟨H.alignmentOfRealization hm g ha.levels_length ha.levels_wf hrecursors hrules hrec,
      H.kOfRealization hm g hrec, H.majorOfRealization hm hrec⟩

end VerifyInductive
end Lean4Lean
