import Lean4Lean.Verify.Inductive.Nested.Restoration

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- A checked restoration fold preserves every lookup from its source
production environment. -/
theorem FreshConstantTrace.preservesSourceFind
    (H : FreshConstantTrace source entries target)
    (hsourceWF : source.constants.WF)
    (hfind : source.find? name = some found) :
    target.find? name = some found := by
  induction H with
  | nil => exact hfind
  | cons hfresh Htail ih =>
      rename_i cis out env ci
      have hne : ci.name ≠ name := by
        intro heq
        subst name
        rw [hfind] at hfresh
        contradiction
      have hfreshMap : env.constants.find? ci.name = none := by
        rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
          at hfresh
      have hnextWF : (env.add ci).constants.WF :=
        constantsWF_add_checked hsourceWF hfresh
      apply ih hnextWF
      rw [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?] at hfind
      change (env.constants.insert ci.name ci).find?' name = some found
      rw [(hsourceWF.insert ci.name ci hfreshMap).find?'_eq_find?,
        hsourceWF.find?_insert]
      split
      · rename_i heq
        exact False.elim (hne (by simpa using heq))
      · exact hfind

/-- Map-level form of source-lookup preservation, used directly by the
concrete `AddInduct` relation. -/
theorem FreshConstantTrace.preservesSourceMapFind
    (H : FreshConstantTrace source entries target)
    (hsourceWF : source.constants.WF)
    (hfind : source.constants.find? name = some found) :
    target.constants.find? name = some found := by
  have hsource : source.find? name = some found := by
    rw [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
    exact hfind
  have htarget := H.preservesSourceFind hsourceWF hsource
  rw [Lean.Kernel.Environment.find?,
    (H.targetWF hsourceWF).find?'_eq_find?] at htarget
  exact htarget

/-- A restoration fold consisting only of non-definitional constant kinds
cannot introduce a delta-reducible production declaration. -/
theorem FreshConstantTrace.deltaConservative
    (H : FreshConstantTrace source entries target)
    (hsourceWF : source.constants.WF)
    (hnondelta : ∀ ci ∈ entries, ci.deltaValue? = none) :
    ∀ {name found}, target.constants.find? name = some found →
      found.deltaValue?.isSome →
      source.constants.find? name = some found := by
  induction H with
  | nil =>
      intro name found hfind _hdelta
      exact hfind
  | cons hfresh Htail ih =>
      rename_i cis out env ci
      intro name found hfind hdelta
      have hfreshMap : env.constants.find? ci.name = none := by
        rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
          at hfresh
      have hnextWF : (env.add ci).constants.WF :=
        constantsWF_add_checked hsourceWF hfresh
      have hnext : (env.add ci).constants.find? name = some found :=
        ih hnextWF (fun entry hentry =>
          hnondelta entry (by simp [hentry])) hfind hdelta
      change (env.constants.insert ci.name ci).find? name = some found at hnext
      rw [hsourceWF.find?_insert] at hnext
      split at hnext
      · cases hnext
        have hnone := hnondelta ci (by simp)
        simp [hnone] at hdelta
      · exact hnext

/-- The exact constructor-restoration fold installs only constructor
constants, hence every entry in its fresh trace is non-definitional. -/
theorem StateForMTrace.constructorFreshTraceNondelta
    (H : StateForMTrace (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ ci ∈ entries, ci.deltaValue? = none := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
      rename_i _head source _middle _tail _target
      let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
      have hfresh : source.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have htarget := congrArg Prod.snd Hstep.restored.output
      simp only at htarget
      rw [htarget] at Htail ih
      rcases ih (constantsWF_add_checked hsourceWF hfresh) with
        ⟨entries, Hentries, hnondelta⟩
      refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
      intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · rfl
      · exact hnondelta entry hentry

/-- The exact recursor-restoration fold installs only recursor constants. -/
theorem StateForMTrace.recursorFreshTraceNondelta
    (H : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ ci ∈ entries, ci.deltaValue? = none := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
      rename_i _head source _middle _tail _target
      let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
      have hfresh : source.find? ci.name = none :=
        find?_none_of_contains_false hsourceWF Hstep.restored.fresh
      have htarget := congrArg Prod.snd Hstep.restored.output
      simp only at htarget
      rw [htarget] at Htail ih
      rcases ih (constantsWF_add_checked hsourceWF hfresh) with
        ⟨entries, Hentries, hnondelta⟩
      refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
      intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · rfl
      · exact hnondelta entry hentry

/-- One restored source family installs a header, constructor batch, and
primary recursor, all of which are non-definitional constant kinds. -/
theorem RestoredInductiveDeclResult.freshTraceNondelta
    (H : RestoredInductiveDeclResult result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hsourceWF : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ ci ∈ entries, ci.deltaValue? = none := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hsourceWF H.header.fresh
  have hheaderWF := constantsWF_add_checked hsourceWF hheaderFresh
  have Hconstructors : StateForMTrace
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors.constructorFreshTraceNondelta hheaderWF with
    ⟨constructors, HconstructorTrace, hconstructorsNondelta⟩
  have hconstructorWF : H.constructorEnv.constants.WF :=
    HconstructorTrace.targetWF hheaderWF
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecursorFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hconstructorWF H.recursor.restored.fresh
  rw [htarget]
  refine ⟨header :: constructors ++ [recursor],
    .cons hheaderFresh
      (HconstructorTrace.append (.cons hrecursorFresh .nil)), ?_⟩
  intro entry hentry
  rcases List.mem_append.mp hentry with hentry | hentry
  · simp only [List.mem_cons] at hentry
    rcases hentry with rfl | hentry
    · rfl
    · exact hconstructorsNondelta entry hentry
  · have heq : entry = recursor := by simpa using hentry
    subst entry
    rfl

/-- The outer source-family restoration fold preserves the same non-delta
property compositionally. -/
theorem StateForMTrace.inductiveFreshTraceNondelta
    (H : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hsourceWF : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ ci ∈ entries, ci.deltaValue? = none := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
      rcases Hstep.restored.freshTraceNondelta hsourceWF with
        ⟨headEntries, Hhead, hheadNondelta⟩
      rcases ih (Hhead.targetWF hsourceWF) with
        ⟨tailEntries, Htail, htailNondelta⟩
      refine ⟨headEntries ++ tailEntries, Hhead.append Htail, ?_⟩
      intro entry hentry
      rcases List.mem_append.mp hentry with hentry | hentry
      · exact hheadNondelta entry hentry
      · exact htailNondelta entry hentry

/-- Complete nested restoration supplies its own fresh non-delta production
trace; the final concrete `AddInduct` delta clause therefore needs no external
semantic assumption. -/
theorem RestoredNestedDeclarationsResult.freshTraceNondelta
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (hsourceWF : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries out.2 ∧
      ∀ ci ∈ entries, ci.deltaValue? = none := by
  rcases H.inductives.inductiveFreshTraceNondelta hsourceWF with
    ⟨primaryEntries, Hprimary, hprimaryNondelta⟩
  rcases H.auxiliaries.recursorFreshTraceNondelta
      (Hprimary.targetWF hsourceWF) with
    ⟨auxiliaryEntries, Hauxiliary, hauxiliaryNondelta⟩
  refine ⟨primaryEntries ++ auxiliaryEntries,
    Hprimary.append Hauxiliary, ?_⟩
  intro entry hentry
  rcases List.mem_append.mp hentry with hentry | hentry
  · exact hprimaryNondelta entry hentry
  · exact hauxiliaryNondelta entry hentry

end VerifyInductive
end Lean4Lean
