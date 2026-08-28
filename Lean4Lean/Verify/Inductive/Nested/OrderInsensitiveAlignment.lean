import Lean4Lean.Verify.Inductive.Nested.FreshTraceLemmas
import Lean4Lean.Verify.Inductive.Recursor.Installation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Every lookup introduced by a fresh production trace is one of its exact
entries; all other lookups come from the source environment. -/
theorem FreshConstantTrace.entryOrigin
    (H : FreshConstantTrace source entries target)
    (hsourceWF : source.constants.WF)
    (hfind : target.find? name = some found) :
    source.find? name = some found ∨
      ∃ entry ∈ entries, name = entry.name ∧ found = entry := by
  induction H with
  | nil => exact Or.inl hfind
  | cons hfresh Htail ih =>
    rename_i rest out env ci
    have hfreshMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
        at hfresh
    have hnextWF : (env.add ci).constants.WF :=
      constantsWF_add_checked hsourceWF hfresh
    rcases ih hnextWF hfind with hnext | ⟨entry, hentry, hname, hfound⟩
    · change (env.add ci).constants.find?' name = some found at hnext
      rw [hnextWF.find?'_eq_find?] at hnext
      change (env.constants.insert ci.name ci).find? name = some found at hnext
      rw [hsourceWF.find?_insert] at hnext
      split at hnext
      · rename_i heq
        right
        simp only [Option.some.injEq] at hnext
        exact ⟨ci, by simp, (LawfulBEq.eq_of_beq heq).symm, hnext.symm⟩
      · left
        rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
    · exact Or.inr ⟨entry, by simp [hentry], hname, hfound⟩

/-- Every exact entry of a fresh production trace is present in the target
environment with unchanged metadata. -/
theorem FreshConstantTrace.findEntry
    (H : FreshConstantTrace source entries target)
    (hsourceWF : source.constants.WF)
    (hentry : info ∈ entries) :
    target.find? info.name = some info := by
  induction H with
  | nil => simp at hentry
  | cons hfresh Htail ih =>
    rename_i rest out env ci
    simp only [List.mem_cons] at hentry
    have hfreshMap : env.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?]
        at hfresh
    have hnextWF : (env.add ci).constants.WF :=
      constantsWF_add_checked hsourceWF hfresh
    rcases hentry with hhead | htail
    · have hinfo : info = ci := hhead
      subst info
      apply Htail.preservesSourceFind hnextWF
      change (env.constants.insert ci.name ci).find?' ci.name = some ci
      rw [(hsourceWF.insert ci.name ci hfreshMap).find?'_eq_find?,
        hsourceWF.find?_insert]
      simp
    · exact ih hnextWF htail

/-- Fresh insertion order is irrelevant to production lookup semantics.
This is deliberately an extensional statement: the two `SMap`
representations need not be propositionally equal. -/
theorem FreshConstantTrace.lookupEqOfPerm
    (Hleft : FreshConstantTrace source leftEntries leftTarget)
    (Hright : FreshConstantTrace source rightEntries rightTarget)
    (hsourceWF : source.constants.WF)
    (hperm : leftEntries ~ rightEntries) :
    ∀ name, leftTarget.constants.find? name =
      rightTarget.constants.find? name := by
  intro name
  have hleftWF := Hleft.targetWF hsourceWF
  have hrightWF := Hright.targetWF hsourceWF
  have forward : ∀ {found},
      leftTarget.constants.find? name = some found →
      rightTarget.constants.find? name = some found := by
    intro found hfind
    have hfindEnv : leftTarget.find? name = some found := by
      rw [Lean.Kernel.Environment.find?, hleftWF.find?'_eq_find?]
      exact hfind
    rcases Hleft.entryOrigin hsourceWF hfindEnv with hold | hnew
    · have htarget := Hright.preservesSourceFind hsourceWF hold
      rwa [Lean.Kernel.Environment.find?, hrightWF.find?'_eq_find?]
        at htarget
    · rcases hnew with ⟨entry, hentry, hname, hfound⟩
      subst found
      subst name
      have hentry' : entry ∈ rightEntries := hperm.mem_iff.mp hentry
      have htarget := Hright.findEntry hsourceWF hentry'
      rwa [Lean.Kernel.Environment.find?, hrightWF.find?'_eq_find?]
        at htarget
  have backward : ∀ {found},
      rightTarget.constants.find? name = some found →
      leftTarget.constants.find? name = some found := by
    intro found hfind
    have hfindEnv : rightTarget.find? name = some found := by
      rw [Lean.Kernel.Environment.find?, hrightWF.find?'_eq_find?]
      exact hfind
    rcases Hright.entryOrigin hsourceWF hfindEnv with hold | hnew
    · have htarget := Hleft.preservesSourceFind hsourceWF hold
      rwa [Lean.Kernel.Environment.find?, hleftWF.find?'_eq_find?]
        at htarget
    · rcases hnew with ⟨entry, hentry, hname, hfound⟩
      subst found
      subst name
      have hentry' : entry ∈ leftEntries := hperm.mem_iff.mpr hentry
      have htarget := Hleft.findEntry hsourceWF hentry'
      rwa [Lean.Kernel.Environment.find?, hleftWF.find?'_eq_find?]
        at htarget
  cases hleft : leftTarget.constants.find? name with
  | none =>
    cases hright : rightTarget.constants.find? name with
    | none => rfl
    | some found =>
      have := backward hright
      rw [hleft] at this
      contradiction
  | some found =>
    exact (forward hleft).symm

/-- Rebase a checking environment across an exact extensional change of its
production constant-map representation. -/
theorem CheckingEnv.mapExt
    (H : CheckingEnv safety source venv)
    (htargetWF : target.constants.WF)
    (heq : ∀ name, source.constants.find? name =
      target.constants.find? name) :
    CheckingEnv safety target venv where
  aligned := H.aligned.mapExt htargetWF heq
  wf := H.wf
  of_value := by
    intro name ci value hfind hs hvalue
    have hfindTarget : target.constants.find? name = some ci := by
      rw [← htargetWF.find?'_eq_find?, ← Lean.Kernel.Environment.find?]
      exact hfind
    have hfindSource : source.constants.find? name = some ci := by
      rw [heq]
      exact hfindTarget
    have hfindSource' : source.find? name = some ci := by
      rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?]
      exact hfindSource
    exact H.of_value hfindSource' hs hvalue

/-- Rebase the complete executable type-checking invariant across an exact
extensional change of the production constant-map representation.  The
abstract environment is unchanged; primitive metadata and the operational
annotation wrappers are transported through the same lookup equality as the
checking relation. -/
theorem CheckingEnv.Valid.mapExt
    (H : CheckingEnv.Valid safety source venv)
    (htargetWF : target.constants.WF)
    (heq : ∀ name, source.constants.find? name =
      target.constants.find? name) :
    CheckingEnv.Valid safety target venv where
  tr := CheckingEnv.mapExt H.tr htargetWF heq
  hasPrimitives := H.hasPrimitives
  safePrimitives := by
    intro name ci hfind hprimitive
    have hfindTarget : target.constants.find? name = some ci := by
      rw [← htargetWF.find?'_eq_find?,
        ← Lean.Kernel.Environment.find?]
      exact hfind
    have hfindSource : source.constants.find? name = some ci := by
      rw [heq]
      exact hfindTarget
    apply H.safePrimitives _ hprimitive
    rw [Lean.Kernel.Environment.find?, H.tr.map_wf.find?'_eq_find?]
    exact hfindSource
  typeAnnotationWrappers := H.typeAnnotationWrappers.rebase (by
    intro name ci hfind
    have hfindSource : source.constants.find? name = some ci := by
      rw [← H.tr.map_wf.find?'_eq_find?,
        ← Lean.Kernel.Environment.find?]
      exact hfind
    have hfindTarget : target.constants.find? name = some ci := by
      rw [← heq]
      exact hfindSource
    rw [Lean.Kernel.Environment.find?, htargetWF.find?'_eq_find?]
    exact hfindTarget)

/-- Forget the semantic part of a canonical lockstep installation while
retaining its exact production freshness trace. -/
theorem AddConstants.freshTrace
    (H : AddConstants safety source sourceVEnv entries target targetVEnv) :
    FreshConstantTrace source (entries.map Prod.fst) target := by
  induction H with
  | nil => exact .nil
  | cons hfresh _ _ _ _ _ _ ih => exact .cons hfresh ih

/-- A lockstep semantic installation preserves the local checking invariant.
Unlike `AddConstants.valid`, this needs no primitive-metadata side
conditions. -/
theorem AddConstants.checking
    (H : AddConstants safety source sourceVEnv entries target targetVEnv)
    (Hsource : CheckingEnv safety source sourceVEnv) :
    CheckingEnv safety target targetVEnv := by
  induction H with
  | nil => exact Hsource
  | cons hfresh _ htr hwf hadd hdelta _ ih =>
    exact ih (Hsource.add hfresh htr.1 hwf hadd hdelta)

/-- A canonical dependency-ordered semantic installation can justify the
actual family-interleaved production environment whenever their exact
production entries are permutations.  Typing is used only in the canonical
trace; the actual trace contributes freshness, order, and the target map. -/
theorem AddConstants.checkingOfFreshPermutation
    (Hcanonical : AddConstants safety source sourceVEnv canonicalEntries
      canonicalTarget targetVEnv)
    (Hactual : FreshConstantTrace source actualEntries actualTarget)
    (hperm : actualEntries ~ canonicalEntries.map Prod.fst)
    (Hsource : CheckingEnv safety source sourceVEnv) :
    CheckingEnv safety actualTarget targetVEnv := by
  have HcanonicalChecking : CheckingEnv safety canonicalTarget targetVEnv :=
    Hcanonical.checking Hsource
  have heq := Hactual.lookupEqOfPerm Hcanonical.freshTrace
    Hsource.map_wf hperm
  exact CheckingEnv.mapExt HcanonicalChecking
    (Hactual.targetWF Hsource.map_wf) fun name => (heq name).symm

/-- Full-validity form of `checkingOfFreshPermutation`.  This is the
dependency-order bridge used by nested restoration: constants are typed in
canonical header/constructor/recursor order, while the executable restoration
installs the same finite batch in family-interleaved order. -/
theorem AddConstants.validOfFreshPermutation
    (Hcanonical : AddConstants safety source sourceVEnv canonicalEntries
      canonicalTarget targetVEnv)
    (Hactual : FreshConstantTrace source actualEntries actualTarget)
    (hperm : actualEntries ~ canonicalEntries.map Prod.fst)
    (Hsource : CheckingEnv.Valid safety source sourceVEnv) :
    CheckingEnv.Valid safety actualTarget targetVEnv := by
  have HcanonicalValid :
      CheckingEnv.Valid safety canonicalTarget targetVEnv :=
    Hcanonical.valid Hsource
  have heq := Hactual.lookupEqOfPerm Hcanonical.freshTrace
    Hsource.tr.map_wf hperm
  exact CheckingEnv.Valid.mapExt HcanonicalValid
    (Hactual.targetWF Hsource.tr.map_wf) fun name => (heq name).symm

end VerifyInductive
end Lean4Lean
