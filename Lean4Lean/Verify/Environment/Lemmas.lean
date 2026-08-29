import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

private theorem find?_add_of_ne
    {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hne : ci.name ≠ name) :
    (env.add ci).find? name = env.find? name := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change SMap.find?' (env.constants.insert ci.name ci) name = env.find? name
  rw [(hwf.insert ci.name ci hfresh).find?'_eq_find?,
    hwf.find?_insert, if_neg (by simpa using hne)]
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]

private theorem find?_add_cases
    {env : Environment} (hwf : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hfind : (env.add ci).find? name = some found) :
    (name = ci.name ∧ found = ci) ∨ env.find? name = some found := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hfresh
  change SMap.find?' (env.constants.insert ci.name ci) name = some found at hfind
  rw [(hwf.insert ci.name ci hfresh).find?'_eq_find?,
    hwf.find?_insert] at hfind
  split at hfind
  · left
    exact ⟨(LawfulBEq.eq_of_beq (by assumption)).symm,
      (Option.some.inj hfind).symm⟩
  · right
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
    exact hfind

theorem TypeAnnotationWrappers.addConstant
    (H : TypeAnnotationWrappers env)
    (hwf : env.constants.WF) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none) :
    TypeAnnotationWrappers (env.add ci) := by
  apply H.rebase
  intro name old hlookup
  have hne : ci.name ≠ name := by
    intro heq
    subst name
    rw [hlookup] at hfresh
    contradiction
  rw [find?_add_of_ne hwf ci hfresh hne]
  exact hlookup

theorem TypeAnnotationWrappers.addDefinitions
    (H : TypeAnnotationWrappers env) (hwf : env.constants.WF) :
    ∀ (vs : List DefinitionVal),
      (∀ v ∈ vs, env.find? v.name = none) →
      (vs.map (·.name)).Nodup →
      TypeAnnotationWrappers
        (vs.foldl (fun env v => env.add (.defnInfo v)) env)
  | [], _, _ => H
  | v :: vs, hfresh, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hvfresh := hfresh v (by simp)
      have hvfreshMap : env.constants.find? v.name = none := by
        rwa [← hwf.find?'_eq_find?]
      have hwf' : (env.add (.defnInfo v)).constants.WF := by
        change (env.constants.insert v.name (.defnInfo v)).WF
        exact hwf.insert v.name (.defnInfo v) hvfreshMap
      apply TypeAnnotationWrappers.addDefinitions
        (TypeAnnotationWrappers.addConstant H hwf (.defnInfo v) hvfresh)
        hwf' vs
      · intro w hw
        have hne : v.name ≠ w.name := by
          intro heq
          exact hnodup.1 (List.mem_map.mpr ⟨w, hw, heq.symm⟩)
        rw [find?_add_of_ne hwf (.defnInfo v) hvfresh hne]
        exact hfresh w (by simp [hw])
      · exact hnodup.2

/-- Adding a fresh non-constructor constant preserves constructor-owner
presence. -/
theorem ConstructorOwnersPresent.addNonConstructor
    {ci : ConstantInfo}
    (H : ConstructorOwnersPresent env)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnctor : ∀ info, ci ≠ .ctorInfo info) :
    ConstructorOwnersPresent (env.add ci) := by
  intro name info hfind
  rcases find?_add_cases hwf ci hfresh hfind with
    ⟨_, hnew⟩ | hold
  · exact False.elim (hnctor info hnew.symm)
  · rcases H name info hold with ⟨owner, howner⟩
    have hne : ci.name ≠ info.induct := by
      intro heq
      rw [← heq, hfresh] at howner
      contradiction
    exact ⟨owner, (find?_add_of_ne hwf ci hfresh hne).trans howner⟩

/-- Adding a fresh constructor whose owner is already present preserves
constructor-owner presence. -/
theorem ConstructorOwnersPresent.addConstructor
    (H : ConstructorOwnersPresent env)
    (hwf : env.constants.WF) (info : ConstructorVal)
    (hfresh : env.find? info.name = none)
    (howner : env.find? info.induct = some (.inductInfo owner)) :
    ConstructorOwnersPresent (env.add (.ctorInfo info)) := by
  intro name found hfind
  rcases find?_add_cases hwf (.ctorInfo info) hfresh hfind with
    ⟨_, hnew⟩ | hold
  · have hfound : found = info :=
      ConstantInfo.ctorInfo.inj hnew
    subst found
    have hne : info.name ≠ info.induct := by
      intro heq
      rw [← heq, hfresh] at howner
      contradiction
    exact ⟨owner,
      (find?_add_of_ne hwf (.ctorInfo info) hfresh hne).trans howner⟩
  · rcases H name found hold with ⟨oldOwner, holdOwner⟩
    have hne : info.name ≠ found.induct := by
      intro heq
      rw [← heq, hfresh] at holdOwner
      contradiction
    exact ⟨oldOwner,
      (find?_add_of_ne hwf (.ctorInfo info) hfresh hne).trans holdOwner⟩

/-- A fresh mutual-definition fold contains no constructor metadata and
hence preserves constructor-owner presence. -/
theorem ConstructorOwnersPresent.addDefinitions
    (H : ConstructorOwnersPresent env) (hwf : env.constants.WF) :
    ∀ (vs : List DefinitionVal),
      (∀ v ∈ vs, env.find? v.name = none) →
      (vs.map (·.name)).Nodup →
      ConstructorOwnersPresent
        (vs.foldl (fun env v => env.add (.defnInfo v)) env)
  | [], _, _ => H
  | v :: vs, hfresh, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hvfresh := hfresh v (by simp)
      have hvfreshMap : env.constants.find? v.name = none := by
        rwa [← hwf.find?'_eq_find?]
      have hwf' : (env.add (.defnInfo v)).constants.WF := by
        change (env.constants.insert v.name (.defnInfo v)).WF
        exact hwf.insert v.name (.defnInfo v) hvfreshMap
      have H' : ConstructorOwnersPresent (env.add (.defnInfo v)) :=
        H.addNonConstructor hwf hvfresh (by intro _ h; cases h)
      apply H'.addDefinitions hwf' vs
      · intro w hw
        have hne : v.name ≠ w.name := by
          intro heq
          exact hnodup.1 (List.mem_map.mpr ⟨w, hw, heq.symm⟩)
        rw [find?_add_of_ne hwf (.defnInfo v) hvfresh hne]
        exact hfresh w (by simp [hw])
      · exact hnodup.2

theorem InductiveMemberInfos.addConstant
    {ci : ConstantInfo}
    (H : InductiveMemberInfos env names)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    InductiveMemberInfos (env.add ci) names := by
  induction H with
  | nil => exact .nil
  | @cons name value names hlookup Htail ih =>
    have hne : ci.name ≠ name := by
      intro heq
      subst name
      rw [hlookup] at hfresh
      contradiction
    exact .cons ((find?_add_of_ne hwf ci hfresh hne).trans hlookup) ih

theorem MutualInductiveClosure.addConstant
    {ci : ConstantInfo}
    (H : MutualInductiveClosure env targetName value)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    MutualInductiveClosure (env.add ci) targetName value := by
  refine ⟨H.members.addConstant hwf hfresh, H.target, H.names, ?_⟩
  intro member info hmember hfind
  rcases H.members.find hmember with ⟨oldInfo, hold⟩
  have hne : ci.name ≠ member := by
    intro heq
    subst member
    rw [hold] at hfresh
    contradiction
  have hfind' := hfind
  rw [find?_add_of_ne hwf ci hfresh hne] at hfind'
  have hinfo : info = oldInfo := by
    rw [hold] at hfind'
    exact ConstantInfo.inductInfo.inj (Option.some.inj hfind'.symm)
  subst info
  exact H.parameters member oldInfo hmember hold

/-- A fresh non-inductive production constant preserves complete mutual-block
metadata. -/
theorem MutualInductivesClosed.addNonInductive
    {ci : ConstantInfo}
    (H : MutualInductivesClosed env)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnind : ∀ value, ci ≠ .inductInfo value) :
    MutualInductivesClosed (env.add ci) := by
  intro targetName value hfind
  rcases find?_add_cases hwf ci hfresh hfind with
    ⟨_, hvalue⟩ | hold
  · exact False.elim (hnind value hvalue.symm)
  · exact (H targetName value hold).addConstant hwf hfresh

/-- A fresh mutual-definition fold contains no inductive metadata and hence
preserves mutual-family closure. -/
theorem MutualInductivesClosed.addDefinitions
    (H : MutualInductivesClosed env) (hwf : env.constants.WF) :
    ∀ (vs : List DefinitionVal),
      (∀ v ∈ vs, env.find? v.name = none) →
      (vs.map (·.name)).Nodup →
      MutualInductivesClosed
        (vs.foldl (fun env v => env.add (.defnInfo v)) env)
  | [], _, _ => H
  | v :: vs, hfresh, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hvfresh := hfresh v (by simp)
      have hvfreshMap : env.constants.find? v.name = none := by
        rwa [← hwf.find?'_eq_find?]
      have hwf' : (env.add (.defnInfo v)).constants.WF := by
        change (env.constants.insert v.name (.defnInfo v)).WF
        exact hwf.insert v.name (.defnInfo v) hvfreshMap
      have H' : MutualInductivesClosed (env.add (.defnInfo v)) :=
        H.addNonInductive hwf hvfresh (by intro _ h; cases h)
      apply H'.addDefinitions hwf' vs
      · intro w hw
        have hne : v.name ≠ w.name := by
          intro heq
          exact hnodup.1 (List.mem_map.mpr ⟨w, hw, heq.symm⟩)
        rw [find?_add_of_ne hwf (.defnInfo v) hvfresh hne]
        exact hfresh w (by simp [hw])
      · exact hnodup.2

theorem InductiveConstructorsCoherent.constructorAt
    (H : InductiveConstructorsCoherent env)
    (hfamily : env.find? familyName = some (.inductInfo familyInfo))
    (hi : i < familyInfo.ctors.length) :
    Nonempty (InductiveConstructorCoherenceAt env familyName familyInfo i hi) :=
  H familyName familyInfo hfamily i hi

theorem InductiveConstructorsCoherent.constructorLookup
    (H : InductiveConstructorsCoherent env)
    (hfamily : env.find? familyName = some (.inductInfo familyInfo))
    (hi : i < familyInfo.ctors.length) :
    ∃ info : ConstructorVal,
      env.find? familyInfo.ctors[i] = some (.ctorInfo info) ∧
      info.induct = familyName ∧
      info.cidx = i ∧
      info.numParams = familyInfo.numParams ∧
      info.levelParams = familyInfo.levelParams ∧
      info.isUnsafe = familyInfo.isUnsafe := by
  rcases H.constructorAt hfamily hi with ⟨C⟩
  exact ⟨C.info, C.lookup, C.induct, C.cidx, C.numParams,
    C.levelParams, C.isUnsafe⟩

def InductiveConstructorCoherenceAt.addConstant
    {ci : ConstantInfo}
    (H : InductiveConstructorCoherenceAt env familyName familyInfo i hi)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    InductiveConstructorCoherenceAt (env.add ci) familyName familyInfo i hi := by
  have hne : ci.name ≠ familyInfo.ctors[i] := by
    intro heq
    rw [heq, H.lookup] at hfresh
    contradiction
  exact { H with lookup :=
    (find?_add_of_ne hwf ci hfresh hne).trans H.lookup }

/-- Adding a fresh constant which is not an inductive header preserves all
previous constructor/header coherence. -/
theorem InductiveConstructorsCoherent.addNonInductive
    {ci : ConstantInfo}
    (H : InductiveConstructorsCoherent env)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnind : ∀ value, ci ≠ .inductInfo value) :
    InductiveConstructorsCoherent (env.add ci) := by
  intro familyName familyInfo hfamily i hi
  rcases find?_add_cases hwf ci hfresh hfamily with
    ⟨_, hvalue⟩ | hold
  · exact False.elim (hnind familyInfo hvalue.symm)
  · rcases H.constructorAt hold hi with ⟨C⟩
    exact ⟨C.addConstant hwf hfresh⟩

/-- A fresh mutual-definition fold contains no inductive headers and hence
preserves constructor/header coherence. -/
theorem InductiveConstructorsCoherent.addDefinitions
    (H : InductiveConstructorsCoherent env) (hwf : env.constants.WF) :
    ∀ (vs : List DefinitionVal),
      (∀ v ∈ vs, env.find? v.name = none) →
      (vs.map (·.name)).Nodup →
      InductiveConstructorsCoherent
        (vs.foldl (fun env v => env.add (.defnInfo v)) env)
  | [], _, _ => H
  | v :: vs, hfresh, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hvfresh := hfresh v (by simp)
      have hvfreshMap : env.constants.find? v.name = none := by
        rwa [← hwf.find?'_eq_find?]
      have hwf' : (env.add (.defnInfo v)).constants.WF := by
        change (env.constants.insert v.name (.defnInfo v)).WF
        exact hwf.insert v.name (.defnInfo v) hvfreshMap
      have H' : InductiveConstructorsCoherent
          (env.add (.defnInfo v)) :=
        H.addNonInductive hwf hvfresh (by intro _ h; cases h)
      apply H'.addDefinitions hwf' vs
      · intro w hw
        have hne : v.name ≠ w.name := by
          intro heq
          exact hnodup.1 (List.mem_map.mpr ⟨w, hw, heq.symm⟩)
        rw [find?_add_of_ne hwf (.defnInfo v) hvfresh hne]
        exact hfresh w (by simp [hw])
      · exact hnodup.2

def InductiveConstructorSemanticCoherenceAt.mono
    (H : InductiveConstructorSemanticCoherenceAt
      env venv familyName familyInfo i hi)
    (hle : venv ≤ venv') :
    InductiveConstructorSemanticCoherenceAt
      env venv' familyName familyInfo i hi :=
  { H with
    familyLookup := hle.constants H.familyLookup
    constructorLookup := hle.constants H.constructorLookup
    familyDefEq := H.familyDefEq.mono hle
    constructorDefEq := H.constructorDefEq.mono hle
    parameterDomains := H.parameterDomains.mono hle }

def InductiveConstructorSemanticCoherenceAt.addConstant
    {ci : ConstantInfo}
    (H : InductiveConstructorSemanticCoherenceAt
      env venv familyName familyInfo i hi)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hle : venv ≤ venv') :
    InductiveConstructorSemanticCoherenceAt
      (env.add ci) venv' familyName familyInfo i hi :=
  { H.mono hle with
    toInductiveConstructorCoherenceAt :=
      H.toInductiveConstructorCoherenceAt.addConstant hwf hfresh }

/-- Transport one semantic constructor witness across an arbitrary
production-environment extension once the exact constructor lookup has been
shown to survive.  All semantic fields only require monotonicity of the
abstract environment. -/
def InductiveConstructorSemanticCoherenceAt.rebaseProduction
    (H : InductiveConstructorSemanticCoherenceAt
      env venv familyName familyInfo i hi)
    (hlookup : env'.find? familyInfo.ctors[i] = some (.ctorInfo H.info))
    (hle : venv ≤ venv') :
    InductiveConstructorSemanticCoherenceAt
      env' venv' familyName familyInfo i hi :=
  { H.mono hle with
    toInductiveConstructorCoherenceAt :=
      { H.toInductiveConstructorCoherenceAt with lookup := hlookup } }

theorem InductiveConstructorsSemanticallyCoherent.mono
    (H : InductiveConstructorsSemanticallyCoherent safety env venv)
    (hle : venv ≤ venv') :
    InductiveConstructorsSemanticallyCoherent safety env venv' := by
  intro familyName familyInfo hfamily hvisible i hi
  rcases H familyName familyInfo hfamily hvisible i hi with ⟨C⟩
  exact ⟨C.mono hle⟩

/-- A fresh non-inductive production constant and any monotone abstract
extension preserve visible constructor semantics. -/
theorem InductiveConstructorsSemanticallyCoherent.addNonInductive
    {ci : ConstantInfo}
    (H : InductiveConstructorsSemanticallyCoherent safety env venv)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnind : ∀ value, ci ≠ .inductInfo value)
    (hle : venv ≤ venv') :
    InductiveConstructorsSemanticallyCoherent safety (env.add ci) venv' := by
  intro familyName familyInfo hfamily hvisible i hi
  rcases find?_add_cases hwf ci hfresh hfamily with
    ⟨_, hvalue⟩ | hold
  · exact False.elim (hnind familyInfo hvalue.symm)
  · rcases H familyName familyInfo hold hvisible i hi with ⟨C⟩
    exact ⟨C.addConstant hwf hfresh hle⟩

/-- A fresh mutual-definition fold changes no inductive metadata.  All old
semantic witnesses may be transported directly to the final abstract model,
then retained while the remaining production definitions are inserted. -/
theorem InductiveConstructorsSemanticallyCoherent.addDefinitions
    (H : InductiveConstructorsSemanticallyCoherent safety env venv)
    (hwf : env.constants.WF) :
    ∀ (vs : List DefinitionVal),
      (∀ v ∈ vs, env.find? v.name = none) →
      (vs.map (·.name)).Nodup →
      venv ≤ venv' →
      InductiveConstructorsSemanticallyCoherent safety
        (vs.foldl (fun env v => env.add (.defnInfo v)) env) venv'
  | [], _, _, hle => H.mono hle
  | v :: vs, hfresh, hnodup, hle => by
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hvfresh := hfresh v (by simp)
      have hvfreshMap : env.constants.find? v.name = none := by
        rwa [← hwf.find?'_eq_find?]
      have hwf' : (env.add (.defnInfo v)).constants.WF := by
        change (env.constants.insert v.name (.defnInfo v)).WF
        exact hwf.insert v.name (.defnInfo v) hvfreshMap
      have H' : InductiveConstructorsSemanticallyCoherent safety
          (env.add (.defnInfo v)) venv' :=
        H.addNonInductive hwf hvfresh (by intro _ h; cases h) hle
      apply H'.addDefinitions hwf' vs
      · intro w hw
        have hne : v.name ≠ w.name := by
          intro heq
          exact hnodup.1 (List.mem_map.mpr ⟨w, hw, heq.symm⟩)
        rw [find?_add_of_ne hwf (.defnInfo v) hvfresh hne]
        exact hfresh w (by simp [hw])
      · exact hnodup.2
      · exact VEnv.LE.rfl

/-- An entry hidden from the current safety observer cannot introduce a
visible inductive family, even if another observer installed it. -/
theorem InstalledInductiveProvenance.insertInvisible
    (H : InstalledInductiveProvenance safety C env)
    (hwf : C.WF) (hfresh : C.find? ci.name = none)
    (hhidden : ¬ safety ≤ ci.safety) :
    InstalledInductiveProvenance safety (C.insert ci.name ci) env := by
  have hpreserves : ∀ {name found}, C.find? name = some found →
      (C.insert ci.name ci).find? name = some found := by
    intro name found hfind
    rw [hwf.find?_insert]
    split
    · rename_i heq
      have hname : ci.name = name := LawfulBEq.eq_of_beq heq
      subst name
      rw [hfind] at hfresh
      contradiction
    · exact hfind
  intro familyName familyInfo hfind hvisible
  have hold : C.find? familyName = some (.inductInfo familyInfo) := by
    rw [hwf.find?_insert] at hfind
    split at hfind
    · have heq : ci = .inductInfo familyInfo := Option.some.inj hfind
      exact False.elim (hhidden (by simpa [heq] using hvisible))
    · exact hfind
  rcases H familyName familyInfo hold hvisible with ⟨P⟩
  exact ⟨P.mono (by simpa [P.name] using hfind) hpreserves VEnv.LE.rfl⟩

/-- Rebase an observer across a production extension whose genuinely new
inductive headers are all hidden at that observer's safety. -/
theorem InstalledInductiveProvenance.rebaseHidden
    (H : InstalledInductiveProvenance safety source env)
    (hpreserves : ∀ {name found}, source.find? name = some found →
      target.find? name = some found)
    (hhidden : ∀ familyName familyInfo,
      target.find? familyName = some (.inductInfo familyInfo) →
      source.find? familyName = none →
      ¬ safety ≤ (ConstantInfo.inductInfo familyInfo).safety) :
    InstalledInductiveProvenance safety target env := by
  intro familyName familyInfo hfind hvisible
  cases hold : source.find? familyName with
  | none => exact False.elim (hhidden familyName familyInfo hfind hold hvisible)
  | some oldInfo =>
      have hsame := hpreserves hold
      rw [hfind] at hsame
      have heq : oldInfo = .inductInfo familyInfo := Option.some.inj hsame.symm
      subst oldInfo
      rcases H familyName familyInfo hold hvisible with ⟨P⟩
      exact ⟨P.mono (by simpa [P.name] using hfind) hpreserves VEnv.LE.rfl⟩

/-- A fresh mutual-definition fold contains no inductive headers and hence
preserves installed declaration provenance. -/
theorem InstalledInductiveProvenance.insertDefs
    (H : InstalledInductiveProvenance safety C env)
    (hwf : C.WF) : ∀ (cis : List DefinitionVal),
      (∀ ci ∈ cis, C.find? ci.name = none) →
      (cis.map (·.name)).Nodup → env ≤ env' →
      InstalledInductiveProvenance safety (insertDefs C cis) env'
  | [], _, _, henv => InstalledInductiveProvenance.monoEnv H henv
  | ci :: cis, hfresh, hnodup, henv => by
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hciFresh := hfresh ci (by simp)
      have hwf' := hwf.insert ci.name (.defnInfo ci) hciFresh
      have H' : InstalledInductiveProvenance safety
          (C.insert ci.name (.defnInfo ci)) env' :=
        InstalledInductiveProvenance.insertNonInductive
          (ci := .defnInfo ci) H hwf hciFresh
          (by intro _ h; cases h) henv
      apply InstalledInductiveProvenance.insertDefs H' hwf' cis
      · intro cj hcj
        rw [hwf.find?_insert]
        have hne : ci.name ≠ cj.name := by
          intro heq
          exact hnodup.1 (List.mem_map.mpr ⟨cj, hcj, heq.symm⟩)
        rw [if_neg (by simpa using hne)]
        exact hfresh cj (by simp [hcj])
      · exact hnodup.2
      · exact VEnv.LE.rfl

end VerifyInductive

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih => exact ih
  | mapExt _ htarget _ _ => exact htarget

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih
  | mapExt _ _ heq ih =>
    rw [← heq]
    exact ih

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

theorem Aligned.addInduct (H : AddInduct safety C₁ venv₁ decl C₂ venv₂) :
    Aligned safety C₁ venv₁ → Aligned safety C₂ venv₂ := by
  cases H with
  | intro _ _ _ _ _ _ _ haligned _ => exact haligned

theorem Aligned.addDefEqs {C : ConstMap} : ∀ {cis' : List VDefVal} {venv},
    Aligned safety C venv → Aligned safety C (venv.addDefEqs cis')
  | [], _, H => H
  | ci :: cis, venv, H => by
    show Aligned safety C (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis)
    exact Aligned.addDefEqs H.defeq

theorem Aligned.insertDefs : ∀ {cis : List DefinitionVal} {cis' : List VDefVal} {C venv venv'},
    Aligned safety C venv → (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    List.Forall₂ (fun ci ci' => TrConstVal safety venv (.defnInfo ci) ci'.toVConstVal) cis cis' →
    venv.addConsts cis' = some venv' → Aligned safety (insertDefs C cis) venv'
  | [], _, _, _, _, H, _, _, hblk, e => by
    cases hblk; simp [VEnv.addConsts] at e; cases e; exact H
  | ci :: cis, _, C, venv, _, H, hnd, hfr, hblk, e => by
    cases hblk with | @cons _ ci' _ _ htr hblk => ?_
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h1, h2⟩ := e
    have hname := htr.2
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1' : venv.addConst ci.name ci'.toVConstant = some venv₁ := by rw [hname]; exact h1
    show Aligned safety
      (_root_.Lean4Lean.insertDefs (SMap.insert C ci.name (.defnInfo ci)) cis) _
    refine Aligned.insertDefs (H.const (hfr _ (.head _)) htr.1 h1' rfl) hnd.2
      (fun c hc => ?_) (Lean4Lean.List.Forall₂.imp
        (fun _ _ h => h.mono (VEnv.addConst_le h1')) hblk) h2
    rw [H.map_wf.find?_insert]
    have : ¬ (ci.name == c.name) = true := by
      simp only [beq_iff_eq]; intro h
      exact hnd.1 ⟨c, hc, h.symm⟩
    simp [this]
    exact hfr c (.tail _ hc)

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | ignore h1 h2 _ ih => exact ih.ignoreConst h1 h2 rfl
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | thm h1 h2 _ _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | mutualDef hblk hnd hfr _ hadd _ _ ih =>
    exact Aligned.addDefEqs <| ih.insertDefs hnd hfr
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) hblk) hadd
  | quot _ h _ ih => exact ih.addQuot h
  | induct _ h _ ih => exact ih.addInduct h

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩
  | mapExt _ _ heq ih =>
    rw [← heq] at h
    exact ih h

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩
  | mapExt _ _ heq ih =>
    rw [← heq] at h
    exact ih h hs

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem VEnv.addDefEqs_le : ∀ {cis' : List VDefVal} {venv : VEnv}, venv ≤ venv.addDefEqs cis'
  | [], _ => .rfl
  | ci :: cis, venv => by
    show venv ≤ VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis
    exact VEnv.addDefEq_le.trans VEnv.addDefEqs_le

theorem VEnv.addDefEqs_self : ∀ {cis' : List VDefVal} {venv : VEnv} {ci'}, ci' ∈ cis' →
    (venv.addDefEqs cis').defeqs ci'.toDefEq
  | ci :: cis, venv, _, hc => by
    show (VEnv.addDefEqs (venv.addDefEq ci.toDefEq) cis).defeqs _
    cases hc with
    | head => exact VEnv.addDefEqs_le.defeqs VEnv.addDefEq_self
    | tail _ hc => exact VEnv.addDefEqs_self hc

theorem insertDefs_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    (insertDefs C cis).find? name = some ci →
    C.find? name = some ci ∨ ∃ d ∈ cis, d.name = name ∧ ConstantInfo.defnInfo d = ci
  | [], _, _, _, _, _, _, h => .inl h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    have h : (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci := h
    rcases insertDefs_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h with h | ⟨e, he, h1, h2⟩
    · rw [hC.find?_insert] at h; split at h
      · rename_i hb; cases h
        exact .inr ⟨d, .head _, by simpa using hb, rfl⟩
      · exact .inl h
    · exact .inr ⟨e, .tail _ he, h1, h2⟩

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | ignore h1 h2 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact ih h
    · exact (h2 hs).elim
  | «axiom» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | mutualDef hblk hnd hfr _ hadd _ H ih =>
    have' le := (VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le
    rcases insertDefs_find? H.map_wf hfr hnd h with h | ⟨d, hd, rfl, rfl⟩
    · exact (ih h).mono le
    · obtain ⟨d', hd', htr, hval⟩ := Lean4Lean.List.Forall₂.forall_exists_l hblk _ hd
      cases hv
      have hdefeq := VEnv.IsDefEq.extra0 (VEnv.addDefEqs_self hd')
        ((H.mutualDef hblk hnd hfr ‹_› hadd ‹_›).wf.ordered.defEqWF (VEnv.addDefEqs_self hd'))
      let ⟨⟨b1, b2, b3⟩, b4⟩ := htr
      exact ⟨_, hval.mono VEnv.addDefEqs_le, b2.symm ▸ b4.symm ▸ ⟨_, hdefeq.symm⟩⟩
  | thm h2 h3 h4 h5 h1 H ih =>
    have' le := VEnv.addConst_le h1
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      dsimp only [ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal] at b2 b4 ⊢
      have hp := h5.mono le
      have hb := h4.mono le
      have hc := VEnv.HasType.const0 (VEnv.addConst_self h1) ⟨_, hp⟩
      rw [b4] at hc
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ?_⟩
      exact ⟨_, .proofIrrel hp hb hc⟩
  | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | induct _ h1 H ih =>
    cases h1 with
    | intro block _ _ _ hinstall _ _ _ hdelta =>
      exact (ih (hdelta h (by simp [hv]))).mono
        (VInductBlock.install_le hinstall)

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.deltaValue? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv

/-- The fragment of `TrEnv` needed by the executable type checker. Unlike
`TrEnv`, this invariant does not assert that the current production environment
was assembled from complete declarations, so it can also describe the staged
header/constructor environments used while checking an inductive block. -/
structure CheckingEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop where
  aligned : Aligned safety env.constants venv
  wf : venv.WF
  of_value : env.find? name = some ci → safety ≤ ci.safety → ci.deltaValue? = some v →
    TrExpr venv ci.levelParams [] v
      (.const ci.name (VLevel.params ci.levelParams.length))

theorem TrEnv.toChecking (H : TrEnv safety env venv) : CheckingEnv safety env venv where
  aligned := H.aligned
  wf := H.wf
  of_value := H.of_value

theorem CheckingEnv.map_wf (H : CheckingEnv safety env venv) : env.constants.WF :=
  H.aligned.map_wf

theorem CheckingEnv.find?_iff (H : CheckingEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔
      ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

theorem CheckingEnv.find? (H : CheckingEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem CheckingEnv.find?_uniq (H : CheckingEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

open private Lean.Kernel.Environment.add from Lean.Environment

/-- Extend a checking environment by a typed, non-delta constant. This is the
operation used for temporary inductive headers, constructors, and recursors. -/
theorem CheckingEnv.add (H : CheckingEnv safety env venv)
    (hn : env.find? ci.name = none)
    (htr : TrConstant safety venv ci ci')
    (hci : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv')
    (hdelta : ci.deltaValue? = none) :
    CheckingEnv safety (env.add ci) venv' := by
  have hn' : env.constants.find? ci.name = none := by
    rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?] at hn
    exact hn
  refine {
    aligned := H.aligned.const hn' htr hadd rfl
    wf := ?_
    of_value := ?_ }
  · obtain ⟨ds, hds⟩ := H.wf
    let vi : VConstVal := { ci' with name := ci.name }
    exact ⟨_, hds.decl (.axiom (ci := vi) hci hadd)⟩
  · intro name ci₀ value hfind hs hvalue
    change (env.constants.insert ci.name ci).find?' name = some ci₀ at hfind
    rw [(H.map_wf.insert _ _ hn').find?'_eq_find?, H.map_wf.find?_insert] at hfind
    split at hfind
    · cases hfind
      rw [hdelta] at hvalue
      contradiction
    · have hold : env.find? name = some ci₀ := by
        rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?]
        exact hfind
      exact (H.of_value hold hs hvalue).mono (VEnv.addConst_le hadd)

/-- Adding a nonprimitive constant cannot change the metadata of any primitive
looked up by the executable type checker. -/
theorem CheckingEnv.safePrimitives_add (H : CheckingEnv safety env venv)
    (hn : env.find? ci.name = none)
    (hnprim : ¬ Kernel.Environment.primitives.contains ci.name)
    (hsafe : ∀ {n ci}, env.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []) :
    ∀ {n ci₀}, (env.add ci).find? n = some ci₀ →
      Kernel.Environment.primitives.contains n →
      ci₀.safety = .safe ∧ ci₀.levelParams = [] := by
  have hn' : env.constants.find? ci.name = none := by
    rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?] at hn
    exact hn
  intro n ci₀ hfind hprim
  change (env.constants.insert ci.name ci).find?' n = some ci₀ at hfind
  rw [(H.map_wf.insert _ _ hn').find?'_eq_find?, H.map_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    have hname : ci.name = n := by simpa using heq
    subst n
    exact False.elim (hnprim hprim)
  · apply hsafe (n := n) (ci := ci₀) _ hprim
    rw [Lean.Kernel.Environment.find?, H.map_wf.find?'_eq_find?]
    exact hfind

/-- All global invariants needed to run the verified executable type checker
against an environment assembled in stages. -/
structure CheckingEnv.Valid (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv) : Prop where
  tr : CheckingEnv safety env venv
  hasPrimitives : venv.HasPrimitives
  safePrimitives : ∀ {n ci}, env.find? n = some ci →
    Kernel.Environment.primitives.contains n →
    ci.safety = .safe ∧ ci.levelParams = []
  typeAnnotationWrappers : TypeAnnotationWrappers env

theorem TrEnv.toCheckingValid (H : TrEnv safety env venv)
    (hprims : venv.HasPrimitives)
    (hsafe : ∀ {n ci}, env.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hannotations : TypeAnnotationWrappers env) :
    CheckingEnv.Valid safety env venv :=
  ⟨H.toChecking, hprims, hsafe, hannotations⟩

theorem CheckingEnv.Valid.add (H : CheckingEnv.Valid safety env venv)
    (hn : env.find? ci.name = none)
    (hnprim : ¬ Kernel.Environment.primitives.contains ci.name)
    (htr : TrConstant safety venv ci ci')
    (hci : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv')
    (hdelta : ci.deltaValue? = none) :
    CheckingEnv.Valid safety (env.add ci) venv' where
  tr := H.tr.add hn htr hci hadd hdelta
  hasPrimitives := H.hasPrimitives.addConst_of_not_primitive hadd hnprim
  safePrimitives := H.tr.safePrimitives_add hn hnprim H.safePrimitives
  typeAnnotationWrappers := VerifyInductive.TypeAnnotationWrappers.addConstant
    H.typeAnnotationWrappers H.tr.map_wf ci hn
