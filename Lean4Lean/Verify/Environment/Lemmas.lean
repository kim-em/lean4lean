import Lean4Lean.Std.SMap
import Lean4Lean.Declaration
import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Environment.QuotCoherence
import Lean4Lean.Verify.Typing.TelescopeTranslationLemmas

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

/-- What a constant installation must supply for the projection-walk corner: nothing for a
non-constructor; for a visible constructor, its telescope certificate (stated in the environment
before the installation, which is where the constructor was checked). -/
def _root_.Lean4Lean.CtorCornerStep (safety : DefinitionSafety) (venv : VEnv)
    (ci : ConstantInfo) : Prop :=
  ∀ info, ci = .ctorInfo info → safety ≤ ci.safety → CtorTelescopeAt venv info

theorem _root_.Lean4Lean.CtorCornerStep.of_not_ctor (h : ∀ info, ci ≠ .ctorInfo info) :
    CtorCornerStep safety venv ci := fun info e => absurd e (h info)

theorem _root_.Lean4Lean.CtorCornerStep.mono (H : CtorCornerStep safety venv ci)
    (hle : venv ≤ venv') : CtorCornerStep safety venv' ci :=
  fun info e hs => (H info e hs).mono hle

/-- Certificates of an installed constant: none for a non-constructor; for a visible constructor,
its certificate in the environment before the installation. -/
theorem _root_.Lean4Lean.CtorTelescopes.add {env : Environment}
    (H : CtorTelescopes safety env venv) (hwf : env.constants.WF)
    (hn : env.find? ci.name = none) (hle : venv ≤ venv')
    (hstep : CtorCornerStep safety venv ci) :
    CtorTelescopes safety (env.add ci) venv' := by
  intro name ci₂ hfind hvis
  rcases find?_add_cases hwf _ hn hfind with ⟨-, heq⟩ | hold
  · exact (hstep ci₂ heq.symm (heq ▸ hvis)).mono hle
  · exact (H hold hvis).mono hle

theorem _root_.Lean4Lean.CtorTelescopes.addNonCtor {env : Environment}
    (H : CtorTelescopes safety env venv) (hwf : env.constants.WF)
    (hn : env.find? ci.name = none) (hle : venv ≤ venv')
    (hnot : ∀ info, ci ≠ .ctorInfo info) : CtorTelescopes safety (env.add ci) venv' :=
  H.add hwf hn hle fun info e => absurd e (hnot info)

/-- A fresh batch of non-constructor constants preserves the certificates. -/
theorem _root_.Lean4Lean.CtorTelescopes.foldlAdd {α} {f : α → ConstantInfo}
    (hnot : ∀ v info, f v ≠ .ctorInfo info) (hle : venv ≤ venv') :
    ∀ (vs : List α) {env : Environment}, CtorTelescopes safety env venv →
      env.constants.WF → (∀ v ∈ vs, env.find? (f v).name = none) →
      (vs.map (fun v => (f v).name)).Nodup →
      CtorTelescopes safety (vs.foldl (fun e v => e.add (f v)) env) venv'
  | [], _, H, _, _, _ => H.mono hle
  | v :: vs, env, H, hwf, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hn := hfresh v List.mem_cons_self
    have hnMap : env.constants.find? (f v).name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hwf' : (env.add (f v)).constants.WF := hwf.insert _ _ hnMap
    refine CtorTelescopes.foldlAdd hnot hle vs (H.addNonCtor hwf hn VEnv.LE.rfl (hnot v))
      hwf' (fun w hw => ?_) hnd.2
    cases hfind : (env.add (f v)).find? (f w).name with
    | none => rfl
    | some found =>
      rcases find?_add_cases hwf _ hn hfind with ⟨hname, -⟩ | hold
      · exact absurd (List.mem_map.2 ⟨w, hw, hname⟩) hnd.1
      · rw [hfresh w (List.mem_cons_of_mem _ hw)] at hold; cases hold

/-- The certificates transport to an environment whose constructors are constructors of the
source. -/
theorem _root_.Lean4Lean.CtorTelescopes.ofCtors {source target : Environment}
    (H : CtorTelescopes safety source venv)
    (hctors : ∀ {name ci}, target.find? name = some (.ctorInfo ci) →
      source.find? name = some (.ctorInfo ci)) :
    CtorTelescopes safety target venv :=
  fun _ _ hfind hvis => H (hctors hfind) hvis

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

def CtorInfoCoherentAt.addConstant
    {ci : ConstantInfo}
    (H : CtorInfoCoherentAt env familyName familyInfo i hi)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    CtorInfoCoherentAt (env.add ci) familyName familyInfo i hi := by
  have hne : ci.name ≠ familyInfo.ctors[i] := by
    intro heq
    rw [heq, H.lookup] at hfresh
    contradiction
  exact { H with lookup :=
    (find?_add_of_ne hwf ci hfresh hne).trans H.lookup }

def CtorParamsAgreeAt.mono
    (H : CtorParamsAgreeAt
      env venv familyName familyInfo i hi)
    (hle : venv ≤ venv') :
    CtorParamsAgreeAt
      env venv' familyName familyInfo i hi :=
  { H with
    familyLookup := hle.constants H.familyLookup
    constructorLookup := hle.constants H.constructorLookup
    familyDefEq := H.familyDefEq.mono hle
    constructorDefEq := H.constructorDefEq.mono hle
    parameterDomains := H.parameterDomains.mono hle }

def CtorParamsAgreeAt.addConstant
    {ci : ConstantInfo}
    (H : CtorParamsAgreeAt
      env venv familyName familyInfo i hi)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hle : venv ≤ venv') :
    CtorParamsAgreeAt
      (env.add ci) venv' familyName familyInfo i hi :=
  { H.mono hle with
    toCtorInfoCoherentAt :=
      H.toCtorInfoCoherentAt.addConstant hwf hfresh }

/-- Transport one semantic constructor witness across an arbitrary
production-environment extension once the exact constructor lookup has been
shown to survive.  All semantic fields only require monotonicity of the
abstract environment. -/
def CtorParamsAgreeAt.rebaseProduction
    (H : CtorParamsAgreeAt
      env venv familyName familyInfo i hi)
    (hlookup : env'.find? familyInfo.ctors[i] = some (.ctorInfo H.info))
    (hle : venv ≤ venv') :
    CtorParamsAgreeAt
      env' venv' familyName familyInfo i hi :=
  { H.mono hle with
    toCtorInfoCoherentAt :=
      { H.toCtorInfoCoherentAt with lookup := hlookup } }

theorem CtorParamsAgree.mono
    (H : CtorParamsAgree safety env venv)
    (hle : venv ≤ venv') :
    CtorParamsAgree safety env venv' := by
  intro familyName familyInfo hfamily hvisible i hi
  rcases H familyName familyInfo hfamily hvisible i hi with ⟨C⟩
  exact ⟨C.mono hle⟩

/-- A fresh non-inductive production constant and any monotone abstract
extension preserve visible constructor semantics. -/
theorem CtorParamsAgree.addNonInductive
    {ci : ConstantInfo}
    (H : CtorParamsAgree safety env venv)
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none)
    (hnind : ∀ value, ci ≠ .inductInfo value)
    (hle : venv ≤ venv') :
    CtorParamsAgree safety (env.add ci) venv' := by
  intro familyName familyInfo hfamily hvisible i hi
  rcases find?_add_cases hwf ci hfresh hfamily with
    ⟨_, hvalue⟩ | hold
  · exact False.elim (hnind familyInfo hvalue.symm)
  · rcases H familyName familyInfo hold hvisible i hi with ⟨C⟩
    exact ⟨C.addConstant hwf hfresh hle⟩

/-- A fresh mutual-definition fold changes no inductive metadata.  All old
semantic witnesses may be transported directly to the final abstract model,
then retained while the remaining production definitions are inserted. -/
theorem CtorParamsAgree.addDefinitions
    (H : CtorParamsAgree safety env venv)
    (hwf : env.constants.WF) :
    ∀ (vs : List DefinitionVal),
      (∀ v ∈ vs, env.find? v.name = none) →
      (vs.map (·.name)).Nodup →
      venv ≤ venv' →
      CtorParamsAgree safety
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
      have H' : CtorParamsAgree safety
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

/-- Rebase an observer across a production extension whose genuinely new
inductive headers are all hidden at that observer's safety. -/
theorem InductFamiliesInstalled.rebaseHidden
    (H : InductFamiliesInstalled safety source env)
    (hpreserves : ∀ {name found}, source.find? name = some found →
      target.find? name = some found)
    (hhidden : ∀ familyName familyInfo,
      target.find? familyName = some (.inductInfo familyInfo) →
      source.find? familyName = none →
      ¬ safety ≤ (ConstantInfo.inductInfo familyInfo).safety) :
    InductFamiliesInstalled safety target env := by
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
theorem InductFamiliesInstalled.insertDefs
    (H : InductFamiliesInstalled safety C env)
    (hwf : C.WF) : ∀ (cis : List DefinitionVal),
      (∀ ci ∈ cis, C.find? ci.name = none) →
      (cis.map (·.name)).Nodup → env ≤ env' →
      InductFamiliesInstalled safety (insertDefs C cis) env'
  | [], _, _, henv => InductFamiliesInstalled.monoEnv H henv
  | ci :: cis, hfresh, hnodup, henv => by
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hciFresh := hfresh ci (by simp)
      have hwf' := hwf.insert ci.name (.defnInfo ci) hciFresh
      have H' : InductFamiliesInstalled safety
          (C.insert ci.name (.defnInfo ci)) env' :=
        InductFamiliesInstalled.insertNonInductive
          (ci := .defnInfo ci) H hwf hciFresh
          (by intro _ h; cases h) henv
      apply InductFamiliesInstalled.insertDefs H' hwf' cis
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
  | empty => exact .empty_stage _
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih => exact ih
  | projections _ ih => exact ih
  | eliminators _ ih => exact ih
  | mapExt _ htarget _ _ => exact htarget

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih
  | projections _ ih =>
    simpa only [VEnv.addEliminators_constants, VEnv.addProjections_constants] using ih
  | eliminators _ ih => exact ih
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
  | empty => simp at h
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
  | projections h1 ih =>
    rename_i entries
    rcases ih h with ⟨ci', hci', htr⟩
    exact ⟨ci', by simpa only [VEnv.addEliminators_constants, VEnv.addProjections_constants] using hci',
      htr.mono (VEnv.addProjections_le (entries := entries))⟩
  | eliminators _ ih =>
    rcases ih h with ⟨ci', hci', htr⟩
    exact ⟨ci', hci', htr.mono VEnv.addEliminator_le⟩
  | mapExt _ _ heq ih =>
    rw [← heq] at h
    exact ih h

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp at h
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
  | projections h1 ih =>
    rename_i entries
    rcases ih h (by simpa only [VEnv.addEliminators_constants, VEnv.addProjections_constants] using hs) with
      ⟨hname, htr⟩
    exact ⟨hname, htr.mono
      (VEnv.addProjections_le (env := _) (entries := entries))⟩
  | eliminators _ ih =>
    rcases ih h hs with ⟨hname, htr⟩
    exact ⟨hname, htr.mono VEnv.addEliminator_le⟩
  | mapExt _ _ heq ih =>
    rw [← heq] at h
    exact ih h hs

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

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
  | empty => simp at h
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

/-! ## Recursor rules and quotient facts along the environment trace -/

theorem insertDefs_find?_of_find? : ∀ {cis : List DefinitionVal} {C : ConstMap} {name ci}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    C.find? name = some ci → (insertDefs C cis).find? name = some ci
  | [], _, _, _, _, _, _, h => h
  | d :: ds, C, name, ci, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ e ∈ ds, (SMap.insert C d.name (.defnInfo d)).find? e.name = none := by
      intro e he
      rw [hC.find?_insert]
      have : ¬ (d.name == e.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨e, he, hh.symm⟩
      simp [this]; exact hfr e (.tail _ he)
    show (insertDefs (SMap.insert C d.name (.defnInfo d)) ds).find? name = some ci
    refine insertDefs_find?_of_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 ?_
    rw [hC.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; rw [← hb, hfr d (.head _)] at h; cases h
    · exact h

theorem insertDefs_find?_self : ∀ {cis : List DefinitionVal} {C : ConstMap} {d}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup →
    d ∈ cis → (insertDefs C cis).find? d.name = some (.defnInfo d)
  | [], _, _, _, _, _, h => by cases h
  | e :: ds, C, d, hC, hfr, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hfr' : ∀ f ∈ ds, (SMap.insert C e.name (.defnInfo e)).find? f.name = none := by
      intro f hf
      rw [hC.find?_insert]
      have : ¬ (e.name == f.name) = true := by
        simp only [beq_iff_eq]; intro hh; exact hnd.1 ⟨f, hf, hh.symm⟩
      simp [this]; exact hfr f (.tail _ hf)
    show (insertDefs (SMap.insert C e.name (.defnInfo e)) ds).find? d.name = some _
    cases h with
    | head =>
      refine insertDefs_find?_of_find? (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 ?_
      rw [hC.find?_insert]; simp
    | tail _ h =>
      exact insertDefs_find?_self (hC.insert _ _ (hfr _ (.head _))) hfr' hnd.2 h

/-- Lookup of a constant through the four quotient insertions. -/
theorem AddQuot.find? (H : AddQuot C₁ C₂ venv₁ venv₂) (hwf : C₁.WF) :
    C₁.find? ``Quot = none ∧
    (∀ {n ci}, C₁.find? n = some ci → C₂.find? n = some ci) ∧
    (∃ q : QuotVal, C₂.find? ``Quot = some (.quotInfo q) ∧ q.kind = .type) ∧
    (∃ q : QuotVal, C₂.find? ``Quot.lift = some (.quotInfo q) ∧ q.kind = .lift) ∧
    (∀ {n ci}, C₂.find? n = some ci → C₁.find? n = some ci ∨ ∃ q, ci = .quotInfo q) := by
  obtain ⟨l1, t1, e1, -, f1, -, l2, t2, e2, -, f2, -, l3, t3, e3, -, f3, -, l4, t4, e4, -, f4, -,
    hm, -⟩ := H
  subst hm
  have w1 := hwf.insert _ (.quotInfo ⟨⟨``Quot, l1, t1⟩, .type⟩) f1
  have w2 := w1.insert _ (.quotInfo ⟨⟨``Quot.mk, l2, t2⟩, .ctor⟩) f2
  have w3 := w2.insert _ (.quotInfo ⟨⟨``Quot.lift, l3, t3⟩, .lift⟩) f3
  -- the intermediate freshness facts on the base map
  have g2 : C₁.find? ``Quot.mk = none := by
    rw [hwf.find?_insert] at f2; simpa using f2
  have g3 : C₁.find? ``Quot.lift = none := by
    rw [w1.find?_insert, hwf.find?_insert] at f3; simpa using f3
  have g4 : C₁.find? ``Quot.ind = none := by
    rw [w2.find?_insert, w1.find?_insert, hwf.find?_insert] at f4; simpa using f4
  have look : ∀ n, ((((C₁.insert ``Quot (.quotInfo ⟨⟨``Quot, l1, t1⟩, .type⟩)).insert ``Quot.mk
      (.quotInfo ⟨⟨``Quot.mk, l2, t2⟩, .ctor⟩)).insert ``Quot.lift
      (.quotInfo ⟨⟨``Quot.lift, l3, t3⟩, .lift⟩)).insert ``Quot.ind
      (.quotInfo ⟨⟨``Quot.ind, l4, t4⟩, .ind⟩)).find? n =
      if ``Quot.ind = n then some (.quotInfo ⟨⟨``Quot.ind, l4, t4⟩, .ind⟩)
      else if ``Quot.lift = n then some (.quotInfo ⟨⟨``Quot.lift, l3, t3⟩, .lift⟩)
      else if ``Quot.mk = n then some (.quotInfo ⟨⟨``Quot.mk, l2, t2⟩, .ctor⟩)
      else if ``Quot = n then some (.quotInfo ⟨⟨``Quot, l1, t1⟩, .type⟩)
      else C₁.find? n := by
    intro n
    rw [w3.find?_insert, w2.find?_insert, w1.find?_insert, hwf.find?_insert]
    simp only [beq_iff_eq]
  refine ⟨f1, ?_, ?_, ?_, ?_⟩
  · intro n ci h
    rw [look]
    split
    · rename_i hb; subst hb; rw [g4] at h; cases h
    split
    · rename_i hb; subst hb; rw [g3] at h; cases h
    split
    · rename_i hb; subst hb; rw [g2] at h; cases h
    split
    · rename_i hb; subst hb; rw [f1] at h; cases h
    exact h
  · exact ⟨_, by rw [look, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl],
      rfl⟩
  · exact ⟨_, by rw [look, if_neg (by decide), if_pos rfl], rfl⟩
  · intro n ci h
    rw [look] at h
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    split at h
    · exact .inr ⟨_, (Option.some.inj h).symm⟩
    exact .inl h

/-- The stored equations after quotient initialization. -/
theorem AddQuot.defeqs (H : AddQuot C₁ C₂ venv₁ venv₂) :
    ∀ df, venv₂.defeqs df → venv₁.defeqs df ∨ df = quotDefEq := by
  obtain ⟨_, _, e1, -, -, h1, _, _, e2, -, -, h2, _, _, e3, -, -, h3, _, _, e4, -, -, h4, -, rfl⟩ :=
    H
  intro df hdf
  rcases hdf with rfl | hdf
  · exact .inr rfl
  · rw [VEnv.addConst_defeqs h4, VEnv.addConst_defeqs h3, VEnv.addConst_defeqs h2,
      VEnv.addConst_defeqs h1] at hdf
    exact .inl hdf

theorem TrEnv'.recursorEnvCoherent (H : TrEnv' safety C Q venv) :
    RecursorEnvCoherent safety C venv := by
  induction H with
  | empty =>
    refine ⟨?_, ?_, ?_⟩
    · intro name rec h; simp at h
    · intro name rec h; simp at h
    · intro df h; exact h.elim
  | ignore h1 h2 h3 ih => exact ih.insertInvisible h3.map_wf h1 h2
  | «axiom» _ h2 _ h4 h5 ih =>
    exact ih.insert h5.map_wf h2 (.of_not_rec nofun) (VEnv.addConst_le h4)
      fun df hdf => by rwa [VEnv.addConst_defeqs h4] at hdf
  | thm _ h2 _ _ h4 h5 ih =>
    exact ih.insert h5.map_wf h2 (.of_not_rec nofun) (VEnv.addConst_le h4)
      fun df hdf => by rwa [VEnv.addConst_defeqs h4] at hdf
  | «opaque» _ h2 _ h4 h5 ih =>
    exact ih.insert h5.map_wf h2 (.of_not_rec nofun) (VEnv.addConst_le h4)
      fun df hdf => by rwa [VEnv.addConst_defeqs h4] at hdf
  | @defn _ ci _ C _ ci' h1 h2 _ h4 h5 ih =>
    have hname := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal, VDefVal.toVConstVal] at hname
    refine (ih.insert h5.map_wf h2 (RecursorInstallStep.of_not_rec (ci := .defnInfo _) nofun)
      (VEnv.addConst_le h4) fun df hdf => by rwa [VEnv.addConst_defeqs h4] at hdf).addDefEq ?_
    have hfind : (SMap.insert C ci.name (ConstantInfo.defnInfo ci)).find? ci'.name =
        some (ConstantInfo.defnInfo ci) := by
      rw [← hname, h5.map_wf.find?_insert, if_pos (beq_self_eq_true _)]
    exact EquationHeadOf.ofDefn ⟨_, _, _, VDefVal.toDefEq_head _, hfind⟩
  | @mutualDef _ _ C _ cis cis' hblk hnd hfr _ hadd _ htr ih =>
    refine ih.extend (insertDefs_find?_of_find? htr.map_wf hfr hnd) ?_
      ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le) ?_
    · intro n rec hn _
      rcases insertDefs_find? htr.map_wf hfr hnd hn with h | ⟨d, -, -, h⟩
      · exact .inl h
      · cases h
    · intro df hdf
      rcases VEnv.addDefEqs_defeqs_iff.1 hdf with hdf | ⟨ci', hci', rfl⟩
      · rw [VEnv.addConsts_defeqs hadd] at hdf; exact .inl hdf
      · obtain ⟨ci, hci, htrc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hblk ci' hci'
        have hname := htrc.1.2
        dsimp [ConstantInfo.name, ConstantInfo.toConstantVal, VDefVal.toVConstVal] at hname
        have hfind : (insertDefs C cis).find? ci'.name = some (ConstantInfo.defnInfo ci) := by
          rw [← hname]
          exact insertDefs_find?_self htr.map_wf hfr hnd hci
        exact .inr (EquationHeadOf.ofDefn ⟨_, _, _, VDefVal.toDefEq_head _, hfind⟩)
  | quot _ hq htr ih =>
    obtain ⟨-, hpres, -, ⟨q, hlift, hkind⟩, hnew⟩ := hq.find? htr.map_wf
    refine ih.extend hpres ?_ hq.le ?_
    · intro n rec hn _
      rcases hnew hn with h | ⟨q, h⟩
      · exact .inl h
      · cases h
    · intro df hdf
      rcases hq.defeqs df hdf with h | rfl
      · exact .inl h
      · exact .inr ⟨``Quot.lift, _, _, rfl, hlift, nofun, fun q' hq' => by
          cases hq'; exact hkind⟩
  | induct _ hadd _ ih =>
    exact ih.addInduct hadd.recursorProvenance hadd.preservesSourceFind hadd.le

theorem TrEnv'.quotEnvCoherent (H : TrEnv' safety C Q venv) (hQ : Q = true) :
    QuotEnvCoherent C venv := by
  induction H with
  | empty => cases hQ
  | ignore h1 h2 h3 ih =>
    refine (ih hQ).extend ?_ VEnv.LE.rfl (TrEnv'.ignore h1 h2 h3).recursorEnvCoherent.heads
    intro n ci h
    rw [h3.map_wf.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; subst hb; rw [h1] at h; cases h
    · exact h
  | «axiom» h1 h2 h3 h4 h5 ih =>
    refine (ih hQ).extend ?_ (VEnv.addConst_le h4)
      (TrEnv'.axiom h1 h2 h3 h4 h5).recursorEnvCoherent.heads
    intro n ci h
    rw [h5.map_wf.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; subst hb; rw [h2] at h; cases h
    · exact h
  | thm h1 h2 h3 h3' h4 h5 ih =>
    refine (ih hQ).extend ?_ (VEnv.addConst_le h4)
      (TrEnv'.thm h1 h2 h3 h3' h4 h5).recursorEnvCoherent.heads
    intro n ci h
    rw [h5.map_wf.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; subst hb; rw [h2] at h; cases h
    · exact h
  | «opaque» h1 h2 h3 h4 h5 ih =>
    refine (ih hQ).extend ?_ (VEnv.addConst_le h4)
      (TrEnv'.opaque h1 h2 h3 h4 h5).recursorEnvCoherent.heads
    intro n ci h
    rw [h5.map_wf.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; subst hb; rw [h2] at h; cases h
    · exact h
  | defn h1 h2 h3 h4 h5 ih =>
    refine (ih hQ).extend ?_ ((VEnv.addConst_le h4).trans VEnv.addDefEq_le)
      (TrEnv'.defn h1 h2 h3 h4 h5).recursorEnvCoherent.heads
    intro n ci h
    rw [h5.map_wf.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; subst hb; rw [h2] at h; cases h
    · exact h
  | mutualDef hblk hnd hfr hwf hadd hci htr ih =>
    exact (ih hQ).extend (insertDefs_find?_of_find? htr.map_wf hfr hnd)
      ((VEnv.addConsts_le hadd).trans VEnv.addDefEqs_le)
      (TrEnv'.mutualDef hblk hnd hfr hwf hadd hci htr).recursorEnvCoherent.heads
  | quot _ hq htr _ =>
    obtain ⟨hf1, -, hquot, -, -⟩ := hq.find? htr.map_wf
    exact ⟨AddQuot.quotCoherent hq (htr.recursorEnvCoherent.heads.rigid_of_fresh hf1), hquot⟩
  | induct hdecl hadd htr ih =>
    exact (ih hQ).extend hadd.preservesSourceFind hadd.le
      (TrEnv'.induct hdecl hadd htr).recursorEnvCoherent.heads

theorem TrEnv.recursorEnvCoherent (H : TrEnv safety env venv) :
    RecursorEnvCoherent safety env.constants venv :=
  TrEnv'.recursorEnvCoherent H

theorem TrEnv.quotEnvCoherent (H : TrEnv safety env venv) (hQ : env.quotInit = true) :
    QuotEnvCoherent env.constants venv :=
  TrEnv'.quotEnvCoherent H hQ

/-- Local invariants of a staged checking environment that every fresh
constant installation preserves: the translation relation itself, primitive
metadata, and the type-annotation wrappers.  Constant installation
certificates carry this part between the points at which the type checker
actually runs. -/
structure CheckingEnv.ValidCore (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv) : Prop where
  tr : CheckingEnv safety env venv
  hasPrimitives : venv.HasPrimitives
  safePrimitives : ∀ {n ci}, env.find? n = some ci →
    Kernel.Environment.primitives.contains n →
    ci.safety = .safe ∧ ci.levelParams = []

/-- All global invariants needed to run the verified executable type checker
against an environment assembled in stages.  Beyond the local invariants,
production constructor metadata is closed under owners, and every visible
singleton family whose constructor is present aligns with the abstract
projection registry.  Both are required by projection inference, so they
hold at every point where the type checker runs. -/
structure CheckingEnv.Valid (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv) : Prop extends
    CheckingEnv.ValidCore safety env venv where
  constructorOwners : VerifyInductive.ConstructorOwnersPresent env
  projectionRegistry : ProjectionRegistryCoherent safety env.constants venv
  /-- Every visible recursor is aligned with the stored iota equations, and every stored
  equation is headed by a non-inductive constant. This is what recursor reduction reads. -/
  recursors : RecursorEnvCoherent safety env.constants venv
  /-- Once quotients are initialized, the quotient constants and the `Quot.lift` equation are
  present. This is what quotient reduction reads. -/
  quot : env.quotInit = true → QuotEnvCoherent env.constants venv
  /-- What resolves the projection-walk corner of `inferProj`: a telescope certificate of every
  visible constructor (`TelTrN.delete_closed`). Constructor installations supply it through
  `CtorCornerStep`. -/
  corner : CtorTelescopes safety env venv

theorem TrEnv.toCheckingValid (H : TrEnv safety env venv)
    (hprims : venv.HasPrimitives)
    (hsafe : ∀ {n ci}, env.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (howners : VerifyInductive.ConstructorOwnersPresent env)
    (hregistry : ProjectionRegistryCoherent safety env.constants venv)
    (hcorner : CtorTelescopes safety env venv) :
    CheckingEnv.Valid safety env venv :=
  ⟨⟨H.toChecking, hprims, hsafe⟩, howners, hregistry,
    H.recursorEnvCoherent, H.quotEnvCoherent, hcorner⟩

theorem CheckingEnv.ValidCore.add (H : CheckingEnv.ValidCore safety env venv)
    (hn : env.find? ci.name = none)
    (hnprim : ¬ Kernel.Environment.primitives.contains ci.name)
    (htr : TrConstant safety venv ci ci')
    (hci : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv')
    (hdelta : ci.deltaValue? = none) :
    CheckingEnv.ValidCore safety (env.add ci) venv' where
  tr := H.tr.add hn htr hci hadd hdelta
  hasPrimitives := H.hasPrimitives.addConst_of_not_primitive hadd hnprim
  safePrimitives := H.tr.safePrimitives_add hn hnprim H.safePrimitives

/-- Constructor-owner presence of a valid environment, stated on its
constant map. -/
theorem CheckingEnv.Valid.constructorOwnersMap
    (H : CheckingEnv.Valid safety env venv) :
    ConstructorOwnersPresentMap env.constants := by
  intro name info hfind
  have hfind' : env.find? name = some (.ctorInfo info) := by
    rw [Lean.Kernel.Environment.find?, H.tr.map_wf.find?'_eq_find?]
    exact hfind
  rcases H.constructorOwners name info hfind' with ⟨owner, howner⟩
  refine ⟨owner, ?_⟩
  rwa [Lean.Kernel.Environment.find?, H.tr.map_wf.find?'_eq_find?] at howner

/-- Extend a valid environment by a fresh, typed, non-delta, nonprimitive
constant.  Headers and non-inductive constants need no further evidence;
constructors supply their owner and, for singleton families, the projection
alignment through `ProjectionRegistryStep`. -/
theorem CheckingEnv.Valid.add (H : CheckingEnv.Valid safety env venv)
    (hn : env.find? ci.name = none)
    (hnprim : ¬ Kernel.Environment.primitives.contains ci.name)
    (htr : TrConstant safety venv ci ci')
    (hci : ci'.WF venv)
    (hadd : venv.addConst ci.name ci' = some venv')
    (hdelta : ci.deltaValue? = none)
    (hstep : ProjectionRegistryStep env.constants venv' ci)
    (hrec : RecursorInstallStep safety env.constants venv' ci)
    (hcstep : CtorCornerStep safety venv ci) :
    CheckingEnv.Valid safety (env.add ci) venv' := by
  have hcore := H.toValidCore.add hn hnprim htr hci hadd hdelta
  have hfresh : env.constants.find? ci.name = none := by
    rw [Lean.Kernel.Environment.find?, H.tr.map_wf.find?'_eq_find?] at hn
    exact hn
  have hle : venv ≤ venv' := VEnv.addConst_le hadd
  have hrecursors : RecursorEnvCoherent safety (env.add ci).constants venv' :=
    H.recursors.insert H.tr.map_wf hfresh hrec hle fun df hdf => by
      rwa [VEnv.addConst_defeqs hadd] at hdf
  have hquot : (env.add ci).quotInit = true → QuotEnvCoherent (env.add ci).constants venv' := by
    intro hq
    refine (H.quot hq).extend ?_ hle hrecursors.heads
    intro n ci' h
    show (env.constants.insert ci.name ci).find? n = some ci'
    rw [H.tr.map_wf.find?_insert]
    split
    · rename_i hb; rw [beq_iff_eq] at hb; subst hb; rw [hfresh] at h; cases h
    · exact h
  refine { hcore with
    constructorOwners := ?_
    projectionRegistry := ?_
    recursors := hrecursors
    quot := hquot
    corner := H.corner.add H.tr.map_wf hn hle hcstep }
  · cases ci with
    | ctorInfo info =>
      rcases hstep.1 with ⟨owner, howner⟩
      have howner' : env.find? info.induct = some (.inductInfo owner) := by
        rw [Lean.Kernel.Environment.find?, H.tr.map_wf.find?'_eq_find?]
        exact howner
      exact H.constructorOwners.addConstructor H.tr.map_wf info hn howner'
    | _ => exact H.constructorOwners.addNonConstructor H.tr.map_wf hn nofun
  · cases ci with
    | ctorInfo info =>
      exact H.projectionRegistry.insertConstructor H.tr.map_wf hfresh hle hstep
    | inductInfo info =>
      exact H.projectionRegistry.insertInductiveHeader H.tr.map_wf
        H.constructorOwnersMap hfresh hle
    | _ =>
      exact H.projectionRegistry.insertNonInductive H.tr.map_wf hfresh nofun
        nofun hle

theorem CheckingEnv.addProjections
    (H : CheckingEnv safety env venv)
    (hwf : (venv.addProjections entries).WF) :
    CheckingEnv safety env (venv.addProjections entries) where
  aligned := .projections H.aligned
  wf := hwf
  of_value := fun hfind hvisible hvalue =>
    (H.of_value hfind hvisible hvalue).mono VEnv.addProjections_le

theorem Aligned.addEliminators {C : ConstMap} :
    ∀ {venv : VEnv} {es : List (Name × InductiveSignature.CaseSchema)}, Aligned safety C venv →
      Aligned safety C (venv.addEliminators es)
  | _, [], H => H
  | v, (k, sc) :: rest, H =>
    Aligned.addEliminators (venv := v.addEliminator k sc) (es := rest) (.eliminators H)

theorem VEnv.HasPrimitives.addEliminators :
    ∀ {venv : VEnv} {es : List (Name × InductiveSignature.CaseSchema)}, venv.HasPrimitives →
      (venv.addEliminators es).HasPrimitives
  | _, [], H => H
  | v, (k, sc) :: rest, H =>
    VEnv.HasPrimitives.addEliminators (venv := v.addEliminator k sc) (es := rest) H.addEliminator

theorem CheckingEnv.addEliminators
    (H : CheckingEnv safety env venv)
    (hwf : (venv.addEliminators es).WF) :
    CheckingEnv safety env (venv.addEliminators es) where
  aligned := H.aligned.addEliminators
  wf := hwf
  of_value := fun hfind hvisible hvalue =>
    (H.of_value hfind hvisible hvalue).mono VEnv.addEliminators_le

theorem CheckingEnv.ValidCore.addEliminators
    (H : CheckingEnv.ValidCore safety env venv)
    (hwf : (venv.addEliminators es).WF) :
    CheckingEnv.ValidCore safety env (venv.addEliminators es) where
  tr := H.tr.addEliminators hwf
  hasPrimitives := H.hasPrimitives.addEliminators
  safePrimitives := H.safePrimitives

theorem CheckingEnv.ValidCore.addProjections
    (H : CheckingEnv.ValidCore safety env venv)
    (hwf : (venv.addProjections entries).WF) :
    CheckingEnv.ValidCore safety env (venv.addProjections entries) where
  tr := H.tr.addProjections hwf
  hasPrimitives := H.hasPrimitives.addProjections
  safePrimitives := H.safePrimitives

/-- Add an exact, independently well-formed projection table without changing
the represented production environment. -/
theorem CheckingEnv.Valid.addEliminators
    (H : CheckingEnv.Valid safety env venv)
    (hwf : (venv.addEliminators es).WF) :
    CheckingEnv.Valid safety env (venv.addEliminators es) where
  toValidCore := H.toValidCore.addEliminators hwf
  constructorOwners := H.constructorOwners
  projectionRegistry := H.projectionRegistry.monoEnv VEnv.addEliminators_le
  recursors := H.recursors.extendSimple (fun h => h) (fun h _ => h)
    VEnv.addEliminators_le (fun _ h => by simpa using h)
  quot hq := (H.quot hq).extend (fun h => h) VEnv.addEliminators_le
    (H.recursors.extendSimple (fun h => h) (fun h _ => h)
      VEnv.addEliminators_le (fun _ h => by simpa using h)).heads
  corner := H.corner.mono VEnv.addEliminators_le

theorem CheckingEnv.Valid.addProjections
    (H : CheckingEnv.Valid safety env venv)
    (hwf : (venv.addProjections entries).WF) :
    CheckingEnv.Valid safety env (venv.addProjections entries) where
  toValidCore := H.toValidCore.addProjections hwf
  constructorOwners := H.constructorOwners
  projectionRegistry := H.projectionRegistry.monoEnv VEnv.addProjections_le
  recursors := H.recursors.addProjections entries
  quot hq := (H.quot hq).extend (fun h => h) VEnv.addProjections_le
    (H.recursors.addProjections entries).heads
  corner := H.corner.mono VEnv.addProjections_le

/-- Promote the local invariants to the full checking invariant once
constructor-owner presence and registry coherence are known. -/
theorem CheckingEnv.ValidCore.toValid
    (H : CheckingEnv.ValidCore safety env venv)
    (howners : VerifyInductive.ConstructorOwnersPresent env)
    (hregistry : ProjectionRegistryCoherent safety env.constants venv)
    (hrecursors : RecursorEnvCoherent safety env.constants venv)
    (hquot : env.quotInit = true → QuotEnvCoherent env.constants venv)
    (hcorner : CtorTelescopes safety env venv) :
    CheckingEnv.Valid safety env venv :=
  { H with
    constructorOwners := howners
    projectionRegistry := hregistry
    recursors := hrecursors
    quot := hquot
    corner := hcorner }
