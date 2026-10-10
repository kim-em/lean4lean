import Lean4Lean.Verify.Inductive.Nested.Install.Permutation
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData

/-! # The rule-free stage of a restored nested block

The recursor-rule validation pass checks the restored rules in the output environment with the
new recursors' rules removed (`stripRecursorRules`). Its model is the recursor stage of the
restored declaration with every recursor's rules removed (`RuleFreeStage`,
`Validation/Stripped.lean`), stated over a step witness `AddInduct` whose output map is an
`insertConsts`. The stripped environment re-inserts each recursor, so its constant map is not
structurally an `insertConsts` of the block's constants. This file builds the rule-free stage
over `S0`, the source environment extended by the stripped block (`ruleFreeEnv`), shows that
the stripped environment has the same lookups (`stripRecursorRules_find?`, `ruleFreeEnv_find?`),
and transfers the checking invariant along that extensional equality
(`CheckingEnv.Valid.mapExt`). -/

namespace Lean.SMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

theorem insert_stage₁ (s : SMap α β) (k : α) (v : β) : (s.insert k v).stage₁ = s.stage₁ := by
  unfold insert; split <;> rfl

/-- After an insertion outside the first stage, the key is in the persistent stage. -/
theorem insert_map₂_contains_self {s : SMap α β} (h : s.map₂.WF) (hst : s.stage₁ = false)
    (k : α) (v : β) : (s.insert k v).map₂.contains k := by
  unfold insert; split
  · simp_all
  · rw [PersistentHashMap.find?_isSome, h.find?_insert]; simp

/-- An insertion keeps the persistent stage's keys. -/
theorem insert_map₂_contains {s : SMap α β} (h : s.map₂.WF) {x : α} (hx : s.map₂.contains x)
    (k : α) (v : β) : (s.insert k v).map₂.contains x := by
  unfold insert; split
  · exact hx
  · rw [PersistentHashMap.find?_isSome] at hx ⊢
    rw [h.find?_insert]; split <;> simp_all

/-- Replacing the value of a key of the persistent stage (or any key in the first stage) keeps
the map well formed. -/
theorem WF.insert_replace {s : SMap α β} (h : s.WF) {k : α} (v : β)
    (hk : s.stage₁ = true ∨ s.map₂.contains k) : (s.insert k v).WF := by
  unfold insert; split
  · exact ⟨h.map₂, h.stage, fun h1 => by have := h.stage rfl; simp_all [PersistentHashMap.find?_isSome, PersistentHashMap.WF.empty.find?_eq]⟩
  · rename_i m₁ m₂
    refine ⟨h.map₂.insert .., nofun, fun {a} h1 => ?_⟩
    rcases hk with hk | hk
    · cases hk
    rw [PersistentHashMap.find?_isSome, h.map₂.find?_insert] at h1
    by_cases hka : k = a
    · subst hka; exact h.disjoint hk
    · simp [hka] at h1
      exact h.disjoint (by rw [PersistentHashMap.find?_isSome]; simpa using h1)

end Lean.SMap

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- A recursor with its rules removed, at the stripped names. -/
def stripRecCI (names : List Name) (x : Name) (ci : ConstantInfo) : ConstantInfo :=
  if x ∈ names then
    match ci with
    | .recInfo r => .recInfo { r with rules := [] }
    | ci => ci
  else ci

theorem stripRecCI_cons_of_ne {names : List Name} {n x : Name} (h : x ≠ n) (ci : ConstantInfo) :
    stripRecCI (n :: names) x ci = stripRecCI names x ci := by
  simp [stripRecCI, h]

theorem stripRecCI_nonrec {names : List Name} {x : Name} {ci : ConstantInfo}
    (h : ∀ r, ci ≠ .recInfo r) : stripRecCI names x ci = ci := by
  unfold stripRecCI; split
  · cases ci with
    | recInfo r => exact absurd rfl (h r)
    | _ => rfl
  · rfl

theorem stripRecCI_stripped {names : List Name} {x : Name} (r : RecursorVal) :
    stripRecCI names x (.recInfo { r with rules := [] }) = .recInfo { r with rules := [] } := by
  unfold stripRecCI; split <;> rfl

/-- **The lookups of the stripped environment**: a named recursor is found with its rules
removed, every other constant unchanged. -/
theorem stripRecursorRules_find? :
    ∀ (names : List Name) (env : Environment), env.constants.WF →
      (∀ x ci, env.constants.find? x = some ci → ci.name = x) →
      (∀ x ∈ names, env.constants.stage₁ = true ∨ env.constants.map₂.contains x) →
      (stripRecursorRules env names).constants.WF ∧
      ∀ x, (stripRecursorRules env names).constants.find? x =
        (env.constants.find? x).map (stripRecCI names x)
  | [], env, hwf, _, _ => ⟨hwf, fun x => by
      change env.constants.find? x = _
      cases env.constants.find? x <;> simp [stripRecCI]⟩
  | n :: names, env, hwf, hname, hrepl => by
    have hstep : stripRecursorRules env (n :: names) = stripRecursorRules
        (match env.find? n with
          | some (.recInfo info) => env.add (.recInfo { info with rules := [] })
          | _ => env) names := rfl
    rw [hstep]
    have hfindn : env.find? n = env.constants.find? n := by
      rw [Kernel.Environment.find?, hwf.find?'_eq_find?]
    cases hfn : env.constants.find? n with
    | none =>
      rw [hfindn, hfn]
      obtain ⟨hwf', hf⟩ := stripRecursorRules_find? names env hwf hname
        (fun x hx => hrepl x (.tail _ hx))
      refine ⟨hwf', fun x => ?_⟩
      rw [hf x]
      by_cases hx : x = n
      · subst hx; rw [hfn]; rfl
      · cases env.constants.find? x <;> simp [stripRecCI_cons_of_ne hx]
    | some ci =>
      rw [hfindn, hfn]
      cases ci with
      | recInfo info =>
        dsimp only
        have hnm : info.name = n := hname n _ hfn
        let ci' : ConstantInfo := .recInfo { info with rules := [] }
        have hconst : (env.add ci').constants = env.constants.insert n ci' := by
          change env.constants.insert ci'.name ci' = _
          rw [show ci'.name = n from hnm]
        have hwf1 : (env.add ci').constants.WF := by
          rw [hconst]; exact hwf.insert_replace ci' (hrepl n (.head _))
        have hfind1 : ∀ x, (env.add ci').constants.find? x =
            if n = x then some ci' else env.constants.find? x := by
          intro x; rw [hconst, hwf.find?_insert]; simp
        have hname1 : ∀ x c, (env.add ci').constants.find? x = some c → c.name = x := by
          intro x c h
          rw [hfind1] at h
          split at h
          · cases h; rename_i h'; subst h'; exact hnm
          · exact hname x c h
        have hrepl1 : ∀ x ∈ names, (env.add ci').constants.stage₁ = true ∨
            (env.add ci').constants.map₂.contains x := by
          intro x hx
          rw [hconst, SMap.insert_stage₁]
          rcases hrepl x (.tail _ hx) with h | h
          · exact .inl h
          · exact .inr (SMap.insert_map₂_contains hwf.map₂ h n ci')
        obtain ⟨hwf', hf⟩ := stripRecursorRules_find? names (env.add ci') hwf1 hname1 hrepl1
        refine ⟨hwf', fun x => ?_⟩
        rw [hf x, hfind1 x]
        by_cases hx : x = n
        · subst hx; simp [hfn, ci', stripRecCI]
        · rw [if_neg (Ne.symm hx)]
          cases env.constants.find? x <;> simp [stripRecCI_cons_of_ne hx]
      | _ =>
        obtain ⟨hwf', hf⟩ := stripRecursorRules_find? names env hwf hname
          (fun x hx => hrepl x (.tail _ hx))
        refine ⟨hwf', fun x => ?_⟩
        rw [hf x]
        by_cases hx : x = n
        · subst hx; rw [hfn]
          simp only [Option.map_some]
          rw [stripRecCI_nonrec (by intro r h; cases h), stripRecCI_nonrec (by intro r h; cases h)]
        · cases env.constants.find? x <;> simp [stripRecCI_cons_of_ne hx]

/-! ### The rule-free environment -/

/-- Inserting a list of constants keeps the first-stage flag. -/
theorem insertConsts_stage₁ : ∀ (C : ConstMap) (cis : List ConstantInfo),
    (insertConsts C cis).stage₁ = C.stage₁
  | _, [] => rfl
  | C, ci :: cis => by
    rw [insertConsts_cons, insertConsts_stage₁, SMap.insert_stage₁]

theorem insertConsts_map₂_contains_of : ∀ {C : ConstMap} {cis : List ConstantInfo} {x : Name},
    C.map₂.WF → C.map₂.contains x → (insertConsts C cis).map₂.contains x
  | _, [], _, _, h => h
  | C, d :: ds, x, hwf, h => by
    rw [insertConsts_cons]
    exact insertConsts_map₂_contains_of (SMap.insert_map₂ hwf)
      (SMap.insert_map₂_contains hwf h d.name d)

/-- Outside the first stage, inserted constants land in the persistent stage. -/
theorem insertConsts_map₂_contains : ∀ {C : ConstMap} {cis : List ConstantInfo}, C.map₂.WF →
    C.stage₁ = false → ∀ ci ∈ cis, (insertConsts C cis).map₂.contains ci.name
  | _, [], _, _, _, h => by cases h
  | C, d :: ds, hwf, hst, ci, hci => by
    rw [insertConsts_cons]
    have hwf' := SMap.insert_map₂ (k := d.name) (v := d) hwf
    have hst' : (C.insert d.name d).stage₁ = false := by rw [SMap.insert_stage₁, hst]
    rcases List.mem_cons.mp hci with rfl | hci
    · exact insertConsts_map₂_contains_of hwf' (SMap.insert_map₂_contains_self hwf hst _ _)
    · exact insertConsts_map₂_contains hwf' hst' ci hci

/-- The source environment extended by a list of constants, one `add` each. -/
def addConstsEnv (env : Environment) (cis : List ConstantInfo) : Environment :=
  cis.foldl (fun e ci => e.add ci) env

theorem addConstsEnv_constants : ∀ (env : Environment) (cis : List ConstantInfo),
    (addConstsEnv env cis).constants = insertConsts env.constants cis
  | _, [] => rfl
  | env, ci :: cis => addConstsEnv_constants (env.add ci) cis

theorem addConstsEnv_quotInit : ∀ (env : Environment) (cis : List ConstantInfo),
    (addConstsEnv env cis).quotInit = env.quotInit
  | _, [] => rfl
  | env, ci :: cis => addConstsEnv_quotInit (env.add ci) cis

/-- The constants of a block with the named recursors' rules removed. -/
def stripEntries (names : List Name) (entries : List ConstantInfo) : List ConstantInfo :=
  entries.map fun ci => stripRecCI names ci.name ci

theorem stripRecCI_name (names : List Name) (x : Name) (ci : ConstantInfo) :
    (stripRecCI names x ci).name = ci.name := by
  unfold stripRecCI; split
  · split <;> rfl
  · rfl

/-- **The stripped environment and the rule-free environment have the same lookups.** -/
theorem stripRecursorRules_find?_eq_strip {source outEnv : Environment}
    {entries : List ConstantInfo} {names : List Name}
    (hsourceWF : source.constants.WF)
    (hsourceNames : ∀ x ci, source.constants.find? x = some ci → ci.name = x)
    (hfresh : ∀ ci ∈ entries, source.constants.find? ci.name = none)
    (hnodup : (entries.map (·.name)).Nodup)
    (hmap : outEnv.constants = insertConsts source.constants entries)
    (hnames : ∀ x ∈ names, x ∈ entries.map (·.name)) :
    (stripRecursorRules outEnv names).constants.WF ∧
    (addConstsEnv source (stripEntries names entries)).constants.WF ∧
    ∀ x, (stripRecursorRules outEnv names).constants.find? x =
      (addConstsEnv source (stripEntries names entries)).constants.find? x := by
  have houtWF : outEnv.constants.WF := by
    rw [hmap]; exact insertConsts_wf hsourceWF hfresh hnodup
  have hstripNames : (stripEntries names entries).map (·.name) = entries.map (·.name) := by
    simp [stripEntries, stripRecCI_name]
  have hfresh' : ∀ ci ∈ stripEntries names entries, source.constants.find? ci.name = none := by
    intro ci hci
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hci
    rw [stripRecCI_name]; exact hfresh d hd
  have hnodup' : ((stripEntries names entries).map (·.name)).Nodup := by
    rw [hstripNames]; exact hnodup
  have hS0WF : (addConstsEnv source (stripEntries names entries)).constants.WF := by
    rw [addConstsEnv_constants]; exact insertConsts_wf hsourceWF hfresh' hnodup'
  have houtNames : ∀ x ci, outEnv.constants.find? x = some ci → ci.name = x := by
    intro x ci h
    rw [hmap] at h
    rcases insertConsts_find? hsourceWF hfresh hnodup h with h | ⟨_, h⟩
    · exact hsourceNames x ci h
    · exact h
  have hrepl : ∀ x ∈ names, outEnv.constants.stage₁ = true ∨ outEnv.constants.map₂.contains x := by
    intro x hx
    rw [hmap, insertConsts_stage₁]
    cases hst : source.constants.stage₁
    · right
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp (hnames x hx)
      exact insertConsts_map₂_contains hsourceWF.map₂ hst ci hci
    · exact .inl rfl
  obtain ⟨hstripWF, hstrip⟩ := stripRecursorRules_find? names outEnv houtWF houtNames hrepl
  refine ⟨hstripWF, hS0WF, fun x => ?_⟩
  rw [hstrip x, addConstsEnv_constants, hmap]
  by_cases hx : ∃ ci ∈ entries, ci.name = x
  · obtain ⟨ci, hci, rfl⟩ := hx
    rw [insertConsts_find?_self hsourceWF hfresh hnodup ci hci]
    have h := insertConsts_find?_self hsourceWF hfresh' hnodup' _
      (List.mem_map_of_mem (f := fun ci => stripRecCI names ci.name ci) hci)
    rw [stripRecCI_name] at h
    rw [h]; rfl
  · have hne : ∀ ci ∈ entries, ci.name ≠ x := fun ci hci h => hx ⟨ci, hci, h⟩
    have hne' : ∀ ci ∈ stripEntries names entries, ci.name ≠ x := by
      intro ci hci
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hci
      rw [stripRecCI_name]; exact hne d hd
    cases hs : source.constants.find? x with
    | none =>
      rw [insertConsts_find?_none hsourceWF.map₂ hne hs,
        insertConsts_find?_none hsourceWF.map₂ hne' hs]; rfl
    | some c =>
      rw [insertConsts_find?_mono hsourceWF.map₂ hne hs,
        insertConsts_find?_mono hsourceWF.map₂ hne' hs]
      have hxn : x ∉ names := by
        intro hxn
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (hnames x hxn)
        rw [hfresh d hd] at hs; cases hs
      simp [stripRecCI, hxn]

end VerifyInductive
end Lean4Lean
