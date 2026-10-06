import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean

theorem VEnv.addConsts_eliminators {env env' : VEnv} :
    ∀ {cis}, env.addConsts cis = some env' → env'.eliminators = env.eliminators
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨middle, hfirst, hrest⟩ := h
    exact (VEnv.addConsts_eliminators hrest).trans (VEnv.addConst_eliminators hfirst)

@[simp] theorem VEnv.addDefEqs_eliminators (env : VEnv) (cis : List VDefVal) :
    (env.addDefEqs cis).eliminators = env.eliminators := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem VInductBlock.install_eliminators {env env' : VEnv}
    (H : VInductBlock.install env block = some env') :
    env'.eliminators = env.eliminators := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := H
  rw [VEnv.addDefEqRules_eliminators, VEnv.addConstVals_eliminators hr,
    VEnv.addProjections_eliminators, VEnv.addConstVals_eliminators hc,
    VEnv.addConstVals_eliminators ht]

theorem VEnv.addQuot_eliminators {env env' : VEnv}
    (H : env.addQuot = some env') : env'.eliminators = env.eliminators := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := H
  exact (VEnv.addConst_eliminators hd).trans <|
    (VEnv.addConst_eliminators hc).trans <|
      (VEnv.addConst_eliminators hb).trans (VEnv.addConst_eliminators ha)

theorem VDecl.WF.eliminators (H : VDecl.WF env decl env') :
    env'.eliminators = env.eliminators := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact VEnv.addConst_eliminators h
  | «def» _ h => exact (VEnv.addConst_eliminators h : _ = env.eliminators)
  | «example» => rfl
  | mutualDef _ h _ =>
    exact (VEnv.addDefEqs_eliminators ..).trans (VEnv.addConsts_eliminators h)
  | quot _ h => exact VEnv.addQuot_eliminators h
  | induct _ h => cases h with | intro _ _ _ h => exact VInductBlock.install_eliminators h

/-- Fresh registration fixes a schema for every abstract block key. -/
theorem VEnv.WF.eliminators_unique (H : VEnv.WF env)
    (hleft : env.eliminators key left) (hright : env.eliminators key right) :
    left = right := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hleft
  | decl h _ ih =>
    rw [h.eliminators] at hleft hright
    exact ih hleft hright
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hleft hright
    exact ih hleft hright
  | inductEliminators _ _ _ _ _ _ hfresh _ _ ih =>
    rcases hleft with ⟨rfl, rfl⟩ | hleft
    · rcases hright with ⟨_, rfl⟩ | hright
      · rfl
      · exact (hfresh.1 _ hright).elim
    · rcases hright with ⟨rfl, rfl⟩ | hright
      · exact (hfresh.1 _ hleft).elim
      · exact ih hleft hright

theorem VEnv.WF.eliminators_originalFamilies_nodup (H : VEnv.WF env)
    (hlookup : env.eliminators key schema) : schema.originalFamilies.Nodup := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hlookup
  | decl h _ ih =>
    rw [h.eliminators] at hlookup
    exact ih hlookup
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hlookup
    exact ih hlookup
  | inductEliminators _ _ _ hformed _ _ _ _ _ ih =>
    rcases hlookup with ⟨_, rfl⟩ | hlookup
    · exact hformed.originalFamilies_nodup
    · exact ih hlookup

/-- A native family has one registered block and schema. In particular,
typed projection translation cannot choose another block's owner slot. -/
theorem VEnv.WF.eliminators_owner_unique (H : VEnv.WF env)
    (hleft : env.eliminators leftKey left) (hright : env.eliminators rightKey right)
    (hnameLeft : name ∈ left.originalFamilies)
    (hnameRight : name ∈ right.originalFamilies) : leftKey = rightKey ∧ left = right := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hleft
  | decl h _ ih =>
    rw [h.eliminators] at hleft hright
    exact ih hleft hright
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hleft hright
    exact ih hleft hright
  | inductEliminators _ _ _ _ _ _ hfresh _ _ ih =>
    rcases hleft with ⟨rfl, rfl⟩ | hleft
    · rcases hright with ⟨rfl, rfl⟩ | hright
      · exact ⟨rfl, rfl⟩
      · exact (hfresh.2 _ _ hright hnameLeft hnameRight).elim
    · rcases hright with ⟨rfl, rfl⟩ | hright
      · exact (hfresh.2 _ _ hleft hnameRight hnameLeft).elim
      · exact ih hleft hright

theorem VEnv.addConsts_le {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' → env ≤ env'
  | [], h => by cases h; exact .rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConsts_le h2)

theorem VEnv.addConst_eq_none {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

theorem VEnv.addConst_constants_eq {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') :
    env'.constants = fun n => if name = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

/-- A block of constants can be added as long as each name is fresh and the block has no
duplicates; the latter is what `addMutual`'s `found` set checks. -/
theorem VEnv.exists_addConsts {env : VEnv} : ∀ {cis : List VDefVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConsts cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConsts (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConsts, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

theorem VEnv.addConsts_congr {env : VEnv} : ∀ {cis cis' : List VDefVal},
    List.Forall₂ (fun a b => a.toVConstVal = b.toVConstVal) cis cis' →
    env.addConsts cis = env.addConsts cis'
  | [], [], _ => rfl
  | a :: _, b :: _, .cons h t => by
    have h1 : a.name = b.name := congrArg VConstVal.name h
    have h2 : a.toVConstant = b.toVConstant := congrArg VConstVal.toVConstant h
    show (env.addConst a.name a.toVConstant).bind _ = (env.addConst b.name b.toVConstant).bind _
    rw [h1, h2]
    cases env.addConst b.name b.toVConstant
    · rfl
    · exact VEnv.addConsts_congr t

theorem VEnv.addConsts_ordered {env env' : VEnv} : ∀ {cis}, Ordered env →
    (∀ ci ∈ cis, ci.toVConstant.WF env) → env.addConsts cis = some env' → Ordered env'
  | [], h, _, e => by cases e; exact h
  | _ :: _, h, hw, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine VEnv.addConsts_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (VEnv.addConst_le h1)

theorem VEnv.addConsts_constants {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' →
    ∀ ci ∈ cis, env'.constants ci.name = some ci.toVConstant
  | [], _, _, hc => nomatch hc
  | _ :: _, e, c, hc => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    cases hc with
    | head => exact (VEnv.addConsts_le h2).constants (VEnv.addConst_self h1)
    | tail _ hc => exact VEnv.addConsts_constants h2 c hc

theorem VEnv.addDefEqs_ordered : ∀ {env : VEnv} {cis}, Ordered env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) →
    (∀ ci ∈ cis, ci.WF env) → Ordered (env.addDefEqs cis)
  | _, [], h, _, _ => h
  | env, ci :: cis, h, hmem, hw => by
    have hci : ci.WF env := hw _ (.head _)
    have hord : Ordered (env.addDefEq ci.toDefEq) := by
      refine .defeq h ⟨?_, hci⟩
      simp [VDefVal.toDefEq]
      rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
      exact .const (hmem _ (.head _)) VLevel.id_WF (by simp)
    show Ordered ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine VEnv.addDefEqs_ordered hord (fun c hc => ?_) (fun c hc => ?_)
    · exact (VEnv.addDefEq_le (df := ci.toDefEq)).constants (hmem c (.tail _ hc))
    · exact (hw c (.tail _ hc)).mono VEnv.addDefEq_le

theorem VEnv.WF.ordered : WF env → Ordered env
  | ⟨ds, H⟩ => by
    induction H with
    | empty => exact .empty
    | inductEliminators _ _ _ _ _ _ _ _ _ ih => exact .eliminator ih
    | decl h _ ih =>
      cases h with
      | «axiom» h1 h2 => exact .const ih h1 h2
      | @«def» env env' ci h1 h2 =>
        refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
        · simp [VDefVal.toDefEq]
          rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
          exact .const (addConst_self h2) VLevel.id_WF (by simp)
        · exact h1.mono (addConst_le h2)
      | mutualDef h0 h1 h2 =>
        exact VEnv.addDefEqs_ordered (VEnv.addConsts_ordered ih h0 h1)
          (VEnv.addConsts_constants h1) h2
      | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
      | «example» _ => exact ih
      | quot h1 h2 => exact addQuot_WF ih h1 h2
      | induct h1 h2 => exact addInduct_WF ih h1 h2
    | inductProjections _ _ hsource htypesWF hconstructorUvars hctorsWF hparams hshape htypesSource
        hctorsSource hprojections htypes hctors ihBase ihCtors =>
      exact .inductProjections ihBase ihCtors hsource htypesWF hconstructorUvars hctorsWF hparams
        hshape htypesSource hctorsSource hprojections htypes hctors

/-- A dependency-ordered list of well-formed constants may be viewed as a
sequence of abstract axioms extending a well-formed environment.  Stating
the input typing in the original environment is sufficient because each
constant can be weakened through the preceding fresh additions. -/
theorem VEnv.WF.addConstVals
    {env env' : VEnv} {cis : List VConstVal}
    (Henv : env.WF)
    (Hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (Hadd : env.addConstVals cis = some env') : env'.WF := by
  induction cis generalizing env env' with
  | nil =>
    simp [VEnv.addConstVals] at Hadd
    subst env'
    exact Henv
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hci] at Hadd
    | some next =>
      simp [VEnv.addConstVals, hci] at Hadd
      have hhead : ci.toVConstant.WF env := Hwf ci (by simp)
      have Hnext : next.WF := by
        rcases Henv with ⟨ds, Hds⟩
        exact ⟨.axiom ci :: ds, .decl (.axiom hhead hci) Hds⟩
      apply ih Hnext (env' := env')
      · intro ci' hmem
        exact (Hwf ci' (by simp [hmem])).mono (VEnv.addConst_le hci)
      · exact Hadd

instance : CoeOut (VEnv.WF env) env.Ordered := ⟨(·.ordered)⟩
