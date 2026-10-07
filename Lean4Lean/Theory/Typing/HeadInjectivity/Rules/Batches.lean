import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Definitions

/-! # Rule batches: rules sharing a head constant come from one declaration

`VEnv.WF'.sameHead`: two installed rules whose left-hand sides are headed by the same constant
belong to one batch of rules installed by a single declaration: a definition's delta rule,
the delta rules of a mutual block, the quotient rule, or the restored equations of one finite
inductive compilation. Proved by induction on the declaration history as in
`Rules/Definitions.lean`: every new rule is headed by a constant installed by the same
declaration, hence absent before, while the heads of old rules are old constants. -/

namespace Lean4Lean
open InductiveSignature
open private addDefEqs_as_rules addConsts_as_values defeqs_addRules
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity

namespace VEnv

/-- The rules installed by one declaration. -/
inductive RuleBatch : List VDefEq → Prop
  | mutual (cis : List VDefVal) : RuleBatch (cis.map (·.toDefEq))
  | quot : RuleBatch [quotDefEq]
  | native {base : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
      {g : Instance s} {aux : List ContainerSpecialization} {block : VInductBlock} :
      CompilationData base source expanded s g aux block → RuleBatch block.rules

/-- Rules with a common head constant lie in one batch. -/
def SameHead (env : VEnv) : Prop :=
  ∀ df df', env.defeqs df → env.defeqs df' → ∀ n ls ls',
    df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
    df'.lhs.stripLams.getAppFnArgs.1 = .const n ls' →
    ∃ rs, RuleBatch rs ∧ df ∈ rs ∧ df' ∈ rs

theorem SameHead.extend {env env' : VEnv} {new : List VDefEq} (H : env.SameHead)
    (hord : env.Ordered)
    (hdefeqs : ∀ df, env'.defeqs df ↔ df ∈ new ∨ env.defeqs df)
    (hbatch : RuleBatch new)
    (hfresh : ∀ df ∈ new, ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      env.constants n = none) :
    env'.SameHead := by
  have oldHead : ∀ df, env.defeqs df → ∀ n ls,
      df.lhs.stripLams.getAppFnArgs.1 = .const n ls → ∃ ci, env.constants n = some ci :=
    fun df hdf n ls h => (hord.defEqWF hdf).1.head_const_lookup hord (Γ := []) ⟨⟩ h
  intro df df' hdf hdf' n ls ls' h h'
  rcases (hdefeqs df).1 hdf with hm | ho <;> rcases (hdefeqs df').1 hdf' with hm' | ho'
  · exact ⟨new, hbatch, hm, hm'⟩
  · obtain ⟨_, hc⟩ := oldHead df' ho' n ls' h'
    rw [hfresh df hm n ls h] at hc; cases hc
  · obtain ⟨_, hc⟩ := oldHead df ho n ls h
    rw [hfresh df' hm' n ls' h'] at hc; cases hc
  · exact H df df' ho ho' n ls ls' h h'

theorem RuleBatch.nil : RuleBatch [] := RuleBatch.mutual []

theorem WF'.sameHead {env : VEnv} (H : env.WF' ds) : env.SameHead := by
  induction H with
  | empty => intro df; nofun
  | @decl d env' ds env hdecl hbase ih =>
    have hord := (show env.WF from ⟨ds, hbase⟩).ordered
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      exact ih.extend hord (new := [])
        (fun df => by rw [VEnv.addConst_defeqs hadd]; simp) .nil nofun
    | «example» => exact ih
    | @«def» env₁ _ ci _ hadd =>
      have hnone : env.constants ci.name = none := by
        unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; assumption
      refine ih.extend hord (new := [ci.toDefEq])
        (fun df => by rw [defeqs_addDefEq, VEnv.addConst_defeqs hadd]) (RuleBatch.mutual [ci]) ?_
      intro df hm n ls h
      simp only [List.mem_singleton] at hm; subst hm
      cases h; exact hnone
    | @mutualDef cis env₁ _ _ hadd _ =>
      rw [addConsts_as_values] at hadd
      rw [addDefEqs_as_rules]
      refine ih.extend hord (new := cis.map (·.toDefEq))
        (fun df => by rw [defeqs_addRules, VEnv.addConstVals_defeqs hadd]) (.mutual cis) ?_
      intro df hm n ls h
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
      cases h
      exact addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci)
    | quot _ installed =>
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
      refine ih.extend hord (new := [quotDefEq])
        (fun df => by
          rw [defeqs_addDefEq, VEnv.addConst_defeqs he, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha]) .quot ?_
      intro df hm n ls h
      simp only [List.mem_singleton] at hm; subst hm
      have hn : n = ``Quot.lift := by cases h; rfl
      subst hn
      have hnone : b.constants ``Quot.lift = none := by
        unfold VEnv.addConst at hc; split at hc <;> cases hc; assumption
      cases h' : env.constants ``Quot.lift with
      | none => rfl
      | some ci =>
        have := (VEnv.addConst_le hb).constants <| (VEnv.addConst_le ha).constants h'
        rw [this] at hnone; cases hnone
    | induct _ installed =>
      cases installed with
      | @intro block _ _ compiled _ installed =>
        obtain ⟨base, expanded, signature, generated, auxiliaries, _, compilation, _⟩ :=
          compiled.compiled.compilationOrigin
        have howned := compiled.compiled.equation_head_owned
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at installed
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := installed
        refine ih.extend hord (new := block.rules)
          (fun df => by
            rw [defeqs_addRules, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
              VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht]) (.native compilation) ?_
        intro df hm n ls h
        obtain ⟨recursor, hrec, ls', hhead⟩ := howned df hm
        have hn : recursor.name = n := (VExpr.const.inj (hhead.symm.trans h)).1
        subst hn
        have hfresh := addConstVals_names_fresh hr recursor hrec
        cases h' : env.constants recursor.name with
        | none => rfl
        | some ci =>
          have := (addConstVals_le hc).constants ((addConstVals_le ht).constants h')
          simp only [VEnv.addProjections_constants] at hfresh
          rw [this] at hfresh; cases hfresh
  | inductEliminators _ _ _ _ _ _ _ _ ih => exact ih
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro df df' hdf hdf'
    exact ih df df' (by simpa using hdf) (by simpa using hdf')

theorem WF.sameHead {env : VEnv} (H : env.WF) : env.SameHead :=
  let ⟨_, H⟩ := H; H.sameHead

end VEnv
end Lean4Lean
