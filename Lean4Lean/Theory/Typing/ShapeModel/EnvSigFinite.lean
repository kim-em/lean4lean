import Lean4Lean.Theory.Typing.Env

/-!
# Finitely many constants

Every `VEnv.WF'` environment declares finitely many constants. The semantic signature of the
shape model (`EnvSig.lean`) enumerates the constructors of a family as a list, chosen from a list
of all declared constant names.
-/

namespace Lean4Lean.ShapeModel
open VEnv

/-- `L` lists (at least) every declared constant of `env`. -/
def ConstList (env : VEnv) (L : List Name) : Prop := ∀ n ci, env.constants n = some ci → n ∈ L

theorem ConstList.addConst {env env' : VEnv} {L : List Name} (H : ConstList env L)
    (h : env.addConst name ci = some env') : ConstList env' (name :: L) := by
  intro n ci' hn
  unfold VEnv.addConst at h
  split at h
  · cases h
  · cases h
    simp only at hn
    split at hn
    · rename_i he; exact he ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (H _ _ hn)

theorem ConstList.addConstVals {env env' : VEnv} {L : List Name} {cis : List VConstVal}
    (H : ConstList env L) (h : env.addConstVals cis = some env') :
    ConstList env' (cis.map (·.name) ++ L) := by
  induction cis generalizing env L with
  | nil =>
    simp only [VEnv.addConstVals, Option.some.injEq] at h
    subst h; simpa using H
  | cons ci cis ih =>
    simp only [VEnv.addConstVals, bind, Option.bind_eq_some_iff] at h
    obtain ⟨e1, h1, h2⟩ := h
    have := ih (H.addConst h1) h2
    intro n c hn
    have := this _ _ hn
    simp only [List.mem_append, List.mem_map, List.mem_cons] at this ⊢
    rcases this with ⟨a, ha, rfl⟩ | rfl | h
    · exact .inl ⟨a, .inr ha, rfl⟩
    · exact .inl ⟨ci, .inl rfl, rfl⟩
    · exact .inr h

theorem ConstList.addConsts {env env' : VEnv} {L : List Name} {cis : List VDefVal}
    (H : ConstList env L) (h : env.addConsts cis = some env') :
    ConstList env' (cis.map (·.name) ++ L) := by
  induction cis generalizing env L with
  | nil =>
    simp only [VEnv.addConsts, List.foldlM, Option.pure_def, Option.some.injEq] at h
    subst h; simpa using H
  | cons ci cis ih =>
    simp only [VEnv.addConsts, List.foldlM, bind, Option.bind_eq_some_iff] at h
    obtain ⟨e1, h1, h2⟩ := h
    have := ih (H.addConst h1) h2
    intro n c hn
    have := this _ _ hn
    simp only [List.mem_append, List.mem_map, List.mem_cons] at this ⊢
    rcases this with ⟨a, ha, rfl⟩ | rfl | h
    · exact .inl ⟨a, .inr ha, rfl⟩
    · exact .inl ⟨ci, .inl rfl, rfl⟩
    · exact .inr h

theorem ConstList.of_constants {env env' : VEnv} {L : List Name} (H : ConstList env L)
    (h : env'.constants = env.constants) : ConstList env' L := fun _ _ hn => H _ _ (h ▸ hn)

theorem addDefEqs_constants' {env : VEnv} {cis : List VDefVal} :
    (env.addDefEqs cis).constants = env.constants := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem ConstList.install {env env' : VEnv} {L : List Name} {block : VInductBlock}
    (H : ConstList env L) (h : block.install env = some env') :
    ∃ L', ConstList env' L' := by
  simp only [VInductBlock.install, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at h
  obtain ⟨e1, h1, e2, h2, e3, h3, rfl⟩ := h
  have H1 := H.addConstVals h1
  have H2 := H1.addConstVals h2
  have H2' : ConstList (e2.addProjections block.projections) _ :=
    H2.of_constants (VEnv.addProjections_constants _ _)
  exact ⟨_, (H2'.addConstVals h3).of_constants (VEnv.addDefEqRules_constants _ _)⟩

theorem ConstList.addQuot {env env' : VEnv} {L : List Name}
    (H : ConstList env L) (h : env.addQuot = some env') : ∃ L', ConstList env' L' := by
  simp only [VEnv.addQuot, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, rfl⟩ := h
  exact ⟨_, ((((H.addConst h1).addConst h2).addConst h3).addConst h4).of_constants rfl⟩

/-- A `VEnv.WF'` environment declares finitely many constants. -/
theorem WF'.constList {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    ∃ L, ConstList env L := by
  induction H with
  | empty => exact ⟨[], fun _ _ h => by cases h⟩
  | decl hdecl _ ih =>
    obtain ⟨L, hL⟩ := ih
    cases hdecl with
    | «axiom» _ h => exact ⟨_, hL.addConst h⟩
    | «def» _ h => exact ⟨_, (hL.addConst h).of_constants rfl⟩
    | mutualDef _ h _ => exact ⟨_, (hL.addConsts h).of_constants addDefEqs_constants'⟩
    | «opaque» _ h => exact ⟨_, hL.addConst h⟩
    | «example» => exact ⟨_, hL⟩
    | quot _ h => exact hL.addQuot h
    | induct _ h =>
      cases h with
      | intro _ _ _ hinst => exact hL.install hinst
  | inductEliminators _ _ _ _ _ _ _ _ ih => exact ih
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L, hL.of_constants (VEnv.addProjections_constants _ _)⟩

theorem WF.constList {env : VEnv} (H : env.WF) : ∃ L, ConstList env L :=
  WF'.constList H.choose_spec

end Lean4Lean.ShapeModel
