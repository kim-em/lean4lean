import Lean4Lean.Theory.Typing.EnvLemmas

/-! # A well-formed history with its stages

`VEnv.WFH ds hs env` is a well-formedness derivation `VEnv.WF' ds env` that records, in `hs`
(latest first), the environment every declaration step starts from (a constructor-and-projection
prefix, `VEnv.WF'.inductProjections`, is not listed). A chosen such history of an
environment (`VEnv.stages`) pins the recursor registry of the confluence engine to one
installation order: its stages are well-formed prefixes of the environment, totally ordered by
extension (`VEnv.WFH.chain`). The coverage of the registered ι rules is proved by induction along
it. -/

namespace Lean4Lean

/-- A well-formedness derivation recording the environment each declaration step starts from. -/
inductive VEnv.WFH : List VDecl → List VEnv → VEnv → Prop where
  | empty : VEnv.WFH [] [] .empty
  | decl {env env' : VEnv} {d : VDecl} {ds : List VDecl} {hs : List VEnv} :
    VDecl.WF env d env' → env.WF' ds → VEnv.WFH ds hs env → VEnv.WFH (d :: ds) (env :: hs) env'
  | inductProjections {env env' : VEnv} {decl : VInductDecl} {ds : List VDecl} {hs : List VEnv} :
    decl.ProjectionStage env env' → env.WF' ds → VEnv.WFH ds hs env →
    VEnv.WFH (.induct decl :: ds) hs env'

namespace VEnv

theorem WF'.wfh {ds : List VDecl} {env : VEnv} (H : env.WF' ds) : ∃ hs, env.WFH ds hs := by
  induction H with
  | empty => exact ⟨[], .empty⟩
  | decl hd hds ih => obtain ⟨hs, h⟩ := ih; exact ⟨_, .decl hd hds h⟩
  | inductProjections hstage hds ih =>
    obtain ⟨hs, h⟩ := ih; exact ⟨hs, .inductProjections hstage hds h⟩

/-- The stages of a well-formed history are well-formed prefixes of the environment. -/
theorem WFH.stage {ds : List VDecl} {hs : List VEnv} {env : VEnv} (H : env.WFH ds hs)
    {e : VEnv} (he : e ∈ hs) : e.WF ∧ env.WFPrefix e := by
  induction H with
  | empty => cases he
  | decl hd hds _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨⟨_, hds⟩, .decl hd .rfl⟩
    · obtain ⟨h1, h2⟩ := ih he; exact ⟨h1, .decl hd h2⟩
  | inductProjections hstage _ _ ih =>
    obtain ⟨h1, h2⟩ := ih he; exact ⟨h1, .inductProjections hstage h2⟩

/-- The stages of a history are below the environment. -/
theorem WFH.stage_le {ds : List VDecl} {hs : List VEnv} {env : VEnv} (H : env.WFH ds hs)
    {e : VEnv} (he : e ∈ hs) : e ≤ env := (H.stage he).2.le

/-- **The stages of a history are totally ordered by extension**: a later stage (smaller index)
extends an earlier one. -/
theorem WFH.chain {ds : List VDecl} {hs : List VEnv} {env : VEnv} (H : env.WFH ds hs) :
    ∀ {i j : Nat} (hi : i < hs.length) (hj : j < hs.length), i ≤ j → hs[j] ≤ hs[i] := by
  induction H with
  | empty => intro i j hi; simp at hi
  | decl hd hds H ih =>
    intro i j hi hj hij
    cases i with
    | zero =>
      cases j with
      | zero => exact .rfl
      | succ j => exact H.stage_le (List.getElem_mem _)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih (by simpa using hi) (by simpa using hj) (by omega)
  | inductProjections _ _ _ ih => exact ih

open Classical in
/-- A chosen history of an environment: its stages, latest first (empty if the environment is
not well-formed). -/
noncomputable def stages (env : VEnv) : List VEnv :=
  if h : ∃ p : List VDecl × List VEnv, env.WFH p.1 p.2 then (Classical.choose h).2 else []

theorem WF.stagesH {env : VEnv} (henv : env.WF) : ∃ ds, env.WFH ds env.stages := by
  have h : ∃ p : List VDecl × List VEnv, env.WFH p.1 p.2 := by
    obtain ⟨ds, H⟩ := henv
    obtain ⟨hs, h⟩ := H.wfh
    exact ⟨(ds, hs), h⟩
  unfold stages
  rw [dif_pos h]
  exact ⟨_, Classical.choose_spec h⟩

end VEnv
end Lean4Lean
