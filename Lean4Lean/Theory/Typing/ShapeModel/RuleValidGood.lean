import Lean4Lean.Theory.Typing.ShapeModel.RuleValidCtor
import Lean4Lean.Theory.Typing.ShapeModel.Separation

/-!
# Soundness for earlier environments of a history

`Good env E`: the computation rules, eliminators and structures of `E` are valid in the shape
model of `env` (for the semantic signature `envSig env`). Then every strong derivation in an
environment below `E` (and below `env`) is sound in that model (`Good.sound`). The validity of the
rules of `env` is proved by induction along the history that built its tables
(`RuleValidHistory.lean`); at each step the new rules are validated using soundness for the
earlier environments of the step, through `Good.sound`.

Also: the semantic family headers (`FamSem`) of families whose header derivation lives in a good
environment (`famSem_of_famShape`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

/-- The rules, eliminators and structures of `E` are valid in the shape model of `env`. -/
def Good (env E : VEnv) : Prop :=
  letI := envSig env
  (∀ df, E.defeqs df → ExtraValid env df) ∧ ElimValidIn E env ∧
    ∀ {s info}, E.projections s info → FamTypeSem env s info

theorem Good.mono (h : Good env E) (hle : E' ≤ E) : Good env E' :=
  letI := envSig env
  ⟨fun df hdf => h.1 df (hle.defeqs hdf), fun hb => h.2.1 (hle.eliminators hb),
    fun hp => h.2.2 (hle.projections hp)⟩

/-- Soundness of strong derivations in a good environment below `env`. -/
theorem Good.sound (H : env.WF) (h : Good env E) (hle : E ≤ env) (hE : E.Ordered)
    (D : E.IsDefEqStrong U Γ M N A) : letI := envSig env; StrongSoundEq env Γ M N A := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  exact StrongSoundEq.of_isDefEqStrong hle (envSig_envFactsIn_of_wf H hle h.2.2)
    (fun _ hdf => ⟨(hE.closed.2 hdf).1.1, (hE.closed.2 hdf).2.1⟩) h.1 h.2.1 D

/-- Soundness of derivations in the empty context in a good environment. -/
theorem Good.sound_nil (H : env.WF) (h : Good env E) (hle : E ≤ env) (hE : E.Ordered)
    (D : E.IsDefEq U [] M N A) :
    letI := envSig env; ∀ m, Interp env .nil m M ↔ Interp env .nil m N := by
  letI := envSig env
  exact fun m => (h.sound H hle hE (VEnv.IsDefEq.strong hE (Γ := []) trivial D)).sound Valuation.Fits.nil

/-! ### Universe levels -/

/-- An upper bound of the universe parameters of a level. -/
def levelBound : VLevel → Nat
  | .zero => 0
  | .succ l => levelBound l
  | .max l₁ l₂ => max (levelBound l₁) (levelBound l₂)
  | .imax l₁ l₂ => max (levelBound l₁) (levelBound l₂)
  | .param i => i + 1

theorem wf_of_levelBound : ∀ {l : VLevel} {U : Nat}, levelBound l ≤ U → l.WF U
  | .zero, _, _ => trivial
  | .succ l, _, h => wf_of_levelBound (l := l) h
  | .max _ _, _, h => ⟨wf_of_levelBound (Nat.le_trans (Nat.le_max_left _ _) h),
      wf_of_levelBound (Nat.le_trans (Nat.le_max_right _ _) h)⟩
  | .imax _ _, _, h => ⟨wf_of_levelBound (Nat.le_trans (Nat.le_max_left _ _) h),
      wf_of_levelBound (Nat.le_trans (Nat.le_max_right _ _) h)⟩
  | .param i, _, h => by simp only [levelBound] at h; exact h

theorem level_wf_mono : ∀ {l : VLevel} {U U' : Nat}, l.WF U → U ≤ U' → l.WF U'
  | .zero, _, _, _, _ => trivial
  | .succ l, _, _, h, hu => level_wf_mono (l := l) h hu
  | .max _ _, _, _, h, hu => ⟨level_wf_mono h.1 hu, level_wf_mono h.2 hu⟩
  | .imax _ _, _, _, h, hu => ⟨level_wf_mono h.1 hu, level_wf_mono h.2 hu⟩
  | .param _, _, _, h, hu => Nat.lt_of_lt_of_le h hu

theorem exists_levels_wf : ∀ ls : List VLevel, ∃ U, ∀ l ∈ ls, l.WF U
  | [] => ⟨0, nofun⟩
  | x :: xs => by
    obtain ⟨U, hU⟩ := exists_levels_wf xs
    refine ⟨max (levelBound x) U + U, fun l hl => ?_⟩
    rcases List.mem_cons.1 hl with rfl | h
    · exact wf_of_levelBound (by omega)
    · have := hU l h
      exact level_wf_mono this (by omega)

/-- Soundness of a derivation of the empty context at universe parameters `U`, instantiated at
arbitrary levels. -/
theorem Good.sound_nil_instL (H : env.WF) (h : Good env E) (hle : E ≤ env) (hE : E.Ordered)
    (D : E.IsDefEq U [] M N A) (ls : List VLevel) :
    letI := envSig env; ∀ m, Interp env .nil m (M.instL ls) ↔ Interp env .nil m (N.instL ls) := by
  obtain ⟨U', hU'⟩ := exists_levels_wf ls
  have := D.instL hU'
  exact h.sound_nil H hle hE (by simpa using this)

/-! ### Semantic family headers -/

/-- A family whose header shape is derived in a good environment has a semantic header. -/
theorem famSem_of_famShape (H : env.WF) (h : Good env E) (hle : E ≤ env) (hE : E.Ordered)
    (hshape : FamShape E I d) :
    letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices) := by
  letI := envSig env
  obtain ⟨ci, hci, huv, doms, result, type, h1, hlen, h2⟩ := hshape
  have hctx := hasType_wrapForalls_inv hE (Γ := []) trivial h1.hasType.2
  obtain ⟨_, hw⟩ := wrapForalls_congr_body' (Γ := []) (by simpa using hctx) (by simpa using h2)
  refine ⟨ci, doms, hle.constants hci, hlen, fun ls hls m => ?_⟩
  rw [huv] at hls
  exact (h.sound_nil_instL H hle hE h1 ls m).trans (h.sound_nil_instL H hle hE hw ls m)

end

end Lean4Lean.ShapeModel
