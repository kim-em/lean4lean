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

theorem takeForalls_wrapForalls' : ∀ {n : Nat} {e r : VExpr} {ds : List VExpr},
    e.takeForalls n = some (ds, r) → e = VExpr.wrapForalls ds r ∧ ds.length = n
  | 0, e, r, ds, h => by
    cases Option.some.inj h
    exact ⟨rfl, rfl⟩
  | n + 1, e, r, ds, h => by
    cases e with
    | forallE dom body =>
      cases hb : body.takeForalls n with
      | none => simp [VExpr.takeForalls, hb] at h
      | some out =>
        rw [VExpr.takeForalls, hb] at h
        cases Option.some.inj h
        obtain ⟨h1, h2⟩ := takeForalls_wrapForalls' hb
        exact ⟨congrArg (VExpr.forallE dom) h1, by simp [h2]⟩
    | _ => simp [VExpr.takeForalls] at h

/-- A family whose header shape is derived (as a declaration header) in a good environment has a
semantic header; the family itself may be declared later. -/
theorem famSem_of_typeShape (H : env.WF) (h : Good env E) (hle : E ≤ env) (hE : E.Ordered)
    {decl : VInductDecl} {params : List VExpr} {t : VInductiveType}
    (hshape : decl.TypeShape E params t) (huv : t.uvars = decl.uvars)
    (hc : env.constants t.name = some t.toVConstant) :
    letI := envSig env; FamSem env t.name t.resultLevel (decl.nparams + t.numIndices) := by
  letI := envSig env
  obtain ⟨normalized, ownParams, afterParams, indices, result, exprType, htype, hparams,
    hindices, _, hresult⟩ := hshape
  obtain ⟨hn, hnl⟩ := takeForalls_wrapForalls' hparams
  obtain ⟨ha, hal⟩ := takeForalls_wrapForalls' hindices
  have h1 : E.IsDefEq decl.uvars [] t.type (VExpr.wrapForalls (ownParams ++ indices) result)
      exprType := by
    rw [VExpr.wrapForalls_append, ← ha, ← hn]; exact htype
  have h2 : E.IsDefEq decl.uvars (ownParams ++ indices).reverse result (.sort t.resultLevel)
      (.sort t.resultLevel.succ) := by simpa [List.reverse_append] using hresult
  have hctx : OnCtx ((ownParams ++ indices).reverse ++ []) (E.IsType decl.uvars) :=
    hasType_wrapForalls_inv hE (Γ := []) trivial h1.hasType.2
  obtain ⟨_, hw⟩ := wrapForalls_congr_body' (Γ := []) hctx (by simpa using h2)
  refine ⟨t.toVConstant, ownParams ++ indices, hc, by simp [hnl, hal], fun ls hls m => ?_⟩
  exact (h.sound_nil_instL H hle hE h1 ls m).trans (h.sound_nil_instL H hle hE hw ls m)

/-- Validity of the generic equations of one eliminator registration. -/
def ElimOK (env : VEnv) [SemSig] (block : Name) (schema : CaseSchema) : Prop :=
  ∀ {owner : Fin schema.signature.families.size} {rules : List VDefEq} {df : VDefEq}
    {U : Nat} {levels : List VLevel} {target : VLevel} {Γ : List VExpr} {typeLevel : VLevel},
    schema.genericEquations block owner = some rules →
    df ∈ rules → InductiveSignature.CaseSchema.RuleClosed df →
    schema.Permission U owner levels target →
    StrongSound env Γ (df.type.instL (target :: levels)) (.sort typeLevel) →
    StrongSound env Γ (df.lhs.instL (target :: levels)) (df.type.instL (target :: levels)) →
    StrongSound env Γ (df.rhs.instL (target :: levels)) (df.type.instL (target :: levels)) →
    SoundEq env [] (df.lhs.instL (target :: levels)) (df.rhs.instL (target :: levels))

end

end Lean4Lean.ShapeModel
