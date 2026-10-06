import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.ShapeModel.Sound.Struct

/-!
# Soundness of the shape model for every rule of `VEnv.IsDefEq`

Main result: `StrongSoundEq.of_isDefEqStrong`. For every strong derivation
`E ⊢ Γ ⊢ M ≡ N : A` in an environment `E ≤ env`, `M` and `N` have the same approximations under
every valuation fitting `Γ`, and every approximation of either is below one typed at an
approximation of `A` (`StrongSoundEq env Γ M N A`), in the shape model of `env` read through a
coherent semantic signature `S`. Corollary at the base valuation: `sound_nil`.

The hypotheses, to be discharged for real environments by later milestones:
* `SemSig.Coherent` (from the interpretation, `Signature.lean`);
* `S.EnvFactsIn E env` (`Sound/Ctor.lean`): constant types of `env` are closed, the generic
  types of the eliminators of `E` are the signature's `elimType`, and the structure facts
  `SemSig.StructFacts` (`Sound/Basic.lean`) hold for every projection registered in `E`;
* closedness of the rules of `E` (`∀ df, E.defeqs df → df.lhs.Closed ∧ df.rhs.Closed`), used to
  move the validity of a rule from the empty context to `Γ`;
* `ExtraValid env df` for every rule of `E` and `ElimValidIn E env`: the validity of the
  computation rules of `E` in the model. These are the only places where computation rules
  enter.
Only `ConstClosed env` is asked of all of `env`; everything else is asked only of the
derivation environment `E`, so that soundness for derivations in an earlier environment of a
`VEnv.WF'` chain needs no facts about the later declarations
(`docs/inductives/PHASE1_NOTES.md`, D9). `StrongSoundEq.of_isDefEqStrong_global` is the form
with the facts asked of all of `env` (`SemSig.EnvFacts env`, `ElimValid env`).

The port follows `Lean4Lean/Experimental/ShapeLogRel.lean` (`LE_Interp.strongSound`). The
structural record `StrongSoundCore` (`Sound/Basic.lean`) has informative cases only for
applications, constants, Pi types and projections; its other cases accept any type.

Deviations from the milestone specification, with rationale:
* Shape typing of constructors (`ShapeTyping.lean`) now requires the declared number of fields
  (`ShapeParams.nfields`). Without it, structure eta is unsound in the model: a constructor shape
  with too few fields is typed at the structure, so it can be the value of a variable `e` of the
  structure type, but the approximations of the eta expansion of `e` are constructor shapes with
  exactly the declared number of fields.
* `StrongSoundEq` has no syntactic `defeq` component (the prototype's was only used for its
  transitivity rule with different types, which `IsDefEqStrong` does not have).
* The closedness of the rules of `E` is a separate hypothesis.
* `ElimValid` takes the semantic records of its premises in an arbitrary context `Γ` (the premises
  of `elimIota` are typed in `Γ`, not in the empty context); its conclusion is in the empty
  context, which is equivalent for the closed rule instances (`SoundEq.of_closed`).
* `SemSig.StructFacts` (the projection part of `S.EnvFactsIn E env`) records, besides the facts
  listed in the specification, that the structure constructor is declared with the projection
  data's constructor type, that this type is a telescope over the parameters and fields ending in
  the structure applied to the parameter variables and index expressions, and that the structure
  itself is a rigid former (not a constructor, heading no rule) whose type has the
  approximations of a telescope ending in its sort `S.famLevel` (`famTypeSem`; D8). These are used to realize constructor applications as constructor
  shapes typed at a rigid shape of the structure (`Ctor.realize`). The projection guard
  (`IsNeverZero ∨ fieldLevel ≈ 0`) is not needed for the typing of projections; it is used by
  the projection computation rule, through the structural record of the projection.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

variable (env) in
/-- Validity of a definitional rule `df` in the model: at every level instance, if its type,
left-hand side and right-hand side have semantic typing records in the empty context (the
premises of the `extra` rule), then both sides have the same approximations. -/
def ExtraValid [SemSig] (df : VDefEq) : Prop :=
  ∀ ls u, ls.length = df.uvars →
    StrongSound env [] (df.type.instL ls) (.sort u) →
    StrongSound env [] (df.lhs.instL ls) (df.type.instL ls) →
    StrongSound env [] (df.rhs.instL ls) (df.type.instL ls) →
    SoundEq env [] (df.lhs.instL ls) (df.rhs.instL ls)

/-- Validity of the computation rules of the eliminators of `E` in the model of `env`: for every
instance of the `elimIota` rule of an eliminator of `E` whose type, left-hand side and right-hand
side have semantic typing records (the premises of `elimIota`), both sides have the same
approximations. -/
def ElimValidIn [SemSig] (E env : VEnv) : Prop :=
  ∀ {block : Name} {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq} {df : VDefEq}
    {U : Nat} {levels : List VLevel} {target : VLevel} {Γ : List VExpr} {typeLevel : VLevel},
    E.eliminators block schema → schema.genericEquations block owner = some rules →
    df ∈ rules → InductiveSignature.CaseSchema.RuleClosed df →
    schema.Permission U owner levels target →
    StrongSound env Γ (df.type.instL (target :: levels)) (.sort typeLevel) →
    StrongSound env Γ (df.lhs.instL (target :: levels)) (df.type.instL (target :: levels)) →
    StrongSound env Γ (df.rhs.instL (target :: levels)) (df.type.instL (target :: levels)) →
    SoundEq env [] (df.lhs.instL (target :: levels)) (df.rhs.instL (target :: levels))

/-- Validity of the computation rules of every eliminator of `env`. -/
abbrev ElimValid [SemSig] (env : VEnv) : Prop := ElimValidIn env env

theorem ElimValidIn.mono [SemSig] {E E' env : VEnv} (hle : E ≤ E') (h : ElimValidIn E' env) :
    ElimValidIn E env := fun hb => h (hle.eliminators hb)

/-- Closed terms with the same approximations at the base valuation of the empty context have
the same approximations under every valuation. -/
theorem SoundEq.of_closed (hM : M.Closed) (hN : N.Closed) (H : SoundEq env [] M N) :
    SoundEq env Γ M N := fun _ _ _ _ =>
  (Interp.closed_iff hM).trans ((H .nil).trans (Interp.closed_iff hN))

theorem SoundTy.bvar (h : Lookup Γ i A) : SoundTy env Γ (.bvar i) A := by
  intro Γ₀ ρ W m H
  have a1 := Interp.bvar_iff.1 H; clear H
  induction W generalizing i A m with
  | nil => exact .of_le_bot (a1.trans TShape.bot_le)
  | cons _ h1 h2 h3 ih =>
    cases h with
    | zero => exact ⟨_, _, a1, .bvar', h2.weak, h3⟩
    | succ h =>
      have ⟨_, _, le, b1, b2, b3⟩ := ih h a1
      exact ⟨_, _, le, by simpa [VExpr.liftN] using b1.weak, b2.weak, b3⟩

theorem TShape.HasType.sort_sort {r j : SLvl} (h : ¬j.IsZero) :
    (TShape.sort r).HasType (TShape.sort j) := (WShape.HasType.sort (n := 0) h).T

theorem SoundTy.sort : SoundTy env Γ (.sort l) (.sort (.succ l)) := fun _ _ _ _ H =>
  ⟨_, _, H.le_sort, .sort', .sort', TShape.HasType.sort_sort fun h => by
    have := h []; simp [VLevel.eval] at this⟩

/-- Assemble a `StrongSoundEq` from the soundness of the definitional equality, the typing of
the left-hand side and the structural records of both sides. -/
theorem StrongSoundEq.ofLeft (hs : SoundEq env Γ M N) (ht : SoundTy env Γ M A)
    (cM : StrongSoundCore env Γ M A₁) (eM : SoundEq env Γ A₁ A)
    (cN : StrongSoundCore env Γ N A₂) (eN : SoundEq env Γ A₂ A) : StrongSoundEq env Γ M N A :=
  ⟨hs, ⟨ht, cM, eM⟩, ⟨ht.defeq_l hs, cN, eN⟩⟩

theorem VLevel.equiv_symm' {a b : VLevel} (h : a ≈ b) : b ≈ a :=
  VLevel.equiv_def'.2 (VLevel.equiv_def'.1 h).symm

theorem Interp.eta_sound (W : Valuation.Fits env Γ₀ Γ ρ)
    (hlam : SoundTy env Γ (.lam A (.app F.lift (.bvar 0))) (.forallE A B))
    (he : SoundTy env Γ F (.forallE A B)) :
    Interp env ρ m (.lam A (.app F.lift (.bvar 0))) ↔ Interp env ρ m F := by
  by_cases hm : m ≤ .bot; · exact ⟨fun _ => .mono hm .bot, fun _ => .mono hm .bot⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have ⟨e, t, h1, h2, h3, h4⟩ := hlam W h
    have ht : ¬t ≤ .bot := fun h => hm (h1.trans (h4.bot_r' h))
    cases h2 with
    | bot => cases hm (h1.trans TShape.bot_le')
    | @lam n _ _ _ _ _ f' h2a h2d h2f h2le
    cases h3 with | bot => cases ht TShape.bot_le' | forallE b1 b2 b3 b4 b5
    cases b5.le_forall with | bot b5 => cases ht b5 | forallE b5 b6
    obtain rfl | ⟨n₂, g, rfl, c1⟩ := h4.ty_forallE_inv; · cases hm (h1.trans TShape.bot_le')
    have key {x y} (hmem : (x, y) ∈ f') :
        Interp env ρ (WShape.T (n := n+1) (.lam' (WShapeFun.single x y))) F := by
      by_cases hy : y ≤ .bot
      · refine .mono (WShape.LE.T (?_ : _ ≤ .bot)) .bot
        rw [← WShape.lam'_bot, WShape.lam'_le_lam', WShapeFun.single_le]
        exact ⟨_, _, by simp [WShapeFun.mem_bot], WShape.bot_le, hy⟩
      rw [WShape.le_bot] at hy
      obtain ⟨x', x'le, x'ht, x'app⟩ := WShape.HasDom.iff.1 h2d x
      have := (h2f x' x'ht)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, x'le.T⟩)
        |>.mono (WShape.LE.T <| (WShapeFun.app_of_mem hmem).2.trans x'app)
      cases this with | bot => cases hy rfl | @app n' _ _ _ _ f a' c1 c2 c3
      cases f using WShape.casesOn' with
      | lam g => ?_
      | _ => cases hy (TShape.le_bot.1 (c3.trans TShape.bot_le'))
      obtain ⟨x'', hle, mem⟩ := WShapeFun.app_eq g a'
      have le₁ := Nat.le_max_left n' n; have le₂ := Nat.le_max_right n' n
      refine (Interp.weak_iff.1 c1).mono ?_
      refine (TShape.LE.def (Nat.succ_le_succ le₂) (Nat.succ_le_succ le₁)).2 ?_
      rw [WShape.lift_lam' le₂, WShapeFun.lift_single le₂, WShape.lam_eq_lam',
        WShape.lift_lam' le₁, WShape.lam'_le_lam', WShapeFun.single_le]
      exact ⟨_, _, (WShapeFun.mem_lift le₁).2 ⟨_, _, mem, rfl, rfl⟩,
        hle.T.trans (Interp.bvar_iff.1 c2), (TShape.LE.def le₂ le₁).1 c3⟩
    have main (l : List (WShape n × WShape n)) (H : ∀ p, p ∈ l → p ∈ f') :
        ∃ g, (∀ z : WShapeFun n, g ≤ z ↔ ∀ x ∈ l, .single x.1 x.2 ≤ z) ∧
          Interp env ρ (WShape.T (.lam' g)) F := by
      induction l with | nil => exact ⟨.bot, by simp, WShape.lam'_bot ▸ .bot⟩ | cons p l ih
      obtain ⟨x, y⟩ := p; simp only [List.mem_cons, forall_eq_or_imp] at H
      have ⟨g, a1, a2⟩ := ih H.2
      have hc := (key H.1).compat a2
      have hJ := WShapeFun.Join.mk <| WShape.Compat.lam'.1 <| WShape.Compat.T_iff.2 hc
      refine ⟨_, fun z => (hJ _).trans <| .trans ?_ List.forall_mem_cons.symm, ?_⟩
      · exact and_congr_right' (a1 _)
      · exact (key H.1).join (WShape.Join.lam'.2 hJ).T a2
    have ⟨g, a1, a2⟩ := main f'.elems fun _ => WShapeFun.mem_elems.1
    refine a2.mono (h2le.trans (WShape.lam'_le_lam'.2 ?_).T) |>.mono h1
    refine WShapeFun.LE.def'.2 fun x' y' hmem => WShapeFun.single_le.1 ?_
    exact (a1 _).1 .rfl _ (WShapeFun.mem_elems.2 hmem)
  · have ⟨m', f, a1, a2, a3, a4⟩ := he W h
    have hm' : ¬m' ≤ .bot := fun h => hm (a1.trans h)
    have hf : ¬f ≤ .bot := fun h => hm' (a4.bot_r' h)
    cases a3 with | bot => cases hf TShape.bot_le' | forallE b1 b2 b3 b4 b5
    cases b5.le_forall with | bot b5 => cases hf b5 | @forallE m _ _ _ _ b5 b6
    obtain rfl | ⟨n₂, g, rfl, c1⟩ := a4.ty_forallE_inv; · cases hm' TShape.bot_le'
    have le_k := Nat.le_max_left n₂ m; have le_m := Nat.le_max_right n₂ m
    refine .mono (WShape.lift_lam' le_k ▸ a1.trans (TShape.lift_eqv (Nat.succ_le_succ le_k)).2) <|
      .lam' ((b1.mono b5).lift (Nat.le_max_right ..)) c1.2.1 fun _ _ => ?_
    simpa only [WShape.lift_lam' le_k, WShape.lam'_app] using
      (a2.lift (Nat.succ_le_succ le_k)).weak.app' .bvar0

theorem Interp.beta_sound (W : Valuation.Fits env Γ₀ Γ ρ) (he' : SoundTy env Γ e' A) :
    Interp env ρ m (.app (.lam A e) e') ↔ Interp env ρ m (e.inst e') := by
  by_cases hm : m ≤ .bot; · exact ⟨fun _ => .mono hm .bot, fun _ => .mono hm .bot⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with | bot => cases hm TShape.bot_le' | @app n₁ _ _ _ _ _ a h1 h2 h3
    cases h1 with
    | bot => cases hm (h3.trans TShape.bot_eqv.1)
    | @lam n₂ _ _ _ _ _ f' h4 h5 h6 h7
    let k := max n₂ n₁; have hk := Nat.max_le.1 (Nat.le_refl k)
    obtain ⟨_, b1, b2⟩ := WShapeFun.app_eq (f'.lift k) (a.lift k)
    obtain ⟨a', y', b2', rfl, yb_eq⟩ := (WShapeFun.mem_lift hk.1).1 b2
    obtain ⟨bx', bxle, bx_ht, bapp⟩ := WShape.HasDom.iff.1 h5 a'
    refine Interp.inst.2 ⟨_, ?_, (h2.lift hk.2).mono b1.T⟩
    refine .mono_l (Valuation.LE.push.2 ⟨.rfl, bxle.T.trans (TShape.lift_eqv hk.1).2⟩) ?_
    refine (h6 bx' bx_ht).mono <| h3.trans <| .trans ?_ bapp.T
    rw [TShape.LE.def hk.2 hk.1, WShape.lift_app hk.2]
    have h7' := (TShape.LE.def (Nat.succ_le_succ hk.2) (Nat.succ_le_succ hk.1)).1 h7
    refine (WShape.app_mono_l h7' _).trans ?_
    rw [WShape.lift_lam' hk.1, WShape.lam'_app, yb_eq]
    exact WShape.lift_mono hk.1 (WShapeFun.app_of_mem b2').2
  · have ⟨_, h1, h2⟩ := Interp.inst.1 h
    have ⟨e, a, a1, a2, a3, a4⟩ := he' W h2
    let k := max m.1 (max e.1 a.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    have := (WShape.HasDom.single (y := m.2.lift k)).2 <| .inl <|
      (TShape.HasType.def hk.2.1 hk.2.2).1 a4
    refine .mono ?_ <| .app' (.lam' (a3.lift hk.2.2) this fun _ hx => ?_) (a2.lift hk.2.1)
    · rw [WShape.lam'_app, WShapeFun.single_app, if_pos .rfl]; exact (TShape.lift_eqv hk.1).2
    · simp [WShapeFun.single_app]; split <;> [rename_i h; exact .bot]
      refine (h1.lift hk.1).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.trans ?_⟩
      exact (TShape.LE.lift_l hk.2.1).2 h

theorem StrongSoundEq.beta (ih1 : StrongSoundEq env Γ A A (.sort u))
    (ih3 : StrongSoundEq env (A::Γ) e e B) (ih4 : StrongSoundEq env Γ e' e' A)
    (ih6 : StrongSoundEq env Γ (e.inst e') (e.inst e') (B.inst e')) :
    StrongSoundEq env Γ (.app (.lam A e) e') (e.inst e') (B.inst e') := by
  have hs : SoundEq env Γ (.app (.lam A e) e') (e.inst e') := fun _ _ W _ =>
    Interp.beta_sound W ih4.left.sound
  have hlam : StrongSound env Γ (.lam A e) (.forallE A B) :=
    ⟨fun _ _ W _ h => Interp.sound_lam (InterpTyped.hsort (ih1.left.sound W))
      (fun h1 h2 => ih3.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2)) h,
      .lam, .rfl⟩
  exact ⟨hs, ⟨ih6.left.sound.defeq_l hs.symm, .app hlam ih4.left, .rfl⟩, ih6.left⟩

theorem StrongSoundEq.eta (ih1 : StrongSoundEq env Γ A A (.sort u))
    (ih2 : StrongSoundEq env (A::Γ) B B (.sort v))
    (ih4 : StrongSoundEq env Γ e e (.forallE A B))
    (ih5 : StrongSoundEq env (A::Γ) e.lift e.lift (.forallE A.lift (B.liftN 1 1))) :
    StrongSoundEq env Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B) := by
  have hlamTy : SoundTy env Γ (.lam A (.app e.lift (.bvar 0))) (.forallE A B) :=
    fun _ ρ W _ h => by
      refine Interp.sound_lam (InterpTyped.hsort (ih1.left.sound W))
        (fun {a x} ha hx {m'} hb => ?_) h
      have W' := W.cons (InterpTyped.hsort (ih1.left.sound W)) ha hx
      have hB : ∀ {b}, Interp env (ρ.push x) b ((B.liftN 1 1).inst (.bvar 0)) →
          InterpTyped env (ρ.push x) b ((B.liftN 1 1).inst (.bvar 0)) (.sort v) := by
        rw [VExpr.inst_liftN_bvar]; exact ih2.left.sound W'
      have := Interp.sound_app (ih5.left.sound W') (InterpTyped.hsort hB) hb
      rwa [VExpr.inst_liftN_bvar] at this
  exact ⟨fun _ _ W _ => Interp.eta_sound W hlamTy ih4.left.sound, ⟨hlamTy, .lam, .rfl⟩,
    ih4.left⟩

/-- Soundness of the shape model for every strong derivation in `E ≤ env`. The facts about the
eliminators, projections and definitional rules are only asked for those of `E`. -/
theorem StrongSoundEq.of_isDefEqStrong {E : VEnv} (hle : E ≤ env)
    (hEF : SemSig.EnvFactsIn E env)
    (hEcl : ∀ df, E.defeqs df → df.lhs.Closed ∧ df.rhs.Closed)
    (hextra : ∀ df, E.defeqs df → ExtraValid env df) (helim : ElimValidIn E env)
    (H : E.IsDefEqStrong U Γ M N A) : StrongSoundEq env Γ M N A := by
  have hcl : ConstClosed env := fun h => hEF.constClosed h
  induction H with
  | bvar h1 _ _ ih => exact .rfl ⟨.bvar h1, .bvar, .rfl⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | sortDF h1 h2 h3 =>
    exact .ofLeft (fun _ _ _ _ =>
      ⟨(·.lvlEqv (.sort h3)), (·.lvlEqv (.sort (VLevel.equiv_symm' h3)))⟩) .sort .sort .rfl .sort .rfl
  | constDF h1 h2 h3 h4 h5 h6 _ _ ih1 ih2 =>
    have hc := hle.constants h1
    refine .ofLeft (fun _ _ _ _ =>
      ⟨(·.lvlEqv (.const h5)), (·.lvlEqv (.const (levels_equiv_symm h5)))⟩) ?_ (.const hc h4 ih2.left) .rfl
      (.const hc (h5.length_eq ▸ h4) ih2.right) ih2.sound.symm
    intro _ ρ W m H
    cases H with
    | bot => exact .bot
    | const b1 b2 b3 b4 b5 b6 b7 =>
      cases b1.symm.trans hc
      exact ⟨_, _, b3, .const b1 b2 .rfl b4 b5 b6 b7,
        (Interp.closed_iff (hcl hc).instL).1 b5, b4⟩
  | elimDF h1 h2 h3 h4 h5 h6 h7 _ ih =>
    have he := hEF.elimType h1 h2 h3
    refine .ofLeft (fun _ _ _ _ =>
      ⟨(·.lvlEqv (.elim h6)), (·.lvlEqv (.elim (levels_equiv_symm h6)))⟩) ?_ .elim .rfl .elim .rfl
    intro _ ρ W m H
    cases H with
    | bot => exact .bot
    | elim b1 b3 b4 b5 b6 b7 =>
      cases b1.symm.trans he
      exact ⟨_, _, b3, .elim b1 .rfl b4 b5 b6 b7, (Interp.closed_iff h3.instL).1 b5, b4⟩
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine StrongSoundEq.mk' (.app ih3.left ih4.left) .rfl (.app ih3.right ih4.right)
      ih5.sound.symm fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ Interp.sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      Interp.sound_app (ih3.left.sound W) (InterpTyped.hsort (ih5.left.sound W))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | app h1 h2 h3
    · exact .app ((ih3.sound W).1 h1) ((ih4.sound W).1 h2) h3
    · exact .app ((ih3.sound W).2 h1) ((ih4.sound W).2 h2) h3
  | projDF h1 h2 h3 h4 h5 h6 h7 _ _ _ hclosed hguard ihField ihLeft ihRight =>
    have hF := hEF.proj h1
    have hmm := ihLeft.sound.symm.trans ihRight.sound
    refine .ofLeft (fun _ _ W m => by
      constructor <;> intro H <;> cases H with
      | bot => exact .bot
      | proj a1 a2 a3 a4 =>
        first
        | exact .proj a1 ((hmm W).1 a2) a3 a4
        | exact .proj a1 ((hmm W).2 a2) a3 a4) ?_ (.proj hF ihLeft.right ihField.left hguard) .rfl
      (.proj hF ihRight.right ihField.left hguard) .rfl
    exact fun _ _ W m H => Proj.typed hcl hF h6 h3 h4 (ihLeft.right.sound W) (ihLeft.sound W).2 H
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine StrongSoundEq.mk' .lam .rfl .lam .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ Interp.sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, Interp.sound_lam (InterpTyped.hsort (ih1.left.sound W))
      fun h1 h2 => ih4.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2)⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | lam h1 h2 h3 h4
    · refine .lam ((ih1.sound W).1 h1) h2 (fun _ h => ?_) h4
      exact (ih4.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h.T)).1 (h3 _ h)
    · refine .lam ((ih1.sound W).2 h1) h2 (fun _ h => ?_) h4
      exact (ih4.sound (W.cons (InterpTyped.hsort (ih1.left.sound W))
        ((ih1.sound W).2 h1) h.T)).2 (h3 _ h)
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 =>
    refine StrongSoundEq.mk' (.forallE ih1.left ih2.left) .rfl (.forallE ih1.right ih3.right) .rfl
      fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ Interp.sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, Interp.sound_forallE
      (InterpTyped.hsort' (ih1.left.sound W)) fun h1 h2 =>
        ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2)⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | forallE h1 h2 h3 h4 h5
    · refine .forallE ((ih1.sound W).1 h1) ((ih1.sound W).1 h2) h3 (fun _ h => ?_) h5
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h2 h.T)).1 (h4 _ h)
    · refine .forallE ((ih1.sound W).2 h1) ((ih1.sound W).2 h2) h3 (fun _ h => ?_) h5
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W))
        ((ih1.sound W).2 h2) h.T)).2 (h4 _ h)
  | defeqDF h1 _ _ ih1 ih2 => exact ⟨ih2.sound, ih2.left.defeq_r ih1.sound, ih2.right.defeq_r ih1.sound⟩
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .beta ih1 ih3 ih4 ih6
  | eta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .eta ih1 ih2 ih4 ih5
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    refine ⟨fun _ ρ W m => ?_, ih2.left, ih3.left⟩
    have hz : SLvl.IsZero VLevel.zero.eval := fun _ => Eq.refl _
    exact ⟨fun h => .mono (InterpTyped.proofIrrel (ih2.left.sound W h) (ih1.left.sound W) hz) .bot,
      fun h => .mono (InterpTyped.proofIrrel (ih3.left.sound W h) (ih1.left.sound W) hz) .bot⟩
  | extra h1 h2 h3 h4 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have ⟨c1, c2⟩ := hEcl _ h1
    exact ⟨.of_closed c1.instL c2.instL (hextra _ h1 _ _ h3 ih1.left ih2.left ih3.left),
      ih4.left, ih5.left⟩
  | elimIota h1 h2 h3 h4 h5 h6 _ _ _ ihT ihL ihR =>
    exact ⟨.of_closed h4.1.instL h4.2.1.instL
      (helim h1 h2 h3 h4 h5 ihT.left ihL.left ihR.left), ihL.left, ihR.left⟩
  | projIota h1 _ h3 _ ih1 ih2 =>
    exact ⟨fun _ _ W _ => Struct.iota hcl (hEF.proj h1) W ih1.left ih2.left h3,
      ih1.left, ih2.left⟩
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    exact ⟨fun _ _ W _ => Struct.eta hcl (hEF.proj h1) h3 h2 W ih1.left ih2.left,
      ih2.left, ih1.left⟩
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    have hF := hEF.proj h1
    exact ⟨fun _ _ W _ =>
      ⟨fun h => .mono (Struct.unit hF h3 h4 (ih1.left.sound W) h) .bot,
        fun h => .mono (Struct.unit hF h3 h4 (ih2.left.sound W) h) .bot⟩, ih1.left, ih2.left⟩

/-- `StrongSoundEq.of_isDefEqStrong` with the facts asked for every eliminator and projection of
`env` (the form before the hypotheses were restricted to the derivation environment). -/
theorem StrongSoundEq.of_isDefEqStrong_global {E : VEnv} (hle : E ≤ env)
    (hEF : SemSig.EnvFacts env)
    (hEcl : ∀ df, E.defeqs df → df.lhs.Closed ∧ df.rhs.Closed)
    (hextra : ∀ df, E.defeqs df → ExtraValid env df) (helim : ElimValid env)
    (H : E.IsDefEqStrong U Γ M N A) : StrongSoundEq env Γ M N A :=
  .of_isDefEqStrong hle (hEF.mono hle) hEcl hextra (helim.mono hle) H

/-- Soundness at the base valuation: in an ordered environment, definitionally equal terms in a
well-formed context have the same approximations under `Valuation.nil` (which fits `Γ` with
base context `Γ` itself). -/
theorem sound_nil (henv : VEnv.Ordered env) (hEF : SemSig.EnvFactsIn env env)
    (hextra : ∀ df, env.defeqs df → ExtraValid env df) (helim : ElimValidIn env env)
    (H : VEnv.IsDefEq env U Γ M N A) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ m, Interp env .nil m M ↔ Interp env .nil m N := fun _ =>
  (StrongSoundEq.of_isDefEqStrong VEnv.LE.rfl hEF
    (fun _ h => ⟨(henv.closed.2 h).1.1, (henv.closed.2 h).2.1⟩) hextra helim
    (H.strong henv hΓ)).sound Valuation.Fits.nil

end
