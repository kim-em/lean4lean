import Lean4Lean.Theory.Typing.Strengthening.TypingFront
import Lean4Lean.Theory.Typing.Strengthening.Hunt
import Lean4Lean.Theory.Typing.HeadReduction

/-! # Typing strengthening: local replay of reduction steps

Astra's round 9 design check (`docs/inductives/STRENGTHENING_ASTRA_REVIEW7.md`, checked file
`docs/inductives/history/StrengtheningRound9_2026-10-09.lean`), adapted with names kept:

* `typeFrontN_iff_typeFront`, `typeFrontN_iff_typedFront`: the `LiftN` form of the type front is
  the front form, hence Kripke's `TypedFront` under canonical `Eq` (induction on the insertion,
  abstracting the two types by `Π D`).
* `piExposureRed_iff_piExposure`: exposure in reduction form is exposure in conversion form.
* `retyping_of_typeFrontN`: a term typed below at `T` and above at the lift of a type `A` of `Γ`
  is typed below at `A` (unique typing plus the type front).
* `cancel_iff_typedFront_and_closures`: the exact formulation
  `Cancel ↔ TypedFront ∧ AppFrontN ∧ ProjFrontN ∧ ElimFrontN`.
* `core_exposure_standard`: core standardisation gives head exposure for `ParRedS`; projections
  have no core head exposure (`projection_full_exposure`), so a head strategy for `FullReduction`
  is outside `WHRed`.
* `saturated_projection_replay`: projection iota replays below with no hypothesis.
* `HeadStep`, `LocalReplay` (Astra's `HeadReplay`), `HeadStandard`, `head_path_replay`: given an
  exact local replay interface for the eta-free head fragment, induction on the above path (no
  size component) exposes below; `piExposureRed_of_head_interfaces` assembles the two open
  interfaces into `PiExposureRedN`.

The second part of this file is this branch's own work (`docs/inductives/STRENGTHENING_B2_LOG.md`). -/

namespace Lean4Lean.VEnv.StrengtheningReplay
open VExpr VEnv.StrengtheningTypingFront
variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr} {A B F f Q T e : VExpr}

/-! ## The type front in `LiftN` form is `TypedFront` -/

theorem typeFrontN_of_typeFront (henv : env.WF) (H : TypeFront env) : TypeFrontN env := by
  intro U k Γ Γ' A B u v W
  induction W generalizing A B u v with
  | zero As hn =>
    cases As with
    | nil => simp at hn
    | cons Q As =>
      cases As with
      | nil => exact fun _ hΓ' hA hB hAB => H hΓ' hA hB hAB
      | cons => simp at hn
  | @succ k Γ Γ' D W ih =>
    intro hΓ hΓ' hA hB hAB
    obtain ⟨w, hD⟩ := hΓ.2
    have hD' := hD.weakN henv.ordered W
    have hAB' := hAB.of_l henv hΓ' (hA.weakN henv.ordered W.succ)
    have hPi : env.IsDefEqU U Γ' ((VExpr.forallE D A).liftN 1 k)
        ((VExpr.forallE D B).liftN 1 k) := ⟨_, .forallEDF hD' hAB'⟩
    have hd := ih hΓ.1 hΓ'.1 (.forallE hD hA) (.forallE hD hB) hPi
    obtain ⟨_, hb⟩ := (hd.forallE_inv henv hΓ.1).2
    exact ⟨_, hb⟩

theorem typeFrontN_iff_typeFront (henv : env.WF) : TypeFrontN env ↔ TypeFront env :=
  ⟨TypeFront.of_typeFrontN, typeFrontN_of_typeFront henv⟩

theorem typeFrontN_iff_typedFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypeFrontN env ↔ StrengtheningKripke.TypedFront env :=
  (typeFrontN_iff_typeFront henv).trans (typeFront_iff_typedFront henv heq)

theorem piExposureRed_iff_piExposure (henv : env.WF) (heq : env.HasCanonicalEq) :
    PiExposureRedN henv ↔ PiExposureN env := by
  refine ⟨PiExposureN.of_red henv heq, ?_⟩
  intro H U k Γ Γ' f F u A B W hΓ hΓ' hf hF hr
  letI := henv.params U
  have hc : env.IsDefEqU U Γ' (F.liftN 1 k) (.forallE A B) :=
    ⟨_, hr.defeq hΓ' (hF.weakN henv.ordered W)⟩
  obtain ⟨A₀, B₀, hPi⟩ := H W hΓ hΓ' hf hc
  exact exposure_reduces henv heq hΓ hF hPi

/-- A term typed below at some `T` and above at the lift of a type `A` of `Γ` is typed below at
`A`: unique typing above gives `T↑ ≡ A↑`, the type front descends it. -/
theorem retyping_of_typeFrontN (henv : env.WF) (H : TypeFrontN env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U))
    (hΓ' : OnCtx Γ' (env.IsType U)) (he : env.HasType U Γ e T)
    (hA : env.HasType U Γ A (.sort u))
    (he' : env.HasType U Γ' (e.liftN 1 k) (A.liftN 1 k)) : env.HasType U Γ e A := by
  obtain ⟨v, hT⟩ := he.isType henv.ordered hΓ
  exact he.defeqU_r henv hΓ (H W hΓ hΓ' hT hA
    ((he.weakN henv.ordered W).uniqU henv hΓ' he'))

/-- Two terms typed below (at any types) whose lifts are convertible above are convertible
below: the types agree by unique typing and the type front, then `TypedFront` applies. -/
theorem typedFront_independent_endpoints (henv : env.WF)
    (H : StrengtheningKripke.TypedFront env) (hΓ' : OnCtx (Q :: Γ) (env.IsType U))
    (ha : env.HasType U Γ a A) (hb : env.HasType U Γ b B)
    (hab : env.IsDefEqU U (Q :: Γ) a.lift b.lift) : env.IsDefEqU U Γ a b := by
  have hTy := typeFront_of_typedFront henv H
  obtain ⟨u, hA⟩ := ha.isType henv.ordered hΓ'.1
  obtain ⟨v, hB⟩ := hb.isType henv.ordered hΓ'.1
  have he := hab.of_l henv hΓ' (ha.weak henv.ordered)
  have hAB := he.uniqU henv hΓ' (hb.weak henv.ordered)
  have hbA := hb.defeqU_r henv hΓ'.1 (hTy hΓ' hA hB hAB).symm
  exact ⟨_, H hΓ'.1 hΓ'.2 ha hbA he⟩

/-! ## The exact formulation -/

theorem cancel_iff_typedFront_and_closures (henv : env.WF) (heq : env.HasCanonicalEq) :
    Cancel env ↔ StrengtheningKripke.TypedFront env ∧ AppFrontN env ∧
      ProjFrontN env ∧ ElimFrontN env := by
  constructor
  · intro H
    have ht := typingFrontN_of_cancel henv H
    exact ⟨(typeFrontN_iff_typedFront henv heq).mp (TypeFrontN.of_typingFrontN henv ht),
      AppFrontN.of_typingFrontN ht, ProjFrontN.of_typingFrontN ht, ElimFrontN.of_typingFrontN ht⟩
  · rintro ⟨ht, ha, hp, he⟩
    exact (typingFrontN_iff_cancel henv heq).mp
      (typingFrontN_of_closures henv ha ((typeFrontN_iff_typedFront henv heq).mpr ht) hp he)

theorem cancel_of_typedFront_and_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (ht : StrengtheningKripke.TypedFront env) (hPi : PiExposureN env)
    (hp : ProjFrontN env) (he : ElimFrontN env) : Cancel env := by
  have hTy := (typeFrontN_iff_typedFront henv heq).mpr ht
  exact (cancel_iff_typedFront_and_closures henv heq).mpr
    ⟨ht, AppFrontN.of_piExposure henv hPi hTy, hp, he⟩

/-! ## Standardisation, projections and the head fragment -/

section
open VEnv.Params
variable [VEnv.Params]

theorem core_exposure_standard (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ F (.sort u))
    (hr : ParRedS Γ F (.forallE A B)) :
    ∃ A₀ B₀, WHRedS Γ F (.forallE A₀ B₀) := by
  have hs := hr.standard hΓ ht
  cases hs with
  | forallE h _ _ => exact ⟨_, _, h⟩

theorem whnf_proj (family : Name) (i : Nat) (m : VExpr) : WHNF Γ (.proj family i m) := by
  intro out h
  cases h with
  | schema h =>
    obtain ⟨_, _, _, hh⟩ := h.head
    cases hh
  | extra hp hm _ =>
    obtain ⟨name, hh⟩ := (Params.constHeaded hp).matches_head hm
    cases hh

theorem projection_has_no_core_head_exposure (family : Name) (i : Nat) (m : VExpr) :
    ¬ ∃ A B, WHRedS Γ (.proj family i m) (.forallE A B) := by
  rintro ⟨A, B, hr⟩
  have hh := (whnf_proj family i m).whRedS hr
  cases hh

theorem projection_full_exposure (hp : Params.env.projections family info)
    (ht : Params.env.HasType univs Γ
      (.proj family i (mkApps (.const info.ctorName ls) args)) (.sort u))
    (hi : args[info.nparams + i]? = some (.forallE A B))
    (hPi : Params.env.HasType univs Γ (.forallE A B) (.sort u)) :
    FullReduction Γ (.proj family i (mkApps (.const info.ctorName ls) args)) (.forallE A B) ∧
      ¬ ∃ C D, WHRedS Γ (.proj family i (mkApps (.const info.ctorName ls) args)) (.forallE C D) :=
  ⟨.tail .rfl (.projIota hp ht hi hPi), projection_has_no_core_head_exposure _ _ _⟩

theorem type_not_function (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ F (.sort u)) :
    ¬ Params.env.HasType univs Γ F (.forallE A B) :=
  fun hf => IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ hf)

theorem type_not_structure (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ F (.sort u))
    (hi : Params.env.projections family info) :
    ¬ Params.env.HasType univs Γ F (mkApps (.const family ls) args) := by
  intro hs
  exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
    ((ht.uniqU henv hΓ hs).typeChain henv hΓ (.sort (ht.sort_r henv.ordered hΓ)))

/-- Projection iota replays from the typing of the projection alone. -/
theorem saturated_projection_replay (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hi : Params.env.projections family info)
    (ht : Params.env.HasType univs Γ
      (.proj family i (mkApps (.const info.ctorName ls) args)) T)
    (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + i]? = some field) :
    FullStep Γ (.proj family i (mkApps (.const info.ctorName ls) args)) field :=
  .projIota hi ht hget (HasType.projIota_field hΓ hi ht hlen hget)

/-- Astra's eta-free demanded-head fragment; not claimed complete for `FullReduction`. -/
inductive HeadStep (Γ : List VExpr) : VExpr → VExpr → Prop where
  | beta {A b a : VExpr} : HeadStep Γ (.app (.lam A b) a) (b.inst a)
  | extra {e : VExpr} : Pat p r → p.Matches e ls values →
      r.2.OK (Params.env.IsDefEqU univs Γ) ls values →
      HeadStep Γ e (r.1.apply ls values)
  | schema {e : VExpr} : CaseIota Params.env univs Γ e e' → HeadStep Γ e e'
  | delta : PrefixUnfold Params.env univs recursorData Γ c ls args rhs →
      HeadStep Γ (mkApps (.const c ls) args) rhs
  | quotDelta : QuotPrefixUnfold Params.env univs Γ ls args rhs →
      HeadStep Γ (mkApps (.const ``Quot.lift ls) args) rhs
  | projIota {T : VExpr} : Params.env.projections S info →
      Params.env.HasType univs Γ (.proj S i (mkApps (.const info.ctorName ls) args)) T →
      args[info.nparams + i]? = some field → Params.env.HasType univs Γ field T →
      HeadStep Γ (.proj S i (mkApps (.const info.ctorName ls) args)) field
  | app {f : VExpr} : HeadStep Γ f f' → HeadStep Γ (.app f a) (.app f' a)
  | major {f : VExpr} : IsMajorPremise f → HeadStep Γ a a' → HeadStep Γ (.app f a) (.app f a')
  | caseMajor {f : VExpr} : IsCaseMajorPremise Params.env f → HeadStep Γ a a' →
      HeadStep Γ (.app f a) (.app f a')
  | proj : HeadStep Γ m m' → HeadStep Γ (.proj S i m) (.proj S i m')

theorem HeadStep.full (H : HeadStep Γ e e') : FullStep Γ e e' := by
  induction H with
  | beta => exact .core (.beta .rfl .rfl)
  | extra hp hm hg => exact .core (.extra hp hm hg fun _ => .rfl)
  | schema h => exact .core (.of_schema h)
  | delta h => exact .delta h
  | quotDelta h => exact .quotDelta h
  | projIota hi ht hg hf => exact .projIota hi ht hg hf
  | app _ ih => exact .app ih .rfl
  | major _ _ ih | caseMajor _ _ ih => exact .app .rfl ih
  | proj _ ih => exact .proj ih

/-- OPEN (Astra's `HeadReplay`): the sufficient local replay interface for the head fragment.
A head step above on the lift of a term typed below is the lift of a full step below. -/
def LocalReplay : Prop :=
  ∀ ⦃k Γ Γ' e T out⦄, Ctx.LiftN 1 k Γ Γ' →
    OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    Params.env.HasType univs Γ e T → HeadStep Γ' (e.liftN 1 k) out →
    ∃ e', out = e'.liftN 1 k ∧ FullStep Γ e e'

/-- OPEN: the full-to-demanded-head exposure bridge for this fragment. -/
def HeadStandard : Prop :=
  ∀ ⦃Γ F u A B⦄, OnCtx Γ (Params.env.IsType univs) →
    Params.env.HasType univs Γ F (.sort u) → FullReduction Γ F (.forallE A B) →
    ∃ C D, ReflTransGen (HeadStep Γ) F (.forallE C D)

/-- Given local replay, induction on the above path (no size component) replays it below. -/
theorem head_path_replay (H : LocalReplay) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ e T)
    (hr : ReflTransGen (HeadStep Γ') (e.liftN 1 k) out) :
    ∃ e', out = e'.liftN 1 k ∧ FullReduction Γ e e' := by
  generalize hs : e.liftN 1 k = source at hr
  induction hr using ReflTransGen.headIndOn generalizing e with
  | rfl => exact ⟨e, hs.symm, .rfl⟩
  | head step tail ih =>
    rw [← hs] at step
    obtain ⟨m, hm, hstep⟩ := H W hΓ hΓ' ht step
    obtain ⟨e', he', htail⟩ := ih (hstep.hasType hΓ ht) hm.symm
    exact ⟨e', he', (ReflTransGen.tail .rfl hstep).trans htail⟩

end

theorem piExposureRed_of_head_interfaces (henv : env.WF)
    (standard : ∀ U, @HeadStandard (henv.params U))
    (replay : ∀ U, @LocalReplay (henv.params U)) : PiExposureRedN henv := by
  intro U k Γ Γ' f F u A B W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨C, D, hh⟩ := standard U hΓ' (hF.weakN henv.ordered W) hr
  obtain ⟨F', he, hf⟩ := head_path_replay (replay U) W hΓ hΓ' hF hh
  cases F' <;> simp only [liftN] at he <;> cases he
  exact ⟨_, _, hf⟩

end Lean4Lean.VEnv.StrengtheningReplay
