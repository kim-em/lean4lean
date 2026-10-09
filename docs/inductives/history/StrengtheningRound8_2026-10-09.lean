import Lean4Lean.Theory.Typing.Strengthening.Pilot
import Lean4Lean.Theory.Typing.Strengthening.JoinRepair
import Lean4Lean.Theory.Typing.Strengthening.Obstructions
import Lean4Lean.Theory.Typing.EqTyping

namespace Lean4Lean.Round8
open VEnv VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {Q a b T : VExpr}

def TypingFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q e A⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U (Q :: Γ) e.lift A → ∃ B, env.HasType U Γ e B

def UninhabitedTypingFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q e A⦄, OnCtx (Q :: Γ) (env.IsType U) →
    (∀ q, ¬ env.HasType U Γ q Q) →
    env.HasType U (Q :: Γ) e.lift A → ∃ B, env.HasType U Γ e B

theorem typingFront_of_uninhabited (henv : env.WF)
    (H : UninhabitedTypingFront env) : TypingFront env := by
  intro U Γ Q e A hΓ he
  classical
  by_cases h : ∃ q, env.HasType U Γ q Q
  · obtain ⟨q, hq⟩ := h
    exact ⟨A.inst q, by simpa only [inst_lift] using he.instN henv.ordered Ctx.InstN.zero hq⟩
  · exact H hΓ (by simpa using h) he

-- A type annotation encoded using ordinary application and lambda syntax.
def ascribe (e A : VExpr) : VExpr := .app (.lam A (.bvar 0)) e

theorem ascribe_typed (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.HasType U Γ e A) : env.HasType U Γ (ascribe e A) A := by
  obtain ⟨u, hA⟩ := he.isType henv hΓ
  simpa only [ascribe, inst_lift] using HasType.app (HasType.lam hA (.bvar .zero)) he

theorem ascribe_inv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.HasType U Γ (ascribe e A) B) : env.HasType U Γ e A := by
  obtain ⟨D, E, hf, he⟩ := he.app_inv henv.ordered hΓ
  obtain ⟨C, hPi, _⟩ := hf.lam_inv_forallE henv hΓ
  obtain ⟨u, hAD⟩ := (hPi.forallE_inv henv hΓ).1
  exact .defeqDF hAD.symm he

theorem fixed_typingFront (henv : env.WF) (H : TypingFront env)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U))
    (he : env.HasType U (Q :: Γ) e.lift A.lift) : env.HasType U Γ e A := by
  have ht := ascribe_typed henv.ordered hΓ he
  have ht' : env.HasType U (Q :: Γ) (ascribe e A).lift A.lift := ht
  obtain ⟨B, hb⟩ := H hΓ ht'
  exact ascribe_inv henv hΓ.1 hb

theorem canonicalEq_rigid (henv : env.WF) (heq : env.HasCanonicalEq) : env.Rigid ``Eq := by
  have hm : canonicalEqRecRule.HasConstructorMajor ``Eq.refl :=
    ⟨_, [.param 1], [.bvar 3, .bvar 2], rfl⟩
  have h := henv.installed_constructor_result_rigid heq.2.2.2 hm
  unfold VEnv.CtorResultRigid at h
  obtain ⟨ci, hc, F, ls, hf, _, hr⟩ := h
  rw [heq.2.1] at hc
  cases hc
  have hf : VExpr.const ``Eq [.param 0] = .const F ls := hf
  cases hf
  exact hr

theorem eqApp_injective (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (hT : env.HasType U Γ T (.sort u)) (ha : env.HasType U Γ a T)
    (hu : u.WF U)
    (H : env.IsDefEqU U Γ (eqApp u T a a) (eqApp u T a b)) :
    env.IsDefEqU U Γ a b := by
  have ht := HasType.eqApp heq hu hT ha ha
  have hh := (IsDefEqU.rigidApp_inv (args := [T,a,a]) (args' := [T,a,b]) henv hΓ (canonicalEq_rigid henv heq) H ht).2
  cases hh with | cons _ hh =>
    cases hh with | cons _ hh =>
      cases hh with | cons h _ => exact h

theorem cancel_of_typingFront (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : TypingFront env) : Cancel env := by
  apply Cancel.of_front henv
  intro U Γ Q a b hΓ hab
  obtain ⟨R, hab⟩ := hab
  obtain ⟨A, ha⟩ := H hΓ hab.hasType.1
  obtain ⟨u, hA⟩ := ha.isType henv.ordered hΓ.1
  have hu := hA.sort_r henv.ordered hΓ.1
  have ha' := ha.weak henv.ordered (B := Q)
  have hab' := (show env.IsDefEqU U (Q :: Γ) a.lift b.lift from ⟨_, hab⟩).of_l henv hΓ ha'
  have hA' := hA.weak henv.ordered (B := Q)
  have hr := HasType.eqReflApp heq hu hA' ha'
  have hr' := (IsDefEq.eqApp_r heq hu hA' ha' hab').defeq hr
  have hd : env.HasType U Γ (eqReflApp u A a) (eqApp u A a b) := by
    apply fixed_typingFront henv H hΓ
    simpa only [eqReflApp, eqApp, lift, liftN] using hr'
  have hr₀ := HasType.eqReflApp heq hu hA ha
  exact eqApp_injective henv heq hΓ.1 hA ha hu (hr₀.uniqU henv hΓ.1 hd)

theorem uninhabitedTypingFront_iff_cancel (henv : env.WF) (heq : env.HasCanonicalEq) :
    UninhabitedTypingFront env ↔ Cancel env := by
  constructor
  · intro H
    exact cancel_of_typingFront henv heq (typingFront_of_uninhabited henv H)
  · intro H U Γ Q e A hΓ _ he
    obtain ⟨B, hb⟩ := Front.of_cancel H hΓ ⟨A, he⟩
    exact ⟨B, hb⟩
end Lean4Lean.Round8


namespace Lean4Lean.Round8
open VEnv VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {Q P f h : VExpr}

-- Rigidity of Q does not prevent a proof application from using q.
theorem derived_proof_irrel (henv : env.Ordered)
    (hP : env.HasType U Γ P (.sort .zero))
    (hf : env.HasType U Γ f (.forallE Q P.lift))
    (hh : env.HasType U Γ h P) :
    env.IsDefEq U (Q :: Γ) (.app f.lift (.bvar 0)) h.lift P.lift := by
  have ha : env.HasType U (Q :: Γ) (.app f.lift (.bvar 0)) P.lift := by
    simpa only [lift, liftN, inst_liftN_bvar] using
      HasType.app (hf.weak henv (B := Q)) (HasType.bvar (env := env) (U := U) (Lookup.zero (ty := Q)))
  exact .proofIrrel (hP.weak henv) ha (hh.weak henv)

theorem derived_proof_mentions_q : ¬ (VExpr.app f.lift (.bvar 0)).Skips 1 0 := by
  simp [VExpr.skips_iff, VExpr.Skips']

theorem rigid_q_not_proof (henv : env.WF)
    (hΓ : OnCtx (VExpr.const I ls :: Γ) (env.IsType U))
    (hI : env.HasType U Γ (.const I ls) (.sort u)) (hne : ¬ u ≈ .zero)
    (hP : env.HasType U (.const I ls :: Γ) P (.sort .zero)) :
    ¬ env.HasType U (.const I ls :: Γ) (.bvar 0) P := by
  intro hp
  have hq : env.HasType U (.const I ls :: Γ) (.bvar 0) (.const I ls) := .bvar .zero
  have ht := (hq.uniqU henv hΓ hp).of_r henv hΓ hP
  have hi := hI.weak henv.ordered (B := .const I ls)
  exact hne ((hi.uniqU henv hΓ ht.hasType.1).sort_inv henv hΓ)

-- A bad eta domain works for every Q, including a rigid uninhabited Type.
def badDomain (Q : VExpr) : VExpr := .app (.lam Q.lift (.sort .zero)) (.bvar 0)
def badEta (Q : VExpr) : VExpr :=
  .lam (badDomain Q) (.app StrengtheningObstructions.idProp.lift (.bvar 0))

section
open VEnv.Params
variable [VEnv.Params]

theorem arbitrary_Q_eta :
    FullStep (Q :: Γ) StrengtheningObstructions.idProp.lift (badEta Q) ∧
      ¬ (badEta Q).Skips 1 0 := by
  have hd : Params.env.IsDefEq univs (Q :: Γ) (badDomain Q) (.sort .zero) (.sort (.succ .zero)) :=
    .beta (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hf : Params.env.HasType univs (Q :: Γ) StrengtheningObstructions.idProp
      (.forallE (.sort .zero) (.sort .zero)) := .lamDF (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hp := IsDefEq.forallEDF hd.symm (HasType.sort (env := Params.env) (U := univs)
    (Γ := .sort .zero :: Q :: Γ) (l := .zero) trivial)
  constructor
  · simpa [badEta, StrengtheningObstructions.idProp, lift, liftN, liftVar] using
      FullStep.funEta (IsDefEq.defeqDF hp hf)
  · simp [badEta, badDomain, VExpr.skips_iff, VExpr.Skips']

-- A lifted TYPE can have a non-lift Pi reduct; exact endpoint descent fails.
def headType : VExpr := .forallE
  (.app (.lam (.forallE (.sort .zero) (.sort .zero)) (.sort .zero))
    StrengtheningObstructions.idProp) (.sort .zero)

def headTypeBad (Q : VExpr) : VExpr := .forallE
  (.app (.lam (.forallE (.sort .zero) (.sort .zero)) (.sort .zero)) (badEta Q)) (.sort .zero)

theorem headType_typed : Params.env.HasType univs Γ headType (.sort (.succ .zero)) := by
  have hi : Params.env.HasType univs Γ StrengtheningObstructions.idProp
      (.forallE (.sort .zero) (.sort .zero)) := .lamDF (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hpi : Params.env.HasType univs Γ (.forallE (.sort .zero) (.sort .zero))
      (.sort (.succ .zero)) := StrengtheningObstructions.bodyPi_typed
  have ha : Params.env.HasType univs Γ
      (.app (.lam (.forallE (.sort .zero) (.sort .zero)) (.sort .zero))
        StrengtheningObstructions.idProp) (.sort (.succ .zero)) :=
    .app (.lamDF hpi (HasType.sort (l := .zero) trivial)) hi
  have hh : Params.env.HasType univs Γ headType
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE ha (.sort trivial)
  exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
    (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) hh

theorem headType_bad_reduct :
    FullStep (Q :: Γ) headType.lift (headTypeBad Q) ∧
    ¬ (headTypeBad Q).Skips 1 0 := by
  constructor
  · exact .forallE (.app .rfl arbitrary_Q_eta.1) .rfl
  · simp [headTypeBad, VExpr.skips_iff, VExpr.Skips', badEta, badDomain]

def headSource : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) headType

theorem headSource_typed : Params.env.HasType univs Γ headSource (.sort (.succ .zero)) :=
  .app (.lamDF (HasType.sort (l := .succ .zero) trivial) (.bvar .zero)) headType_typed

theorem headSource_bad_path :
    FullReduction (Q :: Γ) headSource.lift (headTypeBad Q) := by
  refine (ReflTransGen.tail .rfl (FullStep.app FullStep.rfl headType_bad_reduct.1)).tail ?_
  simpa [lift, liftN, liftVar, inst, instVar] using
    (FullStep.core (ParRed.beta (Γ := Q :: Γ) (A := .sort (.succ .zero))
      (e₁ := .bvar 0) (e₂ := headTypeBad Q) .rfl .rfl))

theorem arbitrary_Q_eta_repaired :
    FullStep (Q :: Γ) (badEta Q) StrengtheningObstructions.etaGood.lift := by
  exact .lam (.core (.beta .rfl .rfl)) .rfl

-- With a fixed common Pi, declarative subject reduction retains the eta domain.
theorem fixed_type_eta_peak
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Params.env.HasType univs Γ f (.forallE A B)) (hs : FullStep Γ f g) :
    FullStep Γ g (.lam A (.app g.lift (.bvar 0))) ∧
    FullStep Γ (.lam A (.app f.lift (.bvar 0)))
      (.lam A (.app g.lift (.bvar 0))) := by
  exact ⟨.funEta (hs.hasType hΓ hf), .lam .rfl (.app (hs.weakN Ctx.LiftN.one) .rfl)⟩
end
end Lean4Lean.Round8

namespace Lean4Lean.Round8
open VEnv VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

def pilotId : VExpr := .lam (.sort .zero) (.bvar 0)
def pilotPi : VExpr := .forallE (.sort .zero) (.sort .zero)
def pilotBeta : VExpr := .app (.lam (.sort (.succ .zero)) pilotId) (.sort .zero)
def expand (A e : VExpr) : VExpr := .lam A (.app e.lift (.bvar 0))

theorem pilotId_ty : CTy env U Γ pilotId pilotPi :=
  .ty_lam (.ty_sort trivial) .red_refl (.ty_bvar .zero)

theorem pilotBeta_ty : CTy env U Γ pilotBeta pilotPi := by
  have h : CTy env U Γ pilotBeta (pilotPi.inst (.sort .zero)) :=
    .ty_app (.ty_lam (.ty_sort trivial) .red_refl pilotId_ty) .red_refl (.ty_sort trivial)
      (.conv_mk .red_refl .red_refl (.norm_sort trivial trivial rfl))
  exact h

theorem pilotBeta_step : CStep env U Γ pilotBeta pilotId :=
  .step_beta (.step_lam .step_sort .step_bvar) .step_sort

-- The two actual pilot steps and their two one-step residuals.
theorem pilot_eta_beta_peak :
    CStep env U Γ pilotBeta (expand (.sort .zero) pilotBeta) ∧
    CStep env U Γ pilotBeta pilotId ∧
    CStep env U Γ (expand (.sort .zero) pilotBeta) (expand (.sort .zero) pilotId) ∧
    CStep env U Γ pilotId (expand (.sort .zero) pilotId) := by
  refine ⟨.step_eta pilotBeta_ty .red_refl, pilotBeta_step, ?_,
    .step_eta pilotId_ty .red_refl⟩
  exact .step_lam .step_sort (.step_app pilotBeta_step .step_bvar)

-- Cert is Prop-valued: a numerical rank cannot inspect proof representations.
theorem proof_rank_constant {k : CKind} {a b : VExpr}
    (rank : Cert env U k Γ a b → Nat) (d₁ d₂ : Cert env U k Γ a b) :
    rank d₁ = rank d₂ := congrArg rank (Subsingleton.elim d₁ d₂)

theorem param_nonzero_not_neverzero :
    ¬ (VLevel.param 0 ≈ .zero) ∧ ¬ (VLevel.param 0).IsNeverZero := by
  constructor
  · intro h
    have hh := congrFun h [1]
    simp [VLevel.eval] at hh
  · intro h
    exact h [0] rfl
end Lean4Lean.Round8

#print axioms Lean4Lean.Round8.typingFront_of_uninhabited
#print axioms Lean4Lean.Round8.ascribe_typed
#print axioms Lean4Lean.Round8.ascribe_inv
#print axioms Lean4Lean.Round8.fixed_typingFront
#print axioms Lean4Lean.Round8.canonicalEq_rigid
#print axioms Lean4Lean.Round8.eqApp_injective
#print axioms Lean4Lean.Round8.cancel_of_typingFront
#print axioms Lean4Lean.Round8.uninhabitedTypingFront_iff_cancel
#print axioms Lean4Lean.Round8.derived_proof_irrel
#print axioms Lean4Lean.Round8.derived_proof_mentions_q
#print axioms Lean4Lean.Round8.rigid_q_not_proof
#print axioms Lean4Lean.Round8.arbitrary_Q_eta
#print axioms Lean4Lean.Round8.headType_typed
#print axioms Lean4Lean.Round8.headType_bad_reduct
#print axioms Lean4Lean.Round8.fixed_type_eta_peak
#print axioms Lean4Lean.Round8.pilotId_ty
#print axioms Lean4Lean.Round8.pilotBeta_ty
#print axioms Lean4Lean.Round8.pilotBeta_step
#print axioms Lean4Lean.Round8.pilot_eta_beta_peak
#print axioms Lean4Lean.Round8.proof_rank_constant
#print axioms Lean4Lean.Round8.param_nonzero_not_neverzero

#print axioms Lean4Lean.Round8.headSource_typed
#print axioms Lean4Lean.Round8.headSource_bad_path
#print axioms Lean4Lean.Round8.arbitrary_Q_eta_repaired

namespace Lean4Lean.Round8
open VEnv VExpr

theorem not_cancel_iff_typing_gap {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ Cancel env ↔
      ∃ (U : Nat) (Γ : List VExpr) (Q e A : VExpr),
        OnCtx (Q :: Γ) (env.IsType U) ∧
        (∀ q, ¬ env.HasType U Γ q Q) ∧
        env.HasType U (Q :: Γ) e.lift A ∧
        ∀ B, ¬ env.HasType U Γ e B := by
  classical
  rw [← uninhabitedTypingFront_iff_cancel henv heq]
  simp only [UninhabitedTypingFront, Classical.not_forall, not_exists, exists_prop]
end Lean4Lean.Round8
#print axioms Lean4Lean.Round8.not_cancel_iff_typing_gap

namespace Lean4Lean.Round8
open VEnv VExpr VEnv.Params
variable [VEnv.Params]

/-- An OPEN obligation, not a theorem. The output Pi may differ from the given Pi. -/
def UninhabitedPiExposure : Prop :=
  ∀ {Γ Q T A B u}, OnCtx (Q :: Γ) (Params.env.IsType univs) →
    (∀ q, ¬ Params.env.HasType univs Γ q Q) →
    Params.env.HasType univs Γ T (.sort u) →
    FullReduction (Q :: Γ) T.lift (.forallE A B) →
    ∃ A₀ B₀, FullReduction Γ T (.forallE A₀ B₀)
end Lean4Lean.Round8
