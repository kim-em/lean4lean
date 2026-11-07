import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionAction

/-! # The cost of unrestricted futures in the function-variable case

Action for just the newest function variable is equivalent to reflexive action
for every actual function, even without an outer future quantifier: the
completed result history already permits every later typed substitution.
Applying such reflexive action to an evaluation lambda recovers shared
application for arbitrary completed function histories. Thus the unrestricted
variable case already contains the proposition front; it is not a seed that
can initialize a simultaneous interpretation for free.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Instantiation of a completed history by an actual typed binder image.
The two endpoints may have different actual types; only the history's retained
carrier is shared. This is future closure, not paired substitution coverage. -/
theorem PiInertCarrierHistory.instantiate_typed
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (hx : env.HasType univs Γ x X) (hC : env.HasType univs (X::Γ) C (.sort v))
    (ha : env.HasType univs (X::Γ) a A) (hb : env.HasType univs (X::Γ) b B)
    (H : PiInertCarrierHistory D stage (proofEraseCtx (X::Γ)) (proofErase (X::Γ) C)
      (proofErase (X::Γ) a) (proofErase (X::Γ) b)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (C.inst x))
      (proofErase Γ (a.inst x)) (proofErase Γ (b.inst x)) := by
  have hΓX : OnCtx (X::Γ) (env.IsType univs) := ⟨hΓ, u, hX⟩
  have W : ContextSubstitution (proofEraseCtx (X::Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ x)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓX hx)
      (erasedSubstAgreement_one hΓX hx)
  rw [proofErase_instN hΓX hx Ctx.InstN.zero hC,
    proofErase_instN hΓX hx Ctx.InstN.zero ha, proofErase_instN hΓX hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one]
    using H.substitute W

/-- Missing reflexive action for every typed function. The endpoints of the
function agree, but its carrier-related arguments may differ. All actual typed
futures are admitted, as in FinitePiInertFunctionAction. -/
def FinitePiInertReflexiveAction (D : Definitions) : Prop :=
  ∀ {Γ A B f}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ f (.forallE A B) →
    FinitePiInertFunctionAction D Γ A B f f

/-- Missing action for only the newest variable at its native function type.
The quantification over all typed futures allows that variable to be replaced
by an arbitrary function. No completed function history is assumed here. -/
def FinitePiInertFreshVariableAction (D : Definitions) : Prop :=
  ∀ {Γ A B u}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ (.forallE A B) (.sort u) →
    FinitePiInertFunctionAction D ((.forallE A B)::Γ) A.lift (B.liftN 1 1)
      (.bvar 0) (.bvar 0)

/-- Missing local application law for the newest native function variable.
There is no outer future quantifier: arguments and application are in the
displayed extended context. The returned history still includes all futures.
Even this law is equivalent to universal reflexive action below. -/
def FinitePiInertLocalFreshVariableAction (D : Definitions) : Prop :=
  ∀ {Γ A B u x y stage}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ (.forallE A B) (.sort u) →
    env.HasType univs ((.forallE A B)::Γ) x A.lift →
    env.HasType univs ((.forallE A B)::Γ) y A.lift →
    PiInertCarrierHistory D stage (proofEraseCtx ((.forallE A B)::Γ))
      (proofErase ((.forallE A B)::Γ) A.lift)
      (proofErase ((.forallE A B)::Γ) x) (proofErase ((.forallE A B)::Γ) y) →
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx ((.forallE A B)::Γ))
      (proofErase ((.forallE A B)::Γ) ((B.liftN 1 1).inst x))
      (proofErase ((.forallE A B)::Γ) (.app (.bvar 0) x))
      (proofErase ((.forallE A B)::Γ) (.app (.bvar 0) y))

/-- Extend each actual future by the actual function image. Action of the
fresh variable then supplies reflexive action of the arbitrary function,
including the exact dependent output carrier and complete result history. -/
theorem FinitePiInertFreshVariableAction.reflexive_action
    (H : FinitePiInertFreshVariableAction D) : FinitePiInertReflexiveAction D := by
  intro Γ A B f hΓ hf Γ₀ σ x y stage hΓ₀ W hx hy HX
  obtain ⟨u, hPi⟩ := hf.isType henv hΓ
  have hf' := hf.subst henv.orderedStrong W hΓ₀
  let ρ := σ.cons (f.subst σ)
  have EA : A.lift.subst ρ = A.subst σ := VExpr.lift_subst_cons
  have EB : (B.liftN 1 1).subst ρ.lift = B.subst σ.lift := by
    have E : ((VExpr.forallE A B).lift).subst ρ = (VExpr.forallE A B).subst σ :=
      VExpr.lift_subst_cons
    exact (VExpr.forallE.inj E).2
  have hx' : env.HasType univs Γ₀ x (A.lift.subst ρ) := EA.symm ▸ hx
  have hy' : env.HasType univs Γ₀ y (A.lift.subst ρ) := EA.symm ▸ hy
  have HX' : PiInertCarrierHistory D stage (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.lift.subst ρ)) (proofErase Γ₀ x) (proofErase Γ₀ y) := EA.symm ▸ HX
  have Wρ : Ctx.SubstEq env univs Γ₀ ρ ρ ((.forallE A B)::Γ) :=
    Ctx.SubstEq.cons W hPi hf'
  obtain ⟨n, HN⟩ := H hΓ hPi hΓ₀ Wρ hx' hy' HX'
  exact ⟨n, by simpa only [EB, VExpr.subst_bvar, ρ, VExpr.Subst.cons] using HN⟩

/-- Conversely the native fresh variable is an actual typed function in its
extended context. Thus restricting the source endpoint to this one variable
does not weaken the universal reflexive-action obligation. -/
theorem FinitePiInertReflexiveAction.fresh_variable_action
    (H : FinitePiInertReflexiveAction D) : FinitePiInertFreshVariableAction D := by
  intro Γ A B u hΓ hPi
  have hΓT : OnCtx ((.forallE A B)::Γ) (env.IsType univs) := ⟨hΓ, u, hPi⟩
  exact @H _ _ _ _ hΓT (HasType.bvar .zero)

/-- Exact calibration of the unrestricted future quantifier at fresh variables.
This is an equivalence of missing laws, not a construction of either law. -/
theorem finite_pi_inert_fresh_variable_action_iff_reflexive_action :
    FinitePiInertFreshVariableAction D ↔ FinitePiInertReflexiveAction D :=
  ⟨FinitePiInertFreshVariableAction.reflexive_action,
    FinitePiInertReflexiveAction.fresh_variable_action⟩

/-- Removing the outer future quantifier does not make variable action a
weaker seed. Weaken the supplied argument history under a fresh function
binder, invoke local variable action, then instantiate its completed result
history by the actual function. No action evidence for that image is required
by the history's existing future clause. -/
theorem FinitePiInertLocalFreshVariableAction.reflexive_action
    (H : FinitePiInertLocalFreshVariableAction D) : FinitePiInertReflexiveAction D := by
  intro Γ A B f hΓ hf Γ₀ σ x y stage hΓ₀ W hx hy HX
  have hf' : env.HasType univs Γ₀ (f.subst σ)
      (.forallE (A.subst σ) (B.subst σ.lift)) := hf.subst henv.orderedStrong W hΓ₀
  obtain ⟨u, hPi⟩ := hf'.isType henv hΓ₀
  obtain ⟨⟨v, hA⟩, _⟩ := hPi.forallE_inv henv.ordered
  let T := VExpr.forallE (A.subst σ) (B.subst σ.lift)
  have hΓT : OnCtx (T::Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hPi⟩
  have HXw := HX.weakN hΓ₀ hΓT Ctx.LiftN.one hA hx hy
  obtain ⟨n, HN⟩ := H hΓ₀ hPi (hx.weak henv) (hy.weak henv) HXw
  have hv : env.HasType univs (T::Γ₀) (.bvar 0) T.lift := .bvar .zero
  have hl := hv.app (hx.weak henv)
  have hr := hv.app (hy.weak henv)
  obtain ⟨w, hC⟩ := hl.isType henv hΓT
  have HI := HN.instantiate_typed hΓ₀ hPi hf' hC hl hr
  exact ⟨n, by simpa only [VExpr.lift, ← VExpr.liftN_inst_hi, VExpr.inst_liftN,
    VExpr.inst, VExpr.instVar_zero] using HI⟩

/-- Universal reflexive action includes local variable action at the identity
future. Only the identity typed substitution is used in this direction. -/
theorem FinitePiInertReflexiveAction.local_fresh_variable_action
    (H : FinitePiInertReflexiveAction D) : FinitePiInertLocalFreshVariableAction D := by
  intro Γ A B u x y stage hΓ hPi hx hy HX
  have hΓT : OnCtx ((.forallE A B)::Γ) (env.IsType univs) := ⟨hΓ, u, hPi⟩
  have HA : FinitePiInertFunctionAction D ((.forallE A B)::Γ)
      A.lift (B.liftN 1 1) (.bvar 0) (.bvar 0) := @H _ _ _ _ hΓT (.bvar .zero)
  have HI := Ctx.SubstEq.id henv.ordered hΓT
  obtain ⟨n, HN⟩ := HA hΓT HI (by simpa only [VExpr.subst_id] using hx)
    (by simpa only [VExpr.subst_id] using hy) (by simpa only [VExpr.subst_id] using HX)
  exact ⟨n, by simpa only [VExpr.id_lift, VExpr.subst_id] using HN⟩

/-- The nested future clause already carries the full cost of universal
reflexive function action, even without outer substitution quantification. -/
theorem finite_pi_inert_local_fresh_variable_action_iff_reflexive_action :
    FinitePiInertLocalFreshVariableAction D ↔ FinitePiInertReflexiveAction D :=
  ⟨FinitePiInertLocalFreshVariableAction.reflexive_action,
    FinitePiInertReflexiveAction.local_fresh_variable_action⟩

/-- Reflexive action of the typed evaluation lambda `fun h => h x` consumes
the given history of f and g as its argument history. Independent beta
reductions return the shared applications at their exact dependent carrier.
Hence even reflexive universal action contains full shared application. -/
theorem FinitePiInertReflexiveAction.shared_application
    (H : FinitePiInertReflexiveAction D) : FinitePiInertSharedApplication D := by
  intro stage Γ A B f g x hΓ hf hg hx HF
  obtain ⟨u, hPi⟩ := hf.isType henv hΓ
  let T := VExpr.forallE A B
  let ev := VExpr.lam T (.app (.bvar 0) x.lift)
  have heval : env.HasType univs Γ ev (.forallE T (B.inst x).lift) := by
    apply HasType.lam hPi
    have hv : env.HasType univs (T::Γ) (.bvar 0) T.lift := .bvar .zero
    have happ := hv.app (hx.weak henv)
    simpa only [T, VExpr.lift, VExpr.liftN, ← VExpr.liftN_inst_hi] using happ
  have HA : FinitePiInertFunctionAction D Γ T (B.inst x).lift ev ev := H hΓ heval
  have HI : Ctx.SubstEq env univs Γ VExpr.Subst.id VExpr.Subst.id Γ :=
    Ctx.SubstEq.id henv.ordered hΓ
  have HF' : PiInertCarrierHistory D stage (proofEraseCtx Γ)
      (proofErase Γ (T.subst VExpr.Subst.id)) (proofErase Γ f) (proofErase Γ g) := by
    simpa only [VExpr.subst_id] using HF
  obtain ⟨n, HN⟩ := HA hΓ HI (by simpa only [VExpr.subst_id] using hf)
    (by simpa only [VExpr.subst_id] using hg) HF'
  simp only [VExpr.id_lift, VExpr.subst_id, VExpr.inst_lift] at HN
  have hleft := heval.app hf
  have hright := heval.app hg
  have Rleft : Compute (ErasedLevelCore D) (proofErase Γ (.app ev f))
      (proofErase Γ (.app f x)) := by
    have R := proofErase_beta_forward hΓ hleft (show VExpr.BetaRed (.app ev f)
      ((VExpr.app (.bvar 0) x.lift).inst f) from .beta)
    exact .beta (by simpa only [VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift] using R)
  have Rright : Compute (ErasedLevelCore D) (proofErase Γ (.app ev g))
      (proofErase Γ (.app g x)) := by
    have R := proofErase_beta_forward hΓ hright (show VExpr.BetaRed (.app ev g)
      ((VExpr.app (.bvar 0) x.lift).inst g) from .beta)
    exact .beta (by simpa only [VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift] using R)
  exact ⟨n, HN.endpoint_reducts Rleft Rright⟩

/-- Even local action for the newest native function variable implies the full
proposition front under the established canonical-Eq and closed positive
empty-structure assumptions. Thus restricting only the outer futures cannot
make this a strictly smaller sufficient obligation. The nested future clause
of the returned completed history retains the whole application problem. -/
theorem FinitePiInertLocalFreshVariableAction.propositionFront_of_closed_unit
    (H : FinitePiInertLocalFreshVariableAction D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    PropositionFront :=
  FinitePiInertSharedApplication.propositionFront_of_closed_unit
    (FinitePiInertReflexiveAction.shared_application
      (FinitePiInertLocalFreshVariableAction.reflexive_action H))
    heq hs hreg hoff hRec hi hp hx hf hD hS

end Lean4Lean.VEnv.Strengthening
