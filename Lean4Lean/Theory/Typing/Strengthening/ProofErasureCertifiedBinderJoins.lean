import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery

/-! # Exact component criteria for joins beneath certified binders

Finite computation from a displayed lambda or Pi is confluent exactly when
its annotation and body computations are confluent. Only the annotation needs
an actual typing. Replaying that annotation transports residual body paths
between equal contexts. Certified primitives supply this transport without a
global proposition beta law or a confluence assumption for other sources.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- All finite computational forks at one fixed raw source admit a common
reduct in the same context and relation. No assertion at other sources is made. -/
def ScopedConfluentAt (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (source : ProofShape) : Prop :=
  ∀ {left right}, ScopedCompute Step Δ source left → ScopedCompute Step Δ source right →
    ∃ out, ScopedCompute Step Δ left out ∧ ScopedCompute Step Δ right out

variable [Params]

private theorem binder_confluent_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (bind : ProofShape → ProofShape → ProofShape)
    (hinj : ∀ {A b A' b'}, bind A b = bind A' b' → A = A' ∧ b = b')
    (hcongr : ∀ {Δ A A' b b'}, ScopedCompute Step Δ A A' →
      ScopedCompute Step (A :: Δ) b b' → ScopedCompute Step Δ (bind A b) (bind A' b'))
    (hinv : ∀ {Γ A u body out}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ A (.sort u) →
      ScopedCompute Step (proofEraseCtx Γ) (bind (proofErase Γ A) body) out →
      ∃ A' body', out = bind A' body' ∧
        ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) A' ∧
        ScopedCompute Step (proofEraseCtx (A :: Γ)) body body')
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ScopedConfluentAt Step (proofEraseCtx Γ) (bind (proofErase Γ A) body) ↔
      ScopedConfluentAt Step (proofEraseCtx Γ) (proofErase Γ A) ∧
      ScopedConfluentAt Step (proofEraseCtx (A :: Γ)) body := by
  constructor
  · intro H
    constructor
    · intro left right RL RR
      obtain ⟨out, JL, JR⟩ := H (hcongr RL (.refl (e := body))) (hcongr RR .refl)
      obtain ⟨AL, HL, EL⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl RL
      obtain ⟨AR, HR, ER⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl RR
      obtain ⟨AL', bL', EOL, JAL, _⟩ := hinv hΓ HL.hasType.2 (EL.symm ▸ JL)
      obtain ⟨AR', bR', EOR, JAR, _⟩ := hinv hΓ HR.hasType.2 (ER.symm ▸ JR)
      obtain ⟨E, _⟩ := hinj (EOL.symm.trans EOR)
      exact ⟨AL', EL ▸ JAL, E.symm ▸ ER ▸ JAR⟩
    · intro left right RL RR
      obtain ⟨out, JL, JR⟩ := H (hcongr .refl RL) (hcongr .refl RR)
      obtain ⟨AL', bL', EOL, _, JBL⟩ := hinv hΓ hA JL
      obtain ⟨AR', bR', EOR, _, JBR⟩ := hinv hΓ hA JR
      obtain ⟨_, E⟩ := hinj (EOL.symm.trans EOR)
      exact ⟨bL', JBL, E.symm ▸ JBR⟩
  · rintro ⟨HA, HB⟩ left right RL RR
    obtain ⟨AL, bL, rfl, RAL, RBL⟩ := hinv hΓ hA RL
    obtain ⟨AR, bR, rfl, RAR, RBR⟩ := hinv hΓ hA RR
    obtain ⟨Aout, JAL, JAR⟩ := HA RAL RAR
    obtain ⟨bout, JBL, JBR⟩ := HB RBL RBR
    have move {dom x y} (RD : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) dom)
        (R : ScopedCompute Step (proofEraseCtx (A :: Γ)) x y) :
        ScopedCompute Step (dom :: proofEraseCtx Γ) x y := by
      obtain ⟨A₀, HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl RD
      have H := R.defeqCtx hsubst hΓ (IsDefEqCtx.succ .zero HE)
      simpa only [proofEraseCtx, EA] using H
    exact ⟨bind Aout bout, hcongr JAL (move RAL JBL), hcongr JAR (move RAR JBR)⟩

/-- Finite lambda forks factor exactly into annotation and original-context
body forks. The raw body need not be typed, and the relation stays unchanged.
Soundness and interpreted primitive substitution handle changing annotations. -/
theorem scoped_lambda_confluent_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ScopedConfluentAt Step (proofEraseCtx Γ) (.lam (proofErase Γ A) body) ↔
      ScopedConfluentAt Step (proofEraseCtx Γ) (proofErase Γ A) ∧
      ScopedConfluentAt Step (proofEraseCtx (A :: Γ)) body := by
  apply binder_confluent_iff hstep hsubst ProofShape.lam ProofShape.lam.inj
    (fun R S => .lam R S) ?_ hΓ hA
  intro Γ A u body out hΓ hA R
  exact R.lam_inv_typed hstep hsubst hhead hΓ hA rfl

/-- The same exact criterion holds for Pi computation. In particular a
dependent codomain's residuals can be reindexed to both computed domains
without a global carrier-conversion or proposition-transport premise. -/
theorem scoped_forall_confluent_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ScopedConfluentAt Step (proofEraseCtx Γ) (.forallE (proofErase Γ A) body) ↔
      ScopedConfluentAt Step (proofEraseCtx Γ) (proofErase Γ A) ∧
      ScopedConfluentAt Step (proofEraseCtx (A :: Γ)) body := by
  apply binder_confluent_iff hstep hsubst ProofShape.forallE ProofShape.forallE.inj
    (fun R S => .forallE R S) ?_ hΓ hA
  intro Γ A u body out hΓ hA R
  exact R.forallE_inv_typed hstep hsubst hhead hΓ hA rfl

/-- Certified joint primitives discharge all lambda factorization premises.
No whole-union beta transport, source body typing or global confluence is
assumed; the two component criteria are the exact remaining conditions. -/
theorem certified_lambda_confluent_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ScopedConfluentAt (ErasedBetaStableJoint D) (proofEraseCtx Γ)
        (.lam (proofErase Γ A) body) ↔
      ScopedConfluentAt (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A) ∧
      ScopedConfluentAt (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) body :=
  scoped_lambda_confluent_iff (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) erased_beta_stable_joint_head hΓ hA

/-- Certified Pi forks likewise reduce exactly to their domain and codomain
forks at the original contexts, with no additional transport obligation. -/
theorem certified_forall_confluent_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ScopedConfluentAt (ErasedBetaStableJoint D) (proofEraseCtx Γ)
        (.forallE (proofErase Γ A) body) ↔
      ScopedConfluentAt (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A) ∧
      ScopedConfluentAt (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) body :=
  scoped_forall_confluent_iff (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) erased_beta_stable_joint_head hΓ hA

end Lean4Lean.VEnv.Strengthening
