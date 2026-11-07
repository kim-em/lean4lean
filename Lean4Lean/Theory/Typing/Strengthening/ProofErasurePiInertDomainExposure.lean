import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStrongNeutralFrames

/-! # Computational domain exposure through non-Pi intermediate types

A typed computational witness replaces the vacuous literal-Pi predicate. Its
output domain retains the full carrier history. Readout at a literal Pi uses
both sides of the computation square, including independent domain residuals.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A computation between literal Pis transports a domain's complete residual
history backwards. The ordinary-core output path identifies the same domain
reduct as the Pi-inert input path. This needs no guarded confluence theorem. -/
theorem PiInertInterpret.domain_history
    (H : PiInertInterpret D n .compute Δ (.forallE C E) (.forallE A B))
    (HA : PiInertCarrierResidual D n Δ A x y) : PiInertCarrierResidual D n Δ C x y := by
  intro C' x' y' RC RX RY
  obtain ⟨shared, RS, RT⟩ := H.2 (.forallE RC .refl)
  obtain ⟨A', B', rfl, RA, RB⟩ := RT.pi_parts (fun R => erased_level_core_no_pi R)
  obtain ⟨C'', E'', EQ, RD⟩ := RS.forallE_domain_inv_of_no_root (fun R => pi_inert_stage_no_pi R)
  cases EQ
  exact .carrierCompute RD (HA RA RX RY)

/-- Domain readout retains all future typed substitutions. The target domain
need not have a literal or rigid shape after those substitutions. -/
theorem PiInertEvidence.domain_history
    (H : PiInertEvidence D n .compute Δ (.forallE C E) (.forallE A B))
    (HA : PiInertCarrierHistory D n Δ A x y) : PiInertCarrierHistory D n Δ C x y :=
  ⟨H.base.domain_history HA.base,
    fun W => (H.future W).domain_history (HA.future W)⟩

/-- A core reduct of the source retains the same interpreted computation
output. Only the source residual is prefixed; no new guarded computation is
substituted or normalized. -/
theorem PiInertEvidence.source_core_reduct
    (H : PiInertEvidence D n .compute Δ a b) (R : Compute (ErasedLevelCore D) a a') :
    PiInertEvidence D n .compute Δ a' b := by
  refine ⟨⟨H.base.1, fun S => H.base.2 (R.trans S)⟩, ?_⟩
  intro Δ' τ W
  exact ⟨(H.future W).1, fun S => (H.future W).2
    ((R.subst (fun HR => erased_level_core_subst HR)).trans S)⟩

/-- A computation toward a typed Pi output and a complete history at its
domain. Non-Pi source syntax must supply the computation witness explicitly;
it never satisfies this predicate merely by failing a syntactic test. -/
def PiInertDomainExposure (D : Definitions) (n : Nat)
    (Δ : List ProofShape) (T x y : ProofShape) : Prop :=
  ∃ A B, PiInertEvidence D n .compute Δ T (.forallE A B) ∧
    PiInertCarrierHistory D n Δ A x y

/-- Future substitution transports the output Pi and domain history together. -/
theorem PiInertDomainExposure.substitute (H : PiInertDomainExposure D n Δ T x y)
    (W : ContextSubstitution Δ Δ' τ) :
    PiInertDomainExposure D n Δ' (T.subst τ) (x.subst τ) (y.subst τ) := by
  obtain ⟨A, B, HC, HA⟩ := H
  exact ⟨A.subst τ, B.subst τ.lift, HC.substitute W, HA.substitute W⟩

/-- A literal Pi reads out a complete guard at its own domain, even if the
stored output Pi has a different domain or codomain. -/
theorem PiInertDomainExposure.readout
    (H : PiInertDomainExposure D n Δ (.forallE C E) x y) :
    PiInertCarrierHistory D n Δ C x y := by
  obtain ⟨A, B, HC, HA⟩ := H
  exact HC.domain_history HA

/-- An already typed literal Pi supplies the reflexive computational witness.
Core confluence retains all source residuals at the same finite stage. -/
theorem PiInertDomainExposure.literal
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HT : TypedSource Δ (.forallE A B))
    (HA : PiInertCarrierHistory D n Δ A x y) :
    PiInertDomainExposure D n Δ (.forallE A B) x y :=
  ⟨A, B, .of_core_join hc HT HT ⟨_, .refl, .refl⟩, HA⟩

/-- A certified computation prefix carries the same exposed domain history
back to arbitrary source syntax, without increasing its stage. -/
theorem PiInertDomainExposure.prefix
    (H : PiInertDomainExposure D n Δ T x y)
    (R : PiInertEvidence D n .compute Δ S T) : PiInertDomainExposure D n Δ S x y := by
  obtain ⟨A, B, HC, HA⟩ := H
  exact ⟨A, B, R.trans HC, HA⟩

/-- Ordinary-core source reduction preserves the original output witness and
the same domain history. It does not require source normalization. -/
theorem PiInertDomainExposure.core_reduct
    (H : PiInertDomainExposure D n Δ T x y)
    (R : Compute (ErasedLevelCore D) T S) : PiInertDomainExposure D n Δ S x y := by
  obtain ⟨A, B, HC, HA⟩ := H
  exact ⟨A, B, HC.source_core_reduct R, HA⟩

/-- Every typed ordinary-core join preserves computational domain exposure in
both directions. This includes identity-beta wrappers and other non-Pi syntax.
General strong conversion is not assumed to have an ordinary-core join. -/
theorem pi_inert_domain_exposure_core_join_iff
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HT : TypedSource Δ T) (HS : TypedSource Δ S)
    (R : ComputeJoin (ErasedLevelCore D) T S) :
    PiInertDomainExposure D n Δ T x y ↔ PiInertDomainExposure D n Δ S x y :=
  ⟨fun H => H.prefix (.of_core_join hc HS HT R.symm),
    fun H => H.prefix (.of_core_join hc HT HS R)⟩

/-- On a typed literal Pi, computational exposure is exactly the full domain
history. Thus adding the computational witness neither loses the desired
native guard nor makes the predicate vacuous at the observation point. -/
theorem pi_inert_domain_exposure_literal_iff
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HT : TypedSource Δ (.forallE A B)) :
    PiInertDomainExposure D n Δ (.forallE A B) x y ↔ PiInertCarrierHistory D n Δ A x y :=
  ⟨PiInertDomainExposure.readout, PiInertDomainExposure.literal hc HT⟩

/-- Raising the finite stage preserves the same computational output and all
future domain histories. No new witness is synthesized. -/
theorem PiInertDomainExposure.raise (H : PiInertDomainExposure D n Δ T x y) (hle : n ≤ m) :
    PiInertDomainExposure D m Δ T x y := by
  obtain ⟨A, B, HC, HA⟩ := H
  exact ⟨A, B, HC.raise hle, HA.raise hle⟩

/-- At a variable's native type, computational domain exposure supplies an
actual neutral application check. Recovery uses the original context oracle;
no assigned-domain type conversion or raw substitution closure is presumed. -/
theorem PiInertDomainExposure.neutral_application
    (H : PiInertDomainExposure D n Δ (.forallE A B) x y)
    (HO : contextOracle Δ i = .forallE A B) :
    ComputedJointCompare (PiInertStage D n) Δ true (.app (.bvar i) x) (.app (.bvar i) y) :=
  by
    apply ComputedJointCheck.appCarrier (A := A) (B := B) ?_ (.leaf .refl)
      (H.readout.base .refl .refl .refl)
    rw [← HO]
    exact .bvar

/-- A guarded Eq recursor inside an arbitrary typed consumer inherits a
returned type's computational domain exposure. Only the index history pays
one stage; the result branch may already have an independent finite stage.
Both full substitution futures and domain residual histories are retained. -/
theorem PiInertDomainExposure.eq_rec_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (ht : env.HasType univs (T :: Γ) t (.sort u))
    (Hα : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b))
    (Hm : PiInertDomainExposure D k (proofEraseCtx Γ) (proofErase Γ (t.inst m)) x y) :
    PiInertDomainExposure D (max (n+1) k) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) x y :=
  (Hm.raise (Nat.le_max_right (n+1) k)).prefix
    ((Hα.eq_rec_consumer heq hs hl hcon hc hreg hoff hRec hΓ hr ht).raise
      (Nat.le_max_left (n+1) k))

/-- The unsaturated five-argument Eq prefix has the same computational-domain
rule, with its returned proof lambda explicitly supplied to the typed consumer.
No general conversion coverage is inferred from this guarded constructor. -/
theorem PiInertDomainExposure.eq_prefix_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (ht : env.HasType univs (T :: Γ) t (.sort u))
    (Hα : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b))
    (Hm : PiInertDomainExposure D k (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam (eqApp w α a b) m.lift))) x y) :
    PiInertDomainExposure D (max (n+1) k) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecBeforeMajor v w α a M m b))) x y :=
  (Hm.raise (Nat.le_max_right (n+1) k)).prefix
    ((Hα.eq_prefix_consumer heq hs hl hcon hreg hoff hRec hΓ hr ht).raise
      (Nat.le_max_left (n+1) k))

/-- The actual smaller neutral-application frame initializes computational
domain exposure. Lower-rank conversion handlers then return it to the native
function type, where readout supplies its domain guard. The two handlers are
the unproved semantic induction cases, not consequences of rank extraction. -/
theorem StrongBounded.neutral_domain_history
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs rank Γ a b C)
    (HE : a = .app (.bvar i) x ∨ b = .app (.bvar i) x)
    (hl : Lookup Γ i (.forallE N M))
    (hN : env.HasType univs Γ N (.sort u)) (hM : env.HasType univs (N::Γ) M (.sort v))
    (argument : ∀ {k A B u v}, k < rank → u.WF univs → v.WF univs →
      StrongBounded env univs k Γ A A (.sort u) →
      StrongBounded env univs k (A::Γ) B B (.sort v) →
      BoundedEndpoint env univs k Γ x A →
      PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ A) rawX rawY)
    (edge : ∀ {j X Y w}, j < rank → StrongBounded env univs j Γ X Y (.sort w) →
      PiInertDomainExposure D stage (proofEraseCtx Γ) (proofErase Γ Y) rawX rawY →
      PiInertDomainExposure D stage (proofEraseCtx Γ) (proofErase Γ X) rawX rawY) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ N) rawX rawY := by
  have HP : PiInertDomainExposure D stage (proofEraseCtx Γ)
      (proofErase Γ (.forallE N M)) rawX rawY :=
    H.neutral_native_pullback HE hl
      (fun T => PiInertDomainExposure D stage (proofEraseCtx Γ) (proofErase Γ T) rawX rawY)
      (by
        intro k A B u v hk hu hv hA hB hX
        have ht := HasType.forallE hA.strong.defeq hB.strong.defeq
        have EE : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A::Γ) B) :=
          if_neg (not_isProof_of_sort hΓ ht)
        rw [EE]
        exact .literal hc ⟨Γ, _, _, hΓ, rfl, ht, EE⟩ (argument hk hu hv hA hB hX))
      (fun hj HE => edge hj HE)
  rw [show proofErase Γ (.forallE N M) = .forallE (proofErase Γ N) (proofErase (N::Γ) M) from
    if_neg (not_isProof_of_sort hΓ (.forallE hN hM))] at HP
  exact HP.readout

end Lean4Lean.VEnv.Strengthening
