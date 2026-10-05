import Lean4Lean.Theory.Typing.AnchoredNativeSeededSpine
import Lean4Lean.Theory.Typing.AnchoredLiteralPi

/-! The application consumer required by two-typing coherence.  Its function
premise transports arbitrary TYPE certificates, without a value observation
of the function or application.  This is a consumer of the proposed smaller
coherence call, not a proof of that call for arbitrary original derivations.
The typed cut reindexing needed to implement the argument premise remains a
separate obligation; the existing source syntax used here is type-unindexed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The required type-coherence contract at one source realization.  It is
stronger than reindexing an existing value observation: it accepts every
available code query and requires no observation of the common term. -/
def CodeCoherence (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (left right : VExpr) : Prop :=
  ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    CodeCert env U registry target locals σ left profile footprint →
    footprint.Available available →
    Nonempty (CodeTransferResult env U registry target locals σ σ available left right profile)

theorem literalPiBody
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {A B C D prototypeDomain prototypeBody x : VExpr}
    {n : Nat} {domain result : Profile n} {key : Key n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (bridge : TypeRelated env U registry Γ (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody domain [(key, result)]))
    (admitted : Admitted env U registry Γ key x x) :
    TypeRelated env U registry Γ (B.inst x) (D.inst x) result := by
  have base := bridge Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody domain [(key, result)])
    (List.mem_singleton_self _)
  have route := witness.leftExposure.insertion henv
  have argument := route.admitted henv admitted
  have bodies := witness.rowBodies key result (List.mem_singleton_self _)
    witness.context .refl (.refl (route.targetWF henv hΓ))
    (x.lift' witness.map) (x.lift' witness.map) (by
      simpa only [Lift.comp, Admitted] using argument)
  have left := witness.leftExposure.literalPi_components.2
  have right := witness.rightExposure.literalPi_components.2
  apply route.codeBack henv hscoped
  have pair := bodies.2.2
  simpa only [TypeRelated, Lift.comp, lift'_refl, Profile.rename_refl,
    lift'_depth_zero (l := Lift.refl.cons) rfl, left, right, lift'_inst_hi] using pair

theorem rowInstantiate
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalBody : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (row : PiRowCertificate env U registry target locals σ available A B key result)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (argumentResult : GradedResult env U registry target locals σ available argument key.input) :
    Nonempty (CertificateResult env U registry target locals σ available (B.inst argument) result) := by
  obtain ⟨anchored⟩ := row.reanchor henv hscoped hTarget closed formedA substitutions fits
    originalDomain originalBody admitted
  have bodyScope := formedB.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  have outsideLive := fits.forward.leavesLive henv hscoped hTarget anchored.outsideAvailable
    (anchored.pack.scoped (anchored.body.scoped bodyScope))
  exact anchored.body.instantiate henv hscoped hTarget closed argumentResult
    anchored.pack anchored.covered anchored.outsideAvailable outsideLive

theorem lower_raised {n N : Nat} (bound : n ≤ N) (profile : Profile n) :
    lowerProfile n bound (raiseProfile N bound profile) = profile := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simp only [raiseProfile_self, lowerProfile_self]
    · have low : n ≤ N := by omega
      rw [lowerProfile_step low, raiseProfile_step low, Profile.down_pad]
      exact ih low

/-- Consume the exact function-type coherence call in the paired application
case.  The argument input is produced from the incoming result certificate's
actual cuts.  No value observation of f or f a is required. -/
theorem pairedApplication
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B C D a : VExpr} {domainLevel bodyLevel : VLevel}
    (argument : OriginalTypePayload sourceEnv env U registry source a A)
    (rightDomain : OriginalTypePayload sourceEnv env U registry source C (.sort domainLevel))
    (rightBody : OriginalTypePayload sourceEnv env U registry (C :: source) D (.sort bodyLevel))
    (functionTypes : CodeCoherence env U registry target locals σ available
      (.forallE A B) (.forallE C D))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available) :
    CodeCoherence env U registry target locals σ available (B.inst a) (D.inst a) := by
  intro n result before certificate resources
  let seed : NativeArgumentSeed env U registry target locals σ available a :=
    ⟨0, .empty, [], .empty, by intro i need member; cases member⟩
  obtain ⟨frame, _⟩ := certificate.seededApplicationInput henv hle argument seed closed hTarget
    substitutions fits resources
  obtain ⟨changed⟩ := functionTypes frame.certificate frame.resources
  have formedC := rightDomain.1.defeq.mono hle
  have formedD := rightBody.1.defeq.mono hle
  have origins := changed.certificate.piOrigins henv hscoped hTarget closed formedC formedD
    substitutions fits rightDomain.2 rightBody.2 changed.available
  obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) frame.key _ (List.mem_singleton_self _)
  have admitted : Admitted env U registry target frame.key (a.subst σ) (a.subst σ) := frame.guard.anchor
  have admissionCopy := admitted
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := admissionCopy
  have live := Related.live henv hscoped hTarget anchorRelated
  let argumentResult : GradedResult env U registry target locals σ available a frame.key.input :=
    { rank := frame.collected.rank
      bound := Nat.le_refl _
      raw := frame.input
      footprint := frame.seed.footprint ++ frame.collected.argumentFootprint
      observation := frame.argumentObservation
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := frame.argumentResources
      live := live }
  obtain ⟨rightCode⟩ := rowInstantiate henv hscoped hTarget closed formedC formedD
    substitutions fits rightDomain.2 rightBody.2 row admitted argumentResult
  have paired := literalPiBody henv hscoped hTarget
    (by simpa only [SeededApplicationCodeInput.profile, subst] using changed.related) admitted
  have bound := Nat.le_trans (Nat.le_max_left n frame.seed.rank) frame.collected.bound
  refine ⟨⟨rightCode.footprint, rightCode.certificate.lowerRaised bound, rightCode.resources, ?_⟩⟩
  have lower := TypeRelated.lower henv bound paired
  simpa only [lower_raised, subst_inst] using lower

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
