import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut

/-! # Guarded roots inside a short Eq eta body

Before its proof major, every typed canonical Eq recursor prefix has a Pi
assignment. Its arity excludes ordinary iota and its type excludes structure
eta. After level and wrapper exclusions, only singleton and function eta roots
remain. Reading their guards or eliminating nested eta is not asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

omit [Params] in
private theorem piArity_inst_le (T x : VExpr) (k : Nat) : T.piArity ≤ (T.inst x k).piArity := by
  induction T generalizing k with
  | forallE A B _ ih => simpa only [VExpr.piArity, VExpr.inst] using Nat.add_le_add_right (ih (k+1)) 1
  | _ => simp only [VExpr.piArity]; exact Nat.zero_le _

private theorem typed_spine_pi_of_arity
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (HT : VExpr.WF env univs Γ (VExpr.mkApps f args)) (hlen : args.length < T.piArity) :
    ∃ A B, env.HasType univs Γ (VExpr.mkApps f args) (.forallE A B) := by
  induction args generalizing f T with
  | nil =>
    cases T <;> simp only [VExpr.piArity, List.length_nil] at hlen
    all_goals try omega
    exact ⟨_, _, hf⟩
  | cons x xs ih =>
    cases T <;> simp only [VExpr.piArity, List.length_cons] at hlen
    all_goals try omega
    rename_i A B
    have happ : VExpr.WF env univs Γ (.app f x) := VExpr.WF.of_mkApps henv hΓ HT
    obtain ⟨_, _, hf', hx⟩ := happ.app_inv henv hΓ
    have hxA := argument_at_displayed_domain hΓ hf' hf hx
    apply ih (hf.app hxA) HT
    have hB := piArity_inst_le B x 0
    omega

/-- Every typed canonical Eq recursor prefix before the major has an actual
Pi assignment, independently of its supplied type and universe arguments. -/
theorem eq_rec_short_prefix_pi
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (HT : VExpr.WF env univs Γ (VExpr.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length ≤ 5) :
    ∃ A B, env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec ls) args) (.forallE A B) := by
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ HT
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv hΓ hc
  rw [heq.2.2.1] at hci
  cases Option.some.inj hci
  have hf := HasType.const (Γ := Γ) heq.2.2.1 hw hl
  exact typed_spine_pi_of_arity hΓ hf HT (by change args.length < 6; omega)

/-- A typed erased Eq prefix of at most five arguments cannot be a native
structure major: its Pi assignment is separated from every rigid structure family. -/
theorem typed_eq_short_prefix_no_structure
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length ≤ 5) :
    ¬ NativeMaskedStructureExpansion Step Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) target := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨actual, rfl, Eargs⟩ := proofErase_const_spine_inv Ee
  obtain ⟨A, B, hf⟩ := eq_rec_short_prefix_pi heq hΓ ⟨_, ht⟩ (by
    simpa only [Eargs, List.length_map] using hlen)
  intro H
  rw [← Ee] at H
  cases H with
  | intro hi _ _ _ RN =>
    obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
    obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv EF
    obtain ⟨_, hF⟩ := hfF.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hF
      (hfF.uniqU henv hΓ hf)

/-- The remaining inner root families. This records actual primitive guards;
it does not assume their readout, substitution closure or eta elimination. -/
def EqEtaGuardedRoot (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (source target : ProofShape) : Prop :=
  ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ source target ∨
    ∃ k, k < n ∧
      (CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ source target ∨
       NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target)

/-- Classify a typed short Eq prefix after level, constant and identity
expansions have been excluded. Core reduction lacks its proof major and
structure eta contradicts the prefix's Pi assignment. -/
theorem pi_inert_eq_short_guarded_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length ≤ 5)
    (H : PiInertStage D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ LevelPrimitive univs (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HC : ¬ ConstantExpansion (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HI : ∀ Recovery, ¬ NativeIdentityExpansion Recovery Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    EqEtaGuardedRoot D n Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) target := by
  classical
  by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target
  · exact .inl HQ
  · have Hcore : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) args) target := by
      rintro (Hcore | Hlevel)
      · exact erased_iota_eqRec_no_root hreg hoff hRec (constHead_mkApps _ _)
          (.inl ⟨args, ls, rfl, hlen⟩) Hcore
      · exact HN Hlevel
    have Hstruct := typed_eq_short_prefix_no_structure (target := target) heq
      (erased_static_structure_eta_expansion_stage_descent heq hs n) HT hlen
    rcases static_other_spine_root H.1 Hcore HQ Hstruct with Hconst | ⟨k, hk, HG | HId | HEta⟩
    · exact (HC Hconst).elim
    · exact .inr ⟨k, hk, .inl HG⟩
    · exact (HI _ HId).elim
    · exact .inr ⟨k, hk, .inr HEta⟩

/-- Refine the very same counted body witness to the three remaining guarded
root forms. Component ancestry bounds its prefix by five; all lambda, argument,
prefix, tail, typing and minimality witnesses are retained without reselection. -/
theorem CountedEtaBodySpineCut.eq_guarded
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hshort : pre.length ≤ 4)
    (H : CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct) :
    CountedEtaBodySpineCut D n Δ ``Eq.rec ls pre A u args out ct (EqEtaGuardedRoot D) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, _⟩ := H
  have hlen := HA.length_eq
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlen
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hcut, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, ?_⟩
  exact pi_inert_eq_short_guarded_root heq hs hreg hoff hRec HT (by omega) HR HN HC HI

end Lean4Lean.VEnv.Strengthening
