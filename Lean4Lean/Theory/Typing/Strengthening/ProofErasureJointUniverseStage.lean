import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUniverseContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPrimitiveRenaming

/-! # Universe context transport at actual joint stages

A stage induction transports typed primitive certificates through context
conversion whose recovery oracles undergo universe terminal replacement.
No arbitrary primitive substitution or semantic head exposure is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape InductiveSignature PropElim
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private UniverseContext UniverseContext.of_defeqCtx UniverseContext.cons
  UniverseContext.interprets UniverseContext.interpretation UniverseContext.lookup UniverseTransport
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUniverseContext
open private oracle_cons_change recovery_outputs_equal
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureUniverseOracleRecovery
variable [Params]

private def PrimitiveUniverseTransport
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ e T out Δ'}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    UniverseContext (proofEraseCtx Γ) Δ' → Step (proofEraseCtx Γ) (proofErase Γ e) out →
    Step Δ' (proofErase Γ e) out

private theorem universe_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : PrimitiveUniverseTransport Step)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : UniverseContext Δ Δ') : ScopedCompute Step Δ' source out := by
  induction R generalizing Γ e T Δ' with
  | base H =>
    have H' := hprim hΓ ht (EΓ ▸ W) (by simpa only [EΓ, Ee] using H)
    exact .base (by simpa only [Ee] using H')
  | beta H => exact .beta H
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R₁
    exact .trans (ih₁ hΓ ht EΓ Ee W) (ih₂ hΓ HE.hasType.2 EΓ EE W)
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EΓ Ef W) (iha hΓ ha EΓ Ea W)
  | proj _ ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 EΓ Em W)
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ hA EΓ EA W)
      (ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (by simp only [proofEraseCtx, EA, EΓ]) Eb (UniverseContext.cons W))
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB (by simp only [proofEraseCtx, EA, EΓ]) EB (UniverseContext.cons W))

private theorem universe_recovery
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hprim : PrimitiveUniverseTransport Step)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ UniverseResultChange out out' := by
  induction R generalizing Γ Γ' e T with
  | bvar => exact ⟨_, .bvar, HO _⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, .refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have EAt := proofErase_defeqCtx hΓ W hA
    obtain ⟨out', HR, HB⟩ := ih (Γ := A :: Γ) (Γ' := A :: Γ') ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (.succ W hA)
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_change HO)
    exact ⟨_, .lam (by simpa only [proofEraseCtx, ← EAt, EA] using HR), .forallE HB⟩
  | app R ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hf EΓ Ef W HO
    obtain ⟨X, Y, u, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep R HR hΓ hf EΓ Ef W
    obtain ⟨B', rfl, HBody⟩ := universe_result_typed_pi hΓ hX HXY EX EY HB
    exact ⟨_, .app HR, HBody.inst⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, BA⟩ := ihA hΓ hA EΓ EA W HO
    obtain ⟨u', rfl⟩ := BA.sort_inv
    have EAt := proofErase_defeqCtx hΓ W hA
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have EΓA := congr (congrArg List.cons EA) EΓ
    change proofEraseCtx (A :: Γ) = _ at EΓA
    have WA := IsDefEqCtx.succ W hA
    obtain ⟨outB, HB, BB⟩ := ihB (Γ := A :: Γ) (Γ' := A :: Γ') hΓA hB EΓA EB WA
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_change HO)
    obtain ⟨v', rfl⟩ := BB.sort_inv
    exact ⟨_, .forallE HA (by simpa only [proofEraseCtx, ← EAt, EA] using HB), .toSort⟩
  | @proj Δ m s info ls doms result j args hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hm.hasType.2 EΓ Em W HO
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ :=
      recovery_outputs_equal hstep R HR hΓ hm.hasType.2 EΓ Em W
    obtain rfl := universe_result_typed_record hi hΓ hX HXY EX EY HB
    exact ⟨_, .proj hi HT hj hlen HR, .refl⟩
  | convert R RC ih =>
    obtain ⟨out', HR, HB⟩ := ih hΓ ht EΓ Ee W HO
    have RC' := RC
    rw [← EΓ] at RC'
    obtain ⟨out'', RS, HS⟩ := HB.compute hhead RC'
    obtain ⟨Y, heY, EY⟩ := proofErase_scoped_typeRecovery_replay hstep
      (W.symm henv.ordered).isType (ht.defeqDFC henv W)
      (by simpa only [← proofErase_defeqCtx hΓ W ht, Ee] using HR)
    have hY := ((heY.isType henv (W.symm henv.ordered).isType).choose_spec).defeqDFC henv
      (W.symm henv.ordered)
    have EY₀ := (proofErase_defeqCtx hΓ W hY).trans EY
    have WT := UniverseContext.of_defeqCtx hΓ W (by simpa only [EΓ] using HO)
    exact ⟨out'', HR.convert (universe_compute hstep hprim RS hΓ hY rfl EY₀ WT), HS⟩

/-- Pi recovery under these oracle changes retains the exact original domain.
Only its codomain may change. This is sufficient to reuse an argument guard
once that guard has been transported to the new context. -/
private theorem universe_recovery_pi
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hprim : PrimitiveUniverseTransport Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (.forallE A B)) :
    ∃ B', ScopedTypeRecovery Step (proofEraseCtx Γ') (proofErase Γ e) (.forallE A B') := by
  obtain ⟨out', HR, HB⟩ := universe_recovery hstep hhead hprim R hΓ ht rfl rfl W HO
  obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep R HR hΓ ht rfl rfl W
  obtain ⟨B', rfl, _⟩ := universe_result_typed_pi hΓ hX HXY EX EY HB
  exact ⟨B', HR⟩

private theorem universe_check
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hprim : PrimitiveUniverseTransport Step)
    (H : JointCheck Step Δ kind sa sb) : JointTransportResult UniverseTransport Step Δ kind sa sb := by
  apply H.transport UniverseTransport hstep
  · intro Δ Δ' τ A WT
    obtain ⟨rfl, W⟩ := WT
    have Eid : ProofShape.Subst.id.lift = ProofShape.Subst.id := by
      funext i
      cases i <;> simp [ProofShape.Subst.lift, ProofShape.Subst.id, ProofShape.liftN]
    exact ⟨Eid, by simpa only [ProofShape.subst_id] using (UniverseContext.cons W (A := A))⟩
  · intro Δ Δ' τ A u WT HS
    obtain ⟨rfl, W⟩ := WT
    exact ContextSubstitution.sort (UniverseContext.interprets W) HS
  · intro Γ Δ Δ' τ e T source out R hΓ ht EΓ Ee WT
    obtain ⟨rfl, W⟩ := WT
    simpa only [ProofShape.subst_id] using universe_compute hstep hprim R hΓ ht EΓ Ee W
  · intro Γ Δ' τ f x y D C A B hΓ hf hx hy R HG WT HG'
    obtain ⟨rfl, W⟩ := WT
    obtain ⟨Γ', hΓ', EΓ', HC⟩ := UniverseContext.interpretation W hΓ rfl
    obtain ⟨B', R'⟩ := universe_recovery_pi hstep hhead hprim hΓ hf HC
      (by simpa only [EΓ'] using (UniverseContext.lookup W)) R
    exact ⟨A, B', by simpa only [ProofShape.subst_id, EΓ'] using R', by simpa only [ProofShape.subst_id] using HG'⟩

private theorem universe_telescope
    (W : IsDefEqCtx env univs [] Γ Γ')
    (WT : UniverseContext (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (hctx : OnCtx (ds ++ Γ) (env.IsType univs)) :
    IsDefEqCtx env univs [] (ds ++ Γ) (ds ++ Γ') ∧
      UniverseContext (proofEraseCtx (ds ++ Γ)) (proofEraseCtx (ds ++ Γ')) := by
  induction ds with
  | nil => exact ⟨W, WT⟩
  | cons A ds ih =>
    obtain ⟨hc, u, hA⟩ := hctx
    obtain ⟨W', WT'⟩ := ih hc
    refine ⟨.succ W' hA, ?_⟩
    have EA := proofErase_defeqCtx hc W' hA
    change UniverseContext (proofErase (ds ++ Γ) A :: proofEraseCtx (ds ++ Γ))
      (proofErase (ds ++ Γ') A :: proofEraseCtx (ds ++ Γ'))
    rw [← EA]
    exact UniverseContext.cons WT'

private theorem universe_family_guard {C : SingletonPrefixCode} (V : C.Valid)
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hprim : PrimitiveUniverseTransport Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (WT : UniverseContext (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => JointCompare Step Δ true))
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => JointCompare Step Δ true))
      Γ' C.data C.levels args program C.layout C.elim := by
  obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
  obtain ⟨S, F, hS, hF, WF⟩ := RecursorData.propElim_wf henv V.registered V.large V.zero
    V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hF.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args
    henv hΓ V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht WF
  have htf := (transportedFamily_typings henv heq WF hctx hps hargs).1
  have hpf := WF.family_prop henv hps hargs
  obtain ⟨Wext, WText⟩ := universe_telescope W WT hctx
  have HC := universe_check hstep hhead hprim HG hctx htf hpf rfl rfl rfl ⟨rfl, WText⟩
  simp only [ProofShape.subst_id] at HC
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison at HG ⊢
  rwa [proofErase_defeqCtx hctx Wext htf, proofErase_defeqCtx hctx Wext hpf] at HC

private theorem universe_singleton
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hprim : PrimitiveUniverseTransport Step) :
    PrimitiveUniverseTransport (JointSingletonPrimitive Step) := by
  intro Γ e T out Δ' hΓ ht WT H
  obtain ⟨Γ', hΓ', EΓ', W⟩ := UniverseContext.interpretation WT hΓ rfl
  have WT' : UniverseContext (proofEraseCtx Γ) (proofEraseCtx Γ') := EΓ' ▸ WT
  refine ⟨?_, ?_⟩
  · exact ⟨Γ', e, T, hΓ', EΓ', ht.defeqDFC henv W, (proofErase_defeqCtx hΓ W ht).symm⟩
  have R := H.2
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      have HH := congrArg ProofShape.constHead (hsrc.symm.trans (proofErase_eq_proof.2 hp))
      simp only [constHead_mkApps, ProofShape.constHead] at HH
      cases HH
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq hΓ ha ⟨_, ht⟩ hcalc HG
    have HC := V.checkWith heq (erased_joint_family_descent hstep) hΓ hg ⟨_, ht⟩ HG
    have ht' := ht.defeqDFC henv W
    have HG' := universe_family_guard V heq hstep hhead hprim hΓ W WT' hg ⟨_, ht⟩ HG
    have HC' := V.checkWith heq (erased_joint_family_descent hstep) hΓ' hg ⟨_, ht'⟩ HG'
    have hn' := mt (isProof_defeqCtx W).2 hn
    have HE := V.output_eq heq hΓ hg HC hn
    rw [hd] at HE
    have HE' := V.output_eq heq hΓ' hg HC' hn'
    have ES := proofErase_defeqCtx hΓ W (HC.defeq henv hΓ).hasType.2
    rw [HE, HE'] at ES
    have EA : original.map (proofErase Γ) = original.map (proofErase Γ') := by
      apply List.map_congr_left
      intro a ha
      obtain ⟨_, hat⟩ := (mkApps_arguments_wf henv hΓ ⟨_, ht⟩).2 a ha
      exact proofErase_defeqCtx hΓ W hat
    rw [← EΓ', ES, EA]
    exact .intro V (by simpa only [List.length_map] using ha) (V.telescope_eq hΓ' hg ⟨_, ht'⟩)
      ((V.guardWith_iff heq hΓ' hg ⟨_, ht'⟩).2 HG')

private theorem universe_prefix
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hprim : PrimitiveUniverseTransport Step) :
    PrimitiveUniverseTransport (JointPrefixPrimitive Step) := by
  intro Γ e T out Δ' hΓ ht WT H
  generalize hsrc : proofErase Γ e = source at H
  cases H with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have HC' := universe_check hstep hhead hprim HC hΓ ha hb rfl Hα Ha Hb ⟨rfl, WT⟩
    simp only [ProofShape.subst_id] at HC'
    exact .intro HC'

private theorem universe_stage (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, PrimitiveUniverseTransport (ErasedJointStage D stage) := by
  intro stage
  induction stage with
  | zero => intro Γ e T out Δ' hΓ ht WT H; exact H
  | succ stage ih =>
    intro Γ e T out Δ' hΓ ht WT H
    rcases H with H | H | H
    · exact .inl (ih hΓ ht WT H)
    · exact .inr (.inl (universe_singleton heq (erased_joint_stage_descent heq hs stage)
        (erased_joint_stage_head stage) ih hΓ ht WT H))
    · exact .inr (.inr (universe_prefix heq (erased_joint_stage_descent heq hs stage)
        (erased_joint_stage_head stage) ih hΓ ht WT H))


private theorem universe_union (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    PrimitiveUniverseTransport (ErasedJointUnion D) := by
  intro Γ e T out Δ' hΓ ht WT ⟨stage, H⟩
  exact ⟨stage, universe_stage heq hs stage hΓ ht WT H⟩

/-- Typed computation retains its literal output through universe oracle
changes at the original finite stage. No primitive substitution premise is needed. -/
theorem proofErase_joint_stage_universe_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (stage : Nat)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ') (proofErase Γ' e) out := by
  rw [← proofErase_defeqCtx hΓ W ht]
  exact universe_compute (erased_joint_stage_descent heq hs stage) (universe_stage heq hs stage) R hΓ ht rfl rfl
    (UniverseContext.of_defeqCtx hΓ W HO)

/-- Typed recovery survives universe oracle changes at the same finite stage,
with its output related by universe terminal replacement rather than exact
syntax equality. Pi domains and registered record results remain exact by
`universe_result_typed_pi` and `universe_result_typed_record`. -/
theorem proofErase_joint_stage_universe_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (stage : Nat)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (ErasedJointStage D stage) (proofEraseCtx Γ') (proofErase Γ' e) out' ∧
      UniverseResultChange out out' := by
  rw [← proofErase_defeqCtx hΓ W ht]
  exact universe_recovery (erased_joint_stage_descent heq hs stage) (erased_joint_stage_head stage) (universe_stage heq hs stage) R hΓ ht rfl rfl W HO

/-- Both typed checking modes transport through universe oracle changes at
the same finite stage. This includes every singleton-generated telescope and Eq
prefix, without arbitrary substitution, carrier re-synthesis or head exposure. -/
theorem proofErase_joint_stage_universe_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (stage : Nat)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T) :
    (JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) →
      JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ') mode (proofErase Γ' a) (proofErase Γ' b)) ∧
    (JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ a) (proofErase Γ b) →
      JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ') (proofErase Γ' T) (proofErase Γ' a) (proofErase Γ' b)) := by
  have WT : UniverseTransport (proofEraseCtx Γ) (proofEraseCtx Γ') ProofShape.Subst.id :=
    ⟨rfl, UniverseContext.of_defeqCtx hΓ W HO⟩
  constructor
  · intro H
    have HC := universe_check (erased_joint_stage_descent heq hs stage) (erased_joint_stage_head stage) (universe_stage heq hs stage) H hΓ ha hb rfl rfl rfl WT
    simpa only [ProofShape.subst_id, proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] using HC
  · intro H
    have HC := universe_check (erased_joint_stage_descent heq hs stage) (erased_joint_stage_head stage) (universe_stage heq hs stage) H hΓ ha hb rfl rfl rfl rfl WT
    simpa only [ProofShape.subst_id, proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb,
      proofErase_defeqCtx hΓ W (ha.isType henv hΓ).choose_spec] using HC

/-- An arbitrary actual binder type may be replaced by a definitionally equal
literal universe while preserving both checking modes. No computation to that
universe or exact recovery certificate is required. -/
theorem proofErase_joint_stage_universe_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (stage : Nat)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T) :
    (JointCompare (ErasedJointStage D stage) (proofEraseCtx (A :: Γ)) mode
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCompare (ErasedJointStage D stage) (proofEraseCtx (.sort v :: Γ)) mode
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) ∧
    (JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx (.sort v :: Γ)) (proofErase (.sort v :: Γ) T)
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (.sort v :: Γ) := .succ (.refl hΓ) HE
  have HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (.sort v :: Γ)) i) := by
    intro i
    cases i with
    | zero =>
      change UniverseResultChange ((proofErase Γ A).liftN 1) ((proofErase Γ (.sort v)).liftN 1)
      rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ HE.hasType.2)]
      exact .toSort
    | succ i => exact .refl
  exact proofErase_joint_stage_universe_context heq hs stage hΓA W HO ha hb

/-- Typed computation retains its literal output through universe oracle
changes at the full joint union. No primitive substitution premise is needed. -/
theorem proofErase_joint_union_universe_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' e) out := by
  rw [← proofErase_defeqCtx hΓ W ht]
  exact universe_compute (erased_joint_union_descent heq hs) (universe_union heq hs) R hΓ ht rfl rfl
    (UniverseContext.of_defeqCtx hΓ W HO)

/-- Typed recovery survives universe oracle changes at the full union,
with its output related by universe terminal replacement rather than exact
syntax equality. Pi domains and registered record results remain exact by
`universe_result_typed_pi` and `universe_result_typed_record`. -/
theorem proofErase_joint_union_universe_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' e) out' ∧
      UniverseResultChange out out' := by
  rw [← proofErase_defeqCtx hΓ W ht]
  exact universe_recovery (erased_joint_union_descent heq hs) (erased_joint_union_head) (universe_union heq hs) R hΓ ht rfl rfl W HO

/-- Both typed checking modes transport through universe oracle changes at
the full union. This includes every singleton-generated telescope and Eq
prefix, without arbitrary substitution, carrier re-synthesis or head exposure. -/
theorem proofErase_joint_union_universe_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T) :
    (JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) →
      JointCompare (ErasedJointUnion D) (proofEraseCtx Γ') mode (proofErase Γ' a) (proofErase Γ' b)) ∧
    (JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ a) (proofErase Γ b) →
      JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' T) (proofErase Γ' a) (proofErase Γ' b)) := by
  have WT : UniverseTransport (proofEraseCtx Γ) (proofEraseCtx Γ') ProofShape.Subst.id :=
    ⟨rfl, UniverseContext.of_defeqCtx hΓ W HO⟩
  constructor
  · intro H
    have HC := universe_check (erased_joint_union_descent heq hs) (erased_joint_union_head) (universe_union heq hs) H hΓ ha hb rfl rfl rfl WT
    simpa only [ProofShape.subst_id, proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] using HC
  · intro H
    have HC := universe_check (erased_joint_union_descent heq hs) (erased_joint_union_head) (universe_union heq hs) H hΓ ha hb rfl rfl rfl rfl WT
    simpa only [ProofShape.subst_id, proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb,
      proofErase_defeqCtx hΓ W (ha.isType henv hΓ).choose_spec] using HC

/-- An arbitrary actual binder type may be replaced by a definitionally equal
literal universe while preserving both checking modes. No computation to that
universe or exact recovery certificate is required. -/
theorem proofErase_joint_union_universe_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T) :
    (JointCompare (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) mode
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCompare (ErasedJointUnion D) (proofEraseCtx (.sort v :: Γ)) mode
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) ∧
    (JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx (.sort v :: Γ)) (proofErase (.sort v :: Γ) T)
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (.sort v :: Γ) := .succ (.refl hΓ) HE
  have HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (.sort v :: Γ)) i) := by
    intro i
    cases i with
    | zero =>
      change UniverseResultChange ((proofErase Γ A).liftN 1) ((proofErase Γ (.sort v)).liftN 1)
      rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ HE.hasType.2)]
      exact .toSort
    | succ i => exact .refl
  exact proofErase_joint_union_universe_context heq hs hΓA W HO ha hb

end Lean4Lean.VEnv.Strengthening
