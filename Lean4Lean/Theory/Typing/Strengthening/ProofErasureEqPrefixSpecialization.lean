import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedSpecialization

/-! # A reusable target completion for computed and fresh Eq prefixes

The source context may accumulate fresh eta binders. A typed substitution
specializes its current prefix into a fixed target completion, up to pointwise
semantic equality. Computation is read in its source scope; only the resulting
equalities and actual terms are substituted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erased_carrier_recovered_singleton_rule_descent
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.liftN_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- The chosen substitution and pending target arguments of a prefix
specialization. Keeping these witnesses explicit permits later binder
instantiation to compare its actual argument with the chosen target image. -/
def EqPrefixSpecializationAt (Γ Δ : List VExpr) (v w v' w' : VLevel)
    (original pre : List VExpr) (σ : VExpr.Subst) (pending : List VExpr) : Prop :=
  Ctx.SubstEq env univs Δ σ σ Γ ∧
    env.IsDefEqU univs Δ (.const ``Eq.rec [v,w]) (.const ``Eq.rec [v',w']) ∧
    List.Forall₂ (env.IsDefEqU univs Δ) original (pre.map (·.subst σ) ++ pending)

/-- The current Eq prefix has a typed specialization into the original target
argument vector. Head levels and all arguments may have changed semantically.
The missing target arguments are actual terms, not substitution closure of a
raw guard or a native recovery certificate for its images. -/
def EqPrefixSpecialization (Γ Δ : List VExpr) (v w v' w' : VLevel)
    (original pre : List VExpr) : Prop :=
  ∃ σ pending, EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending

/-- Forget the chosen substitution while retaining the existing specialization
interface. This is only existential packaging of the same witnesses. -/
theorem EqPrefixSpecializationAt.forget
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending) :
    EqPrefixSpecialization Γ Δ v w v' w' original pre := ⟨σ, pending, H⟩

/-- The original typed vector starts the specialization invariant with the
identity substitution. Taking a prefix then supplies its initial completion. -/
theorem EqPrefixSpecialization.of_typed
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T) :
    EqPrefixSpecialization Γ Γ v w v w original original := by
  refine ⟨VExpr.Subst.id, [], Ctx.SubstEq.id henv.ordered hΓ,
    VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩, ?_⟩
  simp only [VExpr.subst_id, List.map_id_fun', id, List.append_nil]
  exact List.Forall₂.rfl (mkApps_arguments_wf henv hΓ ⟨_, ht⟩).2

private theorem args_subst
    (hΔ : OnCtx Δ (env.IsType univs)) (WS : Ctx.SubstEq env univs Δ σ σ Γ)
    (H : List.Forall₂ (env.IsDefEqU univs Γ) args args') :
    List.Forall₂ (env.IsDefEqU univs Δ) (args.map (·.subst σ)) (args'.map (·.subst σ)) := by
  induction H with
  | nil => exact .nil
  | cons H _ ih =>
    obtain ⟨_, H⟩ := H
    exact .cons (H.subst henv WS hΔ).toU ih

/-- A shorter selected prefix retains the same specialization; the omitted
source arguments become part of its actual target completion. -/
theorem EqPrefixSpecializationAt.take
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending) (arity : Nat) :
    EqPrefixSpecializationAt Γ Δ v w v' w' original (pre.take arity) σ
      ((pre.drop arity).map (·.subst σ) ++ pending) := by
  obtain ⟨WS, HC, HA⟩ := H
  refine ⟨WS, HC, ?_⟩
  simpa only [← List.append_assoc, ← List.map_append, List.take_append_drop] using HA

/-- The existential interface inherits truncation from the same chosen
substitution; the omitted source arguments become its target completion. -/
theorem EqPrefixSpecialization.take
    (H : EqPrefixSpecialization Γ Δ v w v' w' original pre) (arity : Nat) :
    EqPrefixSpecialization Γ Δ v w v' w' original (pre.take arity) := by
  obtain ⟨σ, pending, H⟩ := H
  exact (H.take arity).forget

/-- Component and head equalities preserve the original target completion.
Only these semantic equalities are specialized, after their source readout. -/
theorem EqPrefixSpecializationAt.congr
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HP : List.Forall₂ (env.IsDefEqU univs Γ) pre pre') :
    EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending := by
  obtain ⟨WS, Hhead, HA⟩ := H
  obtain ⟨_, HC⟩ := HC
  have HCΔ : env.IsDefEqU univs Δ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']) := by
    simpa only [VExpr.subst] using (HC.subst henv WS hΔ).toU
  have HPΔ := args_subst hΔ WS HP
  have Hreverse : List.Forall₂ (env.IsDefEqU univs Δ) (pre.map (·.subst σ) ++ pending) original :=
    HA.flip.imp (fun _ _ H => IsDefEqU.symm H)
  have Hrefl : List.Forall₂ (env.IsDefEqU univs Δ)
      (pre.map (·.subst σ) ++ pending) (pre.map (·.subst σ) ++ pending) :=
    Hreverse.trans (fun _ _ _ H K => H.trans henv hΔ K) HA
  have Hpending : List.Forall₂ (env.IsDefEqU univs Δ) pending pending := by
    simpa only [List.drop_left] using
      Lean4Lean.List.forall₂_drop Hrefl (pre.map (·.subst σ)).length
  exact ⟨WS, Hhead.trans henv hΔ HCΔ,
    HA.trans (fun _ _ _ H K => H.trans henv hΔ K) (HPΔ.append' Hpending)⟩

/-- Existential specialization inherits component congruence from the
version retaining its chosen substitution and pending target arguments. -/
theorem EqPrefixSpecialization.congr
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' original pre)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HP : List.Forall₂ (env.IsDefEqU univs Γ) pre pre') :
    EqPrefixSpecialization Γ Δ v w v'' w'' original pre' := by
  obtain ⟨σ, pending, H⟩ := H
  exact (H.congr hΔ HC HP).forget

/-- Pointwise raw computation below ambient unused binders is reified before
updating the specialization. The resulting prefix has an exact erased image
and the original source assignment, ready for another recovered eta domain. -/
theorem EqPrefixSpecializationAt.compute
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      ((pre.map (proofErase Γ)).map (·.liftN count offset)) raw) :
    ∃ pre', EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      ((pre'.map (proofErase Γ)).map (·.liftN count offset)) = raw ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F := by
  obtain ⟨pre', HP, EP, HE⟩ := proofErase_scoped_spine_arguments_descend hsource hΓ hΓ' W HC hf HA
  exact ⟨pre', H.congr hΔ HC HP, EP, HE⟩

/-- The existing computation interface forgets only the selected target
substitution; its typed component readout is unchanged. -/
theorem EqPrefixSpecialization.compute
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' original pre)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      ((pre.map (proofErase Γ)).map (·.liftN count offset)) raw) :
    ∃ pre', EqPrefixSpecialization Γ Δ v w v'' w'' original pre' ∧
      ((pre'.map (proofErase Γ)).map (·.liftN count offset)) = raw ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F := by
  obtain ⟨σ, pending, H⟩ := H
  obtain ⟨pre', H', EP, HE⟩ := H.compute hsource hΓ hΓ' W hΔ hf HC HA
  exact ⟨pre', H'.forget, EP, HE⟩

/-- Opening eta consumes the explicitly chosen next target argument and
retains the extended substitution. Later binder consumption can therefore
compare its actual argument with this particular target image. -/
theorem EqPrefixSpecializationAt.eta
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (x :: rest))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B)) :
    EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original
      (pre.map VExpr.lift ++ [.bvar 0]) (σ.cons x) rest := by
  obtain ⟨WS, HC, HA⟩ := H
  have HE := IsDefEqU.mkApps_args hΔ HC HA ht
  have ht' := (HE.of_l henv hΔ ht).hasType.2
  rw [VExpr.mkApps_append] at ht'
  obtain ⟨Tx, hfx⟩ := VExpr.WF.of_mkApps henv hΔ (f := .app _ x) ⟨_, ht'⟩
  have hfx : env.HasType univs Δ
      (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst σ))) x) Tx := hfx
  obtain ⟨_, _, hf', hx⟩ := hfx.app_inv henv hΔ
  have hfσ : env.HasType univs Δ
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst σ)))
      (.forallE (A.subst σ) (B.subst σ.lift)) := by
    simpa only [VExpr.subst_mkApps, VExpr.subst] using hf.subst henv.orderedStrong WS hΔ
  have hxA := argument_at_displayed_domain hΔ hf' hfσ hx
  have WS' : Ctx.SubstEq env univs Δ (σ.cons x) (σ.cons x) (A :: Γ) := .cons WS hA hxA
  refine ⟨WS', HC, ?_⟩
  simpa only [List.map_append, List.map_map, Function.comp_def, VExpr.lift_subst_cons,
    List.map_cons, List.map_nil, VExpr.subst, VExpr.Subst.cons,
    List.append_assoc, List.cons_append, List.nil_append] using HA

/-- Opening one more eta binder preserves the same target completion when
its next target argument exists. The explicit-witness version performs the
extension; this interface forgets only the selected substitution. -/
theorem EqPrefixSpecialization.eta
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' original pre)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hlen : pre.length < original.length) :
    EqPrefixSpecialization (A :: Γ) Δ v w v' w' original (pre.map VExpr.lift ++ [.bvar 0]) := by
  obtain ⟨σ, pending, H⟩ := H
  have hlength := H.2.2.length_eq
  cases pending with
  | nil => simp only [List.length_append, List.length_map, List.length_nil] at hlength; omega
  | cons x rest => exact (H.eta hΔ ht hA hf).forget

/-- A recovered singleton at the current source prefix reads the original
target equation, regardless of how many specialization-preserving prefix
computations, truncations, and fresh eta extensions preceded it. Ambient
unused binders are removed before the semantic equation is specialized. -/
theorem EqPrefixSpecialization.read_singleton
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HG : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      ((proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)).liftN count offset) target) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨σ, pending, WS, HC, HA⟩ := H
  obtain ⟨_, _, HL, _⟩ := erased_carrier_recovered_singleton_rule_descent heq hstep hΓ hΓ' W hf HG
  rw [proofErase_const_spine hΓ hf hn] at HL
  have HE := IsDefEqU.mkApps_congr_left henv hΔ HC (show
    VExpr.WF env univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) [α,a,M,minor,b]) from ⟨_, ht⟩)
  have ht' := (HE.of_l henv hΔ ht).hasType.2
  exact proofErase_recovered_singleton_eq_prefix_specialize_congr heq hstep.descent
    hΓ ⟨_, hf⟩ hΔ ht' WS HA HL.2

/-- Read a singleton on any prefix after another component computation.
This packages reification, preservation of the target completion, truncation,
ambient descent and semantic readout; it can be used after any fresh extensions. -/
theorem EqPrefixSpecialization.read_computed_singleton
    (heq : env.HasCanonicalEq) (hsource : ErasedScopedPrimitiveDescent Source)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      ((pre.map (proofErase Γ)).map (·.liftN count offset)) raw)
    (HG : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.take arity)) target) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨pre', HS, EP, HE⟩ := H.compute hsource hΓ hΓ' W hΔ hf HC HA
  have hnew := HE.hasType.2
  have hnnew : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') :=
    fun hp => hn ((isProof_congr hΓ HE).2 hp)
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.take arity)) (pre'.drop arity)) F := by
    rw [← VExpr.mkApps_append, List.take_append_drop]; exact hnew
  obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsplit⟩
  have hnp := nonproof_spine_head hΓ hsplit (by
    simpa only [← VExpr.mkApps_append, List.take_append_drop] using hnnew)
  apply (HS.take arity).read_singleton heq hstep hΓ hΓ' W hΔ ht hp hnp
  rw [proofErase_const_spine hΓ hp hnp, ProofShape.liftN_mkApps]
  simpa only [← EP, List.map_take, ProofShape.liftN] using HG

/-- Open another eta binder and read a computed singleton there using the
same original target completion. The prefix may already contain older fresh
binders; no direct identification of its next argument with an original target
slot is required, since the specialization witness supplies that argument. -/
theorem EqPrefixSpecialization.read_fresh_singleton
    (heq : env.HasCanonicalEq) (hsource : ErasedScopedPrimitiveDescent Source)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecialization Γ Δ v w v' w' [α,a,M,minor,b] pre)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hlen : pre.length < 5)
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx (A.liftN count offset :: Γ')))
      ((((pre.map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++ [etaArgument u]) raw)
    (RL : ScopedCompute Source (proofEraseCtx (A.liftN count offset :: Γ'))
      (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HG : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx (A.liftN count offset :: Γ'))
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (raw.take arity)) target) :
    env.IsDefEq univs Δ a b α := by
  let fresh := pre.map VExpr.lift ++ [.bvar 0]
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) :=
    ⟨hΓ', u, hA.weakN henv W⟩
  have EE : VExpr.mkApps (.const ``Eq.rec [v',w']) fresh =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [fresh, VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have hbody : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) fresh) B := by
    rw [EE]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body hΓ hA hf hn
  rw [← EE] at EB
  have hnb : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) fresh) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  have Epre : (pre.map VExpr.lift).map (proofErase (A :: Γ)) =
      (pre.map (proofErase Γ)).map (·.liftN 1) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv hΓ ⟨_, hf⟩).2 e he
    exact proofErase_liftN hΓ hΓA Ctx.LiftN.one ht
  have Evector : ((fresh.map (proofErase (A :: Γ))).map (·.liftN count (offset+1))) =
      ((((pre.map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++ [etaArgument u]) := by
    simp only [fresh, List.map_append, Epre, List.map_cons, List.map_nil,
      proofErase_fresh_argument hΓ hA, etaArgument_liftN, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro e _
    exact (ProofShape.liftN_comm _ count 1 offset 0 (Nat.zero_le _)).symm
  obtain ⟨Tc, hc⟩ := VExpr.WF.of_mkApps henv hΓA ⟨_, hbody⟩
  have EC : proofErase (A :: Γ) (.const ``Eq.rec [v',w']) = .const ``Eq.rec [v',w'] :=
    if_neg (nonproof_spine_head hΓA hbody hnb)
  obtain ⟨c', HC, EC'⟩ := proofErase_scoped_compute_descend hsource hΓA hΓA' W.succ hc rfl
    (by simpa only [EC, ProofShape.liftN] using RL)
  obtain rfl := erase_const_inv (ProofShape.liftN_const_inv EC')
  have HF := H.eta hΔ ht hA hf hlen
  exact HF.read_computed_singleton heq hsource hstep hΓA hΓA' W.succ hΔ ht hbody hnb
    HC.toU (Evector.symm ▸ HA) HG

end Lean4Lean.VEnv.Strengthening
