import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertificateDescent

/-! # Certificate descent at every joint stage

General singleton guards descend beneath their generated telescope. Specialized
Eq prefixes retain their carrier guard. These two constructions close the stage
induction for computation certificates without changing the finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

namespace GuardedSingleton
variable {S : SingletonLayout} {E : PropElim}
/-- The lower generated family guard retains its Target comparison certificate;
its endpoints are typed before the mutual comparison descent is used. -/
private theorem family_guard_certificate_below (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (Wblock : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args))
    (HG : FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare Step Δ true)) Γ' data levels (args.map (·.liftN n k)) (program.rename ((Lift.refl.skipN n).consN k)) S E) :
    FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare Target Δ true)) Γ data levels args program S E := by
  let ρ := (Lift.refl.skipN n).consN k
  have hW : Ctx.Lift' ρ Γ Γ' := Ctx.liftN_iff_lift'.1 Wblock
  have HG : FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.JointCompare Step Δ true)) Γ' data levels
      (args.map (·.lift' ρ)) (program.rename ρ) S E := by
    simpa only [ρ, lift'_consN_skipN] using HG
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨hctx, hps, _, hidx, _, _, hargs⟩ :=
    registered_opened_args henv hΓ H hlarge hzero hw hlen howner hS hE hg ht W
  have hsrc := H.prefixType henv hΓ hw hg ht
  have hsrc' := hsrc.weak' henv.ordered hW
  rw [← RecursorData.PrefixUnfolding.rename_type] at hsrc'
  have hctx' := (hsrc'.etaOpen_wf henv.ordered hΓ').1
  have hW' := RecursorData.renameDomains_context program.domains hW
  have Wext : Ctx.LiftN n (k + program.domains.length)
      (program.domains.reverse ++ Γ) ((program.rename ρ).domains.reverse ++ Γ') := by
    apply Ctx.liftN_iff_lift'.2
    simpa only [ρ, Lift.consN_consN, RecursorData.PrefixUnfolding.rename] using hW'
  have hlenD : program.domains.length = data.majorOffset + 1 - args.length := by
    obtain ⟨_, _, _, _, hh, _⟩ := RecursorData.singletonUnfolding_layout hg
    exact hh
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr
    (RecursorData.singletonUnfolding_spec hg).2.1
  have hmajor : (VExpr.bvar 0).lift' (ρ.consN program.domains.length) = .bvar 0 := by
    cases hn : program.domains.length with
    | zero => omega
    | succ n => rfl
  let ps := (data.openedArguments args).take data.numParams
  let idx := ((data.openedArguments args).drop data.indexOffset).take data.numIndices
  have htf := (transportedFamily_typings henv heq W hctx hps hargs).1
  have hpf := W.family_prop henv hps hargs
  have htfLift := transportedFamily_lift' henv heq W hctx hps hargs (ρ.consN program.domains.length)
  rw [hmajor] at htfLift
  have hpfLift : (mkApps E.family (ps ++ idx)).lift' (ρ.consN program.domains.length) =
      mkApps E.family (ps.map (·.lift' (ρ.consN program.domains.length)) ++
        idx.map (·.lift' (ρ.consN program.domains.length))) := by
    rw [lift'_mkApps, W.family_closed.lift'_eq .zero, List.map_append]
  unfold FamilyGuard at HG ⊢
  simp only [openedArguments_lift', ← hlenD, ← List.map_take, ← List.map_drop] at HG
  rw [← htfLift, ← hpfLift] at HG
  unfold ErasedFamilyComparison at HG
  simp only [ρ, Lift.consN_consN, lift'_consN_skipN] at HG
  rw [proofErase_liftN hctx hctx' Wext htf,
    proofErase_liftN hctx hctx' Wext hpf] at HG
  exact (proofErase_joint_compare_certificate_descend hstep hctx hctx' Wext rfl htf hpf HG).1
    ⟨_, HasType.sort (by trivial : VLevel.zero.WF univs)⟩

end GuardedSingleton

/-- Specialized Eq prefixes preserve the lower carrier certificate, and hence
an exact lower prefix computation, under any unused binder insertion. -/
theorem erased_joint_prefix_certificate_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveCertificateDescent (ProofShape.JointPrefixPrimitive Step) (ProofShape.JointPrefixPrimitive Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨αs, as, Ms, ms, bs, E, Eα, Ea, EM, Em, Eb⟩ :=
      ProofShape.liftN_eqRecBeforeMajor_inv hsrc
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv E
    rw [← Hα] at Eα
    rw [← Ha] at Ea
    rw [← HM] at EM
    rw [← Hm] at Em
    rw [← Hb] at Eb
    rw [← Eα, ← Ea, ← Eb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab := proofErase_joint_carrier_descend hstep.descent hΓ hΓ' W ha hb HC
    have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at E
      cases E
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α₀ a₀ b₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    have CC := proofErase_joint_carrier_certificate_descend hstep hΓ hΓ' W ha hb HC
    refine ⟨_, HH, ?_, ?_⟩
    · rw [E, show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
        .lam (proofErase Γ (eqApp w α₀ a₀ b₀)) (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
        proofErase_eqProofType heq hw hΓ hα ha hb,
        proofErase_liftN hΓ hΓE Ctx.LiftN.one hm, ← Hα, ← Ha, ← HM, ← Hm, ← Hb]
      exact .base (.intro CC)
    rw [show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w α₀ a₀ b₀)) (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm]
    simp only [ProofShape.liftN, ProofShape.eqProofType,
      ← ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _), Eα, Ea, Eb, Em]


/-- General singleton code retains its own lower generated family guard and
exact output. The source-stage semantic descent constructs the actual unfolding
check; no soundness or completeness assumption on Target is needed. -/
theorem erased_joint_singleton_certificate_descent
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveCertificateDescent (ProofShape.JointSingletonPrimitive Step)
      (ProofShape.JointSingletonPrimitive Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨_, R⟩ := H
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv hsrc
    obtain ⟨original, rfl, Hargs⟩ := proofErase_const_spine_inv Es
    rw [Hargs] at Eargs
    have hargs := (mkApps_arguments_wf henv hΓ ⟨_, ht⟩).2
    have hmap : (original.map (·.liftN n k)).map (proofErase Γ') = args := by
      rw [Eargs]
      simp only [List.map_map]
      apply List.map_congr_left
      intro a ha
      obtain ⟨_, hat⟩ := hargs a ha
      exact proofErase_liftN hΓ hΓ' W hat
    have hup : env.HasType univs Γ'
        (mkApps (.const C.data.name C.levels) (original.map (·.liftN n k))) (T.liftN n k) := by
      simpa only [liftN_mkApps, liftN] using ht.weakN henv W
    have hlenargs : (original.map (·.liftN n k)).length = C.arity := by
      simpa only [List.length_map] using (congrArg List.length hmap).trans ha
    obtain ⟨program, hg, hd, HG'⟩ := V.realizeWith heq hΓ' hlenargs ⟨_, hup⟩
      (by rwa [hmap]) (by rwa [hmap])
    have HC := V.checkWith heq (erased_joint_family_descent hstep.descent) hΓ' hg ⟨_, hup⟩ HG'
    obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
    have hlen : C.levels.length = C.data.uvars := by
      rw [hl] at hll
      exact hll.trans (RecursorData.singletonEquation_uvars he)
    obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
    obtain ⟨lower, hgl⟩ := V.generate (args := original) (by simpa only [List.length_map] using hlenargs)
    let ρ := (Lift.refl.skipN n).consN k
    have hback := RecursorData.singletonUnfolding_lift' henv V.registered V.large V.zero V.recType_eq
      (V.registered.recursorType_closed henv V.recType_eq) hgl (ρ := ρ)
    have hgρ : C.data.singletonUnfolding env univs C.levels (original.map (·.lift' ρ)) = some program := by
      simpa only [ρ, lift'_consN_skipN] using hg
    have hprogram := RecursorData.singletonUnfolding_unique hgρ hback
    have HGren := hprogram ▸ HG'
    have HGlo := GuardedSingleton.family_guard_certificate_below heq hstep W hΓ hΓ'
      V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hgl ⟨_, ht⟩ HGren
    have HGsem := GuardedSingleton.family_guard_with_below heq (erased_joint_family_descent hstep.descent)
      W hΓ hΓ' V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hgl ⟨_, ht⟩ HGren
    have HClo := GuardedSingleton.check_of_family_conversion henv heq hΓ V.registered V.large V.zero
      V.levels_wf hlen howner V.layout_eq V.elim_eq hgl ⟨_, ht⟩ HGsem
    have HH := (show env.IsDefEqU univs Γ _ _ from ⟨_, HClo.defeq henv hΓ⟩).of_l henv hΓ ht
    have hn : ¬ IsProof Γ (mkApps (.const C.data.name C.levels) original) := by
      intro hp
      exact ProofShape.const_spine_ne_proof (Es.symm.trans (proofErase_eq_proof.2 hp))
    have hnup := mt (isProof_liftN hΓ hΓ' W ht).1 hn
    have hnup' : ¬ IsProof Γ' (mkApps (.const C.data.name C.levels) (original.map (·.liftN n k))) := by
      simpa only [liftN_mkApps, liftN] using hnup
    refine ⟨lower.rhs, HH, ?_, ?_⟩
    · rw [proofErase_const_spine hΓ ht hn, V.output_eq heq hΓ hgl HClo hn]
      exact .base ⟨⟨Γ, _, _, hΓ, rfl, ht, proofErase_const_spine hΓ ht hn⟩,
        .intro V (by simpa only [List.length_map] using hlenargs)
          (V.telescope_eq hΓ hgl ⟨_, ht⟩) ((V.guardWith_iff heq hΓ hgl ⟨_, ht⟩).2 HGlo)⟩
    have Erhs : program.rhs = lower.rhs.liftN n k := by
      rw [hprogram]
      simpa only [ρ, lift'_consN_skipN] using
        (RecursorData.PrefixUnfolding.rename_rhs (ρ := ρ)
          (ClosedSingleton.generated_template_closed henv V.registered V.large V.zero hgl))
    rw [← proofErase_liftN hΓ hΓ' W HH.hasType.2, ← Erhs,
      V.output_eq heq hΓ' hg HC hnup', hd, hmap]

/-- Every finite joint stage preserves lower computation certificates at that
same stage, including its generated singleton and explicit Eq-carrier rules. -/
theorem erased_joint_stage_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveCertificateDescent (ErasedJointStage D stage) (ErasedJointStage D stage) := by
  intro stage
  induction stage with
  | zero => exact erased_joint_zero_certificate_descent hs
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H
    · obtain ⟨e', HE, R, E⟩ := ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inl H), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_joint_singleton_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inl H)), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_joint_prefix_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr H)), E⟩

/-- The full union also preserves computation certificates. Each primitive
chooses its existing finite stage; no uniform bound on an infinite family is
needed. -/
theorem erased_joint_union_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveCertificateDescent (ErasedJointUnion D) (ErasedJointUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  obtain ⟨e', HE, R, E⟩ := erased_joint_stage_certificate_descent heq hs stage hΓ hΓ' W ht H
  exact ⟨e', HE, R.mono (fun H => ⟨stage, H⟩), E⟩

end Lean4Lean.VEnv.Strengthening
