import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainRetained

/-! # Select actual counted Eq cuts through the full insertion chain

The tracked lower prefix keeps its chosen assignment. Additional upper arguments
are permitted only after that prefix is complete, and their actual component
paths and supplied suffix remain visible when a non-level root is selected.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private tracked_spine_hole
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixMinimum
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
variable [Params]

/-- Reify the tracked prefix of an actual upper component path, including
head-level changes. The exact remaining upper arguments keep their original
component certificates and need no target images. Both the chosen assignment
and external pending target vector are unchanged. -/
theorem EqPrefixSpecializationAt.chain_compute_levels
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HL : List.Forall₂ (· ≈ ·) [v',w'] ls)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ))
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra) raw)
    (HT : TypedSource (proofEraseCtx Λ) (ProofShape.mkApps (.const ``Eq.rec ls) raw)) :
    ∃ v'' w'' pre', ls = [v'',w''] ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      ((pre'.map (proofErase Γ)).map blocks.erased) = raw.take pre.length ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ))
        extra (raw.drop pre.length) := by
  obtain ⟨v'', w'', rfl⟩ : ∃ v'' w'', ls = [v'',w''] := by
    cases HL with | cons _ HL => cases HL with | cons _ HL => cases HL; exact ⟨_, _, rfl⟩
  have HW := typed_const_levels_wf
    (show TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (pre.map (proofErase Γ))) from
      ⟨Γ, _, F, H.1.wf, rfl, hf, proofErase_const_spine H.1.wf hf hn⟩)
  have HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']) :=
    ⟨_, .constDF heq.2.2.1 HW (typed_const_levels_wf HT) (by rfl) HL⟩
  have HApre := Lean4Lean.List.forall₂_take HA ((pre.map (proofErase Γ)).map blocks.erased).length
  simp only [List.take_left] at HApre
  simp only [List.length_map] at HApre
  obtain ⟨pre', HP, _, _, EP, _, HE⟩ :=
    H.compute_insertion_chain (pi_inert_stage_certificate_descent heq hs n) hΔ W J hf HC HApre
  have HAextra := Lean4Lean.List.forall₂_drop HA ((pre.map (proofErase Γ)).map blocks.erased).length
  simp only [List.drop_left] at HAextra
  simp only [List.length_map] at HAextra
  exact ⟨v'', w'', pre', rfl, HP, EP, HE, HAextra⟩

/-- An actual non-level cut through a full insertion chain. The chosen lower
prefix and pending target vector remain fixed as witnesses, while untracked
upper arguments are allowed only after completion. The root is an exact prefix
of the reached whole vector; its actual suffix and counted paths are retained. -/
def ChosenEqChainSpineCut (D : Definitions) (Γ Δ Λ : List VExpr) (blocks : EqInsertionPath)
    (v w : VLevel) (original : List VExpr) (σ : VExpr.Subst) (pending : List VExpr)
    (n : Nat) (source endpoint : ProofShape) (budget : Nat) : Prop :=
  ∃ v' w' pre extra arity F target cp ct,
    EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending ∧
    env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
    ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
    (extra = [] ∨ pending = []) ∧ arity ≤ pre.length + extra.length ∧ cp+1+ct ≤ budget ∧
    ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) ∧
    PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).take arity)) target ∧
    ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).take arity)) target ∧
    ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ)
      (ProofShape.mkApps target ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).drop arity)) endpoint

/-- Extract the first actual non-level cut under a paired insertion chain,
including any upper arguments beyond a completed prefix. The alternative is
an exact computed constant spine with the same chosen lower assignment. No
path or root is transported through the paired map or an unused insertion. -/
theorem EqPrefixSpecializationAt.chain_counted_spine_or_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hextra : extra = [] ∨ pending = [])
    (HTsource : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)))
    (R : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint) :
    (∃ v'' w'' pre' extra',
      endpoint = ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (((pre'.map (proofErase Γ)).map blocks.erased) ++ extra') ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F ∧
      List.Forall₂ (· ≈ ·) [v',w'] [v'',w''] ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ))
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)
        (((pre'.map (proofErase Γ)).map blocks.erased) ++ extra') ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)) extra extra' ∧
      (extra' = [] ∨ pending = [])) ∨
    ChosenEqChainSpineCut D Γ Δ Λ blocks v w original σ pending n
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint cost := by
  rcases R.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls, args, EO, HL, HA⟩ | ⟨ls, rawPre, rawRest, target, cp, ct, hc, HL, HA, RP, HR, HN, RT⟩
  · have HT := EO ▸ HTsource.pi_inert_compute heq hs R.forget
    obtain ⟨v'', w'', pre', rfl, HP, EP, HE, HX⟩ := H.chain_compute_levels heq hs hΔ W J hf hn HL HA HT
    have Efull : ((pre'.map (proofErase Γ)).map blocks.erased) ++ args.drop pre.length = args := by
      rw [EP, List.take_append_drop]
    have HX' : args.drop pre.length = [] ∨ pending = [] := by
      rcases hextra with rfl | hp
      · exact .inl (List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using HX.length_eq.symm))
      · exact .inr hp
    exact .inl ⟨v'', w'', pre', args.drop pre.length, by simpa only [Efull] using EO, HP, HE, HL, by simpa only [Efull] using HA, HX, HX'⟩
  · have HT := HTsource.pi_inert_compute heq hs RP.forget
    obtain ⟨v'', w'', full, rfl, HP, EP, HE, HX⟩ := H.chain_compute_levels heq hs hΔ W J hf hn HL HA HT
    have Efull : ((full.map (proofErase Γ)).map blocks.erased) ++ (rawPre ++ rawRest).drop pre.length =
        rawPre ++ rawRest := by rw [EP, List.take_append_drop]
    have HX' : (rawPre ++ rawRest).drop pre.length = [] ∨ pending = [] := by
      rcases hextra with rfl | hp
      · exact .inl (List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using HX.length_eq.symm))
      · exact .inr hp
    refine .inr ⟨v'', w'', full, (rawPre ++ rawRest).drop pre.length, rawPre.length, F, target, cp, ct,
      HP, HE.hasType.2, (fun hp => hn ((isProof_congr H.1.wf HE).2 hp)), HX', ?_, hc, ?_, ?_, ?_, ?_⟩
    · have EL := congrArg List.length Efull
      simp only [List.length_append, List.length_map] at EL
      omega
    · simpa only [Efull] using RP
    · simpa only [Efull, List.take_left] using HR
    · simpa only [Efull, List.take_left] using HN
    · simpa only [Efull, List.drop_left] using RT

/-- Partition a selected actual root without losing its supplied suffix.
Before target completion, its lower prefix has a nonempty pending vector
whose first entries are the omitted actual lower arguments. At or beyond
completion, the original pending vector is empty and only upper extras are
split. Thus no extra argument is assigned an invented target image. -/
theorem EqPrefixSpecializationAt.chain_root_partition
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hextra : extra = [] ∨ pending = []) (hk : arity ≤ pre.length + extra.length)
    (blocks : EqInsertionPath) :
    (∃ y rest, arity < original.length ∧
      (pre.drop arity).map (·.subst σ) ++ pending = y :: rest ∧
      EqPrefixSpecializationAt Γ Δ v w v' w' original (pre.take arity) σ (y :: rest) ∧
      ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).take arity) =
        ((pre.take arity).map (proofErase Γ)).map blocks.erased ∧
      ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).drop arity) =
        (((pre.drop arity).map (proofErase Γ)).map blocks.erased) ++ extra) ∨
    (pending = [] ∧ original.length ≤ arity ∧
      ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).take arity) =
        ((pre.map (proofErase Γ)).map blocks.erased) ++ extra.take (arity-pre.length) ∧
      ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).drop arity) =
        extra.drop (arity-pre.length)) := by
  have HL := H.2.2.length_eq
  simp only [List.length_append, List.length_map] at HL
  by_cases hshort : arity < original.length
  · have hkpre : arity ≤ pre.length := by
      rcases hextra with rfl | rfl <;> simp only [List.length_nil] at * <;> omega
    have HN : 0 < ((pre.drop arity).map (·.subst σ) ++ pending).length := by
      simp only [List.length_append, List.length_map, List.length_drop]
      omega
    cases E : (pre.drop arity).map (·.subst σ) ++ pending with
    | nil => simp only [E, List.length_nil] at HN; omega
    | cons y rest =>
      refine .inl ⟨y, rest, hshort, rfl, E ▸ H.take arity, ?_, ?_⟩
      · rw [List.take_append_of_le_length (by simpa only [List.length_map] using hkpre)]
        simp only [List.map_take]
      · rw [List.drop_append_of_le_length (by simpa only [List.length_map] using hkpre)]
        simp only [List.map_drop]
  · have hlong : original.length ≤ arity := by omega
    have hkpre : pre.length ≤ arity := by omega
    have hp : pending = [] := by
      rcases hextra with rfl | hp
      · have hnil : pending.length = 0 := by simp only [List.length_nil] at hk; omega
        exact List.length_eq_zero_iff.mp hnil
      · exact hp
    refine .inr ⟨hp, hlong, ?_, ?_⟩
    · rw [List.take_append, List.take_of_length_le (by simpa only [List.length_map] using hkpre)]
      simp only [List.length_map]
    · rw [List.drop_append, List.drop_eq_nil_of_le (by simpa only [List.length_map] using hkpre)]
      simp only [List.length_map, List.nil_append]

/-- An actual continuation minimum retaining its chosen lower assignment,
paired frame and full insertion chain. Upper extra arguments are permitted
only after completion. This stores the current concrete frame; it does not
assert agreement with an arbitrary later consumption map. -/
def EqChainContinuationMinimum (D : Definitions) (Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (Ω : List ProofShape) (out : ProofShape) (cost : Nat) : Prop :=
  ∃ Γ Γ' Λ Λ' σ σ' ρ τ κ υ blocks v' w' pre pending extra F,
    EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending ∧
    EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ ∧
    EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks ∧
    env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
    ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
    (extra = [] ∨ pending = []) ∧
    PiInertTypedContinuationMinimum D Ω out (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) cost

/-- Every extracted actual non-level cut strictly descends in the paired-chain
minimum class, or reads the original target equation. Short roots keep the
omitted actual lower arguments in their chosen pending vector; saturated roots
retain their actual upper extras. The exact counted application suffix supplies
the hole used for descent. This closes cut selection under the chain, not the
remaining component-only continuation and used-binder consumption cases. -/
theorem ChosenEqChainSpineCut.eq_or_smaller
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : ChosenEqChainSpineCut D Γ Δ Λ blocks v w [α,a,M,minor,b] σ pending n source endpoint budget)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HT : TypedSource (proofEraseCtx Λ) source)
    (HK : PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ) K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : budget+ck ≤ cost)
    (hmin : ∀ later j tail k,
      ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Λ) source tail →
      K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ smaller, smaller < cost ∧
      EqChainContinuationMinimum D Δ v w [α,a,M,minor,b] Ω out smaller := by
  obtain ⟨v', w', pre, extra, arity, F, target, cp, ct, HP, hf, hn, hextra, hk, hc, RP, HR, HN, RT⟩ := H
  let args := ((pre.map (proofErase Γ)).map blocks.erased) ++ extra
  obtain ⟨C, HC, EC⟩ := tracked_spine_hole (proofEraseCtx Λ) (args.drop arity)
  have RPC : ScopedComputeCount (PiInertStage D n) cp (proofEraseCtx Λ) source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w']) (args.take arity))) := by
    rw [EC, ← ProofShape.mkApps_append, List.take_append_drop]
    exact RP
  have RTC : ScopedComputeCount (PiInertStage D n) ct (proofEraseCtx Λ) (C.plug target) endpoint := by
    rw [EC]
    exact RT
  rcases HP.chain_root_partition hextra hk blocks with
    ⟨y, rest, _, _, Hprefix, Etake, _⟩ | ⟨hp, _, Etake, _⟩
  · have hsplit : env.HasType univs Γ
        (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.take arity)) (pre.drop arity)) F := by
      rw [← VExpr.mkApps_append, List.take_append_drop]
      exact hf
    obtain ⟨Fp, hfp⟩ := VExpr.WF.of_mkApps henv HP.1.wf ⟨_, hsplit⟩
    have hnp := nonproof_spine_head HP.1.wf hsplit
      (by rw [← VExpr.mkApps_append, List.take_append_drop]; exact hn)
    rcases Hprefix.chain_hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht W J hfp hnp
        HC HT (by simpa only [args, Etake] using RPC)
        (by simpa only [Etake] using HR) (by simpa only [Etake] using HN)
        RTC HK HE HO (cost := cost) (by omega) hmin with
      Hlower | ⟨A, B, u, _, hsmall, HM, Hfresh, Wfresh, Jfresh, hb, hnb⟩
    · exact .inl Hlower
    · refine .inr ⟨ct+ck, hsmall, A :: Γ, A.subst ρ :: Γ', blocks.actual A :: Λ,
        blocks.actual (A.subst ρ) :: Λ', σ.cons y, σ'.cons y, ρ.lift, τ.lift, κ.lift, υ.lift,
        blocks.underBinder, v', w', (pre.take arity).map VExpr.lift ++ [VExpr.bvar 0], rest, [], B,
        Hfresh, Wfresh, Jfresh, hb, hnb, .inl rfl, ?_⟩
      simpa only [List.append_nil, proofErase_const_spine Hfresh.1.wf hb hnb,
        EqInsertionPath.erased_const_spine] using HM
  · cases hp
    rcases HP.saturated_chain_hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht W J hf hn
        HC HT (by simpa only [args, Etake] using RPC)
        (by simpa only [Etake] using HR) (by simpa only [Etake] using HN)
        RTC HK HE HO (cost := cost) (by omega) hmin with
      Hlower | ⟨A, u, _, hsmall, Jfresh, _, HM, _⟩
    · exact .inl Hlower
    · exact .inr ⟨ct+ck, hsmall, Γ, Γ', A :: Λ, A.subst κ :: Λ', σ, σ', ρ, τ, κ.lift, υ.lift,
        blocks ++ [(1,0)], v', w', pre, [], (extra.take (arity-pre.length)).map (·.liftN 1) ++ [etaArgument u], F,
        HP, W, Jfresh, hf, hn, .inr rfl, HM⟩

end Lean4Lean.VEnv.Strengthening
