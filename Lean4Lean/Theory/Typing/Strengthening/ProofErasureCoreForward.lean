import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePatternForward
import Lean4Lean.Theory.Typing.Strengthening.PatternStep

/-! # Coverage of concrete core patterns by erased computation

The installed pattern table consists of closed definition templates, quotient
capture application and generated iota templates. Their original universe guards
ensure a non-proof source has a visible match after erasure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PatternCompute CheckFromTyping)
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Every stored iota RHS is a closed typed template applied to selected captures.
The typing comes from the compiled equation, independently of any occurrence. -/
theorem erased_stored_template (hp : env.pats p r) (hls : ∀ l ∈ ls, l.WF univs) :
    ∃ (paths : List p.Path) (rhs : VExpr) (hc : rhs.Closed) (T : VExpr),
      r.1 = (paths.map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed rhs hc) ∧
      env.HasType univs [] (rhs.instL ls) T := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨decl, ds₀, env₀, env₁, _, _, hdecl, hadd, hle, rec, hrec, ru, hru, hc, rfl, rfl⟩ :=
    H.pats_origin hp
  obtain ⟨block, base, expanded, s, g, aux, hcomp, hrecsOf, hbwf, hbase, C, hcont, df, hdf, hof⟩ :=
    hdecl.rule_block hrec hru
  have hwf : df.WF env := by
    unfold VEnv.addInduct at hadd
    obtain ⟨envR, hR, hrules⟩ := Option.bind_eq_some_iff.1 hadd
    have hle' : envR ≤ env := (addRules_le hrules).trans hle
    have hw := VInductDecl.WF.block_rules_wf hcomp hrecsOf hbwf hR df hdf
    exact ⟨hw.1.mono hle', hw.2.mono hle'⟩
  refine ⟨_, ru.rhs, hc, df.type.instL ls, rfl, ?_⟩
  rw [← hof.1]
  exact hwf.2.instL hls

/-- Every concrete enabled root pattern step simulates in the existing erased
iota relation, including whole-proof collapse and zero-argument definitions. -/
theorem proofErase_concrete_pattern_forward (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat p r) (hconcrete : ConcretePattern env p r)
    (hm : p.Matches e ls captures) (hc : CheckFromTyping env univs p r ls)
    (ht : env.HasType univs Γ e T) :
    ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ e)
      (proofErase Γ (r.1.apply ls captures)) := by
  have hls := (hm.levelWF (ht.levelWF (CtxStrong.strong henv.orderedStrong hΓ).levelWF).1).1
  rcases hconcrete with hd | hq | hi
  · cases hd with
    | @intro value hl hclosed =>
      have hreg := (definitionRegistry_registered hl).1
      have hr := (henv.ordered.defEqWF hreg.2).2.instL hls
      exact proofErase_template_forward (paths := []) hΓ hp hc hr hm ht
  · cases hq with
    | intro hq =>
      have HE := (pat_wf hΓ hp hm ht (hc hΓ hm ht)).of_l henv hΓ ht
      by_cases hn : IsProof Γ e
      · rw [proofErase_eq_proof.2 hn, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hn)]
        exact .refl
      have hn' := mt (isProof_congr hΓ HE).2 hn
      have hm' := proofErase_pattern_match_forward hΓ hp hm (hc hΓ hm ht) ht hn
      change ¬ IsProof Γ (.app (captures (.inl (some none))) (captures (.inr none))) at hn'
      change ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ e)
        (proofErase Γ (.app (captures (.inl (some none))) (captures (.inr none))))
      rw [show proofErase Γ (.app (captures (.inl (some none))) (captures (.inr none))) =
        .app (proofErase Γ (captures (.inl (some none)))) (proofErase Γ (captures (.inr none)))
        from if_neg hn']
      exact .base (.inl (.inr (.apply hp hc hm')))
  · obtain ⟨paths, rhs, hclosed, R, HE, hr⟩ := erased_stored_template hi.pats hls
    obtain ⟨r, ck⟩ := r
    dsimp only at HE
    subst r
    simpa only [Pattern.RHS.apply_foldl_var, Pattern.RHS.apply] using
      (proofErase_template_forward (D := D) hΓ hp hc hr hm ht)

private theorem forward_modes (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEq univs Γ e out T)
    (core : ¬ IsProof Γ e → ¬ IsProof Γ out →
      ProofShape.Compute Step (proofErase Γ e) (proofErase Γ out)) :
    ProofShape.Compute Step (proofErase Γ e) (proofErase Γ out) := by
  by_cases hp : IsProof Γ e
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ H).1 hp)]
    exact .refl
  · exact core hp (mt (isProof_congr hΓ H).2 hp)

/-- All compatible single core contractions simulate forwards, including
annotation changes and projections of constructors. -/
theorem proofErase_pattern_step_forward (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : PureObservation.PatternStep D e out) :
    ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ e) (proofErase Γ out) := by
  induction R generalizing Γ T with
  | pattern hp hcon hm hc => exact proofErase_concrete_pattern_forward hΓ hp hcon hm hc ht
  | delta hd => exact (proofErase_delta hs hd hΓ ht).mono (fun h => .inl (.inl h))
  | projIota hi hl hg => exact (proofErase_projIota hs hi hl hg hΓ ht).mono (fun h => .inl (.inl h))
  | beta => exact .beta (proofErase_beta_forward hΓ ht .beta)
  | appL R ih =>
    apply forward_modes hΓ ((PureObservation.PatternStep.appL R).toCompute.simAt hs hΓ T ht)
    intro hn hn'
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .app (ih hΓ hf) .refl
  | appR R ih =>
    apply forward_modes hΓ ((PureObservation.PatternStep.appR R).toCompute.simAt hs hΓ T ht)
    intro hn hn'
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .app .refl (ih hΓ ha)
  | proj R ih =>
    apply forward_modes hΓ ((PureObservation.PatternStep.proj R).toCompute.simAt hs hΓ T ht)
    intro hn hn'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .proj (ih hΓ hm.hasType.2)
  | lamL R ih =>
    apply forward_modes hΓ ((PureObservation.PatternStep.lamL R).toCompute.simAt hs hΓ T ht)
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HAA := R.toCompute.simAt hs hΓ _ hA
    have Eb := proofErase_defeqCtx hΓA (.succ .zero HAA) hb
    simp only [proofErase, if_neg hn, if_neg hn', ← Eb]
    exact .lam (ih hΓ hA) .refl
  | lamR R ih =>
    apply forward_modes hΓ ((PureObservation.PatternStep.lamR R).toCompute.simAt hs hΓ T ht)
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .lam .refl (ih ⟨hΓ, u, hA⟩ hb)
  | forallL R ih =>
    apply forward_modes hΓ ((PureObservation.PatternStep.forallL R).toCompute.simAt hs hΓ T ht)
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HAA := R.toCompute.simAt hs hΓ _ hA
    have EB := proofErase_defeqCtx hΓA (.succ .zero HAA) hB
    simp only [proofErase, if_neg hn, if_neg hn', ← EB]
    exact .forallE (ih hΓ hA) .refl
  | forallR R ih =>
    apply forward_modes hΓ ((PureObservation.PatternStep.forallR R).toCompute.simAt hs hΓ T ht)
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .forallE .refl (ih ⟨hΓ, u, hA⟩ hB)

/-- All finite concrete core computations simulate forwards under typed erasure.
No bound, normalization assumption or special restriction on captures is needed. -/
theorem proofErase_pattern_compute_forward (hs : D.Sound env univs)
    (hc : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : PatternCompute D e out) :
    ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ e) (proofErase Γ out) := by
  have HH : env.HasType univs Γ out T ∧
      ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ e) (proofErase Γ out) := by
    apply PureObservation.pattern_induct_steps hc R (P := fun x => env.HasType univs Γ x T ∧
      ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ e) (proofErase Γ x)) ⟨ht, .refl⟩
    intro x y H Hx
    exact ⟨(H.toCompute.simAt hs hΓ T Hx.1).hasType.2,
      Hx.2.trans (proofErase_pattern_step_forward hs hΓ Hx.1 H)⟩
  exact HH.2

omit [Params] in
/-- Every actual core parallel reduction of a well-formed environment has a
forward erased computation. Singleton prefixes and extensional eta are separate
rules and are not asserted to be covered by this core theorem. -/
theorem proofErase_parRed_forward {E : VEnv} (hE : E.WF) (hs : D.Sound E U)
    (hΓ : OnCtx Γ (E.IsType U)) (ht : E.HasType U Γ e T)
    (R : @ParRed (hE.params U) Γ e out) :
    @ProofShape.Compute (@ErasedIotaPrimitive (hE.params U) D)
      (@proofErase (hE.params U) Γ e) (@proofErase (hE.params U) Γ out) := by
  letI := hE.params U
  exact proofErase_pattern_compute_forward hs (fun h => h) hΓ ht (PatternCompute.of_parRed hE R)

end Lean4Lean.VEnv.Strengthening
