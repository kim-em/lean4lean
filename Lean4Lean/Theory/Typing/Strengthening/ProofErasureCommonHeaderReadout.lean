import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiTelescopeReification
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureSortReadout
import Lean4Lean.Theory.Typing.NormalSubstitution

/-! # Literal checkpoints for common sort-ending header reducts

A computed sort-ending telescope can be exposed at the same arity and returned
to its original result universe. Typed realization then supplies actual domain
syntax. Applying this cleanup to a shared reduct retains both incoming paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

private theorem erase_sort_syntax (H : proofErase Γ e = .sort u) : e = .sort u := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all

private theorem erase_sort_telescope_syntax
    (H : proofErase Γ e = ProofShape.wrapForalls rawDs (.sort u)) :
    ∃ ds, ds.length = rawDs.length ∧ e = VExpr.wrapForalls ds (.sort u) := by
  induction rawDs generalizing Γ e with
  | nil => exact ⟨[], rfl, erase_sort_syntax H⟩
  | cons X rawDs ih =>
    obtain ⟨A, B, rfl, _, _, EB⟩ := erase_forallE_inv H
    obtain ⟨ds, hlen, rfl⟩ := ih EB
    exact ⟨A :: ds, congrArg Nat.succ hlen, rfl⟩

omit [Params] in
private theorem raw_wrap_foralls_compute
    (R : ScopedCompute Step (ds.reverse ++ Δ) b b') :
    ScopedCompute Step Δ (ProofShape.wrapForalls ds b) (ProofShape.wrapForalls ds b') := by
  induction ds generalizing Δ with
  | nil => exact R
  | cons A ds ih =>
    exact .forallE .refl (ih (by simpa only [List.reverse_cons, List.append_assoc,
      List.singleton_append] using R))

/-- Every computed sort-ending header continues to an actual typed literal
header of the same arity and the original result universe. Only its marked Pi
prefix and terminal universe are cleaned up; its parameter domains need not
normalize. No type-fork or type-instantiation joining premise is used. -/
theorem static_structure_sort_header_checkpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ (VExpr.wrapForalls ps (.sort u)) (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ps (.sort u))) out) :
    ∃ qs, qs.length = ps.length ∧
      env.HasType univs Γ (VExpr.wrapForalls qs (.sort u)) (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        out (proofErase Γ (VExpr.wrapForalls qs (.sort u))) := by
  obtain ⟨hctx, w, hSort⟩ := IsType.wrapForalls_inv henv hΓ ⟨v, hT⟩
  have hu := hSort.sort_inv henv.ordered
  obtain ⟨rawDs, body, RD, RB, Rβ⟩ := static_structure_pi_telescope_origin heq hs hΓ ⟨v, hT⟩ R
  have ES : proofErase (ps.reverse ++ Γ) (.sort u) = .sort u :=
    if_neg (not_isProof_of_sort hctx (HasType.sort hu))
  rw [ES] at RB
  obtain ⟨u', HE, _, RBody⟩ := proofErase_static_structure_union_sort_readout heq hs hctx hu RB
  have RS : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (rawDs.reverse ++ proofEraseCtx Γ) body (.sort u) :=
    (ScopedCompute.beta RBody).trans (.base ⟨0, .inl (.inr (.sort HE.symm hu))⟩)
  have RC := (ScopedCompute.beta Rβ).trans (raw_wrap_foralls_compute RS)
  obtain ⟨T, HT, ET⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl (R.trans RC)
  obtain ⟨qs, hlen, rfl⟩ := erase_sort_telescope_syntax ET
  refine ⟨qs, ?_, HT.hasType.2, ?_⟩
  · exact hlen.trans (by simpa only [proofEraseDomains_length] using RD.length_eq.symm)
  · exact ET ▸ RC

/-- A shared reduct of a literal sort-ending header and any other endpoint can
be chosen to be a typed literal header of the same arity and result universe.
Both given paths continue to that single checkpoint, without composing joins. -/
theorem static_structure_common_header_checkpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ (VExpr.wrapForalls ps (.sort u)) (.sort v))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ps (.sort u))) shared)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      other shared) :
    ∃ qs, qs.length = ps.length ∧
      env.HasType univs Γ (VExpr.wrapForalls qs (.sort u)) (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ps (.sort u)))
        (proofErase Γ (VExpr.wrapForalls qs (.sort u))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        other (proofErase Γ (VExpr.wrapForalls qs (.sort u))) := by
  obtain ⟨qs, hlen, hQ, RC⟩ := static_structure_sort_header_checkpoint heq hs hΓ hT RL
  exact ⟨qs, hlen, hQ, RL.trans RC, RR.trans RC⟩

/-- A directed change of sort-ending parameter headers can be reused around
any ordinarily typed tail. Context conversion derives the tail's target typing;
Pi-component readout reuses just the domain paths, with the tail unchanged.
In particular the tail may contain all dependent constructor fields. -/
theorem static_structure_sort_header_retarget_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.IsType univs Γ (VExpr.wrapForalls ps (.sort u)))
    (hQ : env.IsType univs Γ (VExpr.wrapForalls qs (.sort u)))
    (hlen : ps.length = qs.length)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ps (.sort u)))
      (proofErase Γ (VExpr.wrapForalls qs (.sort u))))
    (hB : env.IsType univs (ps.reverse ++ Γ) B) :
    env.IsType univs Γ (VExpr.wrapForalls qs B) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ps B)) (proofErase Γ (VExpr.wrapForalls qs B)) := by
  obtain ⟨Q, HQ, EQ⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hP.choose_spec rfl rfl R
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HQ.hasType.2 hQ.choose_spec EQ).2
    (not_isProof_of_sort hΓ HQ.hasType.2)
  have HE := HQ.toU.trans henv hΓ (HN.defeq hΓ)
  have W := IsDefEqU.wrapForalls_context henv hΓ
    (.zero : IsDefEqCtx env univs Γ Γ Γ) hlen HE
  have hctxP := (IsType.wrapForalls_inv henv hΓ hP).1
  have hctxQ := (IsType.wrapForalls_inv henv hΓ hQ).1
  have hB' := hB.defeqDFC henv W
  obtain ⟨p, HP⟩ := VExpr.wrapForalls_defeq hctxP hB.choose_spec
  obtain ⟨q, HQ⟩ := VExpr.wrapForalls_defeq hctxQ hB'.choose_spec
  have EB := proofErase_defeqCtx hctxP W hB.choose_spec
  rw [proofErase_wrapForalls_type hΓ hQ] at R
  have RD := (static_structure_pi_telescope_components heq hs hΓ hP
    (by simpa only [proofEraseDomains_length] using hlen) R).1
  refine ⟨⟨q, HQ⟩, ?_⟩
  rw [proofErase_wrapForalls_type hΓ ⟨p, HP⟩, proofErase_wrapForalls_type hΓ ⟨q, HQ⟩, ← EB]
  exact RD.wrapForalls .refl

end Lean4Lean.VEnv.Strengthening
