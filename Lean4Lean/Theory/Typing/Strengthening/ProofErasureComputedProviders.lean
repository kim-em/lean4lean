import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixArguments
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-! # Fresh providers beneath computed telescopes

Replay of a residual type computation realizes the new telescope in an actual
definitionally equal context. This preserves the proof status of every fresh
variable, including variables whose declaration erasures change.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Successful raw peeling of a typed type has an actual telescope realization,
with exactly the given annotation and body erasures. -/
theorem proofErase_takeForalls_inv
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.IsType univs Γ T)
    (H : ProofShape.takeForalls count (proofErase Γ T) = some (ds, body)) :
    ∃ domains result, VExpr.takeForalls count T = some (domains, result) ∧
      proofEraseDomains Γ domains = ds ∧
      proofErase (domains.reverse ++ Γ) result = body := by
  induction count generalizing Γ T ds body with
  | zero => cases H; exact ⟨[], T, rfl, rfl, rfl⟩
  | succ count ih =>
    cases ET : proofErase Γ T <;>
      simp only [ET, ProofShape.takeForalls] at H <;> try contradiction
    rename_i Araw Braw
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv ET
    obtain ⟨u, hT⟩ := hT
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [← EA, ← EB] at H
    cases HB : ProofShape.takeForalls count (proofErase (A :: Γ) B) with
    | none => simp [HB] at H
    | some p =>
      obtain ⟨tail, b⟩ := p
      simp only [HB, Option.pure_def] at H
      cases H
      obtain ⟨domains, result, HT, HD, HR⟩ := ih hΓA ⟨w, hB⟩ HB
      refine ⟨A :: domains, result, ?_, ?_, ?_⟩
      · simp only [VExpr.takeForalls, HT, Option.pure_def, bind, Option.bind_some]
      · simp only [proofEraseDomains, HD]
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using HR

/-- A typed residual telescope keeps enough displayed Pi binders after any
sound computation with nonbinder primitive heads. Successful target peeling
is a consequence, rather than an additional shape hypothesis. -/
theorem proofErase_takeForalls_compute_exists
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HT : VExpr.takeForalls count T = some (domains, result))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out) :
    ∃ ds' body', ProofShape.takeForalls count out = some (ds', body') := by
  induction count generalizing Γ T u domains result out with
  | zero => exact ⟨[], out, rfl⟩
  | succ count ih =>
    cases T <;> try contradiction
    rename_i A B
    simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at HT
    obtain ⟨⟨ds, body⟩, HB, HE⟩ := HT
    cases HE
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [show proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
      if_neg (not_isProof_of_sort hΓ hT)] at R
    obtain ⟨A', B', rfl, _, RB⟩ := R.forallE_inv_typed hstep hsubst hhead hΓ hA rfl
    obtain ⟨ds', body', HO⟩ := ih hΓA hB HB RB
    exact ⟨A' :: ds', body', by
      simp only [ProofShape.takeForalls, HO, bind, Option.bind_some, Option.pure_def]⟩

/-- Actual context conversion preserves raw variable providers without needing
the variable itself to have a type or requiring identical context erasures. -/
theorem ProofShape.contextVariable_defeqCtx
    (W : IsDefEqCtx env univs [] Γ Γ') :
    contextVariable (proofEraseCtx Γ) i = contextVariable (proofEraseCtx Γ') i := by
  rw [← proofErase_contextVariable W.isType,
    ← proofErase_contextVariable (W.symm henv.ordered).isType]
  simp only [proofErase]
  rw [propext (isProof_defeqCtx W)]

/-- Peeling a computed typed residual type yields an actual target telescope
whose full context is definitionally equal to the source telescope context. -/
theorem proofErase_computed_telescope_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HT : VExpr.takeForalls count T = some (domains, result))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out)
    (HO : ProofShape.takeForalls count out = some (ds', body')) :
    ∃ domains' result',
      IsDefEqCtx env univs [] (domains.reverse ++ Γ) (domains'.reverse ++ Γ) ∧
      proofEraseDomains Γ domains' = ds' ∧
      proofErase (domains'.reverse ++ Γ) result' = body' := by
  obtain ⟨T', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ hT rfl rfl R
  rw [← EE] at HO
  obtain ⟨domains', result', HT', HD, HR⟩ :=
    proofErase_takeForalls_inv hΓ ⟨u, HE.hasType.2⟩ HO
  refine ⟨domains', result', ?_, HD, HR⟩
  have hlen := (VExpr.takeForalls_domains_length HT).trans
    (VExpr.takeForalls_domains_length HT').symm
  rw [VExpr.eq_wrapForalls_of_takeForalls HT,
    VExpr.eq_wrapForalls_of_takeForalls HT'] at HE
  exact _root_.Lean4Lean.VEnv.IsDefEqU.wrapForalls_context henv (by trivial) (.refl hΓ) hlen ⟨_, HE⟩

/-- All fresh provider markers are unchanged when a typed residual telescope
computes. The two raw contexts may have different annotations. -/
theorem proofErase_computed_telescope_providers
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HT : VExpr.takeForalls count T = some (domains, result))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out)
    (HO : ProofShape.takeForalls count out = some (ds', body')) :
    contextVars ((proofEraseDomains Γ domains).reverse ++ proofEraseCtx Γ) n below =
      contextVars (ds'.reverse ++ proofEraseCtx Γ) n below := by
  obtain ⟨domains', result', W, HD, _⟩ :=
    proofErase_computed_telescope_context hstep hΓ hT HT R HO
  rw [← HD, ← proofEraseDomains_context, ← proofEraseDomains_context]
  simp only [contextVars, contextVariable_defeqCtx W]

/-- Computing supplied arguments computes their opened provider vector beneath
a residual telescope, provided its fresh markers and length are preserved.
Only the original extended context needs an actual typing realization. -/
theorem proofErase_openPrefixArguments_compute
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs))
    (hlen : (proofEraseDomains Γ domains).length = ds'.length)
    (hvars : contextVars ((proofEraseDomains Γ domains).reverse ++ proofEraseCtx Γ)
        ds'.length 0 = contextVars (ds'.reverse ++ proofEraseCtx Γ) ds'.length 0)
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) args args') :
    List.Forall₂ (ScopedCompute Step (proofEraseCtx (domains.reverse ++ Γ)))
      (openPrefixArguments (proofEraseCtx Γ) (proofEraseDomains Γ domains) args)
      (openPrefixArguments (proofEraseCtx Γ) ds' args') := by
  have W := ContextRenaming.of_liftN (n := domains.length) hΓ hctx
    (Ctx.LiftN.zero domains.reverse (by simp only [List.length_reverse]))
  unfold openPrefixArguments
  rw [hlen, hvars]
  apply List.Forall₂.append'
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply RA.imp
    intro a b R
    have H := R.rename hrename W
    simpa only [subst_bvar_liftN, ← hlen, proofEraseDomains_length] using H
  · exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)

end Lean4Lean.VEnv.Strengthening
