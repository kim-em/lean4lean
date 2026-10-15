import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedSingletonSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreForward
import Lean4Lean.Theory.Typing.Strengthening.PrefixOrdinaryExchange

/-! # The exact residual output after computing singleton arguments

Ordinary raw argument paths replay at the typed source. Full original program
congruence then computes the checked output, including all dependent residual
annotations. Forward erasure identifies that output with the same code applied
to the new raw arguments and their newly computed telescope.

This settles the output side of the prefix/argument square. Its other side
still requires a family-guard certificate at the new arguments. The conclusion
exposes precisely that remaining premise; an original unfolding check is not
silently treated as an erased guard certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open PureObservation
open private const_spine_ne_proof from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem core_arguments_replay (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : ∀ a ∈ args, VExpr.WF env univs Γ a)
    (HA : List.Forall₂ (ProofShape.Compute (ErasedIotaPrimitive D))
      (args.map (proofErase Γ)) rawArgs) :
    ∃ args', List.Forall₂ (PatternCompute D) args args' ∧
      args'.map (proofErase Γ) = rawArgs := by
  induction args generalizing rawArgs with
  | nil => cases HA; exact ⟨[], .nil, rfl⟩
  | cons a args ih =>
    cases HA with
    | cons HR Hrest =>
      obtain ⟨T, ha⟩ := ht a (by simp)
      obtain ⟨a', Ra, Ea⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ha HR
      obtain ⟨args', Hargs, Eargs⟩ := ih
        (fun a ha => ht a (List.mem_cons_of_mem _ ha)) Hrest
      exact ⟨a' :: args', .cons Ra Hargs, by simp only [List.map_cons, Ea, Eargs]⟩

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- After arbitrary ordinary computation of the supplied raw arguments, the
same code has a computed telescope, a realizable new source, and an ordinary
path from the old output to its new prescribed output. A certificate of the
new family guard, in any chosen relation, is the sole remaining premise for
the residual typed singleton step. No confluence or guard completeness is used. -/
theorem Valid.core_residual (V : C.Valid)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : ProofShape.TypedSource Δ (ProofShape.mkApps (.const C.data.name C.levels) args))
    (ha : args.length = C.arity)
    (hcalc : C.telescope args = some (domains, result))
    (HG : C.guard Step Δ domains args)
    (HA : List.Forall₂ (ProofShape.Compute (ErasedIotaPrimitive D)) args args') :
    ∃ domains' result', C.telescope args' = some (domains', result') ∧
      ProofShape.TypedSource Δ (ProofShape.mkApps (.const C.data.name C.levels) args') ∧
      ProofShape.Compute (ErasedIotaPrimitive D) (C.output Δ domains args)
        (C.output Δ domains' args') ∧
      ∀ Step', C.guard Step' Δ domains' args' →
        ProofShape.ScopedTypedSingletonPrimitive Step' Δ
          (ProofShape.mkApps (.const C.data.name C.levels) args') (C.output Δ domains' args') := by
  obtain ⟨Γ, source, T, hΓ, rfl, ht, Es⟩ := HT
  obtain ⟨original, rfl, Eargs⟩ := proofErase_const_spine_inv Es
  have hn : ¬ IsProof Γ (mkApps (.const C.data.name C.levels) original) := by
    intro hp
    exact const_spine_ne_proof (Es.symm.trans (proofErase_eq_proof.2 hp))
  rw [Eargs] at ha hcalc HG HA ⊢
  simp only [List.length_map] at ha
  obtain ⟨program, hg, hd, HG₀⟩ := V.realize heq hΓ ha ⟨_, ht⟩ hcalc HG
  have HC := V.check heq hstep hΓ hg ⟨_, ht⟩ HG₀
  obtain ⟨newArgs, Hargs, Enew⟩ := core_arguments_replay hs hΓ
    (mkApps_arguments_wf henv hΓ ⟨_, ht⟩).2 HA
  have HP : PrefixUnfold env univs recursorData Γ C.data.name C.levels original program.rhs :=
    .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg HC
  obtain ⟨newRhs, HP', Rout⟩ := singleton_prefix_congr patternCompute_congrRel
    (patternCompute_congrRel.argRel (fun hΓ R ht => R.simAt hs hΓ _ ht)) hΓ HP Hargs
  cases HP' with
  | @intro data' program' hlookup _ _ _ _ _ hg' HC' =>
    cases Option.some.inj (V.lookup.symm.trans hlookup)
    have Rsource : PatternCompute D (mkApps (.const C.data.name C.levels) original)
        (mkApps (.const C.data.name C.levels) newArgs) :=
      patternCompute_congrRel.mkApps (Γ := Γ) (.refl) Hargs
    have hn' := mt (isProof_congr hΓ (Rsource.simAt hs hΓ _ ht)).2 hn
    have hcalc' := V.telescope_eq hΓ hg' ⟨_, HC'.source_typed⟩
    rw [Enew] at hcalc'
    have HT' : ProofShape.TypedSource (proofEraseCtx Γ)
        (ProofShape.mkApps (.const C.data.name C.levels) args') := by
      refine ⟨Γ, _, _, hΓ, rfl, HC'.source_typed, ?_⟩
      rw [proofErase_const_spine hΓ HC'.source_typed hn', Enew]
    have Hout := proofErase_pattern_compute_forward hs hcon hΓ
      (HC.defeq henv hΓ).hasType.2 Rout
    rw [V.output_eq heq hΓ hg HC hn, V.output_eq heq hΓ hg' HC' hn', hd, Enew] at Hout
    refine ⟨_, _, hcalc', HT', Hout, ?_⟩
    intro Step' HG'
    refine ⟨HT', .intro V ?_ hcalc' HG'⟩
    rw [← Enew, List.length_map, ← Hargs.length_eq]
    exact ha

end SingletonPrefixCode
end Lean4Lean.VEnv.Strengthening
