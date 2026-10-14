import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonCode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedOperationalReplay

/-! # General scoped singleton prefix primitives

The primitive computes its telescope, providers and output from raw inputs and
fixed declaration code. Its only recursive conversion premise is the scoped
family guard. Every typed source realizes it as an actual registered prefix
step, with the exact raw output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
variable [Params]

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- Reflecting the scoped family certificate reconstructs the entire actual
unfolding check. Captures are typed only after this reflection. -/
theorem Valid.check (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (GuardedSingleton.ScopedFamilyComparison Step)
      Γ C.data C.levels args program C.layout C.elim) :
    UnfoldingCheck env univs Γ (mkApps (.const C.data.name C.levels) args) program := by
  obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
  obtain ⟨S, E, hS, hE, W⟩ := RecursorData.propElim_wf henv V.registered V.large V.zero
    V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hE.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args
    henv hΓ V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht W
  have htf := (transportedFamily_typings henv heq W hctx hps hargs).1
  have hpf := W.family_prop henv hps hargs
  have hh := ((proofErase_scoped_compare_reflect hstep hctx htf hpf HG).1
    (.refl ⟨_, HasType.sort (by trivial : VLevel.zero.WF univs)⟩)).of_l henv hctx htf
  exact GuardedSingleton.check_of_family_conversion henv heq hΓ V.registered V.large V.zero
    V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht hh

/-- Any typed input of the code's arity realizes the raw telescope and guard as
an actual generated program. No original representative is stored in the guard. -/
theorem Valid.realize (V : C.Valid) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (domains, result))
    (HG : C.guard Step (proofEraseCtx Γ) domains (args.map (proofErase Γ))) :
    ∃ program, C.data.singletonUnfolding env univs C.levels args = some program ∧
      proofEraseDomains Γ program.domains = domains ∧
      GuardedSingleton.FamilyGuard (GuardedSingleton.ScopedFamilyComparison Step)
        Γ C.data C.levels args program C.layout C.elim := by
  obtain ⟨program, hg⟩ := V.generate ha
  have hd := (Prod.mk.inj (Option.some.inj ((V.telescope_eq hΓ hg ht).symm.trans hcalc))).1
  refine ⟨program, hg, hd, (V.guard_iff heq hΓ hg ht).1 ?_⟩
  rwa [hd]

/-- The raw family guard yields an actual registered prefix step at every typed
non-proof realization, whose output has exactly the code's prescribed erasure. -/
theorem Valid.replay (V : C.Valid) (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (hn : ¬ IsProof Γ (mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (domains, result))
    (HG : C.guard Step (proofEraseCtx Γ) domains (args.map (proofErase Γ))) :
    ∃ out, PrefixUnfold env univs recursorData Γ C.data.name C.levels args out ∧
      proofErase Γ out = C.output (proofEraseCtx Γ) domains (args.map (proofErase Γ)) := by
  obtain ⟨program, hg, hd, HG⟩ := V.realize heq hΓ ha ht hcalc HG
  have HC := V.check heq hstep hΓ hg ht HG
  refine ⟨program.rhs, .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg HC, ?_⟩
  rw [V.output_eq heq hΓ hg HC hn, hd]
end SingletonPrefixCode

namespace ProofShape
/-- A general singleton prefix with arbitrary indexed and dependent field
layouts. The raw family comparison is the sole recursive guard. -/
inductive ScopedSingletonPrefixPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro {C : SingletonPrefixCode} {args domains result} :
      C.Valid → args.length = C.arity → C.telescope args = some (domains, result) →
      C.guard Step Δ domains args →
      ScopedSingletonPrefixPrimitive Step Δ (mkApps (.const C.data.name C.levels) args)
        (C.output Δ domains args)

omit [Params] in
private theorem const_spine_ne_proof : mkApps (.const c ls) args ≠ .proof := by
  cases args using List.snoc_induction with
  | nil => intro h; cases h
  | snoc => rw [mkApps_snoc]; intro h; cases h
end ProofShape

/-- Every general raw singleton primitive has exact operational replay through
the actual registered prefix rule at every typed original source. -/
theorem erased_scoped_singleton_prefix_replay (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrefixReplay D (ProofShape.ScopedSingletonPrefixPrimitive Step) := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact ProofShape.const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨out, HR, HE⟩ := V.replay heq hstep hΓ ha ⟨_, ht⟩ hn hcalc HG
    exact ⟨out, .singleton HR, HE⟩

/-- General raw singleton prefixes descend below every inserted binder block.
The lower source supplies its own generated telescope; the upper raw guard
descends through the exactly renamed telescope, preserving the literal output. -/
theorem erased_scoped_singleton_prefix_descent (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (ProofShape.ScopedSingletonPrefixPrimitive Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
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
    obtain ⟨program, hg, hd, HG'⟩ := V.realize heq hΓ' hlenargs ⟨_, hup⟩
      (by rwa [hmap]) (by rwa [hmap])
    have HC := V.check heq hstep hΓ' hg ⟨_, hup⟩ HG'
    obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
    have hlen : C.levels.length = C.data.uvars := by
      rw [hl] at hll
      exact hll.trans (RecursorData.singletonEquation_uvars he)
    obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
    obtain ⟨lower, hout, HR⟩ := GuardedSingleton.scoped_prefix_descend heq hstep W hΓ hΓ'
      V.lookup V.registered V.large V.zero V.levels_wf hlen howner
      V.layout_eq V.elim_eq hg ht HG'
    have HH := (HR.defeq henv hΓ).of_l henv hΓ ht
    have HE : proofErase Γ'
        (mkApps (.const C.data.name C.levels) (original.map (·.liftN n k))) =
        ProofShape.mkApps (.const C.data.name C.levels) args := by
      simpa only [liftN_mkApps, liftN] using (proofErase_liftN hΓ hΓ' W ht).trans hsrc
    have hn : ¬ IsProof Γ'
        (mkApps (.const C.data.name C.levels) (original.map (·.liftN n k))) := by
      intro hp
      exact ProofShape.const_spine_ne_proof (HE.symm.trans (proofErase_eq_proof.2 hp))
    refine ⟨lower, HH, ?_⟩
    rw [← proofErase_liftN hΓ hΓ' W HH.hasType.2, ← hout,
      V.output_eq heq hΓ' hg HC hn, hd, hmap]

end Lean4Lean.VEnv.Strengthening
