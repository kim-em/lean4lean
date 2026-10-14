import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefixDescent

/-! # Indexed prefix descent with a lower-context equality witness

The generated family comparison has both inhabitants and a propositional Eq
witness already in the lower opened context. This file weakens the endpoint
descent premise to exploit that fact. The weaker descent premise remains open
for arbitrary ambient conversion; no global strengthening reduction is claimed.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim Params
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- Restricted descent at inhabited propositions whose equality has a witness
below the insertion. For arbitrary conversion this is an unproved local front;
it is not the ambient WitnessedPropCoverage premise from the boundary theorem. -/
def WitnessedPropDescent (Cmp : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {ρ Γ Γ' P Q p q witness}, Ctx.Lift' ρ Γ Γ' →
    OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ p P → env.HasType univs Γ q Q →
    env.HasType univs Γ witness (eqApp (.succ .zero) (.sort .zero) P Q) →
    Cmp Γ' (P.lift' ρ) (Q.lift' ρ) → env.IsDefEqU univs Γ P Q

/-- Every previously checked endpoint relation satisfies the restricted premise. -/
theorem WitnessedPropDescent.of_endpoint (hc : EndpointDescent Cmp) :
    WitnessedPropDescent Cmp :=
  fun W hΓ hΓ' hP hQ _ _ _ H => hc W hΓ hΓ' hP hQ H

/-- The reconstructed constructor, original major, and closed family extractor
supply all three witness terms below before the guard is descended. -/
theorem family_guard_below_witnessed (heq : env.HasCanonicalEq) (hcmp : WitnessedPropDescent Cmp)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args))
    (HG : FamilyGuard Cmp Γ' data levels (args.map (·.lift' ρ)) (program.rename ρ) S E) :
    FamilyGuard (fun Δ a b => env.IsDefEq univs Δ a b (.sort .zero)) Γ data levels args program S E := by
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
  exact (hcmp hW' hctx hctx' htf hpf
    (transportedFamily_typings henv heq W hctx hps hargs).2
    (W.major_typed hps hargs) (familyWitness_at_typed henv heq W hps hargs) HG).of_l henv hctx htf

/-- Restricted family descent replays the exact generated lower program. -/
theorem prefix_descend_witnessed (heq : env.HasCanonicalEq) (hcmp : WitnessedPropDescent Cmp)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels (args.map (·.lift' ρ)) = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T)
    (HG : FamilyGuard Cmp Γ' data levels (args.map (·.lift' ρ)) program S E) :
    ∃ out, program.rhs = out.lift' ρ ∧
      env.IsDefEq univs Γ (mkApps (.const data.name levels) args) out T := by
  obtain ⟨lower, hgl⟩ := RecursorData.singletonUnfolding_sameArity hg (args' := args) (by simp)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrt, _⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  have hback := RecursorData.singletonUnfolding_lift' henv H hlarge hzero hrt
    (H.recursorType_closed henv hrt) hgl (ρ := ρ)
  have hprogram := RecursorData.singletonUnfolding_unique hg hback
  rw [hprogram] at HG ⊢
  have hguard := family_guard_below_witnessed heq hcmp hW hΓ hΓ' H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ HG
  have HC := check_of_family_conversion henv heq hΓ H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ hguard
  have hclosed := ClosedSingleton.generated_template_closed henv H hlarge hzero hgl
  exact ⟨lower.rhs, RecursorData.PrefixUnfolding.rename_rhs hclosed,
    (show env.IsDefEqU univs Γ _ _ from ⟨_, HC.defeq henv hΓ⟩).of_l henv hΓ ht⟩

/-- The raw prefix computation needs only witnessed proposition descent. -/
theorem PrefixStep.computeDescent_witnessed (heq : env.HasCanonicalEq) (hcmp : WitnessedPropDescent Cmp) :
    ComputeDescent (PrefixStep Cmp) := by
  intro ρ Γ Γ' e target T R hW hΓ hΓ' ht
  generalize hsrc : e.lift' ρ = source at R
  cases R with
  | intro H hl hz hw hn ho hS hE hg HG =>
    obtain ⟨args, rfl, rfl⟩ := PureObservation.lift'_eq_const_spine hsrc
    exact prefix_descend_witnessed heq hcmp hW hΓ hΓ' H hl hz hw hn ho hS hE hg ht HG

/-- Specializing the restricted premise to actual conversion suffices for
all original singleton-prefix rules, without a certificate-completeness premise.
Proving this restricted descent, and extending it to full strengthening, remain open. -/
theorem prefix_rule_descend_witnessed (heq : env.HasCanonicalEq)
    (hfront : WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (R : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) rhs)
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T) :
    ∃ out, rhs = out.lift' ρ ∧ env.IsDefEq univs Γ (mkApps (.const name levels) args) out T := by
  have hc : FamilyCertificateCoverage (fun Δ a b => env.IsDefEqU univs Δ a b) := by
    intro Δ data levels args program S E hΔ H hl hz hw hS hE hg HC
    obtain ⟨_, _, hlv, hlen, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
    obtain ⟨index, ho, _⟩ := RecursorData.singletonEquation_eq hseq
    rw [hlv] at hlen
    have hlen := hlen.trans (RecursorData.singletonEquation_uvars hseq)
    exact ⟨_, family_conversion_of_check henv heq hΔ H hl hz hw hlen ho hS hE hg HC⟩
  have RR := PrefixStep.of_prefix hc hΓ' R
  have RR' : PrefixStep (fun Δ a b => env.IsDefEqU univs Δ a b) Γ'
      ((mkApps (.const name levels) args).lift' ρ) rhs := by
    simpa only [lift'_mkApps, lift'] using RR
  exact PrefixStep.computeDescent_witnessed heq hfront RR' hW hΓ hΓ' ht

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
