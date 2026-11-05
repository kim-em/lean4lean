import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalStageChains
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalPatternClosure
import Lean4Lean.Theory.Typing.Confluence.WFParams

/-! # Declaration-history induction for computational pattern coverage

A rule installed earlier has strictly smaller remaining history rank. The
induction supplies its coverage while interpreting declaration equations in the
ambient computation system. Thus earlier declaration chains are derived;
type-fork joining and the generic data-domain certificates remain explicit.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params]

/-- All registered patterns have computational coverage under type-fork joining
and generic data-domain certificates. The earlier declaration-chain assumption
is discharged by the actual environment history, not by current completeness. -/
theorem computational_pattern_closure_of_history
    (heq : env.HasCanonicalEq)
    (HF : TypeForkJoin EnvironmentCore.definitions)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HD : RegisteredSingletonDomainChains EnvironmentCore.definitions) :
    ComputationallyTypedPatternClosure EnvironmentCore.definitions := by
  obtain ⟨ds, H⟩ := henv.stagesH
  let Rank (p : Pattern) (n : Nat) : Prop :=
    ∀ {data decl env₀ env₁ rec i} (hi : i < env.stages.length),
      RecursorRegisteredAt env data decl env₀ env₁ → rec ∈ decl.recs →
      rec.name = p.headConst → env.stages[i] = env₀ → env.stages.length ≤ n + i
  have key : ∀ n, ∀ {p : Pattern} {r : p.RHS × p.Check}, env.pats p r → Rank p n →
      ComputationalPatternCoverage EnvironmentCore.definitions p r := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro p r hp hrank Γ e A m1 m2 chk hΓ hm hJ hR hr hall
    obtain ⟨recN, major, ctor, fields, data, rfl, hl, _, _, _⟩ := henv.pats_guarded hp
    have hreg : env.recursorRegistry (SimplePattern.iota recN major ctor fields).toPattern.headConst = some data := by
      rw [SimplePattern.iota_headConst]; exact hl
    by_cases hz : data.largeTarget = true ∧ (data.schema.sourceLevel data.owner data.levels).inst m1 ≈ .zero
    · refine TypedComputationEq.computational_singleton_pattern_of_stage heq EnvironmentCore.sound HF
        (fun _ hc => EnvironmentCore.no_rigid hc) hregistry ?_ hΓ hp hreg hz.1 hz.2
        (fun hw hlen => HD (recursorRegistry_entry hreg).registered hz.1 hz.2 hw hlen) hm hJ hR.hasType
      intro decl env₀ env₁ rec hAt hstage hrec hrname
      obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hstage
      have hbound := hrank hi hAt hrec hrname hie
      obtain ⟨base, expanded, g, auxiliaries, block, _, _, _, _, _, _, _, _, hdecl, hadd, _, hle,
        _⟩ := hAt
      have hcov : ∀ {p' : Pattern} {r' : p'.RHS × p'.Check}, env₀.pats p' r' →
          ComputationalPatternCoverage EnvironmentCore.definitions p' r' := by
        intro p' r' hp'
        have hp'E : env.pats p' r' := (H.stage_le hstage).pats hp'
        have hn : 0 < n := by omega
        have hrk : Rank p' (n - 1) := by
          intro data' decl' env₀' env₁' rec' j hj hAt' hrec' hname' hje
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hadd', _, _, _⟩ := hAt'
          have hlt := WF.stage_rank_lt H hi hj (hie ▸ hp') (hje ▸ hadd') hrec' hname'
          omega
        intro Γ' e' A' m1' m2' chk' hΓ' hm' hJ' hR' hr' hall'
        exact ih (n - 1) (by omega) hp'E hrk hΓ' hm' hJ' hR' hr' hall'
      intro base E
      exact stage_types_computational_chains heq hcon hqpat hstage hdecl hadd hle hcov
    · exact TypedComputationEq.pattern_nonzero EnvironmentCore.sound hcon hguard hΓ hp hreg hz hm hJ.hasType
  intro Γ p r e A ls captures chk hΓ hp hm hJ hR hr hall
  exact key env.stages.length hp (fun _ _ _ _ _ => by omega) hΓ hm hJ hR hr hall

/-- Ordinary equality yields computation chains and computational endpoint
certificates assuming only type-fork joining and registered generic data-domain
chains, in addition to the concrete presentation. These two remaining
assumptions are not claimed to be strictly smaller than strengthening. -/
theorem computational_typing_of_history
    (heq : env.HasCanonicalEq)
    (HF : TypeForkJoin EnvironmentCore.definitions)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HD : RegisteredSingletonDomainChains EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A ∧
      HasTypeC EnvironmentCore.definitions Γ a A ∧ HasTypeC EnvironmentCore.definitions Γ b A :=
  computational_typing_of_defeq heq hcon hqpat
    (computational_pattern_closure_of_history heq HF hregistry hcon hqpat hguard HD) hΓ H

end Lean4Lean.VEnv.Strengthening
