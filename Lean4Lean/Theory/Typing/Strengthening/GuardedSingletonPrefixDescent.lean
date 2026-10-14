import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefix
import Lean4Lean.Theory.Typing.PrefixUnfolding.Weakening

/-! # Descending arbitrary indexed prefixes with family certificates

Only the one family guard is compared above the inserted binders. The generated
residual telescope, capture program and result all rename exactly; their lower
replay check is rebuilt from source typing and the descended guard.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim
open private liftN_lift'_consN vars_lift'_consN
  from Lean4Lean.Theory.Typing.PrefixUnfolding.Renaming

/-- The single comparison read by a generated singleton prefix. -/
def FamilyGuard (Cmp : List VExpr → VExpr → VExpr → Prop) (Γ : List VExpr)
    (data : RecursorData) (levels : List VLevel) (args : List VExpr)
    (program : RecursorData.PrefixUnfolding) (S : SingletonLayout) (E : PropElim) : Prop :=
  let all := data.openedArguments args
  let ps := all.take data.numParams
  let idx := (all.drop data.indexOffset).take data.numIndices
  Cmp (program.domains.reverse ++ Γ)
    (transportedFamily S (data.propParams levels) E ps idx (.bvar 0))
    (mkApps E.family (ps ++ idx))

/-- Opened providers rename under exactly the residual number of binders. -/
theorem openedArguments_lift' (data : RecursorData) (args : List VExpr) (ρ : Lift) :
    data.openedArguments (args.map (·.lift' ρ)) =
      (data.openedArguments args).map (·.lift' (ρ.consN (data.majorOffset + 1 - args.length))) := by
  simp only [RecursorData.openedArguments, List.length_map, List.map_append, List.map_map,
    Function.comp_def, liftN_lift'_consN, vars_lift'_consN]

open Params
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- A descending endpoint certificate lowers the family guard under the exact
renamed residual telescope. Both comparison endpoints are typed below first. -/
theorem family_guard_below (heq : env.HasCanonicalEq) (hcmp : EndpointDescent Cmp)
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
  exact (hcmp hW' hctx hctx' htf hpf HG).of_l henv hctx htf

/-- Rebuild the actual lower generated check from an upper family certificate.
No upper replay check and no lower result typing is required. -/
theorem prefix_descend (heq : env.HasCanonicalEq) (hcmp : EndpointDescent Cmp)
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
  have hguard := family_guard_below heq hcmp hW hΓ hΓ' H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ HG
  have HC := check_of_family_conversion henv heq hΓ H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ hguard
  have hclosed := ClosedSingleton.generated_template_closed henv H hlarge hzero hgl
  exact ⟨lower.rhs, RecursorData.PrefixUnfolding.rename_rhs hclosed,
    (show env.IsDefEqU univs Γ _ _ from ⟨_, HC.defeq henv hΓ⟩).of_l henv hΓ ht⟩

/-- Concrete recovered-comparison stages suffice for arbitrary indexed prefix
replay; proving that every ambient family guard has such a certificate is open. -/
theorem compared_prefix_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels (args.map (·.lift' ρ)) = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T)
    (HG : FamilyGuard (RecoveryComparisonGuard (ComparedEtaCompute D kdepth stage))
      Γ' data levels (args.map (·.lift' ρ)) program S E) :
    ∃ out, program.rhs = out.lift' ρ ∧
      env.IsDefEq univs Γ (mkApps (.const data.name levels) args) out T :=
  prefix_descend heq (RecoveryComparisonGuard.descends (ComparedEtaCompute.computeDescent heq hs stage))
    hW hΓ hΓ' H hlarge hzero hw hlen howner hS hE hg ht HG

/-- A raw registered singleton prefix step with a concrete family certificate.
It retains the actual generated target and has no target-typing premise. -/
inductive PrefixStep (Cmp : List VExpr → VExpr → VExpr → Prop) :
    List VExpr → VExpr → VExpr → Prop where
  | intro {S : SingletonLayout} {E : PropElim} (H : RecursorRegistered env data)
      (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
      (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
      {index : Fin data.schema.signature.constructors.size}
      (howner : data.schema.signature.constructors[index].owner = data.owner)
      (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
      (hg : data.singletonUnfolding env univs levels args = some program)
      (HG : FamilyGuard Cmp Γ data levels args program S E) :
      PrefixStep Cmp Γ (mkApps (.const data.name levels) args) program.rhs

/-- The new indexed rule meets the same scoped-computation descent interface
as beta, guarded K and recovered eta. -/
theorem PrefixStep.computeDescent (heq : env.HasCanonicalEq) (hcmp : EndpointDescent Cmp) :
    ComputeDescent (PrefixStep Cmp) := by
  intro ρ Γ Γ' e target T R hW hΓ hΓ' ht
  generalize hsrc : e.lift' ρ = source at R
  cases R with
  | intro H hl hz hw hn ho hS hE hg HG =>
    obtain ⟨args, rfl, rfl⟩ := PureObservation.lift'_eq_const_spine hsrc
    exact prefix_descend heq hcmp hW hΓ hΓ' H hl hz hw hn ho hS hE hg ht HG

/-- The concrete finite comparison model discharges the indexed rule's descent
premise without invoking arbitrary equality strengthening. -/
theorem PrefixStep.compared_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ComputeDescent (PrefixStep (RecoveryComparisonGuard (ComparedEtaCompute D kdepth stage))) :=
  computeDescent heq (RecoveryComparisonGuard.descends (ComparedEtaCompute.computeDescent heq hs stage))

/-- The remaining local coverage obligation: certify only the two family
propositions generated by an already checked registered prefix. This has not
been proved for the finite comparison model; it does not request arbitrary
proposition comparison or exact replay of all ambient reductions. -/
def FamilyCertificateCoverage (Cmp : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ data levels args program S E}, OnCtx Γ (env.IsType univs) →
    RecursorRegistered env data → data.largeTarget = true → data.sourceLevel levels ≈ .zero →
    (∀ l ∈ levels, l.WF univs) → data.singletonLayout env levels = some S →
    data.propElim levels = some E → data.singletonUnfolding env univs levels args = some program →
    UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program →
    FamilyGuard Cmp Γ data levels args program S E

/-- Family certificate coverage alone covers every original registered prefix
step in the new computation rule. -/
theorem PrefixStep.of_prefix (hcov : FamilyCertificateCoverage Cmp)
    (hΓ : OnCtx Γ (env.IsType univs))
    (R : PrefixUnfold env univs registry Γ name levels args rhs) :
    PrefixStep Cmp Γ (mkApps (.const name levels) args) rhs := by
  cases R with
  | intro _ hr hn hl hw hz hg HC =>
    subst hn
    obtain ⟨S, E, hS, hE, _⟩ := RecursorData.singletonUnfolding_layout hg
    obtain ⟨_, _, hlv, hlen, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
    obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
    rw [hlv] at hlen
    have hlen := hlen.trans (RecursorData.singletonEquation_uvars hseq)
    exact .intro hr hl hz hw hlen howner hS hE hg (hcov hΓ hr hl hz hw hS hE hg HC)

/-- The original indexed prefix rule descends once its generated family guards
are covered. All typing and occurrence replay has already been discharged. -/
theorem prefix_rule_descend (heq : env.HasCanonicalEq) (hcmp : EndpointDescent Cmp)
    (hcov : FamilyCertificateCoverage Cmp)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (R : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) rhs)
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T) :
    ∃ out, rhs = out.lift' ρ ∧ env.IsDefEq univs Γ (mkApps (.const name levels) args) out T := by
  have RR := PrefixStep.of_prefix hcov hΓ' R
  have RR' : PrefixStep Cmp Γ' ((mkApps (.const name levels) args).lift' ρ) rhs := by
    simpa only [lift'_mkApps, lift'] using RR
  exact PrefixStep.computeDescent heq hcmp RR' hW hΓ hΓ' ht

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
