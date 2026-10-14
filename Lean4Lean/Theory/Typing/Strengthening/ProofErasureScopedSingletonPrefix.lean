import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefixDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPrefixStages
import Lean4Lean.Theory.Typing.Strengthening.PrefixComputation

/-! # Scoped certificates for actual indexed singleton prefixes

A contextual erased family comparison reconstructs the lower generated check
under block insertion. The target is the exact generated prefix output, including
its residual telescope and captures; singleton fields may carry data.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim Params
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- Compare a generated family's erased endpoints in their actual erased context. -/
def ScopedFamilyComparison
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b)

/-- Descend the family guard under the renamed generated telescope. Its two
proposition endpoints are typed below before scoped comparison is reflected. -/
theorem scoped_family_guard_below (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (Wblock : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args))
    (HG : FamilyGuard (ScopedFamilyComparison Step) Γ' data levels (args.map (·.liftN n k)) (program.rename ((Lift.refl.skipN n).consN k)) S E) :
    FamilyGuard (fun Δ a b => env.IsDefEq univs Δ a b (.sort .zero)) Γ data levels args program S E := by
  let ρ := (Lift.refl.skipN n).consN k
  have hW : Ctx.Lift' ρ Γ Γ' := Ctx.liftN_iff_lift'.1 Wblock
  have HG : FamilyGuard (ScopedFamilyComparison Step) Γ' data levels
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
  unfold ScopedFamilyComparison at HG
  simp only [ρ, Lift.consN_consN, lift'_consN_skipN] at HG
  rw [proofErase_liftN hctx hctx' Wext htf,
    proofErase_liftN hctx hctx' Wext hpf] at HG
  exact ((proofErase_scoped_compare_descend hstep hctx hctx' Wext rfl htf hpf HG).1
    (.refl ⟨_, HasType.sort (by trivial : VLevel.zero.WF univs)⟩)).of_l henv hctx htf

/-- A scoped certificate at an upper generated prefix reconstructs an actual
lower prefix step with the exact lifted output. No upper unfolding check or
lower target typing is assumed. -/
theorem scoped_prefix_descend (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (Wblock : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hreg : registry data.name = some data) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels (args.map (·.liftN n k)) = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T)
    (HG : FamilyGuard (ScopedFamilyComparison Step) Γ' data levels (args.map (·.liftN n k)) program S E) :
    ∃ out, program.rhs = out.liftN n k ∧
      PrefixUnfold env univs registry Γ data.name levels args out := by
  let ρ := (Lift.refl.skipN n).consN k
  have hg : data.singletonUnfolding env univs levels (args.map (·.lift' ρ)) = some program := by
    simpa only [ρ, lift'_consN_skipN] using hg
  obtain ⟨lower, hgl⟩ := RecursorData.singletonUnfolding_sameArity hg (args' := args) (by simp)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrt, _⟩ :=
    RecursorData.singleton_equation_syntax H hlarge hzero hlen howner hS hE
  have hback := RecursorData.singletonUnfolding_lift' henv H hlarge hzero hrt
    (H.recursorType_closed henv hrt) hgl (ρ := ρ)
  have hprogram := RecursorData.singletonUnfolding_unique hg hback
  rw [hprogram] at HG ⊢
  have hguard := scoped_family_guard_below heq hstep Wblock hΓ hΓ' H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ HG
  have HC := check_of_family_conversion henv heq hΓ H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ hguard
  have hclosed := ClosedSingleton.generated_template_closed henv H hlarge hzero hgl
  refine ⟨lower.rhs, ?_, .intro hreg H rfl hlarge hw hzero hgl HC⟩
  simpa only [ρ, lift'_consN_skipN] using
    (RecursorData.PrefixUnfolding.rename_rhs (ρ := ρ) hclosed)

/-- If the generated guards of checked prefixes have scoped certificates,
every actual upper singleton prefix replays as an actual lower singleton prefix.
Certificate coverage remains an explicit, unproved premise. -/
theorem scoped_prefix_rule_descend (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcov : FamilyCertificateCoverage (ScopedFamilyComparison Step))
    (Wblock : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (R : PrefixUnfold env univs registry Γ' name levels (args.map (·.liftN n k)) rhs)
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T) :
    ∃ out, rhs = out.liftN n k ∧ PrefixUnfold env univs registry Γ name levels args out := by
  cases R with
  | intro hreg hr hn hl hw hz hg HC =>
    subst hn
    obtain ⟨S, E, hS, hE, _⟩ := RecursorData.singletonUnfolding_layout hg
    obtain ⟨_, _, hlv, hlen, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
    obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
    rw [hlv] at hlen
    have hlen := hlen.trans (RecursorData.singletonEquation_uvars hseq)
    exact scoped_prefix_descend heq hstep Wblock hΓ hΓ' hreg hr hl hz hw hlen
      howner hS hE hg ht (hcov hΓ' hr hl hz hw hS hE hg HC)

/-- At every finite scoped K stage, family-certificate coverage gives exact
operational replay of all registered indexed singleton prefixes. This does not
assert that the raw stage itself contains these general prefix rules. -/
theorem scoped_stage_prefix_rule_descend (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hcov : FamilyCertificateCoverage (ScopedFamilyComparison (ErasedScopedPrefixStage D stage)))
    (Wblock : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (R : PrefixUnfold env univs recursorData Γ' name levels (args.map (·.liftN n k)) rhs)
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T) :
    ∃ out, rhs = out.liftN n k ∧
      PureObservation.PrefixCompute D Γ (mkApps (.const name levels) args) out := by
  obtain ⟨out, HE, HR⟩ := scoped_prefix_rule_descend heq
    (erased_scoped_prefix_stage_descent heq hs stage) hcov Wblock hΓ hΓ' R ht
  exact ⟨out, HE, .singleton HR⟩

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
