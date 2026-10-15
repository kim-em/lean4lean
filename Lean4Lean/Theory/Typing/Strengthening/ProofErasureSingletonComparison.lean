import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedSingletonSubstitution

/-! # General singleton prefixes with a replaceable family comparator

The prefix program and its raw templates are unchanged. Only the family
comparison is parameterized. Block descent of proposition comparisons suffices
for exact prefix descent and operational replay. No comparison coverage or
substitution law is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
variable [Params]

/-- A raw family comparator reflects proposition equality below any inserted
block when both propositions are already typed below. -/
def ErasedFamilyDescent
    (Cmp : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' n k P Q}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → env.HasType univs Γ P (.sort .zero) →
    env.HasType univs Γ Q (.sort .zero) →
    Cmp (proofEraseCtx Γ') ((proofErase Γ P).liftN n k) ((proofErase Γ Q).liftN n k) →
    env.IsDefEq univs Γ P Q (.sort .zero)

/-- At zero insertion the same interface reflects a typed family comparison. -/
theorem ErasedFamilyDescent.reflect (H : ErasedFamilyDescent Cmp)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (HC : Cmp (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)) :
    env.IsDefEq univs Γ P Q (.sort .zero) :=
  H hΓ hΓ (show Ctx.LiftN 0 0 Γ Γ from .zero []) hP hQ
    (by simpa only [ProofShape.liftN_zero] using HC)

/-- Interpret a raw comparator at the erasures of original family endpoints. -/
def ErasedFamilyComparison
    (Cmp : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) (P Q : VExpr) : Prop :=
  Cmp (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)

/-- A general raw family guard using exactly the existing closed templates. -/
def SingletonFamilyGuardWith
    (Cmp : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (S : SingletonLayout) (params : List VExpr) (E : PropElim)
    (ps idx : List ProofShape) : Prop :=
  Cmp Δ
    ((erasedTransportedFamilyTemplate S params E).instOuter (ps ++ idx ++ [.proof]))
    ((erasedRequestedFamilyTemplate S params E).instOuter (ps ++ idx ++ [.proof]))

section
variable {S : SingletonLayout} {E : PropElim} {params : List VExpr}
/-- At any typed occurrence, the raw template guard is exactly the contextual
family comparison, without requiring either family conversion or bare fields. -/
theorem singleton_family_template_with_iff (heq : env.HasCanonicalEq)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (singletonOccurrenceDomains S params E) (ps ++ idx ++ [m])) :
    ErasedFamilyComparison Cmp Γ
      (transportedFamily S params E ps idx m) (mkApps E.family (ps ++ idx)) ↔
      SingletonFamilyGuardWith Cmp (proofEraseCtx Γ) S params E
        (ps.map (proofErase Γ)) (idx.map (proofErase Γ)) := by
  unfold ErasedFamilyComparison SingletonFamilyGuardWith
  rw [proofErase_transportedFamily_template heq W hΓ hps hargs,
    proofErase_requestedFamily_template W hΓ hps hargs]

/-- A generated prefix's contextual family guard is exactly the fixed-template
raw guard beneath its erased residual telescope. Only source typing is needed
to identify it; guard coverage and validity remain separate questions. -/
theorem singleton_prefix_template_with_iff (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args)) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison Cmp)
      Γ data levels args program S E ↔
      let Δ := program.domains.reverse ++ Γ
      let all := (data.openedArguments args).map (proofErase Δ)
      SingletonFamilyGuardWith Cmp
        ((proofEraseDomains Γ program.domains).reverse ++ proofEraseCtx Γ)
        S (data.propParams levels) E (all.take data.numParams)
        ((all.drop data.indexOffset).take data.numIndices) := by
  dsimp only
  obtain ⟨_, _, hlv, hlvlen, hseq, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : levels.length = data.uvars := by
    rw [hlv] at hlvlen
    exact hlvlen.trans (RecursorData.singletonEquation_uvars hseq)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ :=
    GuardedSingleton.registered_opened_args henv hΓ H hlarge hzero hw hlen howner hS hE hg ht W
  simpa only [GuardedSingleton.FamilyGuard, List.map_take, List.map_drop, proofEraseDomains_context] using
    singleton_family_template_with_iff (Cmp := Cmp) heq W hctx hps hargs

end

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- Substitute only the family comparator in the fixed raw singleton program. -/
def guardWith (C : SingletonPrefixCode)
    (Cmp : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ domains args : List ProofShape) : Prop :=
  let all := ProofShape.openPrefixArguments Δ domains args
  SingletonFamilyGuardWith Cmp (domains.reverse ++ Δ) C.layout
    (C.data.propParams C.levels) C.elim (all.take C.data.numParams)
    ((all.drop C.data.indexOffset).take C.data.numIndices)

/-- The code's raw guard agrees with the actual generated family guard at any
typed realization, before either guard is assumed true. -/
theorem Valid.guardWith_iff (V : C.Valid) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args)) :
    C.guardWith Cmp (proofEraseCtx Γ) (proofEraseDomains Γ program.domains)
      (args.map (proofErase Γ)) ↔
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison Cmp)
      Γ C.data C.levels args program C.layout C.elim := by
  have hh := singleton_prefix_template_with_iff (Cmp := Cmp) heq hΓ V.registered
    V.large V.zero V.levels_wf V.layout_eq V.elim_eq hg ht
  dsimp only at hh
  rw [proofErase_singleton_prefix_arguments hΓ V.registered V.levels_wf hg ht] at hh
  exact hh.symm

/-- Reflecting the scoped family certificate reconstructs the entire actual
unfolding check. Captures are typed only after this reflection. -/
theorem Valid.checkWith (V : C.Valid) (heq : env.HasCanonicalEq)
    (hcmp : ErasedFamilyDescent Cmp)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison Cmp)
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
  have hh := hcmp.reflect hctx htf hpf HG
  exact GuardedSingleton.check_of_family_conversion henv heq hΓ V.registered V.large V.zero
    V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht hh

/-- Any typed input of the code's arity realizes the raw telescope and guard as
an actual generated program. No original representative is stored in the guard. -/
theorem Valid.realizeWith (V : C.Valid) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (domains, result))
    (HG : C.guardWith Cmp (proofEraseCtx Γ) domains (args.map (proofErase Γ))) :
    ∃ program, C.data.singletonUnfolding env univs C.levels args = some program ∧
      proofEraseDomains Γ program.domains = domains ∧
      GuardedSingleton.FamilyGuard (ErasedFamilyComparison Cmp)
        Γ C.data C.levels args program C.layout C.elim := by
  obtain ⟨program, hg⟩ := V.generate ha
  have hd := (Prod.mk.inj (Option.some.inj ((V.telescope_eq hΓ hg ht).symm.trans hcalc))).1
  refine ⟨program, hg, hd, (V.guardWith_iff heq hΓ hg ht).1 ?_⟩
  rwa [hd]

/-- The raw family guard yields an actual registered prefix step at every typed
non-proof realization, whose output has exactly the code's prescribed erasure. -/
theorem Valid.replayWith (V : C.Valid) (heq : env.HasCanonicalEq)
    (hcmp : ErasedFamilyDescent Cmp)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (hn : ¬ IsProof Γ (mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (domains, result))
    (HG : C.guardWith Cmp (proofEraseCtx Γ) domains (args.map (proofErase Γ))) :
    ∃ out, PrefixUnfold env univs recursorData Γ C.data.name C.levels args out ∧
      proofErase Γ out = C.output (proofEraseCtx Γ) domains (args.map (proofErase Γ)) := by
  obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq hΓ ha ht hcalc HG
  have HC := V.checkWith heq hcmp hΓ hg ht HG
  refine ⟨program.rhs, .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg HC, ?_⟩
  rw [V.output_eq heq hΓ hg HC hn, hd]
end SingletonPrefixCode

namespace GuardedSingleton
variable {S : SingletonLayout} {E : PropElim}
/-- Descend the family guard under the renamed generated telescope. Its two
proposition endpoints are typed below before scoped comparison is reflected. -/
theorem family_guard_with_below (heq : env.HasCanonicalEq)
    (hcmp : ErasedFamilyDescent Cmp)
    (Wblock : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args))
    (HG : FamilyGuard (ErasedFamilyComparison Cmp) Γ' data levels (args.map (·.liftN n k)) (program.rename ((Lift.refl.skipN n).consN k)) S E) :
    FamilyGuard (fun Δ a b => env.IsDefEq univs Δ a b (.sort .zero)) Γ data levels args program S E := by
  let ρ := (Lift.refl.skipN n).consN k
  have hW : Ctx.Lift' ρ Γ Γ' := Ctx.liftN_iff_lift'.1 Wblock
  have HG : FamilyGuard (ErasedFamilyComparison Cmp) Γ' data levels
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
  unfold ErasedFamilyComparison at HG
  simp only [ρ, Lift.consN_consN, lift'_consN_skipN] at HG
  rw [proofErase_liftN hctx hctx' Wext htf,
    proofErase_liftN hctx hctx' Wext hpf] at HG
  exact hcmp hctx hctx' Wext htf hpf HG

/-- A scoped certificate at an upper generated prefix reconstructs an actual
lower prefix step with the exact lifted output. No upper unfolding check or
lower target typing is assumed. -/
theorem prefix_with_descend (heq : env.HasCanonicalEq)
    (hcmp : ErasedFamilyDescent Cmp)
    (Wblock : Ctx.LiftN n k Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (hreg : registry data.name = some data) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels (args.map (·.liftN n k)) = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T)
    (HG : FamilyGuard (ErasedFamilyComparison Cmp) Γ' data levels (args.map (·.liftN n k)) program S E) :
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
  have hguard := family_guard_with_below heq hcmp Wblock hΓ hΓ' H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ HG
  have HC := check_of_family_conversion henv heq hΓ H hlarge hzero hw hlen howner hS hE hgl ⟨_, ht⟩ hguard
  have hclosed := ClosedSingleton.generated_template_closed henv H hlarge hzero hgl
  refine ⟨lower.rhs, ?_, .intro hreg H rfl hlarge hw hzero hgl HC⟩
  simpa only [ρ, lift'_consN_skipN] using
    (RecursorData.PrefixUnfolding.rename_rhs (ρ := ρ) hclosed)

end GuardedSingleton

namespace ProofShape
/-- A general singleton prefix whose raw family guard uses the supplied
comparator. Valid code still fixes its telescope, providers and exact output. -/
inductive SingletonPrimitiveWith
    (Cmp : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro {C : SingletonPrefixCode} {args domains result} :
      C.Valid → args.length = C.arity → C.telescope args = some (domains, result) →
      C.guardWith Cmp Δ domains args →
      SingletonPrimitiveWith Cmp Δ (mkApps (.const C.data.name C.levels) args)
        (C.output Δ domains args)
end ProofShape

open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive

/-- Every general raw singleton primitive has exact operational replay through
the actual registered prefix rule at every typed original source. -/
theorem erased_singleton_with_replay (heq : env.HasCanonicalEq)
    (hcmp : ErasedFamilyDescent Cmp) :
    ErasedScopedPrefixReplay D (ProofShape.SingletonPrimitiveWith Cmp) := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact ProofShape.const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨out, HR, HE⟩ := V.replayWith heq hcmp hΓ ha ⟨_, ht⟩ hn hcalc HG
    exact ⟨out, .singleton HR, HE⟩

/-- General raw singleton prefixes descend below every inserted binder block.
The lower source supplies its own generated telescope; the upper raw guard
descends through the exactly renamed telescope, preserving the literal output. -/
theorem erased_singleton_with_descent (heq : env.HasCanonicalEq)
    (hcmp : ErasedFamilyDescent Cmp) :
    ErasedScopedPrimitiveDescent (ProofShape.SingletonPrimitiveWith Cmp) := by
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
    obtain ⟨program, hg, hd, HG'⟩ := V.realizeWith heq hΓ' hlenargs ⟨_, hup⟩
      (by rwa [hmap]) (by rwa [hmap])
    have HC := V.checkWith heq hcmp hΓ' hg ⟨_, hup⟩ HG'
    obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
    have hlen : C.levels.length = C.data.uvars := by
      rw [hl] at hll
      exact hll.trans (RecursorData.singletonEquation_uvars he)
    obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
    obtain ⟨lower, hout, HR⟩ := GuardedSingleton.prefix_with_descend heq hcmp W hΓ hΓ'
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
