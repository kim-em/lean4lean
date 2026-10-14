import Lean4Lean.Theory.Typing.Strengthening.IndexedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.ComparedRecoverySubstitution
import Lean4Lean.Theory.Typing.PrefixUnfolding.Substitution

/-! # Recoverable substitution through indexed family guards

Source typing supplies both family propositions under the opened telescope.
Substitution may enlarge the comparison stage, but preserves the exact generated
program. The argument must recover its declared type for the staged theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim
open private vars_inst_above from Lean4Lean.Theory.Typing.PrefixUnfolding.Substitution

/-- Opening the remaining recursor binders commutes with outer substitution. -/
theorem openedArguments_inst (data : RecursorData) (args : List VExpr) (x : VExpr) (k : Nat) :
    data.openedArguments (args.map (·.inst x k)) =
      (data.openedArguments args).map (·.inst x (k + (data.majorOffset + 1 - args.length))) := by
  simp only [RecursorData.openedArguments, List.length_map, List.map_append, List.map_map,
    Function.comp_def, vars_inst_above,
    liftN_instN_lo _ _ _ _ _ (Nat.zero_le _), Nat.add_comm]

open Params
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- Source typing suffices to transform the two family endpoints under the
substituted residual telescope, even when the guard relation changes. -/
theorem FamilyGuard.instN_to (heq : env.HasCanonicalEq)
    (hsub : ∀ {k Γ₁ Γ a b α}, OnCtx Γ₁ (env.IsType univs) →
      Ctx.InstN Γ₀ x A₀ k Γ₁ Γ → env.HasType univs Γ₁ a α →
      env.HasType univs Γ₁ b α → Cmp Γ₁ a b →
      Cmp' Γ (a.inst x k) (b.inst x k))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hW : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ₁ (mkApps (.const data.name levels) args))
    (HG : FamilyGuard Cmp Γ₁ data levels args program S E) :
    FamilyGuard Cmp' Γ data levels (args.map (·.inst x k)) (program.instN x k) S E := by
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨hctx, hps, _, hidx, _, _, hargs⟩ :=
    registered_opened_args henv hΓ₁ H hlarge hzero hw hlen howner hS hE hg ht W
  have htf := (transportedFamily_typings henv heq W hctx hps hargs).1
  have hpf := W.family_prop henv hps hargs
  have hW' := Ctx.InstN.reverse program.domains hW
  rw [Nat.add_comm program.domains.length k] at hW'
  have HG' := hsub hctx hW' htf hpf HG
  have hlenD : program.domains.length = data.majorOffset + 1 - args.length := by
    obtain ⟨_, _, _, _, hh, _⟩ := RecursorData.singletonUnfolding_layout hg
    exact hh
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr
    (RecursorData.singletonUnfolding_spec hg).2.1
  have hmajor : (VExpr.bvar 0).inst x (k + program.domains.length) = .bvar 0 := by
    simp only [VExpr.inst, instVar, if_pos (show 0 < k + program.domains.length by omega)]
  have hf := transportedFamily_subst_raw (m := .bvar 0) henv heq W hps hidx
    (Subst.liftN (.one x) (k + program.domains.length))
  simp only [← instN_eq, hmajor] at hf
  unfold FamilyGuard at HG' ⊢
  simp only [openedArguments_inst, ← hlenD, ← List.map_take, ← List.map_drop]
  simpa only [hf, inst_mkApps, W.family_closed.instN_eq (Nat.zero_le _), List.map_append,
    RecursorData.PrefixUnfolding.instN] using HG'

/-- The raw indexed rule preserves its generated output under every typed
substitution whose endpoint certificates transform. -/
theorem PrefixStep.instN_to (heq : env.HasCanonicalEq)
    (hsub : ∀ {k Γ₁ Γ a b α}, OnCtx Γ₁ (env.IsType univs) →
      Ctx.InstN Γ₀ x A₀ k Γ₁ Γ → env.HasType univs Γ₁ a α →
      env.HasType univs Γ₁ b α → Cmp Γ₁ a b →
      Cmp' Γ (a.inst x k) (b.inst x k))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hW : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ht : VExpr.WF env univs Γ₁ e) (R : PrefixStep Cmp Γ₁ e out) :
    PrefixStep Cmp' Γ (e.inst x k) (out.inst x k) := by
  cases R with
  | intro H hl hz hw hn ho hS hE hg HG =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrt, _⟩ :=
      RecursorData.singleton_equation_syntax H hl hz hn ho hS hE
    have hg' := RecursorData.singletonUnfolding_inst henv H hl hz hrt
      (H.recursorType_closed henv hrt) hg (arg := x) (k := k)
    have HG' := HG.instN_to heq hsub hΓ₁ hW H hl hz hw hn ho hS hE hg ht
    have R' := PrefixStep.intro H hl hz hw hn ho hS hE hg' HG'
    rw [RecursorData.PrefixUnfolding.rhs_instN _
      (ClosedSingleton.generated_template_closed henv H hl hz hg)] at R'
    simpa only [inst_mkApps, VExpr.inst] using R'

end Lean4Lean.VEnv.Strengthening.GuardedSingleton

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- Both K and indexed prefixes use the same substituted recovery guard. -/
theorem IndexedNextComputation.substitution (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hx : env.HasType univs Γ₀ x A₀) (Rx : TypeRecoveryWith C' Γ₀ x A₀) :
    ComputeSubstitutionTo (IndexedNextComputation D C) (IndexedNextComputation D C') Γ₀ x A₀ := by
  intro k Γ₁ Γ e out hΓ₁ W ht R
  exact R.elim
    (fun R => .inl (ComparedNextComputation.substitution heq hs hc hw hsub hx Rx hΓ₁ W ht R))
    (fun R => .inr (R.instN_to heq
      (fun hΓ W ha hb H => H.instN_to hc hw hsub hΓ hx Rx W ha hb) hΓ₁ W ht))

/-- Recoverable substitution adds the argument's stage, including guards
under the generated dependent telescope of every indexed prefix. -/
theorem IndexedEtaCompute.substitution (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith (IndexedEtaCompute D kdepth r) Γ₀ x A₀) :
    ∀ stage, ComputeSubstitutionTo (IndexedEtaCompute D kdepth stage)
      (IndexedEtaCompute D kdepth (r + stage)) Γ₀ x A₀ := by
  intro stage
  induction stage with
  | zero =>
    intro k Γ₁ Γ e out hΓ₁ W ht R
    have R' := CertifiedKCompute.instN R heq hs hΓ₁ hx W ht
    exact IndexedEtaCompute.mono (Nat.zero_le _) R'
  | succ stage ih =>
    have hcs : ComputeDescent (IndexedEtaCompute D kdepth stage) := computeDescent heq hs stage
    have hwt : ComputeWeakening (IndexedEtaCompute D kdepth (r + stage)) :=
      computeWeakening heq (r + stage)
    have Rx' : TypeRecoveryWith (IndexedEtaCompute D kdepth (r + stage)) Γ₀ x A₀ :=
      Rx.mono (fun H => H.mono (Nat.le_add_right r stage))
    intro k Γ₁ Γ e out hΓ₁ W ht R
    exact RecoveredEtaWith.instN_to R (IndexedNextComputation.descends heq hs hcs)
      (IndexedNextComputation.weakens heq hwt)
      (IndexedNextComputation.substitution heq hs hcs hwt ih hx Rx') hΓ₁ hx
      (Rx'.mono (fun H => Or.inl (Or.inl H))) W ht

/-- Composition shares one stage bound. -/
theorem IndexedEtaCompute.trans (R : IndexedEtaCompute D kdepth stage Γ a b)
    (S : IndexedEtaCompute D kdepth stage Γ b c) :
    IndexedEtaCompute D kdepth stage Γ a c := by
  cases stage with
  | zero => exact GuardedKCompute.trans R S
  | succ stage => exact RecoveredEtaWith.trans R S

/-- Beta contraction retains an indexed body computation after substituting
an argument that recovers its declared type. -/
theorem IndexedEtaCompute.beta_inst
    (R : IndexedEtaCompute D kdepth stage (A :: Γ) b b')
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (Rx : TypeRecoveryWith (IndexedEtaCompute D kdepth r) Γ x A)
    (hb : VExpr.WF env univs (A :: Γ) b) :
    IndexedEtaCompute D kdepth (r + stage) Γ (.app (.lam A b) x) (b'.inst x) :=
  (IndexedEtaCompute.of_compared _ (ComparedEtaCompute.of_staged _ StagedEtaCompute.beta)).trans
    (substitution heq hs hx Rx stage hΓ .zero hb R)

end Lean4Lean.VEnv.Strengthening
