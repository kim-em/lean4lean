import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFullPrefixReadout

/-! # Completion up to the original Eq target length

Extra arguments, including the proof major, need no target inhabitants.
Completion is retained for the initial segment of the actual spine bounded by
the original target vector. This invariant opens eta both before and after
that vector is exhausted, and survives actual annotation changes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

/-- The actual Eq spine retains target completion up to the original vector's
length. Additional actual arguments are permitted without requiring their
images in the target context. Typing of the full spine, when needed, comes
from the actual execution rather than this prefix-only invariant. -/
def EqTargetPrefixCompletion (Δ : List VExpr) (v w : VLevel) (original : List VExpr)
    (Ξ : List ProofShape) (source : ProofShape) : Prop :=
  ∃ ls args, source = ProofShape.mkApps (.const ``Eq.rec ls) args ∧
    IteratedAmbientEqCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args.take original.length))

/-- A fully completed short source supplies the target-prefix invariant.
The required length bound is already a consequence of completion. -/
theorem EqTargetPrefixCompletion.of_completion
    (H : IteratedAmbientEqCompletion Δ v w original Ξ source) :
    EqTargetPrefixCompletion Δ v w original Ξ source := by
  obtain ⟨ls, args, E, hlen⟩ := H.arity
  exact ⟨ls, args, E, by simpa only [List.take_of_length_le hlen, ← E] using H⟩

/-- At a displayed constant spine, the invariant recovers exactly its bounded
initial segment; the existential presentation does not permit a different head
or argument vector. -/
theorem EqTargetPrefixCompletion.prefix
    (H : EqTargetPrefixCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args)) :
    IteratedAmbientEqCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args.take original.length)) := by
  obtain ⟨ls', args', E, H⟩ := H
  obtain ⟨_, rfl, rfl⟩ := ProofShape.const_spine_inj E
  exact H

/-- Computing all actual components and selecting a source prefix preserves
completion up to the target length, including when additional proof-major or
later arguments are present. -/
theorem EqTargetPrefixCompletion.compute_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqTargetPrefixCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HL : List.Forall₂ (· ≈ ·) ls ls') (HW : ∀ l ∈ ls', l.WF univs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) Ξ) args args') (arity : Nat) :
    EqTargetPrefixCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls') (args'.take arity)) := by
  have HH := H.prefix.compute_components heq hs hΔ HL HW
    (Lean4Lean.List.forall₂_take HA original.length) arity
  exact ⟨ls', args'.take arity, rfl, by simpa only [List.take_take, Nat.min_comm] using HH⟩

/-- A computed annotation change preserves the bounded target prefix even
when the full source extends beyond the target vector. -/
theorem EqTargetPrefixCompletion.compute_annotation
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqTargetPrefixCompletion Δ v w original (A :: Ξ) source)
    (RD : ScopedCompute Step Ξ A A') :
    EqTargetPrefixCompletion Δ v w original (A' :: Ξ) source := by
  obtain ⟨ls, args, E, HP⟩ := H
  exact ⟨ls, args, E, HP.compute_annotation hstep hΔ RD⟩

/-- Native eta opening preserves the same prefix invariant at every arity.
Before the target vector is full, the actual recovered eta binder supplies
its next target argument. At or beyond that length, only the already completed
prefix is lifted under the unused binder; the fresh argument has no target
assignment and requires no target inhabitant. -/
theorem EqTargetPrefixCompletion.eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqTargetPrefixCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B))
    (SD : DomainSort Ξ A u) :
    EqTargetPrefixCompletion Δ v w original (A :: Ξ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
  by_cases hlen : args.length < original.length
  · have HP : IteratedAmbientEqCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) := by
      simpa only [List.take_of_length_le (Nat.le_of_lt hlen)] using H.prefix
    exact .of_completion (HP.eta heq hs hΔ ht hlen RN SD)
  · have hlen : original.length ≤ args.length := by omega
    have HH := H.prefix.under_domain SD
    refine ⟨ls, args.map (·.liftN 1) ++ [etaArgument u], ?_, ?_⟩
    · simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append, ProofShape.mkApps]
    · have hmap : original.length ≤ (args.map (·.liftN 1)).length := by simpa only [List.length_map] using hlen
      simpa only [List.take_append_of_le_length hmap, ← List.map_take,
        ProofShape.liftN_mkApps, ProofShape.liftN] using HH

/-- A nonstructural head-losing root reads the original equation from this
prefix invariant. Canonical typing first bounds that root by five arguments,
so its retained prefix is the entire root. No completion of extra arguments
is needed. -/
theorem EqTargetPrefixCompletion.read_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqTargetPrefixCompletion Δ v w [α,a,M,minor,b] Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HT : TypedSource Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HR : PiInertStage D n Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    env.IsDefEq univs Δ a b α := by
  have hlen := (typed_nonstructural_eq_head_loss_singleton heq hreg hoff hRec HT HR HN Hstruct).1
  have HP : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) := by
    simpa only [List.length_cons, List.length_nil, List.take_of_length_le hlen] using H.prefix
  exact HP.read_loss heq hs hreg hoff hRec hΔ ht HR HN

end Lean4Lean.VEnv.Strengthening
