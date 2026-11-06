import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFrameProgress

/-! # Consume a syntactically unused target-prefix binder

Only the bounded raw prefix must be a lift. Its lower syntax needs no separate
typing or completion witness: insert the actual source domain backwards and
pull the existing constructed embedding through that exact round trip.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- The current top binder is absent from the target-relevant raw arguments.
Extra actual arguments are unrestricted, and no lower typing is required. -/
def UnusedEqPrefix (slots : Nat) (args : List ProofShape) : Prop :=
  ∃ lower : List ProofShape, args.take slots = lower.map (·.liftN 1)

open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

variable [Params]

/-- Equal bounded prefixes carry the same constructed completion. Additional
arguments may differ arbitrarily and need no target images. -/
theorem EqTargetPrefixEmbedding.prefix_congr
    (H : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (E : args.take original.length = args'.take original.length) :
    EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args') := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HP
  refine ⟨Θ, κ, WK, ?_⟩
  simp only [ProofShape.subst_mkApps, ProofShape.subst]
  refine ⟨ls, args'.map (·.subst κ), rfl, ?_⟩
  simpa only [← List.map_take, E] using HP.prefix

/-- Any typed source below a raw top binder supplies its actual domain sort.
No target assignment or proof-valued-domain premise is introduced. -/
theorem TypedSource.top_domain (HT : TypedSource (A :: Δ) e) : ∃ u, DomainSort Δ A u := by
  obtain ⟨Γ, f, F, hΓ, EΓ, _, _⟩ := HT
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    exact ⟨u, Γ, B, hΓ, EΓ, hB, EB⟩

/-- A raw unused bounded prefix survives consumption of any actual top
binder. Reinsert its domain, cancel instantiation on the literal lifted prefix,
and compose the old embedding. No inhabitant, lower source typing, lower
completion, or target-image equality for the supplied argument is needed. -/
theorem EqTargetPrefixEmbedding.consume_unused_prefix
    (H : EqTargetPrefixEmbedding Γ v w original (A :: Δ) (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (SD : DomainSort Δ A u) (HU : UnusedEqPrefix original.length args) (x : ProofShape) :
    EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.inst x))) := by
  obtain ⟨lower, EL⟩ := HU
  have Hprefix := H.prefix_congr (args' := args.take original.length)
    (by simp only [List.take_take, Nat.min_self])
  have W : ContextEmbedding Δ (A :: Δ) (fun i => .bvar (liftVar 1 i 0)) :=
    ContextEmbedding.insert .identity SD
  have ER : (ProofShape.mkApps (.const ``Eq.rec ls) ((args.map (·.inst x)).take original.length)).subst
        (fun i => .bvar (liftVar 1 i 0)) =
      ProofShape.mkApps (.const ``Eq.rec ls) (args.take original.length) := by
    simp only [ProofShape.subst_mkApps, ProofShape.subst, ← List.map_take, EL, List.map_map,
      Function.comp_def, ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]
    simp only [subst_bvar_liftN]
  have Hnext := (ER.symm ▸ Hprefix).pullback W
  exact Hnext.prefix_congr (args' := args.map (·.inst x)) (by simp only [List.take_take, Nat.min_self])

/-- A direct endpoint preserves completion unless it consumes a non-proof
binder that is actually used in the bounded raw prefix. The unused case comes
from the exact source domain and reverse embedding, rather than a lower
completion assumption. -/
theorem EqTargetPrefixEmbedding.direct_endpoint_or_used
    {D : Definitions} (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (W : PiInertEndpointMap Δ Θ τ) :
    EqTargetPrefixEmbedding Γ v w original Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ))) ∨
      ∃ A x, Δ = A :: Θ ∧ τ = ProofShape.Subst.one x ∧
        ¬ DomainSort Θ A .zero ∧ ¬ UnusedEqPrefix original.length args := by
  classical
  cases W with
  | identity => exact .inl (by simpa only [ProofShape.subst_id, List.map_id_fun', id_eq] using H)
  | @inst A _ x WI =>
    by_cases HU : UnusedEqPrefix original.length args
    · obtain ⟨u, SD⟩ := TypedSource.top_domain HT
      exact .inl (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        H.consume_unused_prefix SD HU x)
    · by_cases SD : DomainSort Θ A .zero
      · have Hnext := H.proof_endpoint heq hs hΓ HT (.inst SD WI)
        exact .inl (by simpa only [ProofShape.subst_mkApps, ProofShape.subst] using Hnext)
      · exact .inr ⟨A, x, rfl, rfl, SD, HU⟩

end Lean4Lean.VEnv.Strengthening
