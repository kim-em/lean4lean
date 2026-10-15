import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralStructure

/-! # Carriers with unique inhabitants by structure and function eta

Empty registered structures and dependent function types into such carriers
support common-typed equality independently of endpoint syntax. The finite
shape certificate substitutes and descends; it makes no claim that arbitrary
definitional subsingletons are recognizable by this grammar.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

namespace ProofShape
/-- A structural certificate of unique inhabitants: empty structures, closed
under arbitrary dependent function domains. Parameters may depend on binders. -/
inductive SubsingletonCarrier : ProofShape → Prop where
  | unit (hi : env.projections family info) (hx : info.nindices = 0)
      (hf : info.numFields = 0) (hp : ps.length = info.nparams) :
      SubsingletonCarrier (mkApps (.const family ls) ps)
  | forallE : SubsingletonCarrier B → SubsingletonCarrier (.forallE A B)

/-- Substitution preserves both the static empty-family metadata and the
recursive codomain certificate beneath each dependent function binder. -/
theorem SubsingletonCarrier.subst (H : SubsingletonCarrier A) (σ : Subst) :
    SubsingletonCarrier (A.subst σ) := by
  induction H generalizing σ with
  | unit hi hx hf hp =>
    simp only [subst_mkApps, ProofShape.subst]
    exact .unit hi hx hf (by simpa only [List.length_map] using hp)
  | forallE H ih => exact .forallE (ih σ.lift)

/-- A literal universe is not structurally a subsingleton carrier. -/
theorem SubsingletonCarrier.not_sort (H : SubsingletonCarrier A) : A ≠ .sort u := by
  cases H with
  | unit =>
    intro E
    have HE := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HE
    cases HE
  | forallE => intro E; cases E
end ProofShape

/-- A lifted carrier shape alone suffices to compare arbitrary lower originals
at that type. Function eta is replayed at their shared domain and codomain;
no equality of endpoint annotations is needed or inferred. -/
theorem proofErase_subsingleton_carrier_descend
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : ProofShape.SubsingletonCarrier ((proofErase Γ T).liftN n k)) :
    env.IsDefEq univs Γ a b T := by
  generalize E : (proofErase Γ T).liftN n k = shape at H
  induction H generalizing Γ a b T k with
  | unit hi hx hf hp =>
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv E
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    have Hlen := congrArg List.length Eargs
    rw [Eoriginal] at Hlen
    exact IsDefEq.unitLike hi (by simpa only [List.length_map, hp] using Hlen.symm) hx hf ha hb
  | forallE H ih =>
    obtain ⟨_, _, ET, EA, EB⟩ := ProofShape.liftN_forallE_inv E
    obtain ⟨A, B, rfl, _, EA', EB'⟩ := erase_forallE_inv ET
    rw [← EB'] at EB
    obtain ⟨_, hT⟩ := ha.isType henv hΓ
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hfa : env.HasType univs (A :: Γ) (.app a.lift (.bvar 0)) B := by
      simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (ha.weak henv) (HasType.bvar .zero)
    have hfb : env.HasType univs (A :: Γ) (.app b.lift (.bvar 0)) B := by
      simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (hb.weak henv) (HasType.bvar .zero)
    have HI := ih hΓA hfa hfb EB
    exact (IsDefEq.eta ha).symm.trans ((IsDefEq.lamDF hA HI).trans (IsDefEq.eta hb))

end Lean4Lean.VEnv.Strengthening
