import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-! # Rigid constant heads exclude scoped prefix primitives -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private theorem erased_match_not_rigid (hc : env.Rigid c)
    (hp : Pat p r) (hm : ProofShape.Matches p a ls captures)
    (hh : a.constHead = some c) : False :=
  hc.not_patternHeadsStoredRule (pat_storedRule hp) (hm.constHead.symm.trans hh)

/-- A rigid head with no selected delta equation cannot head any ordinary
erased primitive. Pattern exclusion uses actual stored-rule provenance. -/
theorem erased_iota_primitive_no_rigid (hc : env.Rigid c)
    (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (R : ErasedIotaPrimitive D a b) (hh : a.constHead = some c) : False := by
  rcases R with (R | R) | R
  · cases R with
    | delta H => cases Option.some.inj hh; exact hD _ _ H
    | projIota => cases hh
  · cases R with
    | select hp _ hm => exact erased_match_not_rigid hc hp hm hh
    | apply hp _ hm => exact erased_match_not_rigid hc hp hm hh
  · cases R with
    | intro hp _ _ hm => exact erased_match_not_rigid hc hp hm hh

/-- Canonical Eq.rec heads its installed rule, so a rigid head also excludes
every finite scoped K-prefix stage, independently of the endpoint guard. -/
theorem erased_scoped_prefix_stage_no_rigid (heq : env.HasCanonicalEq)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∀ stage {Δ a b}, ErasedScopedPrefixStage D stage Δ a b → a.constHead = some c → False := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_no_rigid hc hD
  | succ stage ih =>
    intro Δ a b H hh
    rcases H with H | H
    · exact ih H hh
    · cases H with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj hh)

/-- Registered constructor spines retain their head, universes and number of
arguments through arbitrary finite scoped prefix computation. -/
theorem proofErase_scoped_prefix_constructor_inv (heq : env.HasCanonicalEq)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (R : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ
      (ProofShape.mkApps (.const info.ctorName ls) args) out) :
    ∃ args', out = ProofShape.mkApps (.const info.ctorName ls) args' ∧
      List.Forall₂ (ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ) args args' := by
  apply R.const_spine
  intro Δ args out H
  exact erased_scoped_prefix_stage_no_rigid heq (henv.projectionCtorRigid hi) hD stage H
    (ProofShape.constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
