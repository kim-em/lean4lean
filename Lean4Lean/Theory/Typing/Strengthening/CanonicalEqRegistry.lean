import Lean4Lean.Theory.Typing.Strengthening.IndexedPrefixBoundary
import Lean4Lean.Theory.VExpr.TelescopeLemmas

/-! # Canonical Eq's actual indexed recursor registration

The canonical pattern provides the real registry entry. Its index count follows
from the stored recursor type's result spine, independently of declaration names
or any separately assumed metadata.
-/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv}

/-- Every registration of canonical Eq.rec has precisely one index. The result
of its stored type applies the motive to the index and then the proof. -/
theorem RecursorRegistered.eqRec_numIndices (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec) :
    data.numIndices = 1 := by
  obtain ⟨type, ht⟩ := hr.recursorType_exists
  have hc := hr.recursorType ht
  rw [hn, heq.2.2.1] at hc
  have htype := congrArg VConstant.type (Option.some.inj hc)
  change canonicalEqRecType = type at htype
  obtain ⟨domains, motiveDomains, hs, _, _, _⟩ := RecursorData.recursorType_shape ht
  rw [← htype] at hs
  have hresult := congrArg VExpr.forallResult hs
  rw [VExpr.forallResult_wrapForalls, VExpr.mkApps_snoc] at hresult
  change (VExpr.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) =
    .app (mkApps _ (vars data.numIndices 1)) (.bvar 0) at hresult
  have hargs := congrArg (fun e => e.getAppFnArgs.2.length) hresult
  simp [← VExpr.mkApps_snoc, VerifyInductive.VExpr.getAppFnArgs_mkApps] at hargs
  omega

/-- Canonical Eq supplies its own registry entry, major offset, and nonzero
index count; callers need not postulate those separately. -/
theorem HasCanonicalEq.recursorRegistration (heq : env.HasCanonicalEq) (henv : env.WF) :
    ∃ data, env.recursorRegistry ``Eq.rec = some data ∧
      RecursorRegistered env data ∧ data.name = ``Eq.rec ∧
      data.majorOffset = 5 ∧ data.numIndices = 1 := by
  obtain ⟨doms, hc, _, hp⟩ := heq.2.2.2
  obtain ⟨data, hl, hr, hoff⟩ := henv.pat_recursorRegistry hp
  exact ⟨data, hl, hr.registered, hr.name_eq, hoff,
    hr.registered.eqRec_numIndices heq hr.name_eq⟩

namespace Strengthening.ConstructorObservation

/-- The added unindexed singleton equations cannot unfold canonical Eq.rec.
Its one index is forced by the installed type, even for alternate metadata. -/
theorem eqRec_no_unindexed_unfold (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ @ClosedSingleton.Unfolds (henv.params U) ``Eq.rec levels rhs := by
  intro h
  generalize hn : ``Eq.rec = name at h
  cases h with
  | intro hr _ _ _ _ _ hi =>
    have hn := hr.eqRec_numIndices heq hn.symm
    omega

/-- The stored-equation head model fails on canonical K computation without
additional registry or major-offset assumptions. -/
theorem canonical_cast_boundary_registered (henv : env.WF) (heq : env.HasCanonicalEq)
    (hu : u.WF U) (hΓ : OnCtx Γ (env.IsType U))
    (hX : env.HasType U Γ X (.sort u))
    (hq : env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X))
    (hpi : env.HasType U Γ (.forallE A B) X) :
    env.IsDefEq U Γ (typeCast u X X (.bvar i) (.forallE A B)) (.forallE A B) X ∧
      ¬ @EtaCompute (henv.params U) (PureObservation.Definitions.ofEnv env U henv)
        (typeCast u X X (.bvar i) (.forallE A B)) (.forallE A B) := by
  obtain ⟨_, hl, _, _, hoff, _⟩ := heq.recursorRegistration henv
  exact canonical_cast_boundary henv heq hl hoff hu hΓ hX hq hpi

/-- In every canonical-Eq environment the stored-equation model misses a typed
cast-to-Pi equation. The context and all argument typings are constructed here;
no additional existence, registration, or rigidity hypotheses are required. -/
theorem canonical_cast_counterexample (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) :
    ∃ Γ e A B T, OnCtx Γ (env.IsType U) ∧
      env.IsDefEq U Γ e (.forallE A B) T ∧
      ¬ @EtaCompute (henv.params U) (PureObservation.Definitions.ofEnv env U henv)
        e (.forallE A B) := by
  let u : VLevel := .succ (.succ .zero)
  let X : VExpr := .sort (.succ .zero)
  let Q := eqApp (.succ u) (.sort u) X X
  have hu : u.WF U := by trivial
  have hX {Γ} : env.HasType U Γ X (.sort u) := .sort (by trivial)
  have hQ : env.HasType U [] Q (.sort .zero) :=
    HasType.eqApp heq (by trivial) (.sort hu) hX hX
  have hΓ : OnCtx [Q] (env.IsType U) := ⟨trivial, _, hQ⟩
  have hq : env.HasType U [Q] (.bvar 0) Q := by
    have h : env.HasType U [Q] (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, X, eqApp, liftN] using h
  have hpi : env.HasType U [Q] (.forallE (.sort .zero) (.sort .zero)) X := by
    have ht : env.HasType U [Q] (.forallE (.sort .zero) (.sort .zero))
        (.sort (.imax (.succ .zero) (.succ .zero))) :=
      .forallE (.sort (by trivial)) (.sort (by trivial))
    exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq ht
  obtain ⟨he, hn⟩ := canonical_cast_boundary_registered henv heq hu hΓ hX hq hpi
  exact ⟨_, _, _, _, _, hΓ, he, hn⟩

end Strengthening.ConstructorObservation
end Lean4Lean.VEnv
