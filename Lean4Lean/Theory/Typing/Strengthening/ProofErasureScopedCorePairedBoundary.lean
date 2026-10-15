import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreHeadBoundary

/-! # Full ordinary core does not support common paired instantiation

A recursive Pi domain and its reflexive cast along a free equality proof are
convertible by canonical Eq. Common lambda checking hides that conversion.
Paired instantiation would reveal it in self-application, forcing a core Pi
exposure that the checked cast boundary forbids.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
namespace ScopedCorePairedBoundary

/-- A recursive Pi together with a free reflexive equality proof refutes paired
instantiation for the actual ordinary core. The obstruction concerns a closure
law of scoped certificates, not strengthening of declarative equality. -/
theorem not_paired_of_recursive_pi {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ A B u v i}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.IsDefEq U Γ (.forallE A B) (.forallE (.forallE A B) (.sort .zero)) (.sort v) →
      ¬ ScopedPairedInstantiation (fun _ => ErasedCore.Step) := by
  letI := henv.params U
  intro Γ A B u v i heq hu hΓ hX hq Hrec Hinst
  have hs : ErasedCore.definitions.Sound env U :=
    RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedCore.Step) :=
    ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  have hhead : ∀ {Δ : List ProofShape} {a b}, (fun _ => ErasedCore.Step) Δ a b → PrimitiveHead a :=
    fun H => erased_iota_primitive_head H
  have HD := IsDefEq.typeCast_refl henv heq hu hΓ hX hq Hrec.hasType.1
  have HC := Hinst.recursive_type_coverage @hhead hΓ Hrec HD.symm
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ Hrec.hasType.1)
  obtain ⟨A', B', R⟩ := proofErase_scoped_pi_exposure hstep @hhead hΓ Hrec.hasType.1 HD.hasType.1 HC EP
  exact ErasedCore.cast_no_pi henv U heq hu hΓ hX hq Hrec.hasType.1 R

/-- The installed recursive family supplies the recursive Pi needed by the
cast obstruction. All contexts and casts are typed in the original calculus;
ordinary core includes the family's actual unfolding equation. -/
theorem not_paired_recursive {env : VEnv} (henv : env.WF) (U : Nat) (heq : env.HasCanonicalEq)
    (hδ : ∀ Γ, env.IsDefEq U Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) :
    letI := henv.params U
    ¬ ScopedPairedInstantiation (fun _ => ErasedCore.Step) := by
  letI := henv.params U
  have Hrec := RecursiveDomain.domain_recursive hδ
  let D := RecursiveDomain.domainL c
  let P := VExpr.forallE D (.sort .zero)
  have HP : env.IsDefEq U RecursiveDomain.loopCtx P (.forallE P (.sort .zero))
      (.sort (.succ .zero)) := by
    have H := IsDefEq.forallEDF Hrec (HasType.sort (env := env) (l := .zero) (by trivial))
    exact IsDefEq.defeqDF (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self) H
  let u : VLevel := .succ (.succ .zero)
  let X : VExpr := .sort (.succ .zero)
  let Q := eqApp (.succ u) (.sort u) X X
  have hu : u.WF U := by trivial
  have hX {Γ} : env.HasType U Γ X (.sort u) := .sort (by trivial)
  have hQ : env.HasType U RecursiveDomain.loopCtx Q (.sort .zero) :=
    HasType.eqApp heq (by trivial) (.sort hu) hX hX
  have hbase : OnCtx RecursiveDomain.loopCtx (env.IsType U) :=
    ⟨trivial, _, RecursiveDomain.argType_typed env U []⟩
  have hΓ : OnCtx (Q :: RecursiveDomain.loopCtx) (env.IsType U) := ⟨hbase, _, hQ⟩
  have hq : env.HasType U (Q :: RecursiveDomain.loopCtx) (.bvar 0) Q := by
    have H : env.HasType U (Q :: RecursiveDomain.loopCtx) (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, X, eqApp, VExpr.liftN] using H
  have HP' : env.IsDefEq U (Q :: RecursiveDomain.loopCtx)
      (.forallE D.lift (.sort .zero))
      (.forallE (.forallE D.lift (.sort .zero)) (.sort .zero)) X := by
    exact HP.weakN henv Ctx.LiftN.one
  exact not_paired_of_recursive_pi henv U heq hu hΓ hX hq HP'

/-- A well-formed extension preserving canonical Eq refutes common paired
instantiation for its full ordinary core, not only for beta computation. No
installed equation is omitted from the tested core relation. -/
theorem canonical_core_paired_failure (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    (RecursiveDomain.extended base c).HasCanonicalEq ∧
    letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
    ¬ ScopedPairedInstantiation (fun _ => ErasedCore.Step) := by
  have heq' := RecursiveDomain.extended_canonicalEq heq hfresh
  refine ⟨heq', ?_⟩
  apply not_paired_recursive (RecursiveDomain.extended_wf hbase hfresh) 0 heq' (c := c)
  exact fun Γ => RecursiveDomain.equation 0 Γ

end ScopedCorePairedBoundary
end Lean4Lean.VEnv.Strengthening
