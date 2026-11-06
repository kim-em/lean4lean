import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelLoopReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureQuotCoreCastBoundary
import Lean4Lean.Theory.Typing.Strengthening.RecursiveTypeInhabitants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage

/-! # Sort-valued recursive substitution fails in the full level core

A typed single substitution turns common diagonal arguments under a neutral
function into proposition-valued loops. Loop readout would force comparison
of a recursive Pi and its free-major Eq cast. Universe conversion and all
optional quotient programs still cannot expose a Pi from that cast. The actual
canonical-Eq extension separately satisfies PropositionFront, so this refutes
the certificate closure law, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_diagonal from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecursiveCoverage
variable [Params] {Defs : Definitions}

/-- Proposed recursive inferred-certificate closure restricted to two actually
sort-typed sources and a genuine typed single instantiation. This property is
refuted below for the actual universe-extended environment core. -/
def TypedSortRecursiveInstantiationClosure (D : Definitions) : Prop :=
  ∀ {Γ A b c u p}, OnCtx (A :: Γ) (env.IsType univs) →
    env.HasType univs (A :: Γ) b (.sort u) → env.HasType univs (A :: Γ) c (.sort u) →
    env.HasType univs Γ p A →
    LevelRecursiveGuard D false (proofErase (A :: Γ) b) (proofErase (A :: Γ) c) →
    LevelRecursiveGuard D false (proofErase Γ (b.inst p)) (proofErase Γ (c.inst p))

private theorem neutral_diagonals (A B : ProofShape) :
    LevelRecursiveGuard Defs false (.app (.bvar 0) (diagonal A)) (.app (.bvar 0) (diagonal B)) := by
  have HV : LevelRecursiveGuard Defs true (.bvar 0) (.bvar 0) :=
    .neutral (args := []) (args' := []) rfl (by intro i hi; simp at hi)
  have HB : LevelRecursiveGuard Defs true (.app (.bvar 0) (.bvar 0)) (.app (.bvar 0) (.bvar 0)) :=
    .neutral (args := [.bvar 0]) (args' := [.bvar 0]) rfl (by
      intro i hi; have : i = 0 := by simp only [List.length_singleton] at hi; omega
      subst i; exact HV)
  exact .neutral (args := [diagonal A]) (args' := [diagonal B]) rfl (by
    intro i hi; have : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i; exact .lamCommon HB)

/-- Sort-only closure would construct inferred recursive guards between loops
at every two convertible recursive carriers. The neutral source applications
are actual propositions; their shared substitution image is an actual diagonal.
No certificate comparing the carrier annotations occurs in the input. -/
theorem TypedSortRecursiveInstantiationClosure.recursive_loops
    (H : TypedSortRecursiveInstantiationClosure Defs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u))
    (HD : env.IsDefEq univs Γ D D' (.sort u)) :
    LevelRecursiveGuard Defs false (selfLoop (proofErase Γ D)) (selfLoop (proofErase Γ D')) := by
  have hD := Hrec.hasType.1
  have hD' := HD.hasType.2
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hv : env.HasType univs (D :: Γ) (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  have hb : env.HasType univs (D :: Γ) RecursiveDomain.selfBody (.sort .zero) := hf.app hv
  have hb' : env.HasType univs (D' :: Γ) RecursiveDomain.selfBody (.sort .zero) :=
    hb.defeqDFC henv (.succ .zero HD)
  have Hdiag := IsDefEq.lamDF HD hb
  have hx : env.HasType univs Γ (RecursiveDomain.diagonal D) D := Hrec.symm.defeq Hdiag.hasType.1
  have hy : env.HasType univs Γ (RecursiveDomain.diagonal D') D := Hrec.symm.defeq Hdiag.hasType.2
  have EX := erase_diagonal hΓ hD hb
  have EY := erase_diagonal hΓ hD' hb'
  let F := VExpr.forallE D (.sort .zero)
  have hp : env.HasType univs Γ (RecursiveDomain.diagonal D) F := Hdiag.hasType.1
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, hp.isType henv hΓ⟩
  have hfun : env.HasType univs (F :: Γ) (.bvar 0) F.lift := .bvar .zero
  have hleft : env.HasType univs (F :: Γ)
      (.app (.bvar 0) (RecursiveDomain.diagonal D).lift) (.sort .zero) := hfun.app (hx.weak henv)
  have hright : env.HasType univs (F :: Γ)
      (.app (.bvar 0) (RecursiveDomain.diagonal D').lift) (.sort .zero) := hfun.app (hy.weak henv)
  have hnfun := not_isProof_fn hΓF hfun (hx.weak henv) (not_isProof_of_sort hΓF hleft)
  have EL : proofErase (F :: Γ) (.app (.bvar 0) (RecursiveDomain.diagonal D).lift) =
      .app (.bvar 0) (diagonal ((proofErase Γ D).liftN 1)) := by
    rw [show proofErase (F :: Γ) (.app (.bvar 0) (RecursiveDomain.diagonal D).lift) = .app _ _ from
      if_neg (not_isProof_of_sort hΓF hleft),
      show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from if_neg hnfun,
      show proofErase (F :: Γ) (RecursiveDomain.diagonal D).lift =
        (proofErase Γ (RecursiveDomain.diagonal D)).liftN 1 from proofErase_liftN hΓ hΓF Ctx.LiftN.one hx, EX]
    rfl
  have ER : proofErase (F :: Γ) (.app (.bvar 0) (RecursiveDomain.diagonal D').lift) =
      .app (.bvar 0) (diagonal ((proofErase Γ D').liftN 1)) := by
    rw [show proofErase (F :: Γ) (.app (.bvar 0) (RecursiveDomain.diagonal D').lift) = .app _ _ from
      if_neg (not_isProof_of_sort hΓF hright),
      show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from if_neg hnfun,
      show proofErase (F :: Γ) (RecursiveDomain.diagonal D').lift =
        (proofErase Γ (RecursiveDomain.diagonal D')).liftN 1 from proofErase_liftN hΓ hΓF Ctx.LiftN.one hy, EY]
    rfl
  have HG := H hΓF hleft hright hp (EL.symm ▸ ER.symm ▸ neutral_diagonals _ _)
  simp only [VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte, VExpr.liftN_zero, VExpr.inst_lift] at HG
  have htL : env.HasType univs Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D)) (.sort .zero) := hp.app hx
  have htR : env.HasType univs Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D')) (.sort .zero) := hp.app hy
  rw [show proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D)) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ htL),
    show proofErase Γ (.app (RecursiveDomain.diagonal D) (RecursiveDomain.diagonal D')) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ htR), EX, EY] at HG
  apply HG.reducts .refl
  exact .beta (by simpa [diagonal, selfLoop, ProofShape.inst, ProofShape.liftN_zero] using
    (ProofShape.BetaRed.beta (A := proofErase Γ D) (b := .app (.bvar 0) (.bvar 0))
      (a := diagonal (proofErase Γ D'))))

/-- Proposition-valued substitution already forces full-core inferred
comparison of every conversion out of a recursive carrier. -/
theorem TypedSortRecursiveInstantiationClosure.recursive_type_coverage
    (hs : Defs.Sound env univs) (hl : Defs.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore Defs))
    (H : TypedSortRecursiveInstantiationClosure Defs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (.sort .zero)) (.sort u))
    (HD : env.IsDefEq univs Γ D D' (.sort u)) :
    RawCheckedCompare (ErasedLevelCore Defs) false (proofErase Γ D) (proofErase Γ D') :=
  ((H.recursive_loops hΓ Hrec HD).forward hs hl hcon hc .refl .refl).level_selfLoop_annotations

namespace EnvironmentCore

omit [Params] in
/-- Full universe-core computation cannot expose a Pi from the canonical
reflexive cast with a free equality major. Typed factorization reduces the
question to the existing ordinary-core boundary, including optional Quot rules. -/
theorem level_cast_no_pi {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ X i A B A' B'}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ (.forallE A B) X →
      ProofShape.Compute (ErasedLevelCore definitions)
        (proofErase Γ (typeCast u X X (.bvar i) (.forallE A B))) (.forallE A' B') → False := by
  letI := henv.params U
  intro u Γ X i A B A' B' heq hu hΓ hX hq hpi R
  have hcon : ∀ {p r}, Pat p r → ConcretePattern env p r := fun H => H
  have HT := IsDefEq.typeCast_refl henv heq hu hΓ hX hq hpi
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return sound (levelCompatible hcon) hcon hΓ HT.hasType.1 R
  obtain ⟨C, E, rfl, _, _⟩ := RT.pi_parts (fun H => erased_level_core_no_pi H)
  classical
  by_cases hquot : QuotRegistered env
  · rw [definitions_of_quot hquot] at RM
    exact ErasedQuotCore.cast_no_pi henv univs hquot heq hu hΓ hX hq hpi (RM.scoped (fun H => .base H))
  · rw [definitions_of_no_quot hquot] at RM
    exact ErasedCore.cast_no_pi henv univs heq hu hΓ hX hq hpi (RM.scoped (fun H => .base H))

omit [Params] in
/-- A recursive Pi and free reflexive equality major refute genuine typed
single-instantiation closure even with proposition-valued source and result
terms. All ordinary and universe computations in the total core are included. -/
theorem not_sort_recursive_instantiation_of_recursive_pi {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u v Γ i A B}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.IsDefEq U Γ (.forallE A B) (.forallE (.forallE A B) (.sort .zero)) (.sort v) →
      ¬ TypedSortRecursiveInstantiationClosure definitions := by
  letI := henv.params U
  intro u v Γ i A B heq hu hΓ hX hq Hrec H
  have hcon : ∀ {p r}, Pat p r → ConcretePattern env p r := fun H => H
  have HD := IsDefEq.typeCast_refl henv heq hu hΓ hX hq Hrec.hasType.1
  have HC := H.recursive_type_coverage sound (levelCompatible hcon) hcon (typed_level_core_confluence hcon)
    hΓ Hrec HD.symm
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ Hrec.hasType.1)] at HC
  obtain ⟨A', B', R⟩ := HC.level_pi_exposure
  exact level_cast_no_pi henv U heq hu hΓ hX hq Hrec.hasType.1 R

omit [Params] in
/-- The actual recursive declaration supplies a recursive Pi in a well-formed
context with a free reflexive equality proof. -/
theorem not_sort_recursive_instantiation_recursive {env : VEnv} (henv : env.WF) (U : Nat) (heq : env.HasCanonicalEq)
    (hδ : ∀ Γ, env.IsDefEq U Γ (.const c []) (RecursiveDomain.familyValue c)
      RecursiveDomain.familyType) :
    letI := henv.params U
    ¬ TypedSortRecursiveInstantiationClosure definitions := by
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
  exact not_sort_recursive_instantiation_of_recursive_pi henv U heq hu hΓ hX hq HP'

end EnvironmentCore

omit [Params] in
/-- The canonical-Eq recursive extension satisfies PropositionFront while
refuting sort-valued recursive certificate closure for its full level core.
This is a counterexample to the proposed certificate law, not to strengthening. -/
theorem canonical_sort_recursive_instantiation_failure
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) :
    (RecursiveDomain.extended base c).HasCanonicalEq ∧
    letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
    PropositionFront ∧ ¬ TypedSortRecursiveInstantiationClosure EnvironmentCore.definitions := by
  have heq' := RecursiveDomain.extended_canonicalEq heq hfresh
  refine ⟨heq', ?_⟩
  letI := (RecursiveDomain.extended_wf hbase hfresh).params 0
  refine ⟨canonical_recursiveDomain_front hbase heq hfresh, ?_⟩
  exact EnvironmentCore.not_sort_recursive_instantiation_recursive
    (RecursiveDomain.extended_wf hbase hfresh) 0 heq' (fun Γ => RecursiveDomain.equation 0 Γ)

end Lean4Lean.VEnv.Strengthening
