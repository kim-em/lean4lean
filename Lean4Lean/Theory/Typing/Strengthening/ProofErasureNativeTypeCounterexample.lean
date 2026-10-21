import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTypeBoundary

/-! # A well-formed observer extension refutes same-core native type congruence

The observer is installed as an ordinary axiom with a checked closed type.
Canonical Eq and quotient registration persist. The recursive domain already
makes proposition strengthening hold, so failure concerns the proposed
certificate closure law rather than canonical-Eq strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeLoopObserver
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable {base : VEnv}

private def declaration (c : Name) (D : VExpr) : VConstVal where
  name := c
  uvars := 0
  type := nativeLoopObserverType D

/-- Install the observer constant without adding any reduction equations. -/
def extended (base : VEnv) (c : Name) (D : VExpr) : VEnv :=
  { base with constants := fun n => if c = n then some (declaration c D).toVConstant else base.constants n }

private theorem observer_type (henv : base.WF)
    (Hrec : base.IsDefEq 0 [] D (.forallE D (.sort .zero)) (.sort u)) :
    base.IsType 0 [] (nativeLoopObserverType D) := by
  have hv : base.HasType 0 [D] (.bvar 0) D.lift := .bvar .zero
  have hf := (Hrec.weakN henv Ctx.LiftN.one).defeq hv
  have hb : base.HasType 0 [D] RecursiveDomain.selfBody (.sort .zero) := hf.app hv
  exact ⟨_, HasType.forallE Hrec.hasType.1 (HasType.forallE hb (HasType.sort (by trivial)))⟩

private theorem declaration_wf (henv : base.WF)
    (Hrec : base.IsDefEq 0 [] D (.forallE D (.sort .zero)) (.sort u))
    (hfresh : base.constants c = none) :
    VDecl.WF base (.axiom (declaration c D)) (extended base c D) := by
  apply VDecl.WF.axiom (ci := declaration c D)
  · exact observer_type henv Hrec
  · simp [VEnv.addConst, declaration, hfresh, extended]
    rfl

/-- The observer extension is a genuine well-formed environment. -/
theorem extended_wf (henv : base.WF)
    (Hrec : base.IsDefEq 0 [] D (.forallE D (.sort .zero)) (.sort u))
    (hfresh : base.constants c = none) : (extended base c D).WF := by
  obtain ⟨ds, hds⟩ := henv
  exact ⟨_, .decl (declaration_wf ⟨ds, hds⟩ Hrec hfresh) hds⟩

/-- Every declaration and equation of the original environment is retained. -/
theorem extended_le (henv : base.WF)
    (Hrec : base.IsDefEq 0 [] D (.forallE D (.sort .zero)) (.sort u))
    (hfresh : base.constants c = none) : base ≤ extended base c D :=
  (declaration_wf henv Hrec hfresh).le

/-- In a concrete observer extension, native type congruence into the repaired
ordinary core fails even though canonical Eq and PropositionFront hold. The
source relation is arbitrary: the witnessing prefix comparison uses no
primitive computation. The input recursive domain must be a closed literal Pi. -/
theorem canonical_core_failure
    (henv : base.WF) (heq : base.HasCanonicalEq) (hquot : QuotRegistered base)
    (Hrec : base.IsDefEq 0 [] (.forallE A B)
      (.forallE (.forallE A B) (.sort .zero)) (.sort u))
    (hfresh : base.constants c = none) :
    let henv' := extended_wf henv Hrec hfresh
    let hquot' := hquot.mono (extended_le henv Hrec hfresh)
    letI := henv'.params 0
    (extended base c (.forallE A B)).HasCanonicalEq ∧ PropositionFront ∧
      ¬ JointNativePrefixTypeComparison Source (fun _ => ErasedQuotCore.Step hquot') := by
  let henv' := extended_wf henv Hrec hfresh
  letI := henv'.params 0
  have hle := extended_le henv Hrec hfresh
  have heq' := heq.mono hle
  have hquot' := hquot.mono hle
  have Hrec' := Hrec.mono hle
  refine ⟨heq', RecursiveType.propositionFront heq' (fun Γ _ => Hrec'.weak0 henv'.ordered), ?_⟩
  have hu : u.WF 0 := Hrec'.hasType.1.sort_r henv' (by trivial)
  let Q := eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)
  have hQ : (extended base c (.forallE A B)).HasType 0 [] Q (.sort .zero) :=
    HasType.eqApp heq' hu (HasType.sort hu) (HasType.sort hu) (HasType.sort hu)
  have hΓ : OnCtx [Q] ((extended base c (.forallE A B)).IsType 0) := ⟨by trivial, _, hQ⟩
  have hq : (extended base c (.forallE A B)).HasType 0 [Q] (.bvar 0) Q := by
    have H : (extended base c (.forallE A B)).HasType 0 [Q] (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, eqApp, VExpr.liftN] using H
  have hc : (extended base c (.forallE A B)).constants c =
      some (declaration c (.forallE A B)).toVConstant := by simp [extended]
  obtain ⟨_, hT⟩ := observer_type henv' Hrec'
  have hdecl : ((declaration c (.forallE A B)).toVConstant.type).instL [] =
      nativeLoopObserverType (.forallE A B) := by
    simpa [declaration, VLevel.params] using (hT.levelWF (by trivial)).1.instL_id
  exact JointNativePrefixTypeComparison.not_core_of_recursive_pi henv' 0 hquot'
    heq' (show (VLevel.succ u).WF 0 from hu) hΓ hc (by simp) rfl hdecl (HasType.sort hu) hq (Hrec'.weak0 henv'.ordered)

/-- A closed literal Pi obtained from the existing negative recursive family. -/
def domain (r : Name) : VExpr :=
  .forallE (.app (.const r []) (.lam (.sort .zero) (.bvar 0))) (.sort .zero)

private theorem domain_recursive (henv : base.WF) (hfresh : base.constants r = none) :
    (RecursiveDomain.extended base r).IsDefEq 0 [] (domain r)
      (.forallE (domain r) (.sort .zero)) (.sort (.succ .zero)) := by
  have henv' := RecursiveDomain.extended_wf henv hfresh
  let arg := VExpr.lam (.sort .zero) (.bvar 0)
  have harg : (RecursiveDomain.extended base r).HasType 0 [] arg RecursiveDomain.argType :=
    HasType.lam (HasType.sort (by trivial)) (HasType.bvar .zero)
  have H := IsDefEq.appDF (RecursiveDomain.equation (base := base) (c := r) 0 []) harg
  have HB := BetaRed.simAt (env := RecursiveDomain.extended base r)
    henv'.orderedStrong henv'.betaSubjectReduction
    (BetaRed.beta (A := RecursiveDomain.argType)
      (b := .forallE (.app (.const r []) (.bvar 0)) (.sort .zero)) (a := arg))
    (by trivial) _ H.hasType.2
  have HR : (RecursiveDomain.extended base r).IsDefEq 0 [] (.app (.const r []) arg)
      (.forallE (.app (.const r []) arg) (.sort .zero)) (.sort (.succ .zero)) := by
    simpa [RecursiveDomain.familyValue, VExpr.inst, instVar] using H.trans HB
  have HP := IsDefEq.forallEDF HR (HasType.sort (env := RecursiveDomain.extended base r)
    (l := .zero) (by trivial))
  exact IsDefEq.defeqDF (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self) HP

/-- Two actual fresh declarations over any canonical-Eq quotient environment
produce a well-formed counterexample to same-core native type congruence.
The recursive family and observer are both checked, and the resulting
environment still has PropositionFront. This is not a strengthening counterexample. -/
theorem canonical_recursive_extension_failure
    (henv : base.WF) (heq : base.HasCanonicalEq) (hquot : QuotRegistered base)
    (hfreshR : base.constants r = none)
    (hfreshC : (RecursiveDomain.extended base r).constants c = none) :
    let henvR := RecursiveDomain.extended_wf henv hfreshR
    let HR := domain_recursive henv hfreshR
    let henv' := extended_wf henvR HR hfreshC
    let hquotR := hquot.mono (RecursiveDomain.extended_le hfreshR)
    let hquot' := hquotR.mono (extended_le henvR HR hfreshC)
    letI := henv'.params 0
    (extended (RecursiveDomain.extended base r) c (domain r)).HasCanonicalEq ∧
      PropositionFront ∧
      ¬ JointNativePrefixTypeComparison (fun _ => ErasedQuotCore.Step hquot')
        (fun _ => ErasedQuotCore.Step hquot') := by
  exact canonical_core_failure (RecursiveDomain.extended_wf henv hfreshR)
    (heq.mono (RecursiveDomain.extended_le hfreshR))
    (hquot.mono (RecursiveDomain.extended_le hfreshR)) (domain_recursive henv hfreshR) hfreshC

end Lean4Lean.VEnv.Strengthening.NativeLoopObserver
