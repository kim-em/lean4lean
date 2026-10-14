import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary
import Lean4Lean.Theory.Typing.Strengthening.SingletonIndexAlignmentBoundary
import Lean4Lean.Theory.Typing.Confluence.PatternConstructorRigidity
import Lean4Lean.Theory.Typing.FullReduction

/-! # The exact boundary of exposing an equality constructor

Canonical Eq's family rigidity follows from the provenance of its registered
recursor pattern. Any Eq.refl at a requested equality type forces conversion of
the requested endpoints, regardless of the constructor's supplied carrier,
universe, or endpoint. Thus changing a major by conversion, or by an arbitrary
full reduction, cannot expose a constructor at nonconvertible endpoints.
-/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Canonical Eq is rigid in every well-formed environment: its registered
recursor constructor returns Eq, whose head is rigid by declaration provenance. -/
theorem HasCanonicalEq.rigid (heq : env.HasCanonicalEq) (henv : env.WF) : env.Rigid ``Eq := by
  obtain ⟨doms, hc, _, hp⟩ := heq.2.2.2
  have hctor : IsPatCtor env ``Eq.refl := ⟨canonicalEqRecPattern,
    (canonicalEqRecRHS doms hc, .true), ``Eq.rec, 5, 2, hp, rfl⟩
  obtain ⟨ci, hci, F, ls, hF, _, hr⟩ := henv.patCtor_resultRigid hctor
  rw [heq.2.1] at hci
  cases Option.some.inj hci
  change VExpr.const ``Eq [.param 0] = .const F ls at hF
  obtain ⟨rfl, _⟩ := VExpr.const.inj hF
  exact hr

namespace Strengthening

/-- Invert the two canonical constructor arguments at any typing of Eq.refl. -/
theorem eqReflApp_typings (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : VExpr.WF env U Γ (eqReflApp w α a)) :
    w.WF U ∧ env.HasType U Γ α (.sort w) ∧ env.HasType U Γ a α := by
  have H' : VExpr.WF env U Γ (mkApps (.const ``Eq.refl [w]) [α, a]) := H
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ H'
  obtain ⟨ci, hci, hw, _⟩ := HasType.const_inv henv hΓ hc
  rw [heq.2.1] at hci
  cases Option.some.inj hci
  have hhead := HasType.const (Γ := Γ) heq.2.1 hw (by rfl)
  obtain ⟨res, ht, _⟩ := HasType.mkApps_telescope henv hΓ hhead H' (by rfl)
  cases ht with | cons hα ht =>
  cases ht with | cons ha ht =>
  cases ht
  refine ⟨hw _ (by simp), ?_⟩
  simpa [instL, VLevel.inst, inst, instVar, liftN] using And.intro hα ha

/-- Any reflexivity constructor typed at Eq α a b forces a and b to convert.
The constructor's own carrier, universe and endpoint need not match syntactically. -/
theorem eqRefl_typed_endpoint_conversion (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : env.HasType U Γ (eqReflApp w' α' a') (eqApp w α a b)) :
    env.IsDefEqU U Γ a b := by
  obtain ⟨hw', hα', ha'⟩ := eqReflApp_typings henv heq hΓ ⟨_, H⟩
  have hself := HasType.eqReflApp heq hw' hα' ha'
  have hspine : env.IsDefEqU U Γ (mkApps (.const ``Eq [w']) [α', a', a'])
      (mkApps (.const ``Eq [w]) [α, a, b]) := hself.uniqU henv hΓ H
  obtain ⟨_, hargs⟩ := hspine.rigidApp_inv henv hΓ (heq.rigid henv)
    (HasType.eqApp heq hw' hα' ha' ha')
  cases hargs with | cons _ hargs =>
  cases hargs with | cons hleft hargs =>
  cases hargs with | cons hright _ =>
  exact hleft.symm.trans henv hΓ hright

/-- Allowing arbitrary conversion of the major and arbitrary constructor
arguments does not weaken the endpoint-conversion obligation. -/
theorem eqProof_constructor_iff (henv : env.WF) (heq : env.HasCanonicalEq)
    (hw : w.WF U) (hΓ : OnCtx Γ (env.IsType U))
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α)
    (hb : env.HasType U Γ b α) (hp : env.HasType U Γ p (eqApp w α a b)) :
    (∃ w' α' a', env.IsDefEqU U Γ p (eqReflApp w' α' a')) ↔ env.IsDefEqU U Γ a b := by
  constructor
  · rintro ⟨w', α', a', h⟩
    exact eqRefl_typed_endpoint_conversion henv heq hΓ (h.of_l henv hΓ hp).hasType.2
  · intro h
    have href := (IsDefEq.eqApp_r heq hw hα ha (h.of_l henv hΓ ha)).defeq
      (HasType.eqReflApp heq hw hα ha)
    exact ⟨w, α, a, _, IsDefEq.proofIrrel (HasType.eqApp heq hw hα ha hb) hp href⟩

/-- No full computation or eta path of the major can expose reflexivity when
its equality endpoints do not convert. All actual full reduction rules are covered. -/
theorem eqProof_no_constructor_reduction (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hp : env.HasType U Γ p (eqApp w α a b))
    (hne : ¬ env.IsDefEqU U Γ a b) :
    ¬ @FullReduction (henv.params U) Γ p (eqReflApp w' α' a') := by
  letI := henv.params U
  intro h
  exact hne (eqRefl_typed_endpoint_conversion henv heq hΓ (h.hasType hΓ hp))

namespace EqRecResultBoundary

/-- The free equality proof in the constant-motive test is well typed. -/
theorem major_typed (env : VEnv) (U : Nat) :
    env.HasType U context (.bvar 0) equality := by
  have h : env.HasType U context (.bvar 0) equality.lift := .bvar .zero
  simpa [equality, carrier, left, right, eqApp, liftN] using h

/-- Every proof of the test equality, including any transported reconstruction,
fails to convert to every reflexivity constructor. This has no extra rigidity
premise and permits arbitrary changes to the proposed constructor arguments. -/
theorem no_constructor_conversion (henv : env.WF) (heq : env.HasCanonicalEq)
    (hp : env.HasType U context p equality) :
    ¬ env.IsDefEqU U context p (eqReflApp w α a) := by
  intro h
  have hab := eqRefl_typed_endpoint_conversion henv heq (context_wf heq)
    (h.of_l henv (context_wf heq) hp).hasType.2
  exact IsDefEqU.sort_forallE_inv henv (context_wf heq) hab

/-- The same obstruction holds for every finite full reduction of the major,
including generated prefixes and both eta forms. It does not by itself prove
that the enclosing recursor has no alternative conversion to its minor. -/
theorem no_constructor_reduction (henv : env.WF) (heq : env.HasCanonicalEq)
    (hp : env.HasType U context p equality) :
    ¬ @FullReduction (henv.params U) context p (eqReflApp w α a) :=
  eqProof_no_constructor_reduction henv heq (context_wf heq) hp
    (IsDefEqU.sort_forallE_inv henv (context_wf heq))

end EqRecResultBoundary
end Strengthening
end Lean4Lean.VEnv
