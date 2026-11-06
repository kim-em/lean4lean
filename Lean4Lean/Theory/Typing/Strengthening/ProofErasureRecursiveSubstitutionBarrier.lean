import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelRecursiveTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeIdentityExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedCompositionBarrier

/-! # The strengthening cost of unrestricted recursive substitution

Removing atomicity from recursive substitution is not merely a larger path
reflection problem. A single identity-lambda image promotes common lambda
checking inside a neutral application to inferred checking of the lambda itself.
Even with one actual source context, common source typing and a genuinely typed
image, this extension would imply PropositionFront. The witness uses only constant-body probes,
one neutral application and one beta step on each side. This is an implication
barrier, not a counterexample to typed substitution or strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The missing extension of the atomic constructor to arbitrary images,
restricted to inferred certificates whose resulting endpoints have a common
actual type. No closure is assumed elsewhere. The theorem below shows that
this already implies the full proposition front, so it is not a strictly
smaller remaining obligation. Sort-valued-only substitution is not asserted
or refuted by this definition's function-valued witness. -/
def TypedRecursiveSubstitutionClosure (D : Definitions) : Prop :=
  ∀ {Γ e f T a b} {σ : ProofShape.Subst}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ e T → env.HasType univs Γ f T →
    LevelRecursiveGuard D false a b →
    proofErase Γ e = a.subst σ → proofErase Γ f = b.subst σ →
    LevelRecursiveGuard D false (proofErase Γ e) (proofErase Γ f)

/-- One neutral application of commonly checked constant-body lambdas has a
recursive inferred certificate without any comparison of the lambda domains.
The shifted domains will be restored by a single identity substitution. -/
theorem recursive_neutral_probe_guard (hΓ : OnCtx Γ (env.IsType univs))
    (P Q : ProofShape) :
    LevelRecursiveGuard D false
      (.app (.bvar 0) (.lam (P.liftN 1) (.sort .zero)))
      (.app (.bvar 0) (.lam (Q.liftN 1) (.sort .zero))) := by
  have hs : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have ES : proofErase Γ (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort hΓ hs)
  have Hbody : LevelRecursiveGuard D true (.sort .zero) (.sort .zero) := by
    rw [← ES]
    exact .join hΓ hs hs (.of_compute .refl)
  exact .neutral (args := [.lam (P.liftN 1) (.sort .zero)])
    (args' := [.lam (Q.liftN 1) (.sort .zero)]) rfl (by
    intro i hi
    have : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i
    exact .lamCommon Hbody)

/-- The unresolved typed single-instantiation closure rule for recursive
inferred certificates. The sources have a common type in one actual binder
context and the image inhabits that binder's type. The following reduction
shows that adding these typing conditions does not make unrestricted closure
a strictly smaller obligation than PropositionFront. -/
def TypedRecursiveInstantiationClosure (D : Definitions) : Prop :=
  ∀ {Γ A b c B p}, OnCtx (A :: Γ) (env.IsType univs) →
    env.HasType univs (A :: Γ) b B → env.HasType univs (A :: Γ) c B →
    env.HasType univs Γ p A →
    LevelRecursiveGuard D false (proofErase (A :: Γ) b) (proofErase (A :: Γ) c) →
    LevelRecursiveGuard D false (proofErase Γ (b.inst p)) (proofErase Γ (c.inst p))

/-- The stronger raw-image closure includes genuine typed single instantiation.
Erasure commutes with this actual substitution without a strengthening premise. -/
theorem TypedRecursiveSubstitutionClosure.instantiation
    (H : TypedRecursiveSubstitutionClosure D) : TypedRecursiveInstantiationClosure D := by
  intro Γ A b c B p hΓA hb hc hp HG
  exact H hΓA.1 (hb.instN henv.ordered Ctx.InstN.zero hp)
    (hc.instN henv.ordered Ctx.InstN.zero hp) HG
    (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      proofErase_instN hΓA hp Ctx.InstN.zero hb)
    (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      proofErase_instN hΓA hp Ctx.InstN.zero hc)

/-- A concrete, commonly typed neutral probe and identity substitution. Its
stage-zero recursive guard omits the two domain annotations, while the two
substituted outputs beta-reduce to those domain probes. This witness is
independent of any proposed substitution-closure conclusion. -/
theorem recursive_neutral_probe_instantiation
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ T b c B, let A := VExpr.forallE T T.lift;
      let p := VExpr.lam T (.bvar 0);
      OnCtx (A :: Γ) (env.IsType univs) ∧
      env.HasType univs (A :: Γ) b B ∧ env.HasType univs (A :: Γ) c B ∧
      env.HasType univs Γ p A ∧
      LevelRecursiveGuard D false (proofErase (A :: Γ) b) (proofErase (A :: Γ) c) ∧
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (b.inst p))
        (proofErase Γ (domainProbe P)) ∧
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (c.inst p))
        (proofErase Γ (domainProbe Q)) := by
  let T := VExpr.forallE P (.sort (.succ .zero))
  have hf : env.HasType univs Γ (domainProbe P) T := domainProbe_typed hP
  have hg : env.HasType univs Γ (domainProbe Q) T :=
    (IsDefEq.forallEDF HPQ.symm (HasType.sort (by trivial))).defeq (domainProbe_typed hQ)
  obtain ⟨v, hT⟩ := hf.isType henv hΓ
  let I := VExpr.forallE T T.lift
  have hid : env.HasType univs Γ (.lam T (.bvar 0)) I := .lam hT (.bvar .zero)
  have hΓI : OnCtx (I :: Γ) (env.IsType univs) := ⟨hΓ, hid.isType henv hΓ⟩
  have hvar : env.HasType univs (I :: Γ) (.bvar 0) (.forallE T.lift T.lift.lift) := by
    have HV : env.HasType univs (I :: Γ) (.bvar 0) I.lift := .bvar .zero
    simpa only [I, VExpr.lift, VExpr.liftN, ← VExpr.lift_liftN'] using HV
  have hleft : env.HasType univs (I :: Γ) (.app (.bvar 0) (domainProbe P).lift) T.lift := by
    simpa only [VExpr.inst_lift] using HasType.app hvar (hf.weak henv)
  have hright : env.HasType univs (I :: Γ) (.app (.bvar 0) (domainProbe Q).lift) T.lift := by
    simpa only [VExpr.inst_lift] using HasType.app hvar (hg.weak henv)
  have hnL := not_isProof_function_to_sort hΓI hleft
  have hnR := not_isProof_function_to_sort hΓI hright
  have hnvar := not_isProof_fn hΓI hvar (hf.weak henv) hnL
  have EL : proofErase (I :: Γ) (.app (.bvar 0) (domainProbe P).lift) =
      .app (.bvar 0) (.lam ((proofErase Γ P).liftN 1) (.sort .zero)) := by
    rw [show proofErase (I :: Γ) (.app (.bvar 0) (domainProbe P).lift) = .app _ _ from if_neg hnL,
      show proofErase (I :: Γ) (.bvar 0) = .bvar 0 from if_neg hnvar,
      proofErase_liftN hΓ hΓI Ctx.LiftN.one hf, proofErase_domainProbe hΓ hP]
    rfl
  have ER : proofErase (I :: Γ) (.app (.bvar 0) (domainProbe Q).lift) =
      .app (.bvar 0) (.lam ((proofErase Γ Q).liftN 1) (.sort .zero)) := by
    rw [show proofErase (I :: Γ) (.app (.bvar 0) (domainProbe Q).lift) = .app _ _ from if_neg hnR,
      show proofErase (I :: Γ) (.bvar 0) = .bvar 0 from if_neg hnvar,
      proofErase_liftN hΓ hΓI Ctx.LiftN.one hg, proofErase_domainProbe hΓ hQ]
    rfl
  refine ⟨T, _, _, _, hΓI, hleft, hright, hid,
    EL.symm ▸ ER.symm ▸ recursive_neutral_probe_guard hΓ (proofErase Γ P) (proofErase Γ Q), ?_⟩
  have hnf := not_isProof_function_to_sort hΓ hf
  have hng := not_isProof_function_to_sort hΓ hg
  simp only [VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte,
    VExpr.liftN_zero, VExpr.inst_lift]
  constructor
  · rw [proofErase_nativeIdentityExpansion hΓ hf hnf]
    simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
      ProofShape.liftN_zero] using
      (ProofShape.Compute.beta (Step := ErasedLevelCore D)
        (ProofShape.BetaRed.beta (A := proofErase Γ T) (b := .bvar 0) (a := proofErase Γ (domainProbe P))))
  · rw [proofErase_nativeIdentityExpansion hΓ hg hng]
    simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
      ProofShape.liftN_zero] using
      (ProofShape.Compute.beta (Step := ErasedLevelCore D)
        (ProofShape.BetaRed.beta (A := proofErase Γ T) (b := .bvar 0) (a := proofErase Γ (domainProbe Q))))

/-- The neutral probe templates are actual commonly typed terms. Substituting
an actual identity function at their newest variable and taking one beta step
would give inferred recursive guards for all convertible domain probes. -/
theorem TypedRecursiveInstantiationClosure.probe_guard
    (H : TypedRecursiveInstantiationClosure D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    LevelRecursiveGuard D false (proofErase Γ (domainProbe P)) (proofErase Γ (domainProbe Q)) := by
  obtain ⟨T, b, c, B, hΓA, hb, hc, hp, HG, RL, RR⟩ :=
    recursive_neutral_probe_instantiation (D := D) hΓ hP hQ HPQ
  exact (H hΓA hb hc hp HG).reducts RL RR

/-- Coherent common source typing and an actual typed image still leave the
full proposition front in arbitrary recursive single-instantiation closure.
This is a reduction of the original goal, not a refutation of that closure. -/
theorem TypedRecursiveInstantiationClosure.implies_propositionFront
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : TypedRecursiveInstantiationClosure D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  have HG := H.probe_guard hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  have HR := HG.forward hs hl hcon hc .refl .refl
  have EP : (domainProbe P).lift = domainProbe P.lift := rfl
  have ER : (domainProbe R).lift = domainProbe R.lift := rfl
  rw [← EP, ← ER, proofErase_liftN hΓ hΓ' Ctx.LiftN.one (domainProbe_typed hP),
    proofErase_liftN hΓ hΓ' Ctx.LiftN.one (domainProbe_typed hR)] at HR
  have HP := (proofErase_rawChecked_compare_descend (erased_level_core_descent hs)
    hΓ hΓ' Ctx.LiftN.one (domainProbe_typed hP) (domainProbe_typed hR) HR).2
    rfl (not_isProof_function_to_sort hΓ (domainProbe_typed hP))
  have HQ := HP.of_l henv hΓ (domainProbe_typed hP)
  obtain ⟨⟨_, HPR⟩, _⟩ := (HQ.hasType.2.uniqU henv hΓ (domainProbe_typed hR)).forallE_inv henv hΓ
  exact ⟨_, HPR⟩

/-- The arbitrary-image version also yields inferred guards for all convertible
probes, by specializing to the genuine typed identity instantiation above. -/
theorem TypedRecursiveSubstitutionClosure.probe_guard
    (H : TypedRecursiveSubstitutionClosure D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    LevelRecursiveGuard D false (proofErase Γ (domainProbe P)) (proofErase Γ (domainProbe Q)) :=
  TypedRecursiveInstantiationClosure.probe_guard H.instantiation hΓ hP hQ HPQ

/-- Removing atomicity from raw-image recursive substitution would already
settle PropositionFront, even if its resulting endpoints must share a type. -/
theorem TypedRecursiveSubstitutionClosure.implies_propositionFront
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : TypedRecursiveSubstitutionClosure D) : PropositionFront :=
  TypedRecursiveInstantiationClosure.implies_propositionFront hs hl hcon hc H.instantiation

/-- The actual witness is excluded by requiring sort-valued endpoints: neither
its constant-body probe nor its identity wrapper admits any sort typing, even
through conversion. This does not prove sort-valued substitution closure. -/
theorem recursive_probe_identity_not_sort
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort u)) :
    (¬ env.HasType univs Γ (domainProbe P) (.sort v)) ∧
    (¬ env.HasType univs Γ
      (.app (.lam (.forallE P (.sort (.succ .zero))) (.bvar 0)) (domainProbe P)) (.sort w)) := by
  constructor
  · intro H
    exact (H.uniqU henv hΓ (domainProbe_typed hP)).sort_forallE_inv henv hΓ
  · intro H
    exact (H.uniqU henv hΓ (nativeIdentityExpansion_equal (domainProbe_typed hP)).hasType.1).sort_forallE_inv henv hΓ

namespace EnvironmentCore

/-- Actual environment definitions discharge the abstract core assumptions.
Even genuine typed single-instantiation closure for recursive inferred guards
would settle the proposition front. Canonical Eq may be present but is not
needed by this conditional reduction. -/
theorem recursive_instantiation_implies_propositionFront
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : TypedRecursiveInstantiationClosure definitions) : PropositionFront :=
  H.implies_propositionFront sound (levelCompatible hcon) hcon (typed_level_core_confluence hcon)

end EnvironmentCore

end Lean4Lean.VEnv.Strengthening
