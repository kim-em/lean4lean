import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextLambdaAnnotation

/-! # Contextual application through fixed result types

A typed template whose result type is independent of its input preserves
contextual type joins by composing observers. This handles function-position
congruence for dependent applications, and argument-position congruence for
nondependent applications. No computation or native recovery is needed for the
composition itself.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Compose a type observer with a typed template whose result type does not
depend on the input variable. This preserves contextual joins without confluence,
instantiation joining or native coverage. A genuinely dependent result type is
not covered by the displayed typing premise. -/
theorem TypeContextJoin.map
    (he : env.HasType univs (A :: Γ) e T.lift)
    (H : TypeContextJoin D Γ A a b) :
    TypeContextJoin D Γ T (e.inst a) (e.inst b) := by
  intro C v hC
  have hC' := hC.weakN henv (Ctx.LiftN.one.succ : Ctx.LiftN 1 1 (T :: Γ) (T.lift :: A :: Γ))
  have hD := hC'.instN henv.ordered Ctx.InstN.zero he
  obtain ⟨s, L, R⟩ := H hD
  have E (x : VExpr) : ((C.liftN 1 1).inst e).inst x = C.inst (e.inst x) := by
    simpa only [VExpr.inst_liftN] using VExpr.inst_inst_hi (C.liftN 1 1) e x 0 0
  rw [E] at L R
  exact ⟨s, L, R⟩

/-- Contextual comparison in function position respects application to one
fixed typed argument. The function's codomain may be dependent: after fixing
that argument, the result type is independent of the generic function variable. -/
theorem TypeContextJoin.app_fn
    (hx : env.HasType univs Γ x A)
    (H : TypeContextJoin D Γ (.forallE A B) f g) :
    TypeContextJoin D Γ (B.inst x) (.app f x) (.app g x) := by
  have hf : env.HasType univs (.forallE A B :: Γ) (.bvar 0) (VExpr.forallE A B).lift := .bvar .zero
  have he : env.HasType univs (.forallE A B :: Γ) (.app (.bvar 0) x.lift) (B.inst x).lift := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.lift_inst_hi] using HasType.app hf (hx.weak henv.ordered)
  have HM : TypeContextJoin D Γ (B.inst x)
      ((VExpr.app (.bvar 0) x.lift).inst f) ((VExpr.app (.bvar 0) x.lift).inst g) :=
    TypeContextJoin.map he H
  intro C v hC
  simpa only [VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift] using HM hC

/-- A fixed function with nondependent result type preserves contextual
comparison of its arguments. The argument values need no native certificates. -/
theorem TypeContextJoin.app_arg_nondependent
    (hf : env.HasType univs Γ f (.forallE A T.lift))
    (H : TypeContextJoin D Γ A x y) :
    TypeContextJoin D Γ T (.app f x) (.app f y) := by
  have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have he : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) T.lift := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using HasType.app (hf.weak henv.ordered) hx
  have HM : TypeContextJoin D Γ T
      ((VExpr.app f.lift (.bvar 0)).inst x) ((VExpr.app f.lift (.bvar 0)).inst y) :=
    TypeContextJoin.map he H
  intro C v hC
  simpa only [VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift] using HM hC

/-- Both sides of a nondependent application may change contextually. Only
transitivity needs the open type-only fork premise; both congruence steps are
observer composition. The function and its arguments may be arbitrary data. -/
theorem TypeForkJoin.contextual_app_nondependent
    (HF : TypeForkJoin D) (hΓ : OnCtx Γ (env.IsType univs))
    (hg : env.HasType univs Γ g (.forallE A T.lift)) (hx : env.HasType univs Γ x A)
    (Hfg : TypeContextJoin D Γ (.forallE A T.lift) f g)
    (Hxy : TypeContextJoin D Γ A x y) :
    TypeContextJoin D Γ T (.app f x) (.app g y) := by
  have HM : env.HasType univs Γ (.app g x) T := by simpa only [VExpr.inst_lift] using HasType.app hg hx
  have HL : TypeContextJoin D Γ T (.app f x) (.app g x) := by
    intro C v hC
    have hC' : env.HasType univs (T.lift.inst x :: Γ) C (.sort v) := by
      simpa only [VExpr.inst_lift] using hC
    exact TypeContextJoin.app_fn hx Hfg hC'
  intro C v hC
  exact TypeContextJoin.trans HF hΓ HM HL (TypeContextJoin.app_arg_nondependent hg Hxy) hC

/-- A computational join of dependent arguments lifts through a fixed function
and every typed type observer. Ordinary argument equality supplies a common
result assignment and synchronized proof erasure. No native evidence is needed. -/
theorem TypeContextJoin.app_arg_of_compute_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (Hxy : env.IsDefEq univs Γ x y A)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) shared)
    (RY : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ y) shared) :
    TypeContextJoin D Γ (B.inst x) (.app f x) (.app f y) := by
  have HE := IsDefEq.appDF hf Hxy
  obtain ⟨u, hT⟩ := HE.hasType.1.isType henv hΓ
  have hΓT : OnCtx (B.inst x :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  intro C v hC
  classical
  by_cases hp : IsProof Γ (.app f x)
  · have hp' := (isProof_congr hΓ HE).1 hp
    have E : proofErase Γ (.app f x) = proofErase Γ (.app f y) := by
      rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact TypeContextJoin.of_erasure_eq hΓT HE.hasType.1 HE.hasType.2 E hC
  have hp' : ¬ IsProof Γ (.app f y) := fun h => hp ((isProof_congr hΓ HE).2 h)
  have RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (.app (proofErase Γ f) shared) := by
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp]
    exact .app .refl RX
  have RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f y)) (.app (proofErase Γ f) shared) := by
    rw [show proofErase Γ (.app f y) = .app _ _ from if_neg hp']
    exact .app .refl RY
  exact TypeContextJoin.of_compute_join heq hs hΓT HE.hasType.1 HE.hasType.2 RL RR hC

/-- Contextually compared type arguments may be supplied to a dependent
function. The identity observer extracts their computational join, so the
function's result need not be a type-valued template at a generic input. -/
theorem TypeContextJoin.app_arg_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (.sort u) B))
    (Hxy : env.IsDefEq univs Γ x y (.sort u))
    (HJ : TypeContextJoin D Γ (.sort u) x y) :
    TypeContextJoin D Γ (B.inst x) (.app f x) (.app f y) := by
  obtain ⟨shared, RX, RY⟩ := TypeContextJoin.type_join HJ
  intro C v hC
  exact TypeContextJoin.app_arg_of_compute_join heq hs hΓ hf Hxy RX RY hC

/-- Both function and type argument may change in a genuinely dependent
application. Only contextual transitivity uses type-only fork joining; the
argument position is handled by computational joining of its type values. -/
theorem TypeForkJoin.contextual_app_type_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : TypeForkJoin D) (hΓ : OnCtx Γ (env.IsType univs))
    (hg : env.HasType univs Γ g (.forallE (.sort u) B))
    (Hxy : env.IsDefEq univs Γ x y (.sort u))
    (Hfg : TypeContextJoin D Γ (.forallE (.sort u) B) f g)
    (HJ : TypeContextJoin D Γ (.sort u) x y) :
    TypeContextJoin D Γ (B.inst x) (.app f x) (.app g y) := by
  have HL : TypeContextJoin D Γ (B.inst x) (.app f x) (.app g x) :=
    TypeContextJoin.app_fn Hxy.hasType.1 Hfg
  have HR : TypeContextJoin D Γ (B.inst x) (.app g x) (.app g y) :=
    TypeContextJoin.app_arg_type heq hs hΓ hg Hxy HJ
  intro C v hC
  exact TypeContextJoin.trans HF hΓ (HasType.app hg Hxy.hasType.1) HL HR hC

end Lean4Lean.VEnv.Strengthening
