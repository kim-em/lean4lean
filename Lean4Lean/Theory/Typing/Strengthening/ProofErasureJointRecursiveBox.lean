import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRelatedTypes

/-! # Simultaneous checking and recursive Pi/Box type conversion

Recovered Pi domains and Box field types may change recursively. The carrier induction transports
argument checking to those domains while the comparison induction transports
the function. Both branches use actual type equality to interpret contexts.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Simultaneous transport target. Comparison endpoints remain fixed; a
carrier may change recursively through Pi and Box structure, with its actual equality
proved in the source context. Both contexts are actually convertible. -/
def JointRecursiveBoxResult (boxFamily : Name)
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  JointRelatedResult (BoxTypeChange boxFamily) Step Δ kind sa sb

/-- All joint constructors transport simultaneously through recursive Pi/Box
oracle and carrier changes. Actual recovery replay determines the new
application domain and its equality; the smaller carrier derivation adapts
there. Primitive descent, head shape, and substitution are the only closure
premises. -/
theorem ProofShape.JointCheck.recursive_box
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hiBox : env.projections boxFamily infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const boxFamily []) (.bvar 1))))
    (hcBox : env.constants boxFamily = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const boxFamily []) args) out)
    (H : JointCheck Step Δ kind sa sb) : JointRecursiveBoxResult boxFamily Step Δ kind sa sb :=
  H.related_types hstep hsubst
    (BoxTypeChange.transport_laws hstep hhead hsubst hiBox hpBox hfBox hshapeBox hcBox hinert)

/-- In a fixed context, arbitrary typed carrier guards transport through a
recursive Pi/Box type change. Function domains, codomains and Box parameters
may change at any finite depth. Actual type equality is supplied independently. -/
theorem proofErase_joint_recursive_box_carrier
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hiBox : env.projections boxFamily infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const boxFamily []) (.bvar 1))))
    (hcBox : env.constants boxFamily = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const boxFamily []) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HAB : env.IsDefEqU univs Γ A B)
    (HT : BoxTypeChange boxFamily 0 (proofErase Γ A) (proofErase Γ B))
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ B)
      (proofErase Γ a) (proofErase Γ b) :=
  H.recursive_box hstep hhead hsubst hiBox hpBox hfBox hshapeBox hcBox hinert hΓ ha hb rfl rfl rfl rfl
    (.refl hΓ) (fun _ => .refl) HAB HT

/-- Body comparison survives changing an actual binder through Pi and Box
structure. Projection recovery adapts to changed field types, and application
checking adapts to their changed function domains. Actual endpoint erasures are
those of the target context. -/
theorem proofErase_joint_recursive_box_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hiBox : env.projections boxFamily infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const boxFamily []) (.bvar 1))))
    (hcBox : env.constants boxFamily = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const boxFamily []) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HT : BoxTypeChange boxFamily 0 (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : JointCompare Step (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare Step (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have HO : ∀ i, BoxTypeChange boxFamily 0 (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (B :: Γ)) i) := by
    intro i
    cases i with
    | zero => exact (HT.liftN (n := 1) (by omega)).mono (by omega)
    | succ i => exact .refl
  have HC := H.recursive_box hstep hhead hsubst hiBox hpBox hfBox hshapeBox hcBox hinert hΓA ha hb rfl rfl rfl W HO
  rwa [proofErase_defeqCtx hΓA W ha, proofErase_defeqCtx hΓA W hb] at HC

/-- Certified comparison supports recursively changing binder types in the
same certified relation, without assuming a union substitution or proposition
beta law. Recovery and its argument guards are adapted together. -/
theorem proofErase_certified_recursive_box_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hiBox : env.projections boxFamily infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const boxFamily []) (.bvar 1))))
    (hcBox : env.constants boxFamily = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hD : ∀ levels rhs, ¬ D.unfolds boxFamily levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HT : BoxTypeChange boxFamily 0 (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) :=
  proofErase_joint_recursive_box_context (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs)
    hiBox hpBox hfBox hshapeBox hcBox
    (fun R => erased_joint_union_no_rigid heq (henv.projectionRigid hiBox) hD
      (erased_beta_stable_joint_into_union R) (constHead_mkApps _ _)) hΓ HAB HT ha hb H

/-- Every certified guard transports through a typed recursive Pi/Box
carrier change, retaining all nested function and field checking. -/
theorem proofErase_certified_recursive_box_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hiBox : env.projections boxFamily infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const boxFamily []) (.bvar 1))))
    (hcBox : env.constants boxFamily = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hD : ∀ levels rhs, ¬ D.unfolds boxFamily levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HAB : env.IsDefEqU univs Γ A B)
    (HT : BoxTypeChange boxFamily 0 (proofErase Γ A) (proofErase Γ B))
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ B)
      (proofErase Γ a) (proofErase Γ b) :=
  proofErase_joint_recursive_box_carrier (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs)
    hiBox hpBox hfBox hshapeBox hcBox
    (fun R => erased_joint_union_no_rigid heq (henv.projectionRigid hiBox) hD
      (erased_beta_stable_joint_into_union R) (constHead_mkApps _ _)) hΓ ha hb HAB HT H

end Lean4Lean.VEnv.Strengthening
