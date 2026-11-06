import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCorePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelRecursiveTransport

/-! # Full core residuals of paired annotation variants

Primitive simulation and protected local substitution extend paired beta
simulation to the ordinary core with universe conversion. Recursive level-core
guards discharge stability of the marked domains. Confluence is needed only at
one actual typed endpoint, and is supplied by existing core confluence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {Guard : ProofShape → ProofShape → Prop}

/-- Every level-core path has a paired path when the marked domain guard
retains its own level-core reducts. All primitive matching cases are proved;
the guard premise concerns only the recorded ambient domain pairs. -/
theorem ProofShape.AnnotationVariant.level_core_left
    (hg : ∀ {A C A'}, Guard A C → Compute (ErasedLevelCore D) A A' → Guard A' C)
    (R : Compute (ErasedLevelCore D) a a') (V : AnnotationVariant Guard n a b) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧ AnnotationVariant Guard n a' b' := by
  induction R generalizing n b with
  | base R =>
    obtain ⟨b', RB, VB⟩ := erased_level_core_annotation_variant R V
    exact ⟨b', .base RB, VB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ V
    obtain ⟨b₂, RC, V₂⟩ := ih₂ V₁
    exact ⟨b₂, RB.trans RC, V₂⟩
  | app RF RX ihf ihx =>
    cases V with
    | refl => exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      obtain ⟨g, RG, VG⟩ := ihf VF
      obtain ⟨y, RY, VY⟩ := ihx VX
      exact ⟨_, .app RG RY, .app VG VY⟩
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨b, RB, VB⟩ := ih V
      exact ⟨_, .proj RB, .proj VB⟩
  | lam RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .lam RC Rc, .lam VC Vc⟩
    | marked HG VB =>
      obtain ⟨A', RA', rfl⟩ := RA.level_core_lift_inv
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .lam .refl Rc, .marked (hg HG RA') Vc⟩
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .forallE RC Rc, .forallE VC Vc⟩
  | beta R =>
    obtain ⟨b', RB, VB⟩ := AnnotationVariant.beta_left (Guard := Guard)
      (fun H R => hg H (.beta R)) R V
    exact ⟨b', .beta RB, VB⟩

private theorem level_lift (H : ErasedLevelCore D a b) :
    ErasedLevelCore D (a.liftN n k) (b.liftN n k) := by
  rcases H with H | H
  · exact .inl (erased_iota_primitive_liftN H)
  · cases H with
    | sort HE hw => exact .inr (.sort HE hw)
    | const HE hw => exact .inr (.const HE hw)

/-- Recursive level-core domain guards read out paired syntax in either mode.
Marked domains may keep computing and need not have a common reduct. -/
theorem annotation_level_recursive_check
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (V : AnnotationVariant (LevelRecursiveGuard D false) n a b) :
    RawCheckedCompare (ErasedLevelCore D) mode a b := by
  induction V generalizing mode with
  | refl => exact .base .refl
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | marked HG _ ih =>
    exact .lam ((HG.forward hs hl hcon hc .refl .refl).liftN level_lift) ih

/-- Two independent full level-core paths from paired annotation variants
have inferred residual comparisons. Typed confluence is used at the right
source only; there is no global confluence or endpoint-join hypothesis. -/
theorem annotation_level_core_residual_check
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (V : AnnotationVariant (LevelRecursiveGuard D false) n a (proofErase Γ e))
    (RA : Compute (ErasedLevelCore D) a p)
    (RB : Compute (ErasedLevelCore D) (proofErase Γ e) q) :
    RawCheckedCompare (ErasedLevelCore D) mode p q := by
  have hg {A C A'} (H : LevelRecursiveGuard D false A C) (R : Compute (ErasedLevelCore D) A A') :
      LevelRecursiveGuard D false A' C := .reducts H R .refl
  obtain ⟨b₁, RB₁, V₁⟩ := V.level_core_left (Guard := LevelRecursiveGuard D false) (fun H R => hg H R) RA
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ ht RB RB₁
  obtain ⟨p', RP, V₂⟩ := (V₁.symm LevelRecursiveGuard.symm).level_core_left
    (Guard := LevelRecursiveGuard D false) (fun H R => hg H R) RB₁'
  exact .compute RP RQ (annotation_level_recursive_check hs hl hcon hc (V₂.symm LevelRecursiveGuard.symm))

end Lean4Lean.VEnv.Strengthening
