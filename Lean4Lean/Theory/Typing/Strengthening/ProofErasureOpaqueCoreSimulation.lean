import Lean4Lean.Theory.Typing.Strengthening.ProofErasureOpaquePatterns
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCorePrimitives

/-! # Directed core simulation of protected cast occurrences

Ordinary primitives preserve corresponding captures. A reduction inside a
marked source updates its original core path while leaving its payload fixed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {Guard : ProofShape → ProofShape → Prop}

/-- Every core root step has a matching payload path and retains the marked
source certificates. No reduction of a newly exposed payload head is required. -/
theorem opaque_level_core_root
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hshape : ∀ {a b}, Guard a b → EqCastShape a)
    (hg : ∀ {a b a'}, Guard a b → ProofShape.Compute (ErasedLevelCore D) a a' → Guard a' b)
    (R : ErasedLevelCore D a out) (V : OpaqueVariant Guard n a b) :
    ∃ out', ProofShape.Compute (ErasedLevelCore D) b out' ∧ OpaqueVariant Guard n out out' := by
  cases V with
  | refl => exact ⟨_, .base R, .refl⟩
  | marked HG =>
    obtain ⟨a', RA, E⟩ := (ProofShape.Compute.base R).level_core_lift_inv
    refine ⟨_, .refl, ?_⟩
    rw [E]
    exact .marked (hg HG RA)
  | app VF VX =>
    rcases R with ((R | R) | R) | R
    · cases R
    · cases R with
      | select hp hc hm =>
        obtain ⟨caps', HM, HC⟩ := hm.opaque_variant heq hreg hoff hshape hp (.app VF VX)
        exact ⟨_, .base (.inl (.inl (.inr (.select hp hc HM)))), HC _⟩
      | apply hp hc hm =>
        obtain ⟨caps', HM, HC⟩ := hm.opaque_variant heq hreg hoff hshape hp (.app VF VX)
        exact ⟨_, .base (.inl (.inl (.inr (.apply hp hc HM)))), .app (HC _) (HC _)⟩
    · cases R with
      | intro hp hc ht hm =>
        obtain ⟨caps', HM, HC⟩ := hm.opaque_variant heq hreg hoff hshape hp (.app VF VX)
        refine ⟨_, .base (.inl (.inr (.intro hp hc ht HM))), OpaqueVariant.refl.mkApps_pair ?_⟩
        apply List.forall₂_of_getElem (by simp)
        intro i hi hi'
        simp only [List.getElem_map]
        exact HC _
    · cases R
  | @proj n m m' s i VM =>
    rcases R with ((R | R) | R) | R
    · cases R with
      | @projIota _ info args _ ls field hi hlen hget =>
        have hne : info.ctorName ≠ ``Eq.rec := by
          intro E
          have HR := projection_ctor_rigid hi
          rw [E] at HR
          obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
          exact HR.pats _ _ hp (SimplePattern.iota_headConst _ _ _ _)
        obtain ⟨args', rfl, HA⟩ := VM.constant_spine hshape hne
        obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
        have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
        refine ⟨args'[info.nparams + i]'hj', .base (.inl (.inl (.inl
          (.projIota hi (HA.length_eq.symm.trans hlen) (List.getElem?_eq_getElem hj'))))), ?_⟩
        rw [← HE]
        exact HA.getElem_of _ hj hj'
    · cases R with
      | select _ _ hm => cases hm
      | apply _ _ hm => cases hm
    · cases R with | intro _ _ _ hm => cases hm
    · cases R
  | lam VA VB =>
    rcases R with R | R
    · exact (erased_iota_primitive_head R).elim
    · cases R
  | forallE VA VB =>
    rcases R with R | R
    · exact (erased_iota_primitive_head R).elim
    · cases R

/-- Arbitrary finite level-core paths preserve the directed opaque relation.
Local beta steps use protected paired instantiation; primitive steps use the
actual registered pattern exclusions. -/
theorem ProofShape.OpaqueVariant.level_core_left
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hshape : ∀ {a b}, Guard a b → EqCastShape a)
    (hg : ∀ {a b a'}, Guard a b → ProofShape.Compute (ErasedLevelCore D) a a' → Guard a' b)
    (R : ProofShape.Compute (ErasedLevelCore D) a a') (V : OpaqueVariant Guard n a b) :
    ∃ b', ProofShape.Compute (ErasedLevelCore D) b b' ∧ OpaqueVariant Guard n a' b' := by
  induction R generalizing n b with
  | base R => exact opaque_level_core_root heq hreg hoff hshape hg R V
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ V
    obtain ⟨b₂, RC, V₂⟩ := ih₂ V₁
    exact ⟨b₂, RB.trans RC, V₂⟩
  | @app f f' x x' RF RX ihf ihx =>
    generalize E : ProofShape.app f x = source at V
    cases V with
    | refl => cases E; exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      cases E
      obtain ⟨g, RG, VG⟩ := ihf VF
      obtain ⟨y, RY, VY⟩ := ihx VX
      exact ⟨_, .app RG RY, .app VG VY⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.app RF RX).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | proj | lam | forallE => cases E
  | @proj m m' s i R ih =>
    generalize E : ProofShape.proj s i m = source at V
    cases V with
    | refl => cases E; exact ⟨_, .proj R, .refl⟩
    | proj V =>
      cases E
      obtain ⟨b, RB, VB⟩ := ih V
      exact ⟨_, .proj RB, .proj VB⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.proj R).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | app | lam | forallE => cases E
  | @lam A A' body body' RA RB ihA ihB =>
    generalize E : ProofShape.lam A body = source at V
    cases V with
    | refl => cases E; exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      cases E
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨d, RD, VD⟩ := ihB VB
      exact ⟨_, .lam RC RD, .lam VC VD⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.lam RA RB).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | app | proj | forallE => cases E
  | @forallE A A' body body' RA RB ihA ihB =>
    generalize E : ProofShape.forallE A body = source at V
    cases V with
    | refl => cases E; exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      cases E
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨d, RD, VD⟩ := ihB VB
      exact ⟨_, .forallE RC RD, .forallE VC VD⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.forallE RA RB).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | app | proj | lam => cases E
  | beta R =>
    obtain ⟨b', RB, VB⟩ := V.beta_left (Guard := Guard) (fun H => (hshape H).head) (fun H R => hg H (.beta R)) R
    exact ⟨b', .beta RB, VB⟩

end Lean4Lean.VEnv.Strengthening
