import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxTypeChange

/-! # Recursive rigid replacements in recovered types

Unlike fixed-domain result replacement, both sides of every Pi may change.
Actual type equality supplies head separation and transports computation across
changed domains. Raw syntax alone is not required to preserve exposed heads.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]
namespace ProofShape

/-- A type may retain its syntax, change to a closed rigid constant, or change
both the domain and codomain of a displayed Pi recursively.
Actual source/target type equality is required separately for typed use. -/
inductive RigidTypeChange : ProofShape → ProofShape → Prop where
  | refl : RigidTypeChange A A
  | closed (hr : env.Rigid family) : RigidTypeChange A (.const family [])
  | forallE : RigidTypeChange A A' → RigidTypeChange B B' →
      RigidTypeChange (.forallE A B) (.forallE A' B')

/-- The relation survives insertion of any block of variables. -/
theorem RigidTypeChange.liftN (H : RigidTypeChange A B) :
    RigidTypeChange (A.liftN n k) (B.liftN n k) := by
  induction H generalizing k with
  | refl => exact .refl
  | closed hr => exact .closed hr
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

/-- Application may instantiate the changed result with any raw argument. -/
theorem RigidTypeChange.inst (H : RigidTypeChange A B) :
    RigidTypeChange (A.inst x k) (B.inst x k) := by
  induction H generalizing k with
  | refl => exact .refl
  | closed hr => exact .closed hr
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

/-- Every source beta path can be mirrored while retaining the result relation. -/
theorem RigidTypeChange.beta (H : RigidTypeChange A B) (R : BetaRed A out) :
    ∃ out', BetaRed B out' ∧ RigidTypeChange out out' := by
  induction H generalizing out with
  | refl => exact ⟨_, R, .refl⟩
  | closed hr => exact ⟨_, .refl, .closed hr⟩
  | forallE HA HB ihA ihB =>
    obtain ⟨A', B', rfl, RA, RB⟩ := ProofShape.beta_forallE_parts R
    obtain ⟨outA, RA', HA'⟩ := ihA RA
    obtain ⟨outB, RB', HB'⟩ := ihB RB
    exact ⟨_, .forallE RA' RB', .forallE HA' HB'⟩

/-- Arbitrary raw substitution preserves recursive rigid replacement. Closed
replacement leaves contain no variables, and Pi bodies use the lifted map. -/
theorem RigidTypeChange.subst (H : RigidTypeChange A B) :
    RigidTypeChange (A.subst σ) (B.subst σ) := by
  induction H generalizing σ with
  | refl => exact .refl
  | closed hr => exact .closed hr
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

/-- A target beta path can be matched by a source beta path, preserving the
relation. A closed replacement remains fixed; unchanged subtrees mirror the
path and both parts of a Pi recurse independently. -/
theorem RigidTypeChange.beta_target (H : RigidTypeChange A B) (R : BetaRed B out) :
    ∃ out', BetaRed A out' ∧ RigidTypeChange out' out := by
  induction H generalizing out with
  | refl => exact ⟨_, R, .refl⟩
  | closed hr =>
    have RR : BetaRed (mkApps (.const _ []) []) out := R
    obtain ⟨ps, rfl, HP⟩ := RR.const_spine
    cases HP
    exact ⟨_, .refl, .closed hr⟩
  | forallE HA HB ihA ihB =>
    obtain ⟨A', B', rfl, RA, RB⟩ := ProofShape.beta_forallE_parts R
    obtain ⟨outA, RA', HA'⟩ := ihA RA
    obtain ⟨outB, RB', HB'⟩ := ihB RB
    exact ⟨_, .forallE RA' RB', .forallE HA' HB'⟩

/-- Typed computation is simulated through recursively changed Pi domains.
Actual equality identifies the two body contexts, so primitive substitution
moves the recursively simulated body path. Closed replacements discard the
old path and reflexive subtrees retain it. -/
theorem RigidTypeChange.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : RigidTypeChange a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (EA : proofErase Γ A = a) (EB : proofErase Γ B = b)
    (R : ScopedCompute Step (proofEraseCtx Γ) a out) :
    ∃ out', ScopedCompute Step (proofEraseCtx Γ) b out' ∧ RigidTypeChange out out' := by
  induction H generalizing Γ A B u out with
  | refl => exact ⟨_, R, .refl⟩
  | closed hr => exact ⟨_, .refl, .closed hr⟩
  | forallE HD HC ihD ihC =>
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv EA
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv EB
    obtain ⟨⟨v, hD⟩, _, _⟩ := HAB.hasType.1.forallE_inv henv
    obtain ⟨⟨w, Hdom⟩, ⟨z, Hcod⟩⟩ := HAB.toU.forallE_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, v, hD⟩
    have hctx := IsDefEqCtx.succ .zero Hdom
    have EC'' := (proofErase_defeqCtx hΓD hctx Hcod.hasType.2).trans EC'
    obtain ⟨d, c, rfl, RD, RC⟩ := (ED ▸ R).forallE_inv_typed hstep hsubst hhead hΓ hD rfl
    obtain ⟨d', RD', HD'⟩ := ihD hΓ Hdom ED ED' (ED ▸ RD)
    have RC : ScopedCompute Step (proofEraseCtx (D :: Γ)) _ _ := RC
    obtain ⟨c', RC', HC'⟩ := ihC hΓD Hcod EC EC'' RC
    have RC'' := RC'.defeqCtx hsubst hΓ hctx
    simp only [proofEraseCtx, ED'] at RC''
    exact ⟨_, .forallE RD' RC'', .forallE HD' HC'⟩

end ProofShape

/-- Typed Pi exposure retains recursive relations on both domain and body.
Head separation excludes the incompatible closed-replacement alternative. -/
theorem rigid_type_typed_pi
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = .forallE A B) (EY : proofErase Γ Y = out)
    (H : RigidTypeChange (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ RigidTypeChange A A' ∧ RigidTypeChange B B' := by
  cases H with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | forallE HA HB => exact ⟨_, _, rfl, HA, HB⟩
  | closed hr =>
    obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv EX
    obtain rfl := erase_const_inv EY
    exact (henv.headInversion.forallE_rigid (args := []) hΓ hr (HE.typeChain henv hΓ hX)).elim

/-- Actually equal universe results keep their exact erased level. -/
theorem rigid_type_typed_sort
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = .sort v) (EY : proofErase Γ Y = out)
    (H : RigidTypeChange (.sort v) out) : out = .sort v := by
  cases H with
  | refl => rfl
  | closed hr =>
    obtain rfl := erase_sort_inv EX
    obtain rfl := erase_const_inv EY
    exact (henv.headInversion.sort_rigid (args := []) hΓ hr (HE.typeChain henv hΓ hX)).elim

/-- Actually equal registered-record results remain exactly the same erased
carrier. A possible closed replacement forces the original universe and term
argument lists to be empty by rigid-head injectivity. -/
theorem rigid_type_typed_record
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = ProofShape.mkApps (.const family ls) ps)
    (EY : proofErase Γ Y = out)
    (H : RigidTypeChange (ProofShape.mkApps (.const family ls) ps) out) :
    out = ProofShape.mkApps (.const family ls) ps := by
  generalize ES : ProofShape.mkApps (.const family ls) ps = source at H
  cases H with
  | refl => rfl
  | forallE HA HB =>
    have Ehead := congrArg ProofShape.constHead ES
    simp only [constHead_mkApps, ProofShape.constHead] at Ehead
    cases Ehead
  | closed hr =>
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EX
    obtain rfl := erase_const_inv EY
    obtain ⟨rfl, HL, HA⟩ := henv.headInversion.rigid_rigid (args' := []) hΓ
      (henv.projectionRigid hi) hr (HE.typeChain henv hΓ hX)
    cases HL
    cases HA
    simp only [List.map_nil] at Eargs
    subst ps
    exact ES

/-- Structural subsingletons survive recursive rigid changes between actually
equal typed carriers. In the Pi case, the target codomain is interpreted in
the source binder context using forward context conversion. -/
theorem rigid_type_subsingleton
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = source) (EY : proofErase Γ Y = target)
    (H : RigidTypeChange source target) (HS : SubsingletonCarrier source) :
    SubsingletonCarrier target := by
  induction HS generalizing Γ X Y u target with
  | unit hi hz hf hp =>
    have E := rigid_type_typed_record hi hΓ hX HE EX EY H
    rw [E]
    exact .unit hi hz hf hp
  | forallE HS ih =>
    obtain ⟨A', B', rfl, _, HB⟩ := rigid_type_typed_pi hΓ hX HE EX EY H
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv EX
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv EY
    obtain ⟨⟨v, hD⟩, _, _⟩ := hX.forallE_inv henv
    obtain ⟨⟨_, HD⟩, ⟨_, HC⟩⟩ := HE.forallE_inv henv hΓ
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, v, hD⟩
    have W := IsDefEqCtx.succ .zero HD
    have EC'' := (proofErase_defeqCtx hΓD W HC.hasType.2).trans EC'
    exact .forallE (ih hΓD HC.hasType.1 HC.toU EC EC'' HB)

end Lean4Lean.VEnv.Strengthening
