import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure

/-! # Decoding Eq comparisons while retaining carrier computations

The two carrier expressions may compute independently from a common source.
Decoding returns a guard at that source, retaining all carrier and endpoint
paths. Actual typed sources justify recovery after each computation prefix.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Any typing of a canonical Eq proposition gives the native typings of its
three supplied arguments, regardless of its assigned result type. -/
theorem eqApp_typings (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : VExpr.WF env univs Γ (eqApp u α z a)) :
    u.WF univs ∧ env.HasType univs Γ α (.sort u) ∧
      env.HasType univs Γ z α ∧ env.HasType univs Γ a α := by
  have H' : VExpr.WF env univs Γ (mkApps (.const ``Eq [u]) [α, z, a]) := H
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ H'
  obtain ⟨ci, hci, hw, _⟩ := HasType.const_inv henv hΓ hc
  rw [heq.1] at hci
  cases Option.some.inj hci
  have hhead := HasType.const (Γ := Γ) heq.1 hw (by rfl)
  obtain ⟨res, ht, _⟩ := HasType.mkApps_telescope henv hΓ hhead H' (by rfl)
  cases ht with | cons hα ht =>
  cases ht with | cons hz ht =>
  cases ht with | cons ha ht =>
  cases ht
  refine ⟨hw _ (by simp), ?_⟩
  simpa [canonicalEqType, instL, VLevel.inst, VExpr.inst, instVar, VExpr.liftN, inst_lift] using
    And.intro hα (And.intro hz ha)

private def eqRaw (u : VLevel) (α z a : ProofShape) : ProofShape :=
  .app (.app (.app (.const ``Eq [u]) α) z) a

private theorem typed_eq_recovery
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (HT : TypedSource Δ (eqRaw u α z a))
    (R : ScopedTypeRecovery Step Δ (.app (.app (.const ``Eq [u]) α) z) (.forallE A B)) :
    ScopedCompute Step Δ α A := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv (args := [α,z,a]) Ee
  obtain ⟨α₀, z₀, a₀, rfl⟩ : ∃ α₀ z₀ a₀, args = [α₀,z₀,a₀] := by
    have Hlen := congrArg List.length Eargs
    simp only [List.length_map] at Hlen
    cases args with
    | nil => cases Hlen
    | cons x xs => cases xs with
      | nil => cases Hlen
      | cons y ys => cases ys with
        | nil => cases Hlen
        | cons z zs => cases zs with
          | nil => exact ⟨_,_,_,rfl⟩
          | cons => cases Hlen
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at Eargs
  obtain ⟨rfl, rfl, rfl⟩ := Eargs
  obtain ⟨_, hα, hz, _⟩ := eqApp_typings heq hΓ ⟨_, ht⟩
  subst Δ
  exact proofErase_eq_prefix_domain_compute heq hstep hhead hsubst hΓ hα hz R

private theorem typed_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ a) (R : ScopedCompute Step Δ a b) : TypedSource Δ b := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨e', H, E⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R
  exact ⟨Γ, e', T, hΓ, EΓ, H.hasType.2, E⟩

omit [Params] in
private theorem eq_compute
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (R : ScopedCompute Step Δ (eqRaw u α z a) out) :
    ∃ α' z' a', out = eqRaw u α' z' a' ∧ ScopedCompute Step Δ α α' ∧
      ScopedCompute Step Δ z z' ∧ ScopedCompute Step Δ a a' := by
  obtain ⟨args, E, H⟩ := R.const_spine (args := [α,z,a]) hn
  cases H with | cons Rα H =>
  cases H with | cons Rz H =>
  cases H with | cons Ra H =>
  cases H
  exact ⟨_,_,_,E,Rα,Rz,Ra⟩

private theorem eq_carrier_decode_raw
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (H : JointCheck Step Δ kind sa sb) (hm : kind = .compare false)
    (Ea : sa = eqRaw u α z a) (Eb : sb = eqRaw v β w b)
    (HTa : TypedSource Δ sa) (HTb : TypedSource Δ sb)
    (Rα : ScopedCompute Step Δ κ α) (Rβ : ScopedCompute Step Δ κ β) :
    JointCarrierGuard Step Δ κ a b := by
  induction H generalizing u α z a v β w b κ with
  | leaf H =>
    cases hm
    cases H with
    | refl =>
      have EE := Ea.symm.trans Eb
      exact (ProofShape.app.inj EE).2 ▸ JointCheck.carrierChecked (JointCheck.leaf ScopedLeaf.refl)
    | sort | const => cases Ea
  | app HF HX => cases Ea; cases Eb; exact .carrierChecked HX
  | appCarrier R HF HX =>
    cases Ea
    cases Eb
    exact .carrierCompute (Rα.trans (typed_eq_recovery heq hstep hhead hsubst HTa R)) HX
  | compute Ra Rb HC ih =>
    obtain ⟨α', z', a', EA, Rα', _, Ra'⟩ := eq_compute hn (Ea ▸ Ra)
    obtain ⟨β', w', b', EB, Rβ', _, Rb'⟩ := eq_compute hn (Eb ▸ Rb)
    exact .carrierReduce Ra' Rb' (ih hm EA EB (typed_compute hstep HTa Ra)
      (typed_compute hstep HTb Rb) (Rα.trans Rα') (Rβ.trans Rβ'))
  | symm H ih => exact .carrierSymm (ih hm Eb Ea HTb HTa Rβ Rα)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases Ea
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- An inferred Eq comparison yields an endpoint guard at any common ancestor
of its two carriers. The original Eq spines must have actual typed realizations;
primitive computation must preserve Eq heads and interpreted substitution. -/
theorem ProofShape.JointCompare.eq_carrier_decode
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (HTa : TypedSource Δ (.app (.app (.app (.const ``Eq [u]) α) z) a))
    (HTb : TypedSource Δ (.app (.app (.app (.const ``Eq [v]) β) w) b))
    (Rα : ScopedCompute Step Δ κ α) (Rβ : ScopedCompute Step Δ κ β)
    (H : JointCompare Step Δ false
      (.app (.app (.app (.const ``Eq [u]) α) z) a)
      (.app (.app (.app (.const ``Eq [v]) β) w) b)) :
    JointCarrierGuard Step Δ κ a b :=
  eq_carrier_decode_raw heq hstep hhead hsubst hn H rfl rfl rfl HTa HTb Rα Rβ

/-- Either comparison mode between actual Eq propositions reads out a guard at
an arbitrary common supplied carrier. The anchors may differ. -/
theorem proofErase_joint_eq_carrier_decode
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (hw : env.HasType univs Γ w α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (H : JointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α w b))) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b) := by
  have HA := HasType.eqApp heq hu hα hz ha
  have HB := HasType.eqApp heq hu hα hw hb
  have HC := proofErase_joint_types_inferred hstep hΓ HA HB H
  have EA := proofErase_eqProofType heq hu hΓ hα hz ha
  have EB := proofErase_eqProofType heq hu hΓ hα hw hb
  rw [EA, EB] at HC
  exact HC.eq_carrier_decode heq hstep hhead hsubst hn
    ⟨Γ, _, _, hΓ, rfl, HA, EA⟩ ⟨Γ, _, _, hΓ, rfl, HB, EB⟩ .refl .refl

/-- Canonical Eq encodes typed carrier guards without loss, in either comparison
mode. This includes computed carriers and proof-valued endpoints. -/
theorem proofErase_joint_carrier_propositions_iff
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    JointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b) :=
  ⟨proofErase_joint_eq_carrier_decode heq hu hstep hhead hsubst hn hΓ hα hz hz ha hb,
    proofErase_joint_carrier_propositions heq hu hΓ hα hz ha hb⟩

/-- At stage zero, Eq proposition comparison and carrier checking are equivalent
without any global beta-stability, exposure, or recovery-completeness law. -/
theorem proofErase_joint_zero_carrier_propositions_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b) := by
  apply proofErase_joint_carrier_propositions_iff heq hu
    (erased_joint_stage_descent heq hs 0) (erased_joint_stage_head 0) ?_ ?_ hΓ hα hz ha hb
  · intro Δ Δ' a b τ H W
    exact erased_iota_primitive_subst H
  · intro Δ ls args out H
    exact erased_joint_stage_no_rigid heq (heq.rigid henv) hEq 0 H (constHead_mkApps _ _)

/-- Certified joint comparison has the same lossless Eq encoding at its own
relation. Its existing interpreted substitution theorem supplies the only
binder-transport premise required by decoding. -/
theorem proofErase_certified_carrier_propositions_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b) := by
  apply proofErase_joint_carrier_propositions_iff heq hu
    (erased_beta_stable_joint_descent heq hs) erased_beta_stable_joint_head
    (erased_beta_stable_joint_subst heq hs) ?_ hΓ hα hz ha hb
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (heq.rigid henv) hEq
    (erased_beta_stable_joint_into_union H) (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
