import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecursiveNeutral
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment

/-! # Full Box guards with recursively changing field types

The actual Box projection recipe is its type parameter. Recursive neutral
transport therefore handles function-valued fields, while computation of the
parameter is simulated on the target side. All carrier constructors remain
available; neither a field join nor ordinary field comparison is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BoxCarrierAlignment.projection_recipe BoxCarrierAlignment.family_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
open private const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private carrier_raw infer_raw
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private native_walk_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params]
namespace BoxCarrierAlignment

private theorem erase_box
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort (.succ .zero))) :
    proofErase Γ (.app (.const family []) A) = .app (.const family []) (proofErase Γ A) := by
  have hF := BoxCarrierAlignment.family_typed (Γ := Γ) hc
  rw [show proofErase Γ (.app (.const family []) A) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ (hF.app hA)),
    show proofErase Γ (.const family []) = .const family [] from
    if_neg (not_isProof_function_to_sort hΓ hF)]

private theorem recursive_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (H : JointCheck Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort (.succ .zero)))
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (EΓ : proofEraseCtx Γ = Δ) (Ex : proofErase Γ x = a) (Ey : proofErase Γ y = b)
    (E : JointCheckKind.carrier (.app (.const family []) (proofErase Γ A)) = kind) :
    JointCarrierGuard Step Δ (.app (.const family []) (proofErase Γ B)) a b := by
  induction H generalizing Γ A B x y with
  | carrierChecked H => exact .carrierChecked H
  | carrierFunction => cases E
  | carrierSubsingleton HS =>
    cases E
    generalize EC : ProofShape.app (.const family []) (proofErase Γ A) = carrier at HS
    cases HS with
    | unit hi' hx' hf' hp' =>
      obtain ⟨rfl, rfl, _⟩ := const_spine_inj (show mkApps (.const family []) [proofErase Γ A] = _ from EC)
      cases henv.ordered.projections_unique hi hi'
      omega
    | forallE => cases EC
  | carrierSymm H ih => exact .carrierSymm (ih hΓ HAB HT hy hx EΓ Ey Ex E)
  | carrierReduce RA RB H ih =>
    obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize hstep hΓ hx EΓ Ex RA
    obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_realize hstep hΓ hy EΓ Ey RB
    exact .carrierReduce RA RB (ih hΓ HAB HT HX.hasType.2 HY.hasType.2 EΓ EX EY E)
  | carrierCompute R H ih =>
    cases E
    have RR : ScopedCompute Step _ (mkApps (.const family []) [proofErase Γ A]) _ := R
    obtain ⟨ps', Eout, RP⟩ := RR.const_spine hinert
    cases RP with
    | cons RA RT =>
      cases RT
      obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.1 EΓ rfl RA
      obtain ⟨rawB', RB, HT'⟩ := HT.compute hstep hhead hsubst hΓ HAB rfl rfl (EΓ ▸ RA)
      obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.2 rfl rfl RB
      have HF := BoxCarrierAlignment.family_typed (Γ := Γ) hc
      have hxx := (IsDefEq.appDF HF HA).defeq hx
      have hyy := (IsDefEq.appDF HF HA).defeq hy
      have H' := ih hΓ ((HA.symm.trans HAB).trans HB) (by rwa [← EA, ← EB] at HT')
        hxx hyy EΓ Ex Ey (by rw [EA, Eout]; rfl)
      rw [EB] at H'
      exact .carrierCompute (.app .refl (EΓ ▸ RB)) H'
  | carrierIntro hi' hidx hlen hadm HF =>
    obtain ⟨rfl, rfl, rfl⟩ := const_spine_inj
      (show mkApps (.const family []) [proofErase Γ A] = _ from JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    exact .carrierIntro hi hidx (show [proofErase Γ B].length = info.nparams by simp [hp]) hadm HF
  | carrierNested hi' hidx hlen hadm PT HF ih =>
    obtain ⟨rfl, rfl, rfl⟩ := const_spine_inj
      (show mkApps (.const family []) [proofErase Γ A] = _ from JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    have HE := carrier_raw hstep (.carrierNested hi hidx hlen hadm PT HF) hΓ hx hy EΓ
      (erase_box hc hΓ HAB.hasType.1) Ex Ey
    have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi
      (show [A].length = info.nparams by simp [hp]) hidx hx).2 hadm
    apply JointCheck.carrierNested hi hidx (show [proofErase Γ B].length = info.nparams by simp [hp]) hadm PT
    intro j hj hn
    have hj0 : j = 0 := by omega
    subst j
    obtain ⟨F, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexp hj
    have hpa : ¬ IsProof Γ (.proj family 0 x) := fun H =>
      hn (StructureReplay.ProofField.of_projection hΓ hi
        (show [A].length = info.nparams by simp [hp]) hj hexp H)
    have hpb : ¬ IsProof Γ (.proj family 0 y) := by
      rintro ⟨P, hpP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hpP), hP⟩
    obtain ⟨hj', F', hiaF, EF⟩ := proofErase_projection_at_recovered_family hΓ hi PT hia hpa (show env.HasType univs Γ x (VExpr.mkApps (.const family []) [A]) from hx)
    have EF'' : proofErase Γ F' = projectionType family info _ 0 hj' [proofErase Γ A]
        (proofErase Γ x) := by
      simpa only [projectionType, hp, List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_nil] using EF
    have EF' := EF''.trans (BoxCarrierAlignment.projection_recipe hp hf hshape PT hj')
    obtain ⟨_, hF'⟩ := hiaF.isType henv hΓ
    have HFA := infer_raw hstep (JointCheck.leaf ScopedLeaf.refl) hΓ hF' HAB.hasType.1
      rfl EF' rfl (not_isProof_of_sort hΓ hF') (not_isProof_of_sort hΓ HAB.hasType.1)
    have hiaA := HFA.defeq hiaF
    have hibA := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaA)
    have Epa := (show proofErase Γ (.proj family 0 x) = .proj family 0 (proofErase Γ x) from
      if_neg hpa).trans (congrArg (ProofShape.proj family 0) Ex)
    have Epb := (show proofErase Γ (.proj family 0 y) = .proj family 0 (proofErase Γ y) from
      if_neg hpb).trans (congrArg (ProofShape.proj family 0) Ey)
    have HG := HF 0 hj hn
    rw [BoxCarrierAlignment.projection_recipe hp hf hshape PT] at HG
    have HG' := proofErase_joint_recursive_neutral_carrier hstep hhead hsubst hΓ hiaA hibA HAB.toU HT
      (by simpa only [EΓ, Epa, Epb] using HG)
    simpa only [EΓ, Epa, Epb, BoxCarrierAlignment.projection_recipe hp hf hshape PT] using HG'
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Every typed Box guard transports when the parameter types are actually
equal and recursively neutral-related. Its field may itself be a function
with changed input domains; nested checking is preserved rather than replaced
by an assumed ordinary projection comparison. -/
theorem recursive_guard_reindex
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort (.succ .zero)))
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (H : JointCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.app (.const family []) A)) (proofErase Γ x) (proofErase Γ y)) :
    JointCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.app (.const family []) B)) (proofErase Γ x) (proofErase Γ y) := by
  rw [erase_box hc hΓ HAB.hasType.1] at H
  rw [erase_box hc hΓ HAB.hasType.2]
  exact recursive_guard hstep hhead hsubst hinert hi hp hf hshape hc H hΓ HAB HT hx hy rfl rfl rfl rfl

/-- Certified Box guards transport at recursively related field types. The
registered family is excluded from explicit unfolding, and all other
primitive requirements are discharged by the proved certified interfaces. -/
theorem certified_recursive_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort (.succ .zero)))
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const family []) A)) (proofErase Γ x) (proofErase Γ y)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const family []) B)) (proofErase Γ x) (proofErase Γ y) := by
  apply recursive_guard_reindex (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) ?_ hi hp hf hshape hc hΓ HAB HT hx hy H
  intro Δ args out R
  exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD
    (erased_beta_stable_joint_into_union R) (constHead_mkApps _ _)

/-- A native proposition-valued prefix consumes the converted Box guard.
The target recovery and both target argument typings are derived; only the
source endpoint typings, the recursive parameter change, and the literal
target declaration walk are supplied. -/
theorem native_recursive_propositions
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort (.succ .zero)))
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const family []) A)) (proofErase Γ x) (proofErase Γ y))
    (hc' : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) params
      (.forallE (.app (.const family []) B) (.sort .zero))) :
    let f := VExpr.mkApps (.const c ls) params
    env.HasType univs Γ (.app f x) (.sort .zero) ∧
      env.HasType univs Γ (.app f y) (.sort .zero) ∧
      JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  have hfn := native_walk_typing (HasType.const hc' hw hl) HW
  have hn := not_isProof_function_to_sort hΓ hfn
  have RF := proofErase_const_native_recovery (Step := ErasedBetaStableJoint D) hΓ hc' hw hl HW hn
  obtain ⟨_, hPi⟩ := hfn.isType henv hΓ
  rw [show proofErase Γ (.forallE (.app (.const family []) B) (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RF
  have HG := certified_recursive_guard heq hs hD hi hp hf hshape hc hΓ HAB HT hx hy H
  have HE := IsDefEq.appDF (BoxCarrierAlignment.family_typed (Γ := Γ) hc) HAB
  have hL := hfn.app (HE.defeq hx)
  have hR := hfn.app (HE.defeq hy)
  refine ⟨hL, hR, ?_⟩
  rw [show proofErase Γ (.app (VExpr.mkApps (.const c ls) params) x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hL),
    show proofErase Γ (.app (VExpr.mkApps (.const c ls) params) y) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hR)]
  exact .appCarrier RF (.leaf .refl) HG

end BoxCarrierAlignment
end Lean4Lean.VEnv.Strengthening
