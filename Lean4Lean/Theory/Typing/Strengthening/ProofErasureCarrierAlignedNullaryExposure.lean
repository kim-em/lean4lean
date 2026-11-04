import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedDomainExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnion

/-! # Nullary family exposure and selected unit-carrier guards

At type endpoints, aligned checking against a primitive-inert nullary constant
exposes that constant on the other side. No parameter-spine or arbitrary
function-extensionality claim is made. This transfers a nullary unit guard to a
newly recovered domain, with the domain comparison retained by Pi exposure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private sort_not_lam sort_not_constructor from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params]

private def ConstantExposurePair (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (family : Name) (Δ : List ProofShape) (sa sb : ProofShape) : Prop :=
  (∀ ls, sa = .const family ls → ∃ ls', ScopedCompute Step Δ sb (.const family ls')) ∧
  (∀ ls, sb = .const family ls → ∃ ls', ScopedCompute Step Δ sa (.const family ls'))

private theorem computed_constant_pair
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (H : ComputedJointCheck Step Δ kind sa sb) (hm : kind = .compare false) :
    ConstantExposurePair Step family Δ sa sb := by
  induction H with
  | leaf H =>
    cases hm
    cases H with
    | refl => exact ⟨fun ls E => ⟨ls, E ▸ .refl⟩, fun ls E => ⟨ls, E ▸ .refl⟩⟩
    | sort => constructor <;> intro ls E <;> cases E
    | const H =>
      constructor
      · intro ls E; cases E; exact ⟨_, .refl⟩
      · intro ls E; cases E; exact ⟨_, .refl⟩
  | compute RA RB H ih =>
    constructor
    · intro ls E
      have EA := scoped_normal_fixed (Step := Step) (a := .const family ls) (E ▸ RA) (fun _ => ⟨fun _ H => hn H, trivial⟩)
      obtain ⟨ls', R⟩ := (ih hm).1 ls EA
      exact ⟨ls', RB.trans R⟩
    · intro ls E
      have EB := scoped_normal_fixed (Step := Step) (a := .const family ls) (E ▸ RB) (fun _ => ⟨fun _ H => hn H, trivial⟩)
      obtain ⟨ls', R⟩ := (ih hm).2 ls EB
      exact ⟨ls', RA.trans R⟩
  | symm H ih => exact (ih hm).symm
  | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted | etaLams =>
    constructor <;> intro ls E <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

private theorem computed_constants
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (H : ComputedJointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    ConstantExposurePair Step family Δ sa sb := by
  have HI := proofErase_computed_joint_types_inferred hstep hΓ ha hb
    (by simpa only [EΓ, Ea, Eb] using H)
  rw [EΓ, Ea, Eb] at HI
  exact computed_constant_pair hn HI rfl

private theorem carrier_constants
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (RA : ScopedTypeRecovery Step Δ sa rawC)
    (HC : ComputedJointCarrierGuard Step Δ rawC sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    ConstantExposurePair Step family Δ sa sb := by
  obtain ⟨C, haC, EC⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) ha EΓ (by simpa only [List.length_nil, ProofShape.liftN_zero, Ea] using RA)
  simp only [List.length_nil, ProofShape.liftN_zero] at EC
  have H := proofErase_computed_carrier_types_checked hstep hΓ ha hb (.inl haC)
    (by simpa only [EΓ, Ea, Eb, EC] using HC)
  exact computed_constants hstep hn (by simpa only [EΓ, Ea, Eb] using H) hΓ ha hb EΓ Ea Eb

private theorem recovered_constants
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (H : CarrierRecoveredCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    ConstantExposurePair Step family Δ sa sb := by
  induction H generalizing Γ a b u v with
  | base H => exact computed_constants hstep hn H hΓ ha hb EΓ Ea Eb
  | recovered RA RB HC => exact carrier_constants hstep hn RA HC hΓ ha hb EΓ Ea Eb
  | app | proj | forallE => constructor <;> intro ls E <;> cases E
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro ls E
      have EF := scoped_normal_fixed (Step := Step) (a := .const family ls) (E ▸ RA) (fun _ => ⟨fun _ H => hn H, trivial⟩)
      obtain ⟨ls', R⟩ := IH.1 ls EF
      exact ⟨ls', RB.trans R⟩
    · intro ls E
      have EF := scoped_normal_fixed (Step := Step) (a := .const family ls) (E ▸ RB) (fun _ => ⟨fun _ H => hn H, trivial⟩)
      obtain ⟨ls', R⟩ := IH.2 ls EF
      exact ⟨ls', RA.trans R⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

private theorem aligned_constants
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    ConstantExposurePair Step family Δ sa sb := by
  induction H generalizing Γ a b u v with
  | base H => exact recovered_constants hstep hn H hΓ ha hb EΓ Ea Eb
  | commonCarrier RA HC | aligned RA RB HT HC ihT => exact carrier_constants hstep hn RA HC hΓ ha hb EΓ Ea Eb
  | recover RA RB HT HC ihT ihC => exact ihC hΓ ha hb EΓ Ea Eb
  | app | proj | forallE | forallSorted => constructor <;> intro ls E <;> cases E
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_not_lam hΓ ha Ea).elim
  | etaBodyR => exact (sort_not_lam hΓ hb Eb).elim
  | structFields hi hx hp hf => exact (sort_not_constructor hΓ ha hi hx hp hf Ea).elim
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro ls E
      have EF := scoped_normal_fixed (Step := Step) (a := .const family ls) (E ▸ RA) (fun _ => ⟨fun _ H => hn H, trivial⟩)
      obtain ⟨ls', R⟩ := IH.1 ls EF
      exact ⟨ls', RB.trans R⟩
    · intro ls E
      have EF := scoped_normal_fixed (Step := Step) (a := .const family ls) (E ▸ RB) (fun _ => ⟨fun _ H => hn H, trivial⟩)
      obtain ⟨ls', R⟩ := IH.2 ls EF
      exact ⟨ls', RA.trans R⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

/-- Typed aligned comparison exposes a primitive-inert nullary type constant.
This theorem does not assert exposure of parameterized constant spines. -/
theorem proofErase_carrier_aligned_nullary_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .const family ls) :
    ∃ ls', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (.const family ls') :=
  (aligned_constants hstep hn H hΓ ha hb rfl rfl rfl).1 ls Ea

/-- A nullary unit-carrier guard transfers along an actual aligned type
comparison. Only the selected type computes to the exposed family; a literal
join with the old type and its universe arguments is unnecessary. -/
theorem proofErase_carrier_aligned_nullary_unit_target
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .const family ls) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ b) x y := by
  obtain ⟨ls', R⟩ := proofErase_carrier_aligned_nullary_exposure hstep hn hΓ ha hb H Ea
  exact .carrierCompute R (.carrierSubsingleton (.unit (ps := []) hi hx hf hp.symm))

/-- A native type aligned with an assigned Pi supplies its selected Pi and a
nullary unit argument guard together. This is a constructive carrier-selection
case, not general native recovery or carrier re-synthesis. -/
theorem proofErase_carrier_aligned_recovered_nullary_unit_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hfields : info.numFields = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) ∧
      ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ D) x y := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_carrier_aligned_recovered_pi_domain hstep hhead hΓ hf R H
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hPi'⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hPi'.forallE_inv henv
  exact ⟨D, C, hfDC, RD, HD,
    proofErase_carrier_aligned_nullary_unit_target hstep hn hi hx hfields hp hΓ hA hD HD EA⟩

/-- The selected nullary unit guard closes the computed application rule.
Function comparison, initial native recovery, and native-to-assigned type
comparison remain explicit certificates; no global re-synthesis premise is used. -/
theorem proofErase_carrier_aligned_application_nullary_unit
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hfields : info.numFields = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g) :
    ComputedJointCompare Step (proofEraseCtx Γ) resultMode
      (.app (proofErase Γ f) x) (.app g y) := by
  obtain ⟨_, _, _, RD, _, HG⟩ := proofErase_carrier_aligned_recovered_nullary_unit_guard
    hstep hhead hn hi hx hfields hp hΓ hf R H EA (x := x) (y := y)
  exact .appCarrier RD HF HG

/-- The selected-domain application certificate also checks actual erasures,
including the case where both applications erase to proof markers. All actual
arguments are typed at the assigned nullary unit domain. -/
theorem proofErase_carrier_aligned_typed_application_nullary_unit
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hindices : info.nindices = 0)
    (hfields : info.numFields = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls)
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCompare Step (proofEraseCtx Γ) resultMode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have HFG := ((proofErase_computed_joint_compare_reflect hstep hΓ hf hg HF).1
    (by obtain ⟨u, hPi⟩ := hf.isType henv hΓ; exact .refl ⟨_, hPi⟩)).of_l henv hΓ hf
  have HG : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ x) (proofErase Γ y) := by
    rw [EA]
    exact .carrierSubsingleton (.unit (ps := []) hi hindices hfields hp.symm)
  have HXY := proofErase_computed_joint_carrier_reflect hstep hΓ hx hy HG
  have HE := HFG.appDF HXY
  by_cases hproof : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hproof,
      proofErase_eq_proof.2 (isProof_of_common_type hΓ HE.hasType.1 HE.hasType.2 hproof)]
    exact .leaf .refl
  · have hproof' : ¬ IsProof Γ (.app g y) :=
      fun hp' => hproof (isProof_of_common_type hΓ HE.hasType.2 HE.hasType.1 hp')
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hproof,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hproof']
    exact proofErase_carrier_aligned_application_nullary_unit
      hstep hhead hn hi hindices hfields hp hΓ hf R H EA HF

/-- Recovered-carrier stages introduce no primitive at a rigid head excluded
from the definition table. This uses the registered code of singleton and Eq
prefixes, independently of their recursively enlarged comparison guards. -/
theorem erased_carrier_recovered_stage_no_rigid (heq : env.HasCanonicalEq)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    ∀ stage {Δ a b}, ErasedCarrierRecoveredStage D stage Δ a b → a.constHead = some family → False := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_no_rigid hc hD
  | succ stage ih =>
    intro Δ a b H hh
    rcases H with H | H | H
    · exact ih H hh
    · cases H.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        exact V.not_rigid (hn ▸ hc)
    · cases H with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj hh)

/-- Rigid-head exclusion holds at every finite stage in the recovered union. -/
theorem erased_carrier_recovered_union_no_rigid (heq : env.HasCanonicalEq)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (H : ErasedCarrierRecoveredUnion D Δ a b) (hh : a.constHead = some family) : False := by
  obtain ⟨stage, H⟩ := H
  exact erased_carrier_recovered_stage_no_rigid heq hc hD stage H hh

/-- In the concrete recovered-carrier union, rigid nullary unit domains obtain
their selected argument guards from native aligned type comparison. All primitive
soundness, head, and inertness interfaces are discharged from environment facts. -/
theorem proofErase_carrier_aligned_union_nullary_unit_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hrigid : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hfields : info.numFields = 0) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = .const family ls) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ A') (proofErase (A' :: Γ) B')) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ A') ∧
      ComputedJointCarrierGuard (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ A') x y :=
  proofErase_carrier_aligned_recovered_nullary_unit_guard
    (erased_carrier_recovered_union_descent heq hs) erased_carrier_recovered_union_head
    (fun H => erased_carrier_recovered_union_no_rigid heq hrigid hD H rfl)
    hi hx hfields hp hΓ hf R H EA

end Lean4Lean.VEnv.Strengthening
