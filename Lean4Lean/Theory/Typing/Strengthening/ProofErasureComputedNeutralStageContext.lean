import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointRecursiveNeutral
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Recursive neutral context transport through every finite computed stage

Primitive guards are transported at the preceding stage. The outer computation
induction realizes intermediates and extends the equal contexts under binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private oracle_cons_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointRecursiveNeutral
open private const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

private theorem compute_context_from_primitive
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Γ Γ' e T out k}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      IsDefEqCtx env univs [] Γ Γ' →
      (∀ i, NeutralTypeChange k (contextOracle (proofEraseCtx Γ) i)
        (contextOracle (proofEraseCtx Γ') i)) →
      Step (proofEraseCtx Γ) (proofErase Γ e) out →
      ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ e) out)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, NeutralTypeChange k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ScopedCompute Step (proofEraseCtx Γ') source out := by
  induction R generalizing Γ Γ' e T k with
  | base H =>
    have HH := hprim hΓ ht W (by simpa only [EΓ] using HO)
      (by simpa only [EΓ, Ee] using H)
    simpa only [Ee] using HH
  | beta H => exact .beta H
  | trans R S ihR ihS =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R
    exact .trans (ihR hΓ ht EΓ Ee W HO) (ihS hΓ HE.hasType.2 EΓ EE W HO)
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EΓ Ef W HO) (iha hΓ ha EΓ Ea W HO)
  | proj _ ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 EΓ Em W HO)
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HB := ihb hΓA hb (by simp only [proofEraseCtx, EA, EΓ]) Eb
      (.succ W hA) (oracle_cons_typed hΓ W hA EA HO)
    apply ScopedCompute.lam (ihA hΓ hA EΓ EA W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hA, EA] using HB
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HB := ihB hΓA hB (by simp only [proofEraseCtx, EA, EΓ]) EB
      (.succ W hA) (oracle_cons_typed hΓ W hA EA HO)
    apply ScopedCompute.forallE (ihA hΓ hA EΓ EA W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hA, EA] using HB

private theorem context_telescope {domains : List VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, NeutralTypeChange k (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    IsDefEqCtx env univs [] (domains.reverse ++ Γ) (domains.reverse ++ Γ') ∧
    ∀ i, NeutralTypeChange (k + domains.length)
      (contextOracle (proofEraseCtx (domains.reverse ++ Γ)) i)
      (contextOracle (proofEraseCtx (domains.reverse ++ Γ')) i) := by
  induction domains generalizing Γ Γ' k with
  | nil => exact ⟨W, HO⟩
  | cons A ds ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx ⊢
    obtain ⟨_, u, hA⟩ := OnCtx.of_append hctx
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HE := ih hΓA (.succ W hA) (oracle_cons_typed hΓ W hA rfl HO) hctx
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using HE

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

private theorem Valid.family_guard_neutral_context (V : C.Valid) (heq : env.HasCanonicalEq)
    (hcheck : ∀ {Δ kind a b}, ComputedJointCheck Step Δ kind a b →
      ComputedJointRecursiveNeutralResult Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, NeutralTypeChange k (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ComputedJointCompare Step Δ true))
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ComputedJointCompare Step Δ true))
      Γ' C.data C.levels args program C.layout C.elim := by
  obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
  obtain ⟨S, F, hS, hF, WF⟩ := RecursorData.propElim_wf henv V.registered V.large V.zero
    V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hF.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args
    henv hΓ V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht WF
  obtain ⟨Wext, HOext⟩ := context_telescope hΓ W HO hctx
  have htf := (transportedFamily_typings henv heq WF hctx hps hargs).1
  have hpf := WF.family_prop henv hps hargs
  have HC := hcheck HG hctx htf hpf rfl rfl rfl Wext HOext
  rw [proofErase_defeqCtx hctx Wext htf, proofErase_defeqCtx hctx Wext hpf] at HC
  exact HC

end SingletonPrefixCode

private theorem singleton_neutral_context
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hcheck : ∀ {Δ kind a b}, ComputedJointCheck Step Δ kind a b →
      ComputedJointRecursiveNeutralResult Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, NeutralTypeChange k (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (R : SingletonPrimitiveWith (fun Δ => ComputedJointCompare Step Δ true)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    SingletonPrimitiveWith (fun Δ => ComputedJointCompare Step Δ true)
      (proofEraseCtx Γ') (proofErase Γ e) out := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq hΓ ha ⟨_, ht⟩ hcalc HG
    have HC := V.checkWith heq (erased_computed_joint_family_descent hstep) hΓ hg ⟨_, ht⟩ HG
    have hΓ' := (W.symm henv.ordered).isType
    have ht' := ht.defeqDFC henv W
    have HG' := V.family_guard_neutral_context heq hcheck hΓ W HO hg ⟨_, ht⟩ HG
    have HC' := V.checkWith heq (erased_computed_joint_family_descent hstep) hΓ' hg ⟨_, ht'⟩ HG'
    have hn' : ¬ IsProof Γ' (mkApps (.const C.data.name C.levels) original) :=
      mt (isProof_defeqCtx W).2 hn
    have HE := V.output_eq heq hΓ hg HC hn
    rw [hd] at HE
    have HE' := V.output_eq heq hΓ' hg HC' hn'
    have HS := proofErase_defeqCtx hΓ W (HC.defeq henv hΓ).hasType.2
    rw [HE, HE'] at HS
    rw [← hsrc, proofErase_defeqCtx hΓ W ht, proofErase_const_spine hΓ' ht' hn', HS]
    exact .intro V (by simpa only [List.length_map] using ha) (V.telescope_eq hΓ' hg ⟨_, ht'⟩)
      ((V.guardWith_iff heq hΓ' hg ⟨_, ht'⟩).2 HG')

private theorem prefix_neutral_context
    (heq : env.HasCanonicalEq)
    (hcheck : ∀ {Δ kind a b}, ComputedJointCheck Step Δ kind a b →
      ComputedJointRecursiveNeutralResult Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, NeutralTypeChange k (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (R : ComputedJointPrefixPrimitive Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputedJointPrefixPrimitive Step (proofEraseCtx Γ') (proofErase Γ e) out := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, _, _, Hb⟩ :=
      proofErase_eqRecBeforeMajor_inv hsrc
    rw [← Hα, ← Ha, ← Hb] at HC
    obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have HC' := hcheck HC hΓ ha hb rfl rfl rfl rfl W HO ⟨_, hα⟩ .refl
    rw [Hα, Ha, Hb] at HC'
    exact .intro HC'

/-- Every finite computed stage preserves typed computations under equal
contexts with recursively neutral-related oracle types. The stage induction
transports complete singleton-family and Eq-carrier guards at the preceding
stage; it assumes no unrestricted primitive substitution law. -/
theorem erased_computed_joint_stage_neutral_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, RecursiveNeutralComputeContext (ErasedComputedJointStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Γ' e T out k hΓ ht W HO R
    exact compute_context_from_primitive (erased_computed_joint_stage_descent heq hs 0)
      (fun _ _ _ _ H => .base H) R hΓ ht rfl rfl W HO
  | succ stage ih =>
    have hstep : ErasedScopedPrimitiveDescent (ErasedComputedJointStage D stage) :=
      erased_computed_joint_stage_descent heq hs stage
    have hcheck : ∀ {Δ kind a b}, ComputedJointCheck (ErasedComputedJointStage D stage) Δ kind a b →
        ComputedJointRecursiveNeutralResult (ErasedComputedJointStage D stage) Δ kind a b :=
      fun H => H.recursive_neutral_of_context hstep (erased_computed_joint_stage_head stage) ih
    intro Γ Γ' e T out k hΓ ht W HO R
    apply compute_context_from_primitive (erased_computed_joint_stage_descent heq hs (stage + 1))
      (R := R) (hΓ := hΓ) (ht := ht) (EΓ := rfl) (Ee := rfl) (W := W) (HO := HO)
    intro Γ Γ' e T out k hΓ ht W HO H
    rcases H with H | H | H
    · exact (ih hΓ ht W HO (.base H)).mono (fun H => .inl H)
    · apply ScopedCompute.base
      apply Or.inr
      apply Or.inl
      refine ⟨?_, singleton_neutral_context heq hstep hcheck hΓ ht W HO H.2⟩
      exact ⟨Γ', e, T, (W.symm henv.ordered).isType, rfl, ht.defeqDFC henv W,
        (proofErase_defeqCtx hΓ W ht).symm⟩
    · exact .base (.inr (.inr (prefix_neutral_context heq hcheck hΓ ht W HO H)))

/-- Both complete checking views admit recursive neutral context/carrier
conversion at every finite stage, with no stage increase. -/
theorem ProofShape.ComputedJointCheck.recursive_neutral_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedComputedJointStage D stage) Δ kind a b) :
    ComputedJointRecursiveNeutralResult (ErasedComputedJointStage D stage) Δ kind a b :=
  H.recursive_neutral_of_context (erased_computed_joint_stage_descent heq hs stage)
    (erased_computed_joint_stage_head stage) (erased_computed_joint_stage_neutral_context heq hs stage)

/-- The closed union preserves exact computation outputs under the same
recursive neutral context conversion. Each primitive retains its own finite
stage; the proof does not require a uniform bound on the whole computation. -/
theorem erased_computed_joint_union_neutral_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    RecursiveNeutralComputeContext (ErasedComputedJointUnion D) := by
  intro Γ Γ' e T out k hΓ ht W HO R
  apply compute_context_from_primitive (erased_computed_joint_union_descent heq hs)
    (R := R) (hΓ := hΓ) (ht := ht) (EΓ := rfl) (Ee := rfl) (W := W) (HO := HO)
  intro Γ Γ' e T out k hΓ ht W HO H
  obtain ⟨stage, H⟩ := H
  exact (erased_computed_joint_stage_neutral_context heq hs stage hΓ ht W HO (.base H)).mono
    (fun H => ⟨stage, H⟩)

/-- Complete union checking admits simultaneous recursive neutral context and
carrier conversion. This concerns the closed computed relation itself, not
only a selected finite presentation of a certificate. -/
theorem ProofShape.ComputedJointCheck.recursive_neutral_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedComputedJointUnion D) Δ kind a b) :
    ComputedJointRecursiveNeutralResult (ErasedComputedJointUnion D) Δ kind a b :=
  H.recursive_neutral_of_context (erased_computed_joint_union_descent heq hs)
    erased_computed_joint_union_head (erased_computed_joint_union_neutral_context heq hs)

/-- At any finite stage, a whole carrier guard may change recursively at
neutral leaves when the corresponding actual types are equal. -/
theorem proofErase_computed_joint_stage_recursive_neutral_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HAB : env.IsDefEqU univs Γ A B)
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (H : ComputedJointCarrierGuard (ErasedComputedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (ErasedComputedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ a) (proofErase Γ b) :=
  H.recursive_neutral_stage heq hs hΓ ha hb rfl rfl rfl rfl
    (.refl hΓ) (fun _ => .refl) HAB HT

/-- Recursive neutral conversion of an actual binder preserves complete body
comparison at its original finite stage, including all nested guarded reductions. -/
theorem proofErase_computed_joint_stage_recursive_neutral_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedComputedJointStage D stage) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedComputedJointStage D stage) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have HO : ∀ i, NeutralTypeChange 0 (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (B :: Γ)) i) := by
    intro i
    cases i with
    | zero => exact (HT.liftN (n := 1) (by omega)).mono (by omega)
    | succ i => exact .refl
  have HC := H.recursive_neutral_stage heq hs hΓA ha hb rfl rfl rfl W HO
  rwa [proofErase_defeqCtx hΓA W ha, proofErase_defeqCtx hΓA W hb] at HC

/-- Computation at every finite stage survives the same binder conversion,
with its exact raw output retained. -/
theorem proofErase_computed_joint_stage_compute_neutral_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (he : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D stage) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D stage) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have HO : ∀ i, NeutralTypeChange 0 (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (B :: Γ)) i) := by
    intro i
    cases i with
    | zero => exact (HT.liftN (n := 1) (by omega)).mono (by omega)
    | succ i => exact .refl
  have RC := erased_computed_joint_stage_neutral_context heq hs stage hΓA he W HO R
  rwa [proofErase_defeqCtx hΓA W he] at RC

end Lean4Lean.VEnv.Strengthening
