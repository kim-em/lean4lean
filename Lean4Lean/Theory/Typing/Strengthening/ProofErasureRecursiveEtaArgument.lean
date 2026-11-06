import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelRecursiveTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveFixedReferenceBoundary

/-! # A neutral family with an irreversibly computing eta argument

The recursive type is inside the long eta argument itself. Thus the fixed-leaf
method cannot handle that argument. Typed eta plus neutral-spine recursion
compares all independent level-core reducts of the two actual family types.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]
namespace RecursiveEtaArgument

private def shortType : ProofShape := .app (.bvar 0) (.bvar 1)
private def longType (c : Name) : ProofShape :=
  .app (.bvar 0) (.lam (.const c []) (.app (.bvar 2) (.bvar 0)))

private theorem no_join : ¬ ComputeJoin (ErasedLevelCore D) shortType (longType c) := by
  rintro ⟨out, RL, RR⟩
  obtain ⟨x, rfl, RX⟩ := RL.level_core_bvar_app_inv
  obtain ⟨y, E, RY⟩ := RR.level_core_bvar_app_inv
  cases E
  obtain rfl := RX.level_core_bvar_fixed
  obtain ⟨_, _, E, _, _⟩ := RY.level_core_lam_inv
  cases E

private theorem reduct_no_return
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (R : Compute (ErasedLevelCore EnvironmentCore.definitions) (longType c) out) :
    ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) out mid →
      Compute (ErasedLevelCore EnvironmentCore.definitions) mid out) := by
  obtain ⟨arg, rfl, RA⟩ := R.level_core_bvar_app_inv
  obtain ⟨X, body, rfl, RX, _⟩ := RA.level_core_lam_inv
  intro Hreturn
  apply RecursiveFixedReferenceBoundary.recursive_core_reduct_no_return hcon hc HD RX
  intro mid RM
  obtain ⟨arg', E, HR⟩ := (Hreturn (.app .refl (.lam RM .refl))).level_core_bvar_app_inv
  cases E
  obtain ⟨_, _, E, HR, _⟩ := HR.level_core_lam_inv
  cases E
  exact HR

/-- Two actual types differ by eta inside a neutral family's argument. Every
pair of independent level-core reducts compares, but none joins, and every
reduct of the long type fails ordinary-reduct return. The recursive annotation
is inside the eta leaf, rather than in an independent enclosing Pi component.
The displayed recursive guard also feeds the complete-native-output theorem
whenever these types serve as native references. No general coverage is claimed. -/
theorem typed_neutral_eta_all_reducts
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c)) :
    ∃ Γ N A, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ N (.sort (.succ .zero)) ∧
      env.HasType univs Γ A (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ A N (.sort (.succ .zero)) ∧
      LevelRecursiveGuard EnvironmentCore.definitions false (proofErase Γ N) (proofErase Γ A) ∧
      ∀ left right,
        Compute (ErasedLevelCore EnvironmentCore.definitions) (proofErase Γ N) left →
        Compute (ErasedLevelCore EnvironmentCore.definitions) (proofErase Γ A) right →
        RawCheckedCompare (ErasedLevelCore EnvironmentCore.definitions) false left right ∧
        ¬ ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) left right ∧
        ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) right mid →
          Compute (ErasedLevelCore EnvironmentCore.definitions) mid right) := by
  let C := GuardedEta.domain c
  let F := VExpr.forallE C (.sort .zero)
  let G := VExpr.forallE F (.sort (.succ .zero))
  let Γ := [G, F]
  have hC (Δ : List VExpr) : env.HasType univs Δ C (.sort (.succ .zero)) :=
    GuardedEta.domain_typed hc univs Δ
  have hF (Δ : List VExpr) : env.HasType univs Δ F (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE (hC Δ) (.sort (by trivial))
  have hG (Δ : List VExpr) : env.HasType univs Δ G
      (.sort (.imax (.imax (.succ .zero) (.succ .zero)) (.succ (.succ .zero)))) :=
    .forallE (hF Δ) (.sort (by trivial))
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hF []⟩, _, hG [F]⟩
  have hf : env.HasType univs Γ (.bvar 1) F := .bvar (.succ .zero)
  have hg : env.HasType univs Γ (.bvar 0) G := .bvar .zero
  let e := VExpr.lam C (.app (.bvar 2) (.bvar 0))
  have hη : env.IsDefEq univs Γ e (.bvar 1) F := .eta hf
  let N := VExpr.app (.bvar 0) (.bvar 1)
  let A := VExpr.app (.bvar 0) e
  have hN : env.HasType univs Γ N (.sort (.succ .zero)) := .app hg hf
  have hA : env.HasType univs Γ A (.sort (.succ .zero)) := .app hg hη.hasType.1
  have hAN : env.IsDefEq univs Γ A N (.sort (.succ .zero)) := .appDF hg hη
  have hn := not_isProof_function_to_sort hΓ hf
  have Ef : proofErase Γ (.bvar 1) = .bvar 1 := if_neg hn
  have Eg : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_isProof_function_to_sort hΓ hg)
  have EC : proofErase Γ C = .const c [] := if_neg (not_isProof_of_sort hΓ (hC Γ))
  have Earg : etaArgument (.succ .zero) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  have Ee : proofErase Γ e = .lam (.const c []) (.app (.bvar 2) (.bvar 0)) := by
    have hne := mt (isProof_congr hΓ hη).1 hn
    rw [show proofErase Γ e = .lam _ _ from if_neg hne, EC]
    have EB := proofErase_eta_body hΓ (hC Γ) hf hn
    rw [Ef, Earg] at EB
    exact congrArg (ProofShape.lam (.const c [])) EB
  have EN : proofErase Γ N = shortType := by
    rw [show proofErase Γ N = .app _ _ from if_neg (not_isProof_of_sort hΓ hN), Eg, Ef]
    rfl
  have EA : proofErase Γ A = longType c := by
    rw [show proofErase Γ A = .app _ _ from if_neg (not_isProof_of_sort hΓ hA), Eg, Ee]
    rfl
  have Hη : LevelRecursiveGuard EnvironmentCore.definitions true
      (.lam (.const c []) (.app (.bvar 2) (.bvar 0))) (.bvar 1) := by
    rw [← Ee, ← Ef]
    exact .eta hΓ hη.hasType.1 hf (by rw [Ee, Ef]; exact .boundVar (f := .bvar 1))
  have HG : LevelRecursiveGuard EnvironmentCore.definitions false shortType (longType c) := by
    apply LevelRecursiveGuard.symm
    apply LevelRecursiveGuard.neutral (args := [.lam (.const c []) (.app (.bvar 2) (.bvar 0))])
      (args' := [.bvar 1]) rfl
    intro i hi
    cases i with
    | zero => exact Hη
    | succ i => simp at hi
  refine ⟨Γ, N, A, hΓ, hN, hA, hAN, by rw [EN, EA]; exact HG, ?_⟩
  intro left right RL RR
  rw [EN] at RL
  rw [EA] at RR
  refine ⟨HG.forward EnvironmentCore.sound (EnvironmentCore.levelCompatible hcon) hcon
    (EnvironmentCore.typed_level_core_confluence hcon) RL RR, ?_, reduct_no_return hcon hc HD RR⟩
  rintro ⟨out, HL, HR⟩
  exact no_join ⟨out, RL.trans HL, RR.trans HR⟩

/-- Constant expansions and independent final tails also preserve the neutral
eta comparison. Every complete stage-zero tail pair still fails core joining,
and the long side still has no returning reference among its outputs. -/
theorem typed_neutral_eta_all_stage_zero_tails
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c)) :
    ∃ Γ N A, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ N (.sort (.succ .zero)) ∧
      env.HasType univs Γ A (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ A N (.sort (.succ .zero)) ∧
      ∀ left right,
        ScopedCompute (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) (proofErase Γ N) left →
        ScopedCompute (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) (proofErase Γ A) right →
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) false left right ∧
        ¬ ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) left right ∧
        ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) right mid →
          Compute (ErasedLevelCore EnvironmentCore.definitions) mid right) := by
  obtain ⟨Γ, N, A, hΓ, hN, hA, hAN, HG, Hbase⟩ := typed_neutral_eta_all_reducts hcon hc HD
  refine ⟨Γ, N, A, hΓ, hN, hA, hAN, ?_⟩
  intro left right RL RR
  have hcl : TypedCoreConfluence (ErasedLevelCore EnvironmentCore.definitions) :=
    EnvironmentCore.typed_level_core_confluence hcon
  have JL := stage_zero_compute_level_join heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon (EnvironmentCore.typed_core_confluence hcon) hΓ hN RL
  have JR := stage_zero_compute_level_join heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon (EnvironmentCore.typed_core_confluence hcon) hΓ hA RR
  have Hcmp := HG.of_joins EnvironmentCore.sound (EnvironmentCore.levelCompatible hcon) hcon hcl JL.symm JR.symm
  obtain ⟨l, HL, EL⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_stage_descent heq EnvironmentCore.sound 0) hΓ hN rfl rfl RL
  obtain ⟨r, HR, ER⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_stage_descent heq EnvironmentCore.sound 0) hΓ hA rfl rfl RR
  refine ⟨(Hcmp.scoped (fun H => .base (.inl H))).joint.computed, ?_, ?_⟩
  · intro HJ
    have HM := (EL ▸ JL).trans_typed hcl hΓ HL.hasType.2 (EL ▸ HJ)
    exact (Hbase _ _ .refl .refl).2.1 ((ER ▸ HM).trans_typed hcl hΓ HR.hasType.2 (ER ▸ JR.symm))
  · intro Hreturn
    have RP : Compute (ErasedLevelCore EnvironmentCore.definitions) (proofErase Γ A) right := by
      simpa only [ER] using proofErase_returning_core_join_return EnvironmentCore.sound
        (EnvironmentCore.levelCompatible hcon) hcon hΓ HR.hasType.2 (ER ▸ Hreturn) (ER ▸ JR)
    exact (Hbase _ _ .refl RP).2.2 Hreturn

omit [Params] in
/-- The recursive eta-argument example occurs in an actual well-formed
canonical-Eq extension. All concrete-pattern and definition premises are
proved from the installed declaration; every stage-zero tail is still allowed. -/
theorem canonical_recursive_eta_argument
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) (U : Nat) :
    ∃ hE : (GuardedEta.extended base c).WF,
      (GuardedEta.extended base c).HasCanonicalEq ∧
      (letI := hE.params U
       ∃ Γ N A, OnCtx Γ ((GuardedEta.extended base c).IsType U) ∧
         (GuardedEta.extended base c).HasType U Γ N (.sort (.succ .zero)) ∧
         (GuardedEta.extended base c).HasType U Γ A (.sort (.succ .zero)) ∧
         (GuardedEta.extended base c).IsDefEq U Γ A N (.sort (.succ .zero)) ∧
         ∀ left right,
           ScopedCompute (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
             (proofEraseCtx Γ) (proofErase Γ N) left →
           ScopedCompute (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
             (proofEraseCtx Γ) (proofErase Γ A) right →
           ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
             (proofEraseCtx Γ) false left right ∧
           ¬ ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) left right ∧
           ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) right mid →
             Compute (ErasedLevelCore EnvironmentCore.definitions) mid right)) := by
  let hE := GuardedEta.extended_wf hbase hfresh
  have hEq := GuardedEta.extended_canonicalEq heq hfresh
  refine ⟨hE, hEq, ?_⟩
  letI := hE.params U
  apply typed_neutral_eta_all_stage_zero_tails (c := c) hEq (fun H => H)
  · change (GuardedEta.extended base c).constants c = some (GuardedEta.declaration c).toVConstant
    simp [GuardedEta.extended, GuardedEta.stub, VEnv.addDefEq]
  · exact guarded_definition hE U

end RecursiveEtaArgument
end Lean4Lean.VEnv.Strengthening
