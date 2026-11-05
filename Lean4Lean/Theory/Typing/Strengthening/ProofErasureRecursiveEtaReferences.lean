import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativeReferences
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveFixedReferenceBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiTelescopeReification

/-! # Recursive eta references beyond return and common reduction

Two functions with a common assigned type have native types Pi D (Pi N Sort 1)
and Pi D (Pi A Sort 1), where D unfolds recursively and N/A differ by eta in a
neutral argument. All complete stage-zero outputs compare, although no pair
joins in the level core and no output can return from every ordinary reduct.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]
namespace RecursiveEtaReferences
open private context native assigned nativeRaw assignedRaw context_wf native_typed types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private raw_no_join
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary

private theorem shifted_normal :
    NormalSyntax (ErasedIotaPrimitive D) (nativeRaw.liftN 1) ∧
    NormalSyntax (ErasedIotaPrimitive D) (assignedRaw.liftN 1) := by
  have hv (i) : NormalSyntax (ErasedIotaPrimitive D) (.bvar i) :=
    ⟨fun _ H => erased_iota_primitive_head H, trivial⟩
  have hs : NormalSyntax (ErasedIotaPrimitive D) (.sort .zero) :=
    ⟨fun _ H => erased_iota_primitive_head H, trivial⟩
  have happ (i) {a} (H : NormalSyntax (ErasedIotaPrimitive D) a) :
      NormalSyntax (ErasedIotaPrimitive D) (.app (.bvar i) a) :=
    ⟨fun _ H => erased_iota_primitive_head H, (fun _ _ H => nomatch H), hv i, H⟩
  exact ⟨happ 2 (hv 3), happ 2 ⟨(fun _ H => erased_iota_primitive_head H), hs, happ 4 (hv 0)⟩⟩

private theorem shifted_compare :
    RawCheckedCompare (ErasedLevelCore D) false (nativeRaw.liftN 1) (assignedRaw.liftN 1) :=
  RawCheckedCompare.symm (.app (.base .refl) (.base (.etaL (.boundVar (f := ProofShape.bvar 3)))))

private theorem shifted_no_join :
    ¬ ComputeJoin (ErasedLevelCore D) (nativeRaw.liftN 1) (assignedRaw.liftN 1) := by
  intro H
  have H' := H.subst (fun H => erased_level_core_subst H) (σ := ProofShape.Subst.one .proof)
  simp only [ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] at H'
  obtain ⟨out, RL, RR⟩ := H'
  exact raw_no_join (proofErase_expanded_pure_common_join
    (Δ := []) (by intro a ha; cases ha) (by trivial) (by trivial)
    (RL.scoped (fun H => .base ⟨0, .inl H⟩))
    (RR.scoped (fun H => .base ⟨0, .inl H⟩)))

private theorem pi_reduct_no_return
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (R : Compute (ErasedLevelCore EnvironmentCore.definitions) (.forallE (.const c []) B) out) :
    ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) out mid →
      Compute (ErasedLevelCore EnvironmentCore.definitions) mid out) := by
  obtain ⟨X, Y, rfl, RX, _⟩ := R.pi_parts (fun H => erased_level_core_no_pi H)
  intro Hreturn
  apply RecursiveFixedReferenceBoundary.recursive_core_reduct_no_return hcon hc HD RX
  intro mid RM
  obtain ⟨_, _, E, HR, _⟩ := (Hreturn (.forallE RM .refl)).pi_parts
    (fun H => erased_level_core_no_pi H)
  cases E
  exact HR

private theorem native_no_return
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (Rref : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ e) (.forallE (.const c []) B))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) out mid →
      Compute (ErasedLevelCore EnvironmentCore.definitions) mid out) := by
  intro Hreturn
  obtain ⟨P, heP, EP⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq EnvironmentCore.sound 0) hΓ he RN
  obtain ⟨_, hP⟩ := heP.isType henv hΓ
  have HJ := stage_zero_native_outputs_join heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence hcon) hΓ he Rref RN
  have RC : Compute (ErasedLevelCore EnvironmentCore.definitions) (.forallE (.const c []) B) out := by
    simpa only [EP] using proofErase_returning_core_join_return EnvironmentCore.sound
      (EnvironmentCore.levelCompatible hcon) hcon hΓ hP (EP ▸ Hreturn) (EP ▸ HJ)
  exact pi_reduct_no_return hcon hc HD RC Hreturn

/-- Recursive references genuinely exceed both common-reduct and returning
reference methods. The two functions have one actual assigned type and native
recoveries. Every pair of complete stage-zero native outputs compares, has no
common level-core reduct, and neither output can return from all its ordinary
reducts. This is a concrete fragment witness, not universal guard coverage. -/
theorem all_native_outputs_compare_without_join_or_return
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c)) :
    ∃ Γ f g T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f T ∧ env.HasType univs Γ g T ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g) ∧
      (∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ f) out) ∧
      (∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ g) out) ∧
      ∀ left right,
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) (proofErase Γ f) left →
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) (proofErase Γ g) right →
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
          (proofEraseCtx Γ) false left right ∧
        ¬ ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) left right ∧
        (¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) left mid →
          Compute (ErasedLevelCore EnvironmentCore.definitions) mid left)) ∧
        ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) right mid →
          Compute (ErasedLevelCore EnvironmentCore.definitions) mid right) := by
  let Γ := context []
  let C := GuardedEta.domain c
  have hΓ : OnCtx Γ (env.IsType univs) := context_wf trivial
  have hC : env.HasType univs Γ C (.sort (.succ .zero)) := GuardedEta.domain_typed hc univs Γ
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, _, hC⟩
  have hN : env.HasType univs (C :: Γ) native.lift (.sort (.succ .zero)) :=
    native_typed.weakN henv Ctx.LiftN.one
  have hA : env.HasType univs (C :: Γ) assigned.lift (.sort (.succ .zero)) :=
    types_equal.hasType.1.weakN henv Ctx.LiftN.one
  have hE : env.IsDefEq univs (C :: Γ) assigned.lift native.lift (.sort (.succ .zero)) :=
    types_equal.weakN henv Ctx.LiftN.one
  obtain ⟨EN, EA⟩ := erasures (Γ := []) (by trivial)
  have EN' : proofErase (C :: Γ) native.lift = nativeRaw.liftN 1 := by
    rw [proofErase_liftN hΓ hΓC Ctx.LiftN.one native_typed, EN]
  have EA' : proofErase (C :: Γ) assigned.lift = assignedRaw.liftN 1 := by
    rw [proofErase_liftN hΓ hΓC Ctx.LiftN.one types_equal.hasType.1, EA]
  have EC : proofErase Γ C = .const c [] := if_neg (not_isProof_of_sort hΓ hC)
  let b : VExpr := .lam native.lift (.sort .zero)
  let d : VExpr := .lam assigned.lift (.sort .zero)
  let T : VExpr := .forallE assigned.lift (.sort (.succ .zero))
  have hb : env.HasType univs (C :: Γ) b T :=
    (IsDefEq.forallEDF hE.symm (HasType.sort (by trivial))).defeq
      (HasType.lam hN (HasType.sort (by trivial)))
  have hd : env.HasType univs (C :: Γ) d T := .lam hA (.sort (by trivial))
  have hΓN : OnCtx (native.lift :: C :: Γ) (env.IsType univs) := ⟨hΓC, _, hN⟩
  have hΓA : OnCtx (assigned.lift :: C :: Γ) (env.IsType univs) := ⟨hΓC, _, hA⟩
  have Eb : proofErase (C :: Γ) b = .lam (nativeRaw.liftN 1) (.sort .zero) := by
    rw [show proofErase (C :: Γ) b = .lam _ _ from if_neg (not_isProof_function_to_sort hΓC hb), EN',
      show proofErase (native.lift :: C :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓN (HasType.sort (by trivial)))]
  have Ed : proofErase (C :: Γ) d = .lam (assignedRaw.liftN 1) (.sort .zero) := by
    rw [show proofErase (C :: Γ) d = .lam _ _ from if_neg (not_isProof_function_to_sort hΓC hd), EA',
      show proofErase (assigned.lift :: C :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))]
  let f : VExpr := .lam C b
  let g : VExpr := .lam C d
  have hf : env.HasType univs Γ f (.forallE C T) := .lam hC hb
  have hg : env.HasType univs Γ g (.forallE C T) := .lam hC hd
  have hnf : ¬ IsProof Γ f := not_isProof_telescope_to_sort (ds := [C, assigned.lift]) hΓ hf
  have Ef : proofErase Γ f = .lam (.const c []) (.lam (nativeRaw.liftN 1) (.sort .zero)) := by
    rw [show proofErase Γ f = .lam _ _ from if_neg hnf, EC, Eb]
  have Eng : ¬ IsProof Γ g := not_isProof_telescope_to_sort (ds := [C, assigned.lift]) hΓ hg
  have Eg : proofErase Γ g = .lam (.const c []) (.lam (assignedRaw.liftN 1) (.sort .zero)) := by
    rw [show proofErase Γ g = .lam _ _ from if_neg Eng, EC, Ed]
  let L := ProofShape.forallE (.const c []) (.forallE (nativeRaw.liftN 1) (.sort (.succ .zero)))
  let R := ProofShape.forallE (.const c []) (.forallE (assignedRaw.liftN 1) (.sort (.succ .zero)))
  have RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ f) L := by
    rw [Ef]; exact .lam (.lam (.sort (by trivial)))
  have RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ g) R := by
    rw [Eg]; exact .lam (.lam (.sort (by trivial)))
  have Hleaf : LevelRecursiveGuard EnvironmentCore.definitions false (nativeRaw.liftN 1) (assignedRaw.liftN 1) := by
    rw [← EN', ← EA']
    exact .fixed hΓC hN hA (by rw [EN']; exact shifted_normal.1.fixed) (by rw [EA']; exact shifted_normal.2.fixed)
      (by rw [EN', EA']; exact shifted_compare)
  have HC : LevelRecursiveGuard EnvironmentCore.definitions false (.const c []) (.const c []) := by
    rw [← EC]; exact .join hΓ hC hC .refl
  have HS : LevelRecursiveGuard EnvironmentCore.definitions false (.sort (.succ .zero)) (.sort (.succ .zero)) := by
    have ht : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
    have E : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) := if_neg (not_isProof_of_sort hΓ ht)
    rw [← E]; exact .join hΓ ht ht .refl
  have HG : LevelRecursiveGuard EnvironmentCore.definitions false L R := .forallE HC (.forallE Hleaf HS)
  have Hno : ¬ ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) L R := by
    rintro ⟨out, RA, RB⟩
    obtain ⟨X, Y, rfl, _, HA⟩ := RA.pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨X', Y', E, _, HB⟩ := RB.pi_parts (fun H => erased_level_core_no_pi H)
    cases E
    obtain ⟨Z, W, rfl, HN, _⟩ := HA.pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨Z', W', E, HA, _⟩ := HB.pi_parts (fun H => erased_level_core_no_pi H)
    cases E
    exact shifted_no_join ⟨_, HN, HA⟩
  refine ⟨Γ, f, g, .forallE C T, hΓ, hf, hg, ?_, ⟨L, RL⟩, ⟨R, RR⟩, ?_⟩
  · rw [Ef, Eg]
    exact .lam (.leaf .refl) (.lam ((shifted_compare.scoped (fun H => .base (.inl H))).joint.computed) (.leaf .refl))
  · intro left right NL NR
    refine ⟨EnvironmentCore.stage_zero_recursive_reference_outputs_compare heq hcon hΓ hf hg RL RR HG NL NR,
      ?_, native_no_return heq hcon hc HD hΓ hf RL NL, native_no_return heq hcon hc HD hΓ hg RR NR⟩
    intro HJ
    have JL := stage_zero_native_outputs_join heq EnvironmentCore.sound
      (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
      (EnvironmentCore.typed_core_confluence hcon) hΓ hf RL NL
    have JR := stage_zero_native_outputs_join heq EnvironmentCore.sound
      (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
      (EnvironmentCore.typed_core_confluence hcon) hΓ hg NR RR
    have HM := stage_zero_native_output_join_trans heq EnvironmentCore.sound
      (EnvironmentCore.typed_level_core_confluence hcon) hΓ hf NL JL HJ
    exact Hno (stage_zero_native_output_join_trans heq EnvironmentCore.sound
      (EnvironmentCore.typed_level_core_confluence hcon) hΓ hg NR HM JR)


omit [Params] in
/-- The separation is realized in a well-formed canonical-Eq environment by
installing the existing recursive declaration at any fresh name. Concrete
patterns and actual definition lookup are discharged, so the comparison and
both negative properties do not depend on abstract core hypotheses. -/
theorem canonical_recursive_eta_references
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) (U : Nat) :
    ∃ hE : (GuardedEta.extended base c).WF,
      (GuardedEta.extended base c).HasCanonicalEq ∧
      (letI := hE.params U
       ∃ Γ f g T, OnCtx Γ ((GuardedEta.extended base c).IsType U) ∧
         (GuardedEta.extended base c).HasType U Γ f T ∧ (GuardedEta.extended base c).HasType U Γ g T ∧
         ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
           (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g) ∧
         (∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
           (proofEraseCtx Γ) (proofErase Γ f) out) ∧
         (∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
           (proofEraseCtx Γ) (proofErase Γ g) out) ∧
         ∀ left right,
           ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
             (proofEraseCtx Γ) (proofErase Γ f) left →
           ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
             (proofEraseCtx Γ) (proofErase Γ g) right →
           ComputedJointCompare (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
             (proofEraseCtx Γ) false left right ∧
           ¬ ComputeJoin (ErasedLevelCore EnvironmentCore.definitions) left right ∧
           (¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) left mid →
             Compute (ErasedLevelCore EnvironmentCore.definitions) mid left)) ∧
           ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) right mid →
             Compute (ErasedLevelCore EnvironmentCore.definitions) mid right)) := by
  let hE := GuardedEta.extended_wf hbase hfresh
  have hEq := GuardedEta.extended_canonicalEq heq hfresh
  refine ⟨hE, hEq, ?_⟩
  letI := hE.params U
  apply all_native_outputs_compare_without_join_or_return (c := c) hEq (fun H => H)
  · change (GuardedEta.extended base c).constants c = some (GuardedEta.declaration c).toVConstant
    simp [GuardedEta.extended, GuardedEta.stub, VEnv.addDefEq]
  · exact guarded_definition hE U

end RecursiveEtaReferences
end Lean4Lean.VEnv.Strengthening
