import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRankedTypeFamily

/-! # Dependent family readout with generic value results

A locally introduced universe parameter may occur as the final result carrier,
not just as an input. Its values admit the proved type-specialization readout.
The parameter list is preserved under outer substitution; no arbitrary
substitution closure of existential specialization is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private preserves_shift from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolymorphicTypeFamily
open private convert_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionCarrierConversion
variable [Params]

/-- A family with recorded local type parameters and native higher-order inputs.
The result constructor permits an actual generic value carrier; all other
constructors retain their input-specific proved binder conversion. -/
inductive DependentFamily (F : List VExpr → VExpr → Prop) :
    List VExpr → List (Nat × VLevel) → VExpr → Prop where
  | base : ParameterizedTypeFamily Γ ps T → DependentFamily F Γ ps T
  | result : (k, u) ∈ ps → DependentFamily F Γ ps (.bvar k)
  | terminal : TerminalDomain Γ A →
      DependentFamily F (A :: Γ) (shiftTypeParameters ps) B →
      DependentFamily F Γ ps (.forallE A B)
  | callable : CallableDomain Γ A →
      DependentFamily F (A :: Γ) (shiftTypeParameters ps) B →
      DependentFamily F Γ ps (.forallE A B)
  | native : Tree F Γ A →
      DependentFamily F (A :: Γ) (shiftTypeParameters ps) B →
      DependentFamily F Γ ps (.forallE A B)
  | forallUniverse : u.WF univs →
      DependentFamily F (.sort (.succ u) :: Γ) ((0, u) :: shiftTypeParameters ps) B →
      DependentFamily F Γ ps (.forallE (.sort (.succ u)) B)
  | parameter : (k, u) ∈ ps →
      DependentFamily F (.bvar k :: Γ) (shiftTypeParameters ps) B →
      DependentFamily F Γ ps (.forallE (.bvar k) B)

variable {D : PureObservation.Definitions} {F : List VExpr → VExpr → Prop}

/-- Substitution preserves the entire family when it fixes the explicitly
recorded parameters. Root certificates have an empty list, so every outer
actual typed substitution satisfies this condition. -/
theorem DependentFamily.subst [InputLaws D F] (H : DependentFamily F Γ ps T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort v))
    (HP : ∀ {k u}, (k, u) ∈ ps → σ k = .bvar k) :
    DependentFamily F Γ₀ ps (T.subst σ) := by
  induction H generalizing Γ₀ σ v with
  | base HT => exact .base (HT.subst hΓ₀ W hT HP)
  | result hm => simpa only [VExpr.subst, HP hm] using DependentFamily.result (F := F) (Γ := Γ₀) hm
  | terminal HA HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .terminal (HA.subst hΓ₀ W hA)
      (ih ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
        (W.lift henv.ordered hA) hB (preserves_shift HP))
  | callable HA HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .callable (HA.subst hΓ₀ W hA)
      (ih ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
        (W.lift henv.ordered hA) hB (preserves_shift HP))
  | native HA HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .native (HA.subst (D := D) hΓ₀ W hA)
      (ih ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
        (W.lift henv.ordered hA) hB (preserves_shift HP))
  | @forallUniverse w Γ ps B hu HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    apply DependentFamily.forallUniverse hu
    apply ih (Γ₀ := .sort (.succ w) :: Γ₀) ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
      (W.lift henv.ordered hA) hB
    intro k v hm
    rcases List.mem_cons.1 hm with E | hm
    · cases E; rfl
    · exact preserves_shift HP hm
  | @parameter ps k u Γ B hm HB ih =>
    obtain ⟨⟨v, hA⟩, _, hB⟩ := hT.forallE_inv henv
    have HH := ih (Γ₀ := (VExpr.bvar k).subst σ :: Γ₀) ⟨hΓ₀, v, hA.subst henv.orderedStrong W hΓ₀⟩
      (W.lift henv.ordered hA) hB (preserves_shift HP)
    simp only [VExpr.subst, HP hm] at HH ⊢
    exact .parameter hm HH

/-- Whole-carrier readout for both universe and generic-value results. In the
result case, the stored literal universe binder supplies an actual specializing
substitution, and the source guard becomes ordinary comparison. -/
theorem DependentFamily.carrier_convert [InputLaws D F]
    (HT : DependentFamily F Γ ps T) (HP : TypeParametersRealized Γ ps)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  induction HT generalizing f g A with
  | base HT =>
    obtain ⟨_, hA⟩ := hf.isType henv hΓ
    exact (HT.specialized HP hΓ (HE.of_l henv hΓ hA).hasType.2).carrier_convert hs hΓ hf hg HE H
  | result hm =>
    obtain ⟨hu, Γ₀, Γ', W⟩ := HP hm
    exact .carrierChecked (proofErase_computed_type_parameter_carrier_checked
      (ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs))
      W hΓ hu hf hg HE H)
  | terminal HA _ ih =>
    exact convert_raw hs
      (fun hΓ HAB hf hg H => proofErase_computed_joint_zero_carrier_terminal_context hs hΓ HAB
        (HA.convert hΓ HAB.symm) hf hg H)
      (fun hΓ hf hg HE H => ih HP.cons hΓ hf hg HE H) hΓ H hf hg HE rfl rfl rfl rfl
  | callable HA _ ih =>
    exact convert_raw hs
      (fun hΓ HAB hf hg H => proofErase_computed_joint_zero_carrier_callable_context hs hΓ HAB HA hf hg H)
      (fun hΓ hf hg HE H => ih HP.cons hΓ hf hg HE H) hΓ H hf hg HE rfl rfl rfl rfl
  | native HA _ ih =>
    exact convert_raw hs
      (fun hΓ HAB hf hg H => carrier_context hs hΓ HAB HA hf hg H)
      (fun hΓ hf hg HE H => ih HP.cons hΓ hf hg HE H) hΓ H hf hg HE rfl rfl rfl rfl
  | forallUniverse hu _ ih =>
    exact convert_raw hs
      (fun hΓ HAB hf hg H => proofErase_computed_joint_zero_carrier_terminal_context hs hΓ HAB
        (TerminalDomain.sort.convert hΓ HAB.symm) hf hg H)
      (fun hΓ hf hg HE H => ih (HP.universe hu) hΓ hf hg HE H) hΓ H hf hg HE rfl rfl rfl rfl
  | @parameter ps k u Γ B hm HB ih =>
    have transport : ComputedCarrierBinderTransport D Γ (.bvar k) := by
      intro A v f g C hΓ HAB hf hg H
      have hΓX : OnCtx (.bvar k :: Γ) (env.IsType univs) := ⟨hΓ, v, HAB.hasType.2⟩
      obtain ⟨hu, Γ₀, Γ', W⟩ := HP hm
      have hx : env.HasType univs (.bvar k :: Γ) (.bvar 0) (.bvar (k + 1)) := by
        simpa [VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm] using
          (HasType.bvar (env := env) (U := univs) (Lookup.zero (Γ := Γ) (ty := .bvar k)))
      exact proofErase_computed_joint_zero_carrier_specialized_context hs hΓ HAB
        (SortSpecialization.type_parameter (.succ W) hΓX hu hx) hf hg H
    exact convert_raw hs transport (fun hΓ hf hg HE H => ih HP.cons hΓ hf hg HE H)
      hΓ H hf hg HE rfl rfl rfl rfl

/-- Empty-parameter root certificates supply both input laws. Internal
parameters are rebuilt beneath their own binders after outer substitution. -/
theorem DependentFamily.root_inputLaws [InputLaws D F] :
    InputLaws D (fun Γ T => DependentFamily F Γ [] T) :=
  ⟨fun H hΓ W hT => H.subst (D := D) hΓ W hT (by simp),
    fun H hs hΓ hf hg HE HC => H.carrier_convert (by simp [TypeParametersRealized]) hs hΓ hf hg HE HC⟩

/-- Iterated native inputs now permit dependent generic values as results. -/
def ValueRanked : Nat → List VExpr → VExpr → Prop
  | 0 => PolymorphicTypeFamily
  | n + 1 => fun Γ T => DependentFamily (ValueRanked n) Γ [] T

/-- Every finite level has proved input laws, including the new result case. -/
theorem valueRanked_inputLaws (D : PureObservation.Definitions) (n : Nat) :
    InputLaws D (ValueRanked n) := by
  induction n with
  | zero => exact polymorphic_inputLaws
  | succ n ih =>
    letI := ih
    exact DependentFamily.root_inputLaws

/-- Existing ranked families embed at the same level of the dependent hierarchy. -/
theorem ranked_valueRanked (H : Ranked n Γ T) : ValueRanked n Γ T := by
  induction n generalizing Γ T with
  | zero => exact H
  | succ n ih =>
    change Extension (Ranked n) Γ T at H
    induction H with
    | base HT => exact .base HT
    | native HA HB ihB => exact .native (HA.mono (fun H => ih H)) ihB

/-- Enlarging the native input predicate preserves parameters and value results. -/
theorem DependentFamily.mono (hFG : ∀ {Γ T}, F Γ T → G Γ T)
    (H : DependentFamily F Γ ps T) : DependentFamily G Γ ps T := by
  induction H with
  | base HT => exact .base HT
  | result hm => exact .result hm
  | terminal HA _ ih => exact .terminal HA ih
  | callable HA _ ih => exact .callable HA ih
  | native HA _ ih => exact .native (HA.mono hFG) ih
  | forallUniverse hu _ ih => exact .forallUniverse hu ih
  | parameter hm _ ih => exact .parameter hm ih

/-- Every dependent certificate remains available at the next level. -/
theorem valueRanked_step (n : Nat) (H : ValueRanked n Γ T) : ValueRanked (n + 1) Γ T := by
  induction n generalizing Γ T with
  | zero => exact .base H
  | succ n ih => exact DependentFamily.mono (fun H => ih H) H

/-- The dependent hierarchy is monotone in its finite level. -/
theorem valueRanked_mono (h : n ≤ m) (H : ValueRanked n Γ T) : ValueRanked m Γ T := by
  induction h with
  | refl => exact H
  | @step m _ ih => exact valueRanked_step m ih

/-- Every outer typed substitution preserves the rank and dependent result. -/
theorem valueRanked_subst (H : ValueRanked n Γ T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort v)) : ValueRanked n Γ₀ (T.subst σ) := by
  letI := valueRanked_inputLaws PureObservation.Definitions.empty n
  exact InputLaws.subst (D := PureObservation.Definitions.empty) H hΓ₀ W hT

/-- Dependent result carriers admit full readout from arbitrary ordinarily
equal source carriers, with all input laws discharged by the finite hierarchy. -/
theorem valueRanked_carrier_convert (HT : ValueRanked n Γ T)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  letI := valueRanked_inputLaws D n
  exact InputLaws.carrier_convert HT hs hΓ hf hg HE H

end Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
