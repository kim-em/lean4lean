import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFrameworkContext

/-! # Finite levels of higher-order family readout

At each new level, native trees over the preceding input grammar may themselves
become inputs. The two input laws are proved by induction on this level. Every
binder conversion in the successor step uses the already proved lower-level
native transport, so there is no circular carrier-readout assumption.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private convert_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionCarrierConversion
variable [Params]

/-- One extension step: existing polymorphic families remain available, and
native trees over F may be inputs of arbitrarily long dependent telescopes. -/
inductive Extension (F : List VExpr → VExpr → Prop) : List VExpr → VExpr → Prop where
  | base : PolymorphicTypeFamily Γ T → Extension F Γ T
  | native : Tree F Γ A → Extension F (A :: Γ) B → Extension F Γ (.forallE A B)

variable {D : PureObservation.Definitions} {F G : List VExpr → VExpr → Prop}

omit [Params] in
/-- Enlarging the input predicate enlarges the native tree grammar. -/
theorem Tree.mono (hFG : ∀ {Γ T}, F Γ T → G Γ T) (H : Tree F Γ T) : Tree G Γ T := by
  induction H with
  | sort => exact .sort
  | function HA _ ih => exact .function (hFG HA) ih

/-- Each extension step is monotone in its lower-level input predicate. -/
theorem Extension.mono (hFG : ∀ {Γ T}, F Γ T → G Γ T) (H : Extension F Γ T) : Extension G Γ T := by
  induction H with
  | base HT => exact .base HT
  | native HA _ ih => exact .native (HA.mono hFG) ih

/-- A proved lower-level input theory preserves all new family certificates
through arbitrary actual typed substitutions. -/
theorem Extension.subst [InputLaws D F] (H : Extension F Γ T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort v)) : Extension F Γ₀ (T.subst σ) := by
  induction H generalizing Γ₀ σ v with
  | base HT => exact .base (HT.subst hΓ₀ W hT)
  | native HA HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .native (HA.subst (D := D) hΓ₀ W hA)
      (ih ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩ (W.lift henv.ordered hA) hB)

/-- Native context transport at the preceding level supplies every new input
conversion. Codomain readout recurses on the finite extension certificate. -/
theorem Extension.carrier_convert [InputLaws D F] (HT : Extension F Γ T)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  induction HT generalizing f g A with
  | base HT => exact HT.carrier_convert hs hΓ hf hg HE H
  | native HA _ ih =>
    exact convert_raw hs
      (fun hΓ HAB hf hg H => carrier_context hs hΓ HAB HA hf hg H)
      (fun hΓ hf hg HE H => ih hΓ hf hg HE H) hΓ H hf hg HE rfl rfl rfl rfl

/-- Both input laws at the new level are theorems from the preceding level. -/
theorem Extension.inputLaws [InputLaws D F] : InputLaws D (Extension F) :=
  ⟨fun H => H.subst (D := D), fun H => H.carrier_convert⟩

/-- The finite hierarchy starts from polymorphic families and iterates the
native-input extension. Its certificates contain no semantic transport premise. -/
def Ranked : Nat → List VExpr → VExpr → Prop
  | 0 => PolymorphicTypeFamily
  | n + 1 => Extension (Ranked n)

/-- Every finite level has proved substitution and whole-carrier conversion.
The induction is on the external level, not on a checker derivation assumed
stable under its own output conversion. -/
theorem ranked_inputLaws (D : PureObservation.Definitions) (n : Nat) : InputLaws D (Ranked n) := by
  induction n with
  | zero => exact polymorphic_inputLaws
  | succ n ih =>
    letI := ih
    exact Extension.inputLaws

/-- Every family certificate embeds at the next finite level. -/
theorem ranked_step (n : Nat) (H : Ranked n Γ T) : Ranked (n + 1) Γ T := by
  induction n generalizing Γ T with
  | zero => exact .base H
  | succ n ih => exact Extension.mono (fun H => ih H) H

/-- Increasing the level preserves every previously admitted family. -/
theorem ranked_mono (h : n ≤ m) (H : Ranked n Γ T) : Ranked m Γ T := by
  induction h with
  | refl => exact H
  | @step m _ ih => exact ranked_step m ih

/-- Actual typed substitution preserves certificates at their original level. -/
theorem ranked_subst (H : Ranked n Γ T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort v)) : Ranked n Γ₀ (T.subst σ) := by
  letI := ranked_inputLaws (D := PureObservation.Definitions.empty) n
  exact InputLaws.subst (D := PureObservation.Definitions.empty) H hΓ₀ W hT

/-- Full carrier conversion is available at every finite level, including an
arbitrary ordinarily equal source carrier with different erased annotations. -/
theorem ranked_carrier_convert (HT : Ranked n Γ T)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  letI := ranked_inputLaws D n
  exact InputLaws.carrier_convert HT hs hΓ hf hg HE H

/-- Recursive whole-carrier checking survives binder conversion to a native
tree over any finite level of the new grammar. -/
theorem ranked_carrier_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u)) (HB : Tree (Ranked n) Γ B)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  letI := ranked_inputLaws D n
  exact carrier_context hs hΓ HAB HB ha hb H

end Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
