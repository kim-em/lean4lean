import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpecializedTypeFamily

/-! # Substitution-stable families with locally bound type parameters

A finite family certificate records the universe parameters introduced inside
that family. Its parameter inputs refer only to this list. Outer substitutions
therefore preserve the parameters; the actual sort-specialization witnesses are
rebuilt after substitution, rather than transported existentially.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Move the recorded local universe parameters through one new binder. -/
def shiftTypeParameters (ps : List (Nat × VLevel)) : List (Nat × VLevel) :=
  ps.map fun (k, u) => (k + 1, u)

/-- A finite target tree with explicit locally bound universe parameters.
Terminal inputs may depend on the entire context. Generic inputs must refer to
one of the parameters recorded by a surrounding universe constructor. -/
inductive ParameterizedTypeFamily : List VExpr → List (Nat × VLevel) → VExpr → Prop where
  | sort : ParameterizedTypeFamily Γ ps (.sort u)
  | function : TerminalDomain Γ A →
      ParameterizedTypeFamily (A :: Γ) (shiftTypeParameters ps) B →
      ParameterizedTypeFamily Γ ps (.forallE A B)
  | forallUniverse : u.WF univs →
      ParameterizedTypeFamily (.sort (.succ u) :: Γ) ((0, u) :: shiftTypeParameters ps) B →
      ParameterizedTypeFamily Γ ps (.forallE (.sort (.succ u)) B)
  | parameter : (k, u) ∈ ps →
      ParameterizedTypeFamily (.bvar k :: Γ) (shiftTypeParameters ps) B →
      ParameterizedTypeFamily Γ ps (.forallE (.bvar k) B)

/-- Every recorded parameter has its literal successor-universe binder in the
actual context, so substitution by the predecessor universe can be constructed. -/
def TypeParametersRealized (Γ : List VExpr) (ps : List (Nat × VLevel)) : Prop :=
  ∀ {k u}, (k, u) ∈ ps → u.WF univs ∧
    ∃ Γ₀ Γ', Ctx.InstN Γ₀ (.sort u) (.sort (.succ u)) k Γ Γ'

/-- Existing parameter witnesses extend through any local binder. -/
theorem TypeParametersRealized.cons (H : TypeParametersRealized Γ ps) :
    TypeParametersRealized (A :: Γ) (shiftTypeParameters ps) := by
  intro k u hm
  obtain ⟨⟨j, v⟩, hj, E⟩ := List.mem_map.1 hm
  cases E
  obtain ⟨hu, Γ₀, Γ', W⟩ := H hj
  exact ⟨hu, Γ₀, _, .succ W⟩

/-- A literal successor universe adds a fresh parameter witness. -/
theorem TypeParametersRealized.universe (H : TypeParametersRealized Γ ps)
    (hu : u.WF univs) :
    TypeParametersRealized (.sort (.succ u) :: Γ) ((0, u) :: shiftTypeParameters ps) := by
  intro k v hm
  rcases List.mem_cons.1 hm with E | hm
  · cases E
    exact ⟨hu, Γ, Γ, .zero⟩
  · exact H.cons hm

/-- Every structurally recorded generic input has the sort specialization
needed for full context conversion. -/
theorem ParameterizedTypeFamily.specialized (H : ParameterizedTypeFamily Γ ps T)
    (HP : TypeParametersRealized Γ ps) (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort v)) : SpecializedTypeFamily Γ T := by
  induction H generalizing v with
  | sort => exact .sort
  | function HA HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .function (.inl HA) (ih HP.cons ⟨hΓ, u, hA⟩ hB)
  | @forallUniverse w Γ ps B hu HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .function (.inl .sort) (ih (HP.universe hu) ⟨hΓ, u, hA⟩ hB)
  | @parameter ps k u Γ B hm HB ih =>
    obtain ⟨⟨v, hA⟩, _, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (.bvar k :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    obtain ⟨hu, Γ₀, Γ', W⟩ := HP hm
    have hx : env.HasType univs (.bvar k :: Γ) (.bvar 0) (.bvar (k + 1)) := by
      simpa [VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm] using
        (HasType.bvar (env := env) (U := univs) (Lookup.zero (Γ := Γ) (ty := .bvar k)))
    exact .function (.inr (SortSpecialization.type_parameter (.succ W) hΓA hu hx))
      (ih HP.cons hΓA hB)

omit [Params] in
private theorem preserves_shift {σ : VExpr.Subst}
    (H : ∀ {k u}, (k, u) ∈ ps → σ k = .bvar k) :
    ∀ {k u}, (k, u) ∈ shiftTypeParameters ps → σ.lift k = .bvar k := by
  intro k u hm
  obtain ⟨⟨j, v⟩, hj, E⟩ := List.mem_map.1 hm
  cases E
  simp [VExpr.Subst.lift, H hj, VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm]

/-- Typed substitution preserving the recorded variables transports the whole
finite certificate. Under a new local binder the preservation equation lifts;
a fresh universe parameter satisfies it by definition. -/
theorem ParameterizedTypeFamily.subst (H : ParameterizedTypeFamily Γ ps T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort v))
    (HP : ∀ {k u}, (k, u) ∈ ps → σ k = .bvar k) :
    ParameterizedTypeFamily Γ₀ ps (T.subst σ) := by
  induction H generalizing Γ₀ σ v with
  | sort => exact .sort
  | function HA HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    exact .function (HA.subst hΓ₀ W hA)
      (ih ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
        (W.lift henv.ordered hA) hB (preserves_shift HP))
  | @forallUniverse w Γ ps B hu HB ih =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hT.forallE_inv henv
    apply ParameterizedTypeFamily.forallUniverse hu
    apply ih (Γ₀ := .sort (.succ w) :: Γ₀) ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩ (W.lift henv.ordered hA) hB
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

/-- Root certificates contain no externally supplied parameter witnesses.
All generic inputs refer to parameters introduced inside the target family. -/
def PolymorphicTypeFamily (Γ : List VExpr) (T : VExpr) : Prop :=
  ParameterizedTypeFamily Γ [] T

/-- Polymorphic family certificates survive every actual typed substitution. -/
theorem PolymorphicTypeFamily.subst (H : PolymorphicTypeFamily Γ T)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hT : env.HasType univs Γ T (.sort v)) : PolymorphicTypeFamily Γ₀ (T.subst σ) :=
  ParameterizedTypeFamily.subst H hΓ₀ W hT (by simp)

/-- Root certificates give full specialized-family readout in the actual context. -/
theorem PolymorphicTypeFamily.specialized (H : PolymorphicTypeFamily Γ T)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort v)) :
    SpecializedTypeFamily Γ T :=
  ParameterizedTypeFamily.specialized H (by simp [TypeParametersRealized]) hΓ hT

/-- Every earlier terminal-input family has a certificate with any parameter list. -/
theorem TerminalTypeFamily.parameterized (H : TerminalTypeFamily Γ T) :
    ParameterizedTypeFamily Γ ps T := by
  induction H generalizing ps with
  | sort => exact .sort
  | function HA HB ih => exact .function HA ih

/-- Terminal-input families are included in the substitution-stable grammar. -/
theorem TerminalTypeFamily.polymorphic (H : TerminalTypeFamily Γ T) :
    PolymorphicTypeFamily Γ T := H.parameterized

/-- Full carrier conversion at the new substitution-stable family targets. -/
theorem PolymorphicTypeFamily.carrier_convert (HT : PolymorphicTypeFamily Γ T)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  obtain ⟨_, hA⟩ := hf.isType henv hΓ
  exact (HT.specialized hΓ (HE.of_l henv hΓ hA).hasType.2).carrier_convert hs hΓ hf hg HE H

/-- The generic predicate family uses its own bound universe parameter. -/
theorem polymorphicTypeFamily_predicate : PolymorphicTypeFamily Γ
    (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero))) :=
  .forallUniverse (by trivial) (.parameter (u := .zero) (by simp) .sort)

/-- Two independently bound type parameters remain available through both
subsequent value binders. This exercises shifted references to older parameters. -/
theorem polymorphicTypeFamily_binary : PolymorphicTypeFamily Γ
    (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
      (.forallE (.bvar 1) (.forallE (.bvar 1) (.sort .zero))))) :=
  .forallUniverse (by trivial) (.forallUniverse (by trivial)
    (.parameter (u := .zero) (by simp [shiftTypeParameters])
      (.parameter (u := .zero) (by simp [shiftTypeParameters]) .sort)))

/-- The stable grammar strictly extends the former terminal-input grammar on
an actual well-typed family, not only on raw syntax. -/
theorem polymorphicTypeFamily_strict_extension
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ T u, env.HasType univs Γ T (.sort u) ∧ PolymorphicTypeFamily Γ T ∧
      ¬ TerminalTypeFamily Γ T :=
  ⟨_, _, polymorphic_predicate_type_typed, polymorphicTypeFamily_predicate,
    terminalTypeFamily_polymorphic_predicate_failure hΓ⟩

end Lean4Lean.VEnv.Strengthening
