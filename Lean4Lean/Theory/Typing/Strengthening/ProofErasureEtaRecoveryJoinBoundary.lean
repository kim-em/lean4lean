import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary

/-! # Eta also obstructs literal joins of recovered types

Even with identical universe syntax, the neutral types F f and F (fun x => f x)
are fixed by every joint computation. A variable at the first type may be
assigned the second by eta conversion. Its recovered type cannot literally
join that assigned type; the joint checker compares them at stage zero.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]
namespace EtaRecoveryJoinBoundary

private def functionType : VExpr := .forallE (.sort .zero) (.sort .zero)
private def familyType : VExpr := .forallE functionType (.sort (.succ .zero))
private def context (Γ : List VExpr) : List VExpr :=
  .app (.bvar 0) (.bvar 1) :: familyType :: functionType :: Γ
private def native : VExpr := .app (.bvar 1) (.bvar 2)
private def assigned : VExpr := .app (.bvar 1) (.lam (.sort .zero) (.app (.bvar 3) (.bvar 0)))
private def nativeRaw : ProofShape := .app (.bvar 1) (.bvar 2)
private def assignedRaw : ProofShape := .app (.bvar 1) (.lam (.sort .zero) (.app (.bvar 3) (.bvar 0)))

private theorem function_type : env.HasType univs Γ functionType
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallE (.sort (by trivial)) (.sort (by trivial))

private theorem family_type : env.HasType univs Γ familyType
    (.sort (.imax (.imax (.succ .zero) (.succ .zero)) (.succ (.succ .zero)))) :=
  .forallE function_type (.sort (by trivial))

private theorem context_wf (hΓ : OnCtx Γ (env.IsType univs)) :
    OnCtx (context Γ) (env.IsType univs) := by
  refine ⟨⟨⟨hΓ, _, function_type⟩, _, family_type⟩, .succ .zero, ?_⟩
  have hF : env.HasType univs (familyType :: functionType :: Γ) (.bvar 0) familyType := .bvar .zero
  have hf : env.HasType univs (familyType :: functionType :: Γ) (.bvar 1) functionType := .bvar (.succ .zero)
  exact .app hF hf

private theorem family_typed : env.HasType univs (context Γ) (.bvar 1) familyType := .bvar (.succ .zero)
private theorem function_typed : env.HasType univs (context Γ) (.bvar 2) functionType := .bvar (.succ (.succ .zero))
private theorem native_typed : env.HasType univs (context Γ) native (.sort (.succ .zero)) :=
  .app family_typed function_typed
private theorem types_equal : env.IsDefEq univs (context Γ) assigned native (.sort (.succ .zero)) :=
  .appDF family_typed (.eta function_typed)
private theorem source_typed : env.HasType univs (context Γ) (.bvar 0) native := .bvar .zero

private theorem erasures (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase (context Γ) native = nativeRaw ∧ proofErase (context Γ) assigned = assignedRaw := by
  have hC := context_wf hΓ
  have hF := family_typed (Γ := Γ)
  have hf := function_typed (Γ := Γ)
  have hη := (IsDefEq.eta hf).hasType.1
  have hC' : OnCtx (.sort .zero :: context Γ) (env.IsType univs) :=
    ⟨hC, _, HasType.sort (by trivial)⟩
  have hf' : env.HasType univs (.sort .zero :: context Γ) (.bvar 3) functionType :=
    .bvar (.succ (.succ (.succ .zero)))
  have hx : env.HasType univs (.sort .zero :: context Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have hbody : env.HasType univs (.sort .zero :: context Γ) (.app (.bvar 3) (.bvar 0)) (.sort .zero) :=
    .app hf' hx
  have EF : proofErase (context Γ) (.bvar 1) = .bvar 1 :=
    if_neg (not_isProof_function_to_sort hC hF)
  have Ef : proofErase (context Γ) (.bvar 2) = .bvar 2 :=
    if_neg (not_isProof_function_to_sort hC hf)
  constructor
  · change proofErase (context Γ) (.app (.bvar 1) (.bvar 2)) = _
    rw [show proofErase (context Γ) (.app (.bvar 1) (.bvar 2)) = .app _ _ from
      if_neg (not_isProof_of_sort hC native_typed), EF, Ef]
    rfl
  · change proofErase (context Γ) (.app (.bvar 1) (.lam (.sort .zero) (.app (.bvar 3) (.bvar 0)))) = _
    rw [show proofErase (context Γ) (.app (.bvar 1) (.lam (.sort .zero) (.app (.bvar 3) (.bvar 0)))) = .app _ _ from
      if_neg (not_isProof_of_sort hC types_equal.hasType.1), EF]
    rw [show proofErase (context Γ) (.lam (.sort .zero) (.app (.bvar 3) (.bvar 0))) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hC hη)]
    rw [show proofErase (context Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hC (HasType.sort (by trivial)))]
    rw [show proofErase (.sort .zero :: context Γ) (.app (.bvar 3) (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hC' hbody)]
    rw [show proofErase (.sort .zero :: context Γ) (.bvar 3) = .bvar 3 from
      if_neg (not_isProof_function_to_sort hC' hf')]
    rw [show proofErase (.sort .zero :: context Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_of_sort hC' hx)]
    rfl

omit [Params] in
private theorem normal_forms {Step : List ProofShape → ProofShape → ProofShape → Prop}
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a) (Δ) :
    NormalSyntax (Step Δ) nativeRaw ∧ NormalSyntax (Step Δ) assignedRaw := by
  have hv (i) : NormalSyntax (Step Δ) (.bvar i) := ⟨fun _ H => hhead H, trivial⟩
  have hs : NormalSyntax (Step Δ) (.sort .zero) := ⟨fun _ H => hhead H, trivial⟩
  have happ (i) {a} (H : NormalSyntax (Step Δ) a) : NormalSyntax (Step Δ) (.app (.bvar i) a) :=
    ⟨fun _ H => hhead H, (fun _ _ H => nomatch H), hv i, H⟩
  exact ⟨happ 1 (hv 2), happ 1 ⟨(fun _ H => hhead H), hs, happ 3 (hv 0)⟩⟩

/-- A typed variable image defeats literal recovered-type joins solely through
eta conversion in a neutral type argument. No universe-equivalence step is
used. Both type shapes are fixed at every raw context by the whole joint union,
while its stage-zero comparison already relates them. -/
theorem typed_join_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' e T out, e = .bvar 0 ∧ OnCtx Γ' (env.IsType univs) ∧ env.HasType univs Γ' e T ∧ ¬ IsProof Γ' e ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ') (proofErase Γ' e) out ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ') false (proofErase Γ' T) out ∧
      ∀ out' shared,
        ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' e) out' →
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' T) shared →
        ¬ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') out' shared := by
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  have Ee : proofErase (context Γ) (.bvar 0) = .bvar 0 := if_neg hn
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EO : contextOracle (proofEraseCtx (context Γ)) 0 = nativeRaw := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hC (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))]
    exact EN
  refine ⟨context Γ, .bvar 0, assigned, nativeRaw, rfl, hC,
    types_equal.symm.defeq source_typed, hn, ?_, ?_, ?_⟩
  · rw [Ee, ← EO]
    exact .bvar
  · rw [EA]
    exact .app (.leaf .refl) (.leaf (.etaL (.boundVar (f := ProofShape.bvar 2))))
  · intro out' shared R HA HB
    rw [Ee] at R
    have HR := R.bvar_compute
    rw [EO] at HR
    have Eout := scoped_normal_fixed HR (fun Δ => (normal_forms (Step := ErasedJointUnion D) erased_joint_union_head Δ).1)
    rw [EA] at HA
    rw [Eout] at HB
    have E₁ := scoped_normal_fixed HA (fun Δ => (normal_forms (Step := ErasedJointUnion D) erased_joint_union_head Δ).2)
    have E₂ := scoped_normal_fixed HB (fun Δ => (normal_forms (Step := ErasedJointUnion D) erased_joint_union_head Δ).1)
    cases E₁.symm.trans E₂

/-- Even a well-typed substitution by a variable can fail retained renaming:
the source declaration uses an eta-converted type while the target variable's
oracle keeps its native type. Thus arbitrary variable images alone do not
extend the proof-substitution theorem; type alignment is still necessary. -/
theorem variable_substitution_not_retained {D : PureObservation.Definitions} (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' T, OnCtx Γ' (env.IsType univs) ∧ env.HasType univs Γ' (.bvar 0) T ∧
      OnCtx (T :: Γ') (env.IsType univs) ∧
      Ctx.SubstEq env univs Γ' (VExpr.Subst.one (.bvar 0)) (VExpr.Subst.one (.bvar 0)) (T :: Γ') ∧
      ¬ RetainedRenaming (proofEraseCtx (T :: Γ')) (proofEraseCtx Γ') (ProofShape.Subst.one (.bvar 0)) := by
  obtain ⟨Γ', e, T, out, rfl, hΓ', he, hn, _, _, Hno⟩ := typed_join_failure D hΓ
  obtain ⟨u, hT⟩ := he.isType henv hΓ'
  have hΓT : OnCtx (T :: Γ') (env.IsType univs) := ⟨hΓ', u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ') (e₀ := VExpr.bvar 0) (A₀ := T)).substEq hΓT he
  have hx : env.HasType univs (T :: Γ') (.bvar 0) T.lift := .bvar .zero
  have hvn : ¬ IsProof (T :: Γ') (.bvar 0) := fun hp => hn ((isProof_subst hΓ' W hx).2 hp)
  refine ⟨Γ', T, hΓ', he, hΓT, W, ?_⟩
  intro WR
  have R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx (T :: Γ'))
      (proofErase (T :: Γ') (.bvar 0)) (proofErase (T :: Γ') T.lift) :=
    proofErase_scoped_lookup_recovery hΓT Lookup.zero hvn .refl
  have R' := R.rename_retained (erased_joint_union_descent heq hs)
    (erased_joint_union_retained heq hs) hΓT hx rfl rfl WR
  rw [show proofErase (T :: Γ') (.bvar 0) = .bvar 0 from if_neg hvn,
    proofErase_liftN hΓ' hΓT Ctx.LiftN.one hT] at R'
  simp only [ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons,
    ProofShape.lift_subst_cons, ProofShape.subst_id] at R'
  rw [← show proofErase Γ' (.bvar 0) = .bvar 0 from if_neg hn] at R'
  exact Hno _ _ R' .refl .refl

end EtaRecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
