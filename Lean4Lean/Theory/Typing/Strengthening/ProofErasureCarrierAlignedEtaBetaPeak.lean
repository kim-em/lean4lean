import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverySubstitutionBoundary

/-! # Exact beta postponement fails, but the captured eta peak joins

The body of an identity wrapper can eta-expand its variable using the captured
declared domain. Contracting the wrapper first loses that annotation: no
source-typed descending computation can reproduce the exact eta target.
Beta cleanup nevertheless joins the peak. Thus exact residual transport is
too strong even for an actual typed application, while confluence stays live.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeEtaBetaPeak
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape Developments EtaScope
open private ProofShape.liftN_lam_inv ProofShape.liftN_app_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

/-- The retained fresh proposition occurs in a reducible domain annotation. -/
def domain : ProofShape := .app (.lam (.sort .zero) (.sort .zero)) (.bvar 0)
/-- The ordinary closed identity. -/
def short : ProofShape := .lam (.sort .zero) (.bvar 0)
/-- An identity wrapper whose declared type retains the captured domain. -/
def source : ProofShape :=
  .app (.lam (.forallE domain (.sort .zero)) (.bvar 0)) short
/-- Substituting the identity into the eta-expanded wrapper body retains that
domain, although the body itself immediately beta-contracts. -/
def long : ProofShape := .lam domain (.app (short.liftN 1) (.bvar 0))

private theorem short_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (ident 0) = short := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hn := not_isProof_function_to_sort hΓ (ident_typed env univs Γ 0)
  have hx : env.HasType univs (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  change proofErase Γ (.lam (.sort .zero) (.bvar 0)) = short
  change ¬ IsProof Γ (.lam (.sort .zero) (.bvar 0)) at hn
  simp only [proofErase, if_neg hn, if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .zero) (by trivial))),
    if_neg (not_isProof_of_sort hΓS hx), short]

/-- The whole peak starts at an actually typed source in every well-formed
base context, including canonical-Eq environments. -/
theorem source_typed (hΓ : OnCtx Γ (env.IsType univs)) :
    TypedSource (proofEraseCtx (.sort .zero :: Γ)) source := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hx : env.HasType univs (.sort .zero :: Γ) (ident 0).lift (capturedPi (.sort .zero)) :=
    identity_at_captured_pi
  have hn := not_isProof_function_to_sort hΓS hx
  refine ⟨_, _, _, hΓS, rfl, (nativeIdentityExpansion_equal hx).hasType.1, ?_⟩
  rw [proofErase_nativeIdentityExpansion hΓS hx hn,
    ErasedRecoverySubstitutionBoundary.captured_erasure hΓ]
  simpa only [ident, tower, VExpr.lift, VExpr.liftN, liftVar, Nat.zero_lt_succ,
    ↓reduceIte, Nat.zero_add, source, domain, ErasedRecoverySubstitutionBoundary.captured] using
    congrArg (fun a : ProofShape => ProofShape.app (.lam (.forallE domain (.sort .zero)) (.bvar 0)) a)
      (short_erasure hΓS)

omit [Params] in
/-- The ordinary beta branch contracts the identity wrapper. -/
theorem source_beta_short : ProofShape.BetaRed source short := by
  simpa only [source, ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
    (ProofShape.BetaRed.beta (A := .forallE domain (.sort .zero)) (b := .bvar 0) (a := short))

/-- The wrapper's bound variable has a guarded eta step at its declared
captured type. The declaration supplies the native evidence directly. -/
theorem variable_native_eta (hΓ : OnCtx Γ (env.IsType univs)) :
    ErasedEtaExpansionStage D 1
      (.forallE domain (.sort .zero) :: proofEraseCtx (.sort .zero :: Γ))
      (.bvar 0) (.lam (domain.liftN 1) (.app (.bvar 1) (.bvar 0))) := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hx : env.HasType univs (.sort .zero :: Γ) (ident 0).lift (capturedPi (.sort .zero)) :=
    identity_at_captured_pi
  obtain ⟨u, hC⟩ := hx.isType henv hΓS
  have hΓC : OnCtx (capturedPi (.sort .zero) :: .sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓS, u, hC⟩
  have hD : env.HasType univs (.sort .zero :: Γ) (capturedDomain (.sort .zero))
      (.sort (.succ .zero)) :=
    .app (.lam (HasType.sort (by trivial)) (HasType.sort (by trivial))) (.bvar .zero)
  have ED : proofErase (.sort .zero :: Γ) (capturedDomain (.sort .zero)) = domain := by
    have E := ErasedRecoverySubstitutionBoundary.captured_erasure hΓ
    change proofErase _ (.forallE (capturedDomain (.sort .zero)) (.sort .zero)) = _ at E
    have hn := not_isProof_of_sort hΓS hC
    change ¬ IsProof _ (.forallE (capturedDomain (.sort .zero)) (.sort .zero)) at hn
    rw [show proofErase _ (.forallE (capturedDomain (.sort .zero)) (.sort .zero)) =
      .forallE _ _ from if_neg hn] at E
    exact (ProofShape.forallE.inj E).1
  have SD := DomainSort.of_typed hΓC (hD.weak henv (B := capturedPi (.sort .zero)))
  rw [proofEraseCtx, ErasedRecoverySubstitutionBoundary.captured_erasure hΓ,
    proofErase_liftN hΓS hΓC Ctx.LiftN.one hD, ED] at SD
  have R : ScopedTypeRecovery (ErasedEtaExpansionStage D 0)
      (.forallE domain (.sort .zero) :: proofEraseCtx (.sort .zero :: Γ))
      (.bvar 0) (.forallE (domain.liftN 1) (.sort .zero)) := .bvar
  have Earg : etaArgument (.succ .zero) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
  simpa only [Earg, ProofShape.liftN, liftVar, Nat.reduceLT, ↓reduceIte, Nat.reduceAdd] using
    NativeEtaExpansion.intro R SD

omit [Params] in
/-- The exact instantiated eta body retains the captured annotation. -/
theorem eta_body_inst_short :
    (ProofShape.lam (domain.liftN 1) (.app (.bvar 1) (.bvar 0))).inst short = long := by
  simp [long, domain, short, ProofShape.inst, ProofShape.liftN, liftVar]

/-- The other branch eta-expands the bound variable at its declared type and
then contracts the wrapper. Only stage one is needed. -/
theorem source_compute_long (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx (.sort .zero :: Γ)) source long := by
  have RE := variable_native_eta (D := D) hΓ
  have RH := ScopedCompute.app (Step := ErasedEtaExpansionStage D 1)
    (ScopedCompute.lam .refl (.base RE)) (ScopedCompute.refl (e := short))
  apply RH.trans
  simpa [long, domain, short, ProofShape.inst, ProofShape.liftN, liftVar] using
    (ProofShape.BetaRed.beta (A := .forallE domain (.sort .zero))
      (b := .lam (domain.liftN 1) (.app (.bvar 1) (.bvar 0))) (a := short) |> ScopedCompute.beta)

omit [Params] in
/-- No lower raw expression lifts to the captured eta endpoint. -/
theorem long_not_lift (a : ProofShape) : a.liftN 1 ≠ long := by
  intro E
  obtain ⟨_, _, _, ED, _⟩ := ProofShape.liftN_lam_inv E
  obtain ⟨_, x, _, _, Ex⟩ := ProofShape.liftN_app_inv ED
  cases x <;> simp [ProofShape.liftN, liftVar] at Ex

/-- Exact forward residual transport from the beta contractum is impossible
for every source-typed descending relation, regardless of guard depth. -/
theorem short_not_compute_long (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedCompute Step (proofEraseCtx (.sort .zero :: Γ)) short long := by
  intro H
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  obtain ⟨e, _, E⟩ := proofErase_scoped_compute_descend hstep hΓ hΓS Ctx.LiftN.one
    (ident_typed env univs Γ 0) rfl
    (by simpa [short_erasure hΓ, short, ProofShape.liftN, liftVar] using H)
  exact long_not_lift _ E

omit [Params] in
/-- Beta cleanup removes both the captured annotation and the eta body. This
peak has a common reduct despite the failure of exact residual transport. -/
theorem long_beta_short : ProofShape.BetaRed long short := by
  apply ProofShape.BetaRed.lam
  · exact .beta
  · simpa [short, ProofShape.liftN, liftVar, ProofShape.inst] using
      (ProofShape.BetaRed.beta (A := .sort .zero) (b := .bvar 0) (a := .bvar 0))

/-- Exact typed instantiation of computation fails even if the target may use
the entire eta-expanded union. This is a computation obstruction, not merely
the absence of a selected native recovery certificate. Its original argument
and body have the required actual typings. -/
theorem exact_compute_instantiation_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Δ A p b T out, OnCtx (A :: Δ) (env.IsType univs) ∧
      env.HasType univs Δ p A ∧ env.HasType univs (A :: Δ) b T ∧
      ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx (A :: Δ))
        (proofErase (A :: Δ) b) out ∧
      ¬ ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Δ)
        (proofErase Δ (b.inst p)) (out.inst (proofErase Δ p)) := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hx : env.HasType univs (.sort .zero :: Γ) (ident 0).lift (capturedPi (.sort .zero)) :=
    identity_at_captured_pi
  have hΓC : OnCtx (capturedPi (.sort .zero) :: .sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓS, hx.isType henv hΓS⟩
  have hb : env.HasType univs (capturedPi (.sort .zero) :: .sort .zero :: Γ)
      (.bvar 0) (capturedPi (.sort .zero)).lift := .bvar .zero
  have hn := not_isProof_function_to_sort hΓC
    (A := (capturedDomain (.sort .zero)).lift) (u := .zero) hb
  refine ⟨.sort .zero :: Γ, capturedPi (.sort .zero), (ident 0).lift,
    .bvar 0, _, .lam (domain.liftN 1) (.app (.bvar 1) (.bvar 0)), hΓC, hx, hb, ?_, ?_⟩
  · rw [proofEraseCtx, ErasedRecoverySubstitutionBoundary.captured_erasure hΓ,
      show proofErase _ (.bvar 0) = .bvar 0 from if_neg hn]
    exact .base (variable_native_eta hΓ)
  · have EI : proofErase (.sort .zero :: Γ) (ident 0).lift = short := by
      simpa only [ident, tower, VExpr.lift, VExpr.liftN, liftVar, Nat.zero_lt_succ,
        ↓reduceIte, Nat.zero_add] using short_erasure hΓS
    simp only [VExpr.inst, instVar_zero, EI, eta_body_inst_short]
    exact short_not_compute_long (erased_eta_expansion_union_descent heq hs) hΓ

/-- A fully typed beta/guarded-eta peak refutes exact forward residual
transport, yet is explicitly joined by raw beta cleanup. It therefore gives
no counterexample to strengthening or to common-reduct confluence. -/
theorem typed_peak_exact_failure_and_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    TypedSource (proofEraseCtx (.sort .zero :: Γ)) source ∧
      ProofShape.BetaRed source short ∧
      ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx (.sort .zero :: Γ)) source long ∧
      (¬ ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx (.sort .zero :: Γ)) short long) ∧
      ProofShape.BetaRed long short :=
  ⟨source_typed hΓ, source_beta_short, source_compute_long hΓ,
    short_not_compute_long (erased_eta_expansion_union_descent heq hs) hΓ, long_beta_short⟩

end Lean4Lean.VEnv.Strengthening.NativeEtaBetaPeak
