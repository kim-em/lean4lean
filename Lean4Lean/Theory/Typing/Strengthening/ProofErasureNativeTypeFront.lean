import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSpineReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnitBetaBarrier

/-! # Native result-type congruence transports native argument carriers

A nonrecursive dependent observer turns native result-type comparison into
carrier transport along an ordinary typing conversion. The observer's final
arguments check at its declared domain, while its result mentions a variable
function whose context oracle may expose a different, convertible domain.
With a closed positive empty structure and this observer declaration, native
congruence from any fixed finite stage into the union implies PropositionFront.
This is a conditional sufficiency barrier, not a refutation or a smaller front.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private native_app native_const
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction
variable [Params]

/-- A closed dependent observer type: (A : Sort u) -> (f : A -> Prop) ->
(x : A) -> (f x -> Prop). Its fully supplied prefix is a non-proof. -/
def nativePropObserverType (u : VLevel) : VExpr :=
  .forallE (.sort u) (.forallE (.forallE (.bvar 0) (.sort .zero))
    (.forallE (.bvar 1) (.forallE (.app (.bvar 1) (.bvar 0)) (.sort .zero))))

/-- The observer type has a closed lambda inhabitant: return f x under its
final proof binder. Thus the declaration shape needs no recursive type,
new logical axiom, or assumption that its argument domain is inhabited. -/
theorem nativePropObserverType_inhabited (hu : u.WF univs) :
    ∃ e, env.HasType univs [] e (nativePropObserverType u) := by
  have hA : env.HasType univs [.sort u] (.bvar 0) (.sort u) := .bvar .zero
  have hF := HasType.forallE hA (HasType.sort (l := .zero) (by trivial))
  have hA' : env.HasType univs [.forallE (.bvar 0) (.sort .zero), .sort u]
      (.bvar 1) (.sort u) := .bvar (.succ .zero)
  have hf : env.HasType univs [.bvar 1, .forallE (.bvar 0) (.sort .zero), .sort u]
      (.bvar 1) (.forallE (.bvar 2) (.sort .zero)) := .bvar (.succ .zero)
  have hx : env.HasType univs [.bvar 1, .forallE (.bvar 0) (.sort .zero), .sort u]
      (.bvar 0) (.bvar 2) := .bvar .zero
  have hP := hf.app hx
  exact ⟨_, HasType.lam (HasType.sort hu) (HasType.lam hF
    (HasType.lam hA' (HasType.lam hP (hP.weak henv))))⟩

/-- Native prefix congruence transports a guard from the observer's assigned
argument domain to the function variable's native domain. No recursive type,
semantic head adequacy, or beta-transport property is used. -/
theorem JointNativePrefixTypeComparison.native_domain_guard
    (HN : JointNativePrefixTypeComparison Source Target)
    (hstep : ErasedScopedPrimitiveDescent Target)
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars) (hdecl : ci.type.instL ls = nativePropObserverType u)
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (hlookup : Lookup Γ f (.forallE B (.sort .zero)))
    (hfA : env.HasType univs Γ (.bvar f) (.forallE A (.sort .zero)))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard Source (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    JointCarrierGuard Target (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  have h0 : env.HasType univs Γ (.const c ls) (nativePropObserverType u) :=
    hdecl ▸ HasType.const hc hw hl
  have h1 : env.HasType univs Γ (.app (.const c ls) A)
      (.forallE (.forallE A (.sort .zero))
        (.forallE A.lift (.forallE (.app (.bvar 1) (.bvar 0)) (.sort .zero)))) := by
    simpa [nativePropObserverType, VExpr.inst, instVar, VExpr.liftN] using h0.app hA
  have h2 : env.HasType univs Γ (.app (.app (.const c ls) A) (.bvar f))
      (.forallE A (.forallE (.app (.bvar (f + 1)) (.bvar 0)) (.sort .zero))) := by
    simpa [VExpr.inst, instVar, VExpr.liftN, liftVar, VExpr.inst_liftN, VExpr.inst_lift, Nat.add_comm] using h1.app hfA
  have h3x : env.HasType univs Γ (.app (.app (.app (.const c ls) A) (.bvar f)) x)
      (.forallE (.app (.bvar f) x) (.sort .zero)) := by
    simpa [VExpr.inst, instVar] using h2.app hx
  have h3y : env.HasType univs Γ (.app (.app (.app (.const c ls) A) (.bvar f)) y)
      (.forallE (.app (.bvar f) y) (.sort .zero)) := by
    simpa [VExpr.inst, instVar] using h2.app hy
  have hn3x := not_isProof_function_to_sort hΓ h3x
  have hn3y := not_isProof_function_to_sort hΓ h3y
  have hn2 := not_isProof_fn hΓ h2 hx hn3x
  have hn1 := not_isProof_fn hΓ h1 hfA hn2
  have hn0 := not_isProof_fn hΓ h0 hA hn1
  have R0 := native_const (Step := Source) hΓ hc hw hl hn0
  rw [hdecl] at R0
  have R1 := native_app hΓ h0 hA hn1 R0
  have R1 : ScopedTypeRecovery Source (proofEraseCtx Γ)
      (proofErase Γ (.app (.const c ls) A))
      (proofErase Γ (.forallE (.forallE A (.sort .zero))
        (.forallE A.lift (.forallE (.app (.bvar 1) (.bvar 0)) (.sort .zero))))) := by
    simpa [nativePropObserverType, VExpr.inst, instVar, VExpr.liftN] using R1
  have R2 := native_app hΓ h1 hfA hn2 R1
  have R2 : ScopedTypeRecovery Source (proofEraseCtx Γ)
      (proofErase Γ (.app (.app (.const c ls) A) (.bvar f)))
      (proofErase Γ (.forallE A (.forallE (.app (.bvar (f + 1)) (.bvar 0)) (.sort .zero)))) := by
    simpa [VExpr.inst, instVar, VExpr.liftN, liftVar, VExpr.inst_liftN, VExpr.inst_lift, Nat.add_comm] using R2
  obtain ⟨_, hPi2⟩ := h2.isType henv hΓ
  rw [show proofErase Γ (.forallE A (.forallE (.app (.bvar (f + 1)) (.bvar 0)) (.sort .zero))) =
      .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi2)] at R2
  have HC : JointCompare Source (proofEraseCtx Γ) false
      (proofErase Γ (VExpr.mkApps (.const c ls) [A, .bvar f, x]))
      (proofErase Γ (VExpr.mkApps (.const c ls) [A, .bvar f, y])) := by
    change JointCompare Source _ false (proofErase Γ (.app _ x)) (proofErase Γ (.app _ y))
    rw [show proofErase Γ (.app (.app (.app (.const c ls) A) (.bvar f)) x) = .app _ _ from if_neg hn3x,
      show proofErase Γ (.app (.app (.app (.const c ls) A) (.bvar f)) y) = .app _ _ from if_neg hn3y]
    exact .appCarrier R2 (.leaf .refl) HX
  have walk : ∀ {z}, env.HasType univs Γ z A →
      InstForallsC env univs Γ (ci.type.instL ls) [A, .bvar f, z]
        (.forallE (.app (.bvar f) z) (.sort .zero)) := by
    intro z hz
    rw [hdecl]
    apply InstForallsC.cons hA
    simp [VExpr.inst, instVar, VExpr.liftN_zero]
    apply InstForallsC.cons hfA
    simp [VExpr.inst, instVar, VExpr.liftN, liftVar, VExpr.inst_liftN, Nat.add_comm]
    apply InstForallsC.cons hz
    simpa [VExpr.inst, instVar] using (InstForallsC.nil (T := .forallE (.app (.bvar f) z) (.sort .zero)))
  have HC := HN hΓ hc hw hl (walk hx) (walk hy) hn3x hn3y HC
  have hPx := hfA.app hx
  have hPy := hfA.app hy
  have hTx := HasType.forallE hPx (HasType.sort (l := .zero) (by trivial))
  have hTy := HasType.forallE hPy (HasType.sort (l := .zero) (by trivial))
  have HC := proofErase_joint_types_inferred hstep hΓ hTx hTy HC
  rw [show proofErase Γ (.forallE (.app (.bvar f) x) (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hTx),
    show proofErase Γ (.forallE (.app (.bvar f) y) (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hTy)] at HC
  obtain ⟨_, _, R, HC⟩ := HC.forallE_domain_exposure hhead
  obtain ⟨_, _, E, RD⟩ := R.forallE_domain_inv hhead
  cases E
  have HC := JointCheck.compute (ScopedCompute.refl (Step := Target)) RD HC
  have EF : proofErase Γ (.bvar f) = .bvar f :=
    if_neg (not_isProof_function_to_sort hΓ hfA)
  rw [show proofErase Γ (.app (.bvar f) x) = .app _ _ from if_neg (not_isProof_of_sort hΓ hPx),
    show proofErase Γ (.app (.bvar f) y) = .app _ _ from if_neg (not_isProof_of_sort hΓ hPy), EF] at HC
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, v, hB⟩
  have hPiB := HasType.forallE hB (HasType.sort (l := .zero) (by trivial))
  have HO : contextOracle (proofEraseCtx Γ) f =
      .forallE (proofErase Γ B) (.sort .zero) := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hlookup,
      show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ hPiB),
      show proofErase (B :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial)))]
  exact JointCompare.bvar_app_carrier hhead HO HC

open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- Native prefix congruence from any fixed finite stage into the union
transports argument guards along ordinary type conversion, provided the
observer at that universe is declared. The auxiliary function binder is
removed by forward typed substitution with an exactly recoverable inhabitant. -/
theorem JointNativePrefixTypeComparison.carrier_conversion_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HN : JointNativePrefixTypeComparison (ErasedJointStage D stage) (ErasedJointUnion D))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars) (hdecl : ci.type.instL ls = nativePropObserverType u)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A B (.sort u))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  have hA := HE.hasType.1
  have hB := HE.hasType.2
  let F := VExpr.forallE B (.sort .zero)
  have hF : env.HasType univs Γ F (.sort (.imax u (.succ .zero))) :=
    .forallE hB (.sort (by trivial))
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  have HFA : env.IsDefEq univs Γ F (.forallE A (.sort .zero))
      (.sort (.imax u (.succ .zero))) :=
    .forallEDF HE.symm (.sortDF (by trivial) (by trivial) rfl)
  have hlookup : Lookup (F :: Γ) 0 (.forallE B.lift (.sort .zero)) := by
    simpa only [F, lift, VExpr.liftN] using (Lookup.zero (ty := F) (Γ := Γ))
  have hfA : env.HasType univs (F :: Γ) (.bvar 0) (.forallE A.lift (.sort .zero)) := by
    simpa only [lift, VExpr.liftN] using
      (HFA.weak henv (B := F)).defeq (HasType.bvar (Lookup.zero (ty := F)))
  have HL := HX.rename (erased_joint_stage_rename heq hs stage)
    (ContextRenaming.of_liftN hΓ hΓF Ctx.LiftN.one)
  simp only [JointCheckKind.subst, subst_bvar_liftN] at HL
  rw [← proofErase_liftN hΓ hΓF Ctx.LiftN.one hA,
    ← proofErase_liftN hΓ hΓF Ctx.LiftN.one hx,
    ← proofErase_liftN hΓ hΓF Ctx.LiftN.one hy] at HL
  have HC := HN.native_domain_guard (erased_joint_union_descent heq hs) erased_joint_union_head hΓF
    hc hw hl hdecl
    (hA.weak henv) (hB.weak henv) hlookup hfA (hx.weak henv) (hy.weak henv) HL
  obtain ⟨targetStage, HC⟩ := HC.finite_stage erased_joint_stage_mono
  obtain ⟨f, hf, _, RF⟩ := recoverable_prop_function (Step := ErasedJointStage D 0) heq hΓ hB
  have Hout := proofErase_joint_carrier_inst_recoverable heq hs hΓ hf (fun _ => RF)
    ((HE.defeq hx).weak henv) ((HE.defeq hy).weak henv) HC
  simp only [Nat.zero_add, VExpr.inst_lift] at Hout
  exact Hout.mono (fun H => ⟨targetStage, H⟩)

open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnitBetaBarrier

/-- With distinct unit variables above an inserted context block, native result-type
congruence descends arbitrary proposition conversion below that block.
The initial unit guard uses no primitive steps, at any chosen finite stage. -/
theorem JointNativePrefixTypeComparison.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HN : JointNativePrefixTypeComparison (ErasedJointStage D stage) (ErasedJointUnion D))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ lsC, l.WF univs)
    (hl : lsC.length = ci.uvars) (hdecl : ci.type.instL lsC = nativePropObserverType (.succ u))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family ls)) (hne : i ≠ j)
    (HPQ : env.IsDefEqU univs Γ' (P.liftN n) (Q.liftN n)) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family ls) (.sort (.succ u)) := hS.weakN henv W
  have HE := eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  have ES : proofErase Γ' (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ' hSw)
  have Ei : proofErase Γ' (.bvar i) = .bvar i :=
    if_neg (not_proof_at_positive_type hΓ' hSw hiT)
  have Ej : proofErase Γ' (.bvar j) = .bvar j :=
    if_neg (not_proof_at_positive_type hΓ' hSw hjT)
  have HX : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
      (proofErase Γ' (.const family ls)) (proofErase Γ' (.bvar i)) (proofErase Γ' (.bvar j)) := by
    rw [ES]
    exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)
  have HG := HN.carrier_conversion_stage heq hs hc hw hl hdecl hΓ' HE.symm hiT hjT HX
  rw [Ei, Ej] at HG
  rcases HG.checked_or_exposed with HC | ⟨B, R, HB, _⟩
  · exact (hne (HC.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W hS hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Native result-type congruence from one finite stage (including stage zero)
implies PropositionFront when a closed positive empty structure and its
nonrecursive dependent observer are present. This does not establish strictness
or an unconditional converse. -/
theorem JointNativePrefixTypeComparison.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HN : JointNativePrefixTypeComparison (ErasedJointStage D stage) (ErasedJointUnion D))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ lsC, l.WF univs)
    (hl : lsC.length = ci.uvars) (hdecl : ci.type.instL lsC = nativePropObserverType (.succ u))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  let S := VExpr.const family ls
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
  have hSA : env.HasType univs (A :: Γ) S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S :: A :: Γ) (env.IsType univs) := ⟨hΓA, _, hSA⟩
  have hΓSS : OnCtx (S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓS, _, hSA.weak henv⟩
  have W3 : Ctx.LiftN 3 0 Γ (S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
  have hP3 : env.HasType univs (S :: S :: A :: Γ) (P.liftN 3) (.sort .zero) := hP.weakN henv W3
  have hQ3 : env.HasType univs (S :: S :: A :: Γ) (Q.liftN 3) (.sort .zero) := hQ.weakN henv W3
  let E := eqApp (.succ .zero) (.sort .zero) (P.liftN 3) (Q.liftN 3)
  have hE : env.HasType univs (S :: S :: A :: Γ) E (.sort .zero) :=
    HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP3 hQ3
  have hΓE : OnCtx (E :: S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓSS, _, hE⟩
  have W4 : Ctx.LiftN 4 0 Γ (E :: S :: S :: A :: Γ) := W3.cons0
  have hq : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 4) (Q.liftN 4)) := by
    have h := HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := E) (Γ := S :: S :: A :: Γ))
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using h
  have hiT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 1) S := .bvar (.succ .zero)
  have hjT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 2) S := .bvar (.succ (.succ .zero))
  have HPQ4 : env.IsDefEqU univs (E :: S :: S :: A :: Γ) (P.liftN 4) (Q.liftN 4) := by
    obtain ⟨T, HT⟩ := HPQ
    have WX : Ctx.LiftN 3 0 (A :: Γ) (E :: S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
    have H := HT.weakN henv WX
    exact ⟨_, by simpa only [VExpr.lift, VExpr.liftN_liftN] using H⟩
  exact HN.unit_probe_descend heq hs hregistry hEq hRec hc hw hl hdecl hi hp hx hf hΓ hΓE W4
    (hS.weak0 henv.ordered) hP hQ hq hiT hjT (by decide) HPQ4

end Lean4Lean.VEnv.Strengthening
