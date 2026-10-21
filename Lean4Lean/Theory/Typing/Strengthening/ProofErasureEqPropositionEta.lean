import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedNormalSyntax
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqInitialEta

/-! # Eta before the first proposition index of the Eq probe

The eta body contains only Eq.rec, Prop and its fresh proposition variable.
All proper prefixes are excluded by the existing typed arity argument, so
the eta function is fixed under full-joint computation. The consumed arbitrary
proposition therefore needs no recovery certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private nonproof_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqInitialEta
open private type_probe_prefix_typed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
variable [Params]

/-- No proper prefix of a typed retained Prop-carrier Eq prefix has a joint
primitive step. Both core and general singleton alternatives are excluded;
the statement does not assume that its proposition arguments recover types. -/
theorem proofErase_joint_union_eq_prop_short_no_step
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hk : k < 5)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q)) :
    ¬ ErasedJointUnion D (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero])
        (([.sort .zero,P,M,m,Q].map (proofErase Γ)).take k)) out := by
  intro H
  let args : List VExpr := [.sort .zero,P,M,m,Q]
  have ht' : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v,.succ .zero]) (args.take k)) (args.drop k)) T := by
    simpa only [← VExpr.mkApps_append, List.take_append_drop, args, eqRecBeforeMajor] using ht
  obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, ht'⟩
  have hnp := nonproof_head hΓ ht' (by
    simpa only [← VExpr.mkApps_append, List.take_append_drop, args, eqRecBeforeMajor] using hn)
  have EE := proofErase_const_spine hΓ hp hnp
  have HT : TypedSource (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero])
        (([.sort .zero,P,M,m,Q].map (proofErase Γ)).take k)) :=
    ⟨_, _, _, hΓ, rfl, hp, by simpa only [List.map_take] using EE⟩
  rcases erased_joint_union_typed_core_singleton heq hs hregistry HT H with HC | HG
  · obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
    apply erased_iota_eqRec_no_root (hregistry.trans hlookup)
      (hr.eqRec_target heq hn).2.1 hRec (constHead_mkApps _ _) ?_ HC
    exact .inl ⟨_, _, rfl, by simp only [List.length_take, List.length_map,
      List.length_cons, List.length_nil]; omega⟩
  · have HE := proofErase_singleton_eq_prop_prefix_arity heq
      (erased_joint_union_descent heq hs) erased_joint_union_head
      (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
      hΓ (Nat.le_of_lt hk) ht HG
    omega

/-- The eta expansion of Eq.rec Prop is scoped-normal. Its fresh argument is
a proposition variable; the proof uses typed short-prefix exclusion in that
actual extended context, not primitive exclusion in arbitrary raw contexts. -/
theorem eqRec_prop_eta_scoped_normal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedNormalSyntax (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (.sort .zero)
        (.app (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) (.bvar 0))) := by
  have hΓP : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hP : env.HasType univs (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have hS : env.HasType univs (.sort .zero :: Γ) (.sort v) (.sort (.succ v)) := .sort hv
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓP hS hP hP
  have EP : proofErase (.sort .zero :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_isProof_of_sort hΓP hP)
  have ES : proofErase (.sort .zero :: Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓP (HasType.sort (by trivial)))
  have EΓ : proofEraseCtx (.sort .zero :: Γ) = .sort .zero :: proofEraseCtx Γ := by
    simp only [proofEraseCtx, show proofErase Γ (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))]
  have H0 (out : ProofShape) := proofErase_joint_union_eq_prop_short_no_step heq hs hregistry hEq hRec hΓP
    (k := 0) (out := out) (by decide) ht hn
  have H1 (out : ProofShape) := proofErase_joint_union_eq_prop_short_no_step heq hs hregistry hEq hRec hΓP
    (k := 1) (out := out) (by decide) ht hn
  have H2 (out : ProofShape) := proofErase_joint_union_eq_prop_short_no_step heq hs hregistry hEq hRec hΓP
    (k := 2) (out := out) (by decide) ht hn
  simp only [List.map_cons, List.map_nil, List.take, ProofShape.mkApps, ES, EP, EΓ] at H0 H1 H2
  refine ⟨fun _ H => erased_joint_union_head H, ?_, ?_⟩
  · exact ⟨fun _ H => erased_joint_union_head H, trivial⟩
  · exact ⟨fun _ H => H2 _ H, (fun _ _ H => nomatch H),
      ⟨fun _ H => H1 _ H, (fun _ _ H => nomatch H),
        ⟨fun _ H => H0 _ H, trivial⟩,
        ⟨fun _ H => erased_joint_union_head H, trivial⟩⟩,
      ⟨fun _ H => erased_joint_union_head H, trivial⟩⟩

/-- Eta before the first proposition index is removable for every raw argument
and pending spine. Unlike general eta removal, this needs no recovery or even
typing premise for that argument; the eta function is already scoped-normal. -/
theorem eqRec_prop_eta_spine_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (.sort .zero)
        (.app (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) (.bvar 0)))
        (p :: xs)) (.sort w) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.app (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) p)
        xs) (.sort w) := by
  apply ScopedCompute.fixed_eta_spine_sort_iff (Step := ErasedJointUnion D)
    (f := .app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) erased_joint_union_head
  intro out R
  exact R.fixed_of_scoped_normal (eqRec_prop_eta_scoped_normal heq hs hregistry hEq hRec hv hΓ)

/-- The actual Eq type probe retains its exact original index-certificate
criterion after eta before the first proposition argument. That proposition
may be arbitrary; neither its recovery nor a normalization premise is used. -/
theorem eqTypeProbe_proposition_eta_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (.sort .zero)
        (.app (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) (.bvar 0)))
        [proofErase Γ P,
          proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
          .sort v, proofErase Γ Q, .proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqRec_prop_eta_spine_sort_iff heq hs hregistry hEq hRec hv hΓ
    (p := proofErase Γ P) (xs := [
      proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
      .sort v, proofErase Γ Q, .proof]) (w := v)
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have E := eqTypeProbe_erase heq hΓ hS hP hQ hq
  rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hS)] at E
  change _ ↔ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
    (mkApps (.const ``Eq.rec [.succ (.succ v), .succ .zero])
      [.sort .zero, proofErase Γ P,
        proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
        .sort v, proofErase Γ Q, .proof]) (.sort v) at H
  rw [← E] at H
  exact H.trans (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ hP hQ hq)

/-- Removing this proposition-index eta also retains the lower comparison
certificate across arbitrary binder insertion. The equality major is required
only upstairs; the proposition image requires no exact type recovery. -/
theorem eqTypeProbe_proposition_eta_sort_below_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q
      (eqApp (.succ .zero) (.sort .zero) (P.liftN n k) (Q.liftN n k))) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (mkApps (.lam (.sort .zero)
        (.app (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) (.bvar 0)))
        [proofErase Γ' (P.liftN n k),
          proofErase Γ' (constantEqMotive (.succ .zero) (.sort .zero)
            (P.liftN n k) (.sort (.succ v))),
          .sort v, proofErase Γ' (Q.liftN n k), .proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqTypeProbe_proposition_eta_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  exact H.trans (by
    rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ]
    exact proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
