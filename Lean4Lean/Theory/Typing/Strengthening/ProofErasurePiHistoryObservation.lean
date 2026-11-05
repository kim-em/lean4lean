import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiHistory

/-! # Retaining a reified family through hidden Pi control frames

Typed marked observations keep the control frames around a Pi instead of
contracting them before an argument is supplied. Lower-context substitution
changes their payload certificates, without requiring native argument recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation

private theorem raw_liftN_subst_liftN (e : ProofShape) (σ : ProofShape.Subst) :
    (e.liftN n).subst (σ.liftN n) = (e.subst σ).liftN n := by
  induction n with
  | zero => simp only [ProofShape.liftN_zero, ProofShape.Subst.liftN]
  | succ n ih =>
    rw [← ProofShape.liftN_add, ProofShape.Subst.liftN,
      ProofShape.lift_subst_lift, ih, ProofShape.liftN_add]

private theorem raw_subst_liftN_lt (σ : ProofShape.Subst) (h : i < n) :
    σ.liftN n i = .bvar i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => simp [ProofShape.Subst.liftN, ProofShape.Subst.lift, ih (i := i) (by omega),
        ProofShape.liftN, liftVar, Nat.add_comm]

variable [Params] {D : PureObservation.Definitions}

/-- Substitute the original context below temporary controls, transforming
its marked payload at the same time. Free demands are restricted to the
unchanged temporary controls; the lower substitution needs ordinary typing
only, with no native-image or computation-substitution premise. -/
theorem ProofShape.ControlObservation.Obs.subst_lower
    (H : Obs P n Δ S e t o)
    (W : ContextSubstitution Δ Δ' (σ.liftN n))
    (hP : ∀ A B, P A B → Q (A.subst σ) (B.subst σ.lift))
    (hS : ∀ i t key, S i t key → i < n) :
    Obs Q n Δ' S (e.subst (σ.liftN n)) t o := by
  induction H generalizing Δ' with
  | @var Δ i t o S n HT HD h =>
    have E := raw_subst_liftN_lt σ (hS i t o h)
    simpa only [ProofShape.subst, E] using
      (Obs.var (by simpa only [ProofShape.subst, E] using HT.subst W) HD h :
        Obs Q n Δ' S (.bvar i) t o)
  | payload HT HP =>
    have H' := HT.subst W
    rw [raw_liftN_subst_liftN] at H' ⊢
    exact .payload H' (hP _ _ HP)
  | app HT _ _ ihf iha =>
    exact .app (HT.subst W) (ihf W hS) (fun key hk => iha key hk W hS)
  | @lam Δ A b C E keys n S o HT HK HB ih =>
    apply Obs.lam (HT.subst W) HK
    apply ih W.cons
    intro i t key hi
    cases i with
    | zero => omega
    | succ i => exact Nat.succ_lt_succ (hS i t key hi)

/-- A literal unary payload retains a family that computes to its lambda
form and natively recovers the matching sort header. -/
def ReifiedUnaryPiPayload (D : PureObservation.Definitions) (Γ : List VExpr)
    (f : VExpr) (u : VLevel) (X Y : ProofShape) : Prop :=
  ∃ A B, proofErase Γ A = X ∧ proofErase (A :: Γ) B = Y ∧
    NativeFamilyPiHistory D Γ f u [A] B

/-- The family evidence survives arbitrary component computations below
control binders. Certificate descent removes only those temporary binders;
the family keeps the original lower context. -/
theorem reified_unary_pi_payload_componentClosure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    PiOriginComponentClosure (ErasedStaticStructureEtaExpansionUnion D) Γ
      (ReifiedUnaryPiPayload D Γ f u) := by
  intro Γ' n X Y outX outY hΓ' W HP RX RY
  obtain ⟨A, B, rfl, rfl, H⟩ := HP
  obtain ⟨⟨v, hA⟩, _⟩ := (H.typed.isType henv hΓ).forallE_inv henv
  have hB : env.HasType univs (A :: Γ) B (.sort u) := H.body
  obtain ⟨X', Y', HO, EX, EY⟩ := static_structure_piOrigin_componentClosure
    heq hs hΓ hΓ' W (StaticStructurePiOrigin.refl (D := D) hA hB) RX RY
  obtain ⟨A', B', HA', hB', EA', EB', RA', RB'⟩ := HO
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
  have hT' : env.IsType univs Γ (.forallE A' B') := ⟨_, .forallE HA'.hasType.2 hB'⟩
  have RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A' B')) := by
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (.forallE hA hB)),
      show proofErase Γ (.forallE A' B') = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hT'.choose_spec), EA', EB']
    exact .forallE RA' RB'
  exact ⟨X', Y', ⟨A', B', EA', EB', H.convert heq hs hΓ rfl hT' RT⟩, EX, EY⟩

/-- Substituting a supplied parameter transports a generic Pi payload into a
reified unary payload. The full family runs the generic component histories
before application; substitution of those computation certificates is not used. -/
theorem reified_unary_pi_payload_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeFamilyPiHistory D Γ f u [A, B] C)
    (hx : env.HasType univs Γ x A)
    (HP : StaticStructurePiOrigin D (A :: Γ) B C v u X Y) :
    ReifiedUnaryPiPayload D Γ (.app f x) u (X.inst (proofErase Γ x))
      (Y.inst (proofErase Γ x) 1) := by
  obtain ⟨B', C', HBB', hC', EB', EC', RB', RC'⟩ := HP
  obtain ⟨⟨w, hA⟩, _⟩ := (H.typed.isType henv hΓ).forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  have hB := HBB'.hasType.1
  have hC : env.HasType univs (B :: A :: Γ) C (.sort u) := H.body
  have hTarget := HasType.forallE hA (HasType.forallE HBB'.hasType.2 hC')
  have RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A (.forallE B C)))
      (proofErase Γ (.forallE A (.forallE B' C'))) := by
    rw [show proofErase Γ (.forallE A (.forallE B C)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (.forallE hA (.forallE hB hC))),
      show proofErase Γ (.forallE A (.forallE B' C')) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hTarget)]
    apply ScopedCompute.forallE .refl
    rw [show proofErase (A :: Γ) (.forallE B C) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓA (.forallE hB hC)),
      show proofErase (A :: Γ) (.forallE B' C') = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓA (.forallE HBB'.hasType.2 hC')), EB', EC']
    exact .forallE RB' RC'
  have H' := H.convert heq hs hΓ (ds' := [A, B']) (B' := C') rfl ⟨_, hTarget⟩ RT
  have HI := H'.apply hΓ hx
  refine ⟨B'.inst x, C'.inst x 1, ?_, ?_, HI⟩
  · rw [proofErase_instN hΓA hx Ctx.InstN.zero HBB'.hasType.2, EB']
  · have hΓB : OnCtx (B' :: A :: Γ) (env.IsType univs) := ⟨hΓA, v, HBB'.hasType.2⟩
    rw [proofErase_instN hΓB hx Ctx.InstN.zero.succ hC', EC']

/-- A hidden inner Pi retains its reified family after a typed parameter is
supplied. The observation preserves all control frames around that Pi, so a
later selected conversion can run from the original opaque residual. -/
theorem NativeFamilyPiHistory.observe_inner_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeFamilyPiHistory D Γ f u [A, B] C)
    (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.forallE B C)) out) :
    ∃ v, Obs (ReifiedUnaryPiPayload D Γ (.app f x) u) 0 (proofEraseCtx Γ)
      (fun _ _ _ => False) (out.inst (proofErase Γ x)) (.sort v) .pi := by
  obtain ⟨⟨w, hA⟩, hRest⟩ := (H.typed.isType henv hΓ).forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  obtain ⟨⟨v, hB⟩, _⟩ := hRest.forallE_inv henv.ordered
  have hC : env.HasType univs (B :: A :: Γ) C (.sort u) := H.body
  have hPi := HasType.forallE hB hC
  have E : proofErase (A :: Γ) (.forallE B C) =
      .forallE (proofErase (A :: Γ) B) (proofErase (B :: A :: Γ) C) :=
    if_neg (not_isProof_of_sort hΓA hPi)
  have HO : Obs (StaticStructurePiOrigin D (A :: Γ) B C v u) 0 (proofEraseCtx (A :: Γ))
      (fun _ _ _ => False) (proofErase (A :: Γ) (.forallE B C)) (.sort (.imax v u)) .pi := by
    rw [E]
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero, ← E] using
          ControlTyping.of_typed (t := .sort (.imax v u)) hΓA hPi)
        (StaticStructurePiOrigin.refl (D := D) hB hC))
  have HR := proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_controlObservation heq hs)
    (static_structure_piOrigin_componentClosure heq hs hΓA) R hΓA (Ctx.LiftN.zero []) hPi rfl rfl
    (fun _ _ _ h => h.elim) HO
  have WI := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ x)) :=
    ContextSubstitution.of_typed hΓ WI (erasedSubstAgreement_one hΓA hx)
  refine ⟨.imax v u, ?_⟩
  have HS := HR.subst_lower (Q := ReifiedUnaryPiPayload D Γ (.app f x) u) W
    (fun X Y HP => by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using
        reified_unary_pi_payload_inst heq hs hΓ H hx HP)
    (fun _ _ _ h => h.elim)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using HS

/-- A selected Pi exposed only after parameter supply still has the original
partial family as its reified ancestor. The intervening residual may be opaque;
its chosen computation is preserved, without beta-normalizing it first. -/
theorem NativeFamilyPiHistory.inner_inst_selected_pi
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeFamilyPiHistory D Γ f u [A, B] C)
    (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.forallE B C)) middle)
    (RS : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (middle.inst (proofErase Γ x)) (.forallE X Y)) :
    ReifiedUnaryPiPayload D Γ (.app f x) u X Y := by
  obtain ⟨⟨w, hA⟩, hRest⟩ := (H.typed.isType henv hΓ).forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  obtain ⟨⟨v, hB⟩, _⟩ := hRest.forallE_inv henv.ordered
  have hC : env.HasType univs (B :: A :: Γ) C (.sort u) := H.body
  obtain ⟨M, HM, EM⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA
    (HasType.forallE hB hC) rfl rfl R
  have hI := HM.hasType.2.instN henv.ordered Ctx.InstN.zero hx
  have EI : proofErase Γ (M.inst x) = middle.inst (proofErase Γ x) := by
    rw [proofErase_instN hΓA hx Ctx.InstN.zero HM.hasType.2, EM]
  obtain ⟨q, HO⟩ := H.observe_inner_inst heq hs hΓ hx R
  have HS := proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_controlObservation heq hs)
    (reified_unary_pi_payload_componentClosure heq hs hΓ) RS hΓ (Ctx.LiftN.zero []) hI rfl EI
    (fun _ _ _ h => h.elim) HO
  exact HS.literal_pi_payload

/-- Two supplied arguments retain their exact selected native output, even
when the residual Pi is hidden between applications. Only the original term
head's type-origin property is assumed; neither argument needs native recovery. -/
theorem NativeFamilyPiHistory.native_binary_application_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeFamilyPiHistory D Γ g u [A, B] C)
    (hx : env.HasType univs Γ x A)
    (hz : env.HasType univs Γ z (B.inst x))
    (HN : ∀ {T}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f T →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A (.forallE B C))) T)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) imageX)
    (RZ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ z) imageZ)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.app f imageX) imageZ) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.app g x) z)) out := by
  obtain ⟨rawB, rawC, RF1, RFinal⟩ := RN.app_origin
  obtain ⟨rawA, middle, RF0, RBetween⟩ := RF1.app_origin
  have RT := HN RF0
  obtain ⟨⟨w, hA⟩, hRest⟩ := (H.typed.isType henv hΓ).forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  obtain ⟨⟨v, hB⟩, _⟩ := hRest.forallE_inv henv.ordered
  have hC : env.HasType univs (B :: A :: Γ) C (.sort u) := H.body
  have hBC := HasType.forallE hB hC
  rw [show proofErase Γ (.forallE A (.forallE B C)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (.forallE hA hBC))] at RT
  obtain ⟨_, _, _, _, _, _, _, RB⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hBC RT
  obtain ⟨y, HXY, EY⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hx rfl rfl RX
  rw [← EY] at RBetween
  obtain ⟨B', C', EB', EC', HG⟩ := H.inner_inst_selected_pi heq hs hΓ HXY.hasType.2 RB RBetween
  have HX := H.apply hΓ hx
  have HY := H.apply hΓ HXY.hasType.2
  have HE : env.IsDefEq univs Γ (.app g x) (.app g y) (.forallE (B.inst x) (.sort u)) :=
    IsDefEq.appDF H.typed HXY
  have HGY : env.HasType univs Γ (.app g y) (.forallE (B.inst x) (.sort u)) := HE.hasType.2
  obtain ⟨⟨q, HD⟩, _⟩ := (HGY.uniqU henv hΓ HG.typed).forallE_inv henv hΓ
  have hz' := HD.defeq hz
  obtain ⟨z', HZZ', EZ⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hz' rfl rfl RZ
  have HEnd := HG.apply hΓ HZZ'.hasType.2
  have hGXZ : env.HasType univs Γ (.app (.app g x) z) (.sort u) := HX.typed.app hz
  have hGYZ' : env.HasType univs Γ (.app (.app g y) z') (.sort u) := HEnd.typed
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.app g x) z)) (proofErase Γ (.app (.app g y) z')) := by
    rw [show proofErase Γ (.app (.app g x) z) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hGXZ),
      show proofErase Γ (.app (.app g y) z') = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hGYZ'),
      show proofErase Γ (.app g x) = .app _ _ from
      if_neg (not_isProof_telescope_to_sort hΓ HX.typed),
      show proofErase Γ (.app g y) = .app _ _ from
      if_neg (not_isProof_telescope_to_sort hΓ HY.typed), EY, EZ]
    exact .app (.app .refl RX) RZ
  have hΓB' : OnCtx (B' :: Γ) (env.IsType univs) :=
    (HG.typed.etaOpen_wf henv.ordered hΓ).1
  have EFinal : proofErase Γ (C'.inst z') = rawC.inst imageZ := by
    rw [proofErase_instN hΓB' HZZ'.hasType.2 Ctx.InstN.zero HG.body, EC', EZ]
  exact RP.trans (HEnd.finish.trans (EFinal ▸ RFinal))

end Lean4Lean.VEnv.Strengthening
