import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWrappedHeadCut
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpecializedReadout

/-! # The target completion needed at an actual Eq head loss

One semantic ancestry witness supplies both the short-arity bound and readout
of the selected root. Ambient unused binders are descended before the source
prefix is specialized. Producing this witness through arbitrary wrapped-head
histories remains open; typing and a constant head alone do not supply it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private computed_prefix_length
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaComputed
variable [Params]

/-- A selected raw Eq head comes from a typed, nonproof prefix whose semantic
completion is the original target vector. The source realization may lie
below ambient unused binders; no target inhabitant for those binders is
required. This is the ancestry data still missing at arbitrary head losses. -/
def EqHeadCompletion (Δ : List VExpr) (v w : VLevel) (original : List VExpr)
    (Ξ : List ProofShape) (source : ProofShape) : Prop :=
  ∃ Γ Γ' count offset v' w' pre F,
    OnCtx Γ (env.IsType univs) ∧ OnCtx Γ' (env.IsType univs) ∧
    Ctx.LiftN count offset Γ Γ' ∧ proofEraseCtx Γ' = Ξ ∧
    env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
    ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
    EqPrefixSpecialization Γ Δ v w v' w' original pre ∧
    (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)).liftN count offset = source

/-- Completion bounds the actual erased prefix by the original vector's
length. This arity fact is a consequence of ancestry, not a separate premise. -/
theorem EqHeadCompletion.arity
    (H : EqHeadCompletion Δ v w original Ξ source) :
    ∃ ls args, source = ProofShape.mkApps (.const ``Eq.rec ls) args ∧
      args.length ≤ original.length := by
  obtain ⟨Γ, Γ', count, offset, v', w', pre, F, hΓ, _, _, _, hf, hn, HP, rfl⟩ := H
  obtain ⟨σ, pending, HP⟩ := HP
  have hlen := HP.2.2.length_eq
  rw [proofErase_const_spine hΓ hf hn, ProofShape.liftN_mkApps, ProofShape.liftN]
  refine ⟨_, _, rfl, ?_⟩
  simp only [List.length_map, List.length_append] at hlen ⊢
  omega

/-- An actual primitive losing the tracked Eq head reads the original target
equation whenever it has a target completion. Completion supplies the short
arity; the head invariant excludes eta and the other administrative roots.
Both singleton guards are read below ambient binders before specialization. -/
theorem EqHeadCompletion.read_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqHeadCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HR : PiInertStage D n Ξ source target)
    (HN : ¬ WrappedConstHead ``Eq.rec target) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨Γ, Γ', count, offset, v', w', pre, F, hΓ, hΓ', W, rfl, hf, hn, HP, rfl⟩ := H
  have hlen : pre.length ≤ 5 := by
    obtain ⟨σ, pending, HP⟩ := HP
    have HL := HP.2.2.length_eq
    simp only [List.length_cons, List.length_nil, List.length_append, List.length_map] at HL
    omega
  have EE := proofErase_const_spine hΓ hf hn
  have HT : TypedSource (proofEraseCtx Γ')
      ((proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)).liftN count offset) :=
    ⟨Γ', _, _, hΓ', rfl, hf.weakN henv W, proofErase_liftN hΓ hΓ' W hf⟩
  rw [EE, ProofShape.liftN_mkApps, ProofShape.liftN] at HR HT
  rcases pi_inert_short_eq_head_loss_singleton heq hs hreg hoff hRec HT
      (by simpa only [List.length_map] using hlen) HR HN with HQ | ⟨k, _, HG⟩
  · have hfive : pre.length = 5 := by
      simpa only [List.length_map] using computed_prefix_length HQ
    obtain ⟨α', a', M', minor', b', rfl⟩ :
        ∃ α' a' M' minor' b', pre = [α',a',M',minor',b'] := by
      cases pre with | nil => simp at hfive | cons x xs =>
      cases xs with | nil => simp at hfive | cons y ys =>
      cases ys with | nil => simp at hfive | cons z zs =>
      cases zs with | nil => simp at hfive | cons q qs =>
      cases qs with | nil => simp at hfive | cons r rs =>
      cases rs with
      | nil => exact ⟨_, _, _, _, _, rfl⟩
      | cons s ss => simp at hfive
    apply HP.read_computed_guard heq
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs n)
      hΓ hΓ' W hΔ ht hf (rest := []) (pending := []) ?_ HQ
    simp only [List.append_nil]
    exact List.Forall₂.rfl (fun _ _ => ScopedCompute.refl)
  · apply HP.read_singleton heq
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k)
      hΓ hΓ' W hΔ ht hf hn
    simpa only [EE, ProofShape.liftN_mkApps, ProofShape.liftN] using HG

/-- A concrete failure of target ancestry at a selected typed Eq head loss.
Both counted paths and the scoped hole are retained within the original
budget. This is a necessary residue of a counterexample to Eq readout, not
an assertion that such a failure exists or a completed strengthening result. -/
def EqHeadCompletionFailure (D : Definitions) (Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (budget : Nat) : Prop :=
  ∃ Ξ Θ n source endpoint ls args target cp ct, ∃ C : ScopedHole Ξ Θ,
    cp+1+ct ≤ budget ∧ TypedSource Ξ source ∧
    ScopedComputeCount (PiInertStage D n) cp Ξ source (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) args)) ∧
    TypedSource Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∧
    ¬ WrappedConstHead ``Eq.rec target ∧
    ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint ∧
    ¬ EqHeadCompletion Δ v w original Θ (ProofShape.mkApps (.const ``Eq.rec ls) args)

/-- Forgetting only the missing-completion condition recovers the existing
cost-bounded typed head-loss result. The exact paths and hole are unchanged. -/
theorem EqHeadCompletionFailure.forget
    (H : EqHeadCompletionFailure D Δ v w original budget) :
    TypedWrappedHeadLoss D ``Eq.rec budget := by
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, HT, RP, _, HR, HN, RT, _⟩ := H
  exact ⟨Ξ, n, cp+1+ct, source, endpoint, hc, HT,
    Θ, _, target, C, cp, ct, rfl, RP, HR, WrappedConstHead.const.mkApps args, HN, RT⟩

/-- The same selected typed head loss either reads the original Eq equation
or lacks any completing realization, even one below ambient unused binders.
This packages the remaining ancestry gap without imposing a separate arity
hypothesis or adding any assumption to the original computation. -/
theorem TypedWrappedHeadLoss.eq_or_completion_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : TypedWrappedHeadLoss D ``Eq.rec budget) :
    env.IsDefEq univs Δ a b α ∨
      EqHeadCompletionFailure D Δ v w [α,a,M,minor,b] budget := by
  classical
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, HT, RP, HTroot, HR, HN, _, _, _, _, RT⟩ := H.root heq hs
  by_cases HP : EqHeadCompletion Δ v w [α,a,M,minor,b] Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args)
  · exact .inl (HP.read_loss heq hs hreg hoff hRec hΔ ht HR HN)
  · exact .inr ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
      hc, HT, RP, HTroot, HR, HN, RT, HP⟩

end Lean4Lean.VEnv.Strengthening
