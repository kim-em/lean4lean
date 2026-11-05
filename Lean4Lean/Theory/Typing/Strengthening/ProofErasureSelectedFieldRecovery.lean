import Lean4Lean.Theory.Typing.Strengthening.ProofErasureObservedDeclarationHeaders

/-! # Constructing selected recovery after ignored-field header simplification

Header simplification need not preserve ancestry of every old native output.
It does construct one new recovery: a literal telescope with a field-independent
result can be supplied by any raw images of the correct arity.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private raw_liftN_subst_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiHistoryObservation

private theorem inst_wrapForalls (ds : List ProofShape) (B x : ProofShape) (k : Nat) :
    ∃ es, es.length = ds.length ∧ (ProofShape.wrapForalls ds B).inst x k =
      ProofShape.wrapForalls es (B.inst x (k + ds.length)) := by
  induction ds generalizing k with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons A ds ih =>
    obtain ⟨es, hlen, HE⟩ := ih (k+1)
    refine ⟨A.inst x k :: es, congrArg Nat.succ hlen, ?_⟩
    simpa only [ProofShape.wrapForalls, List.foldr_cons, ProofShape.inst,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
      congrArg (ProofShape.forallE (A.inst x k)) HE

private theorem inst_ignored_lift (B x : ProofShape) (n : Nat) :
    (B.liftN (n+1)).inst x n = B.liftN n := by
  have E : B.liftN (n+1) = (B.liftN 1).liftN n := by
    rw [ProofShape.liftN_add]
    congr 1
    omega
  rw [E, ProofShape.inst_eq_subst, raw_liftN_subst_liftN]
  simp only [ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]

variable [Params]

/-- Supplying every field of a literal raw telescope recovers its ignored
result exactly. Images need only the correct arity: they need not be typed,
computational images, or natively recoverable. Dependencies between domains do
not affect the final result. This holds for any primitive relation. -/
theorem ProofShape.ScopedTypeRecovery.supply_ignored_fields
    (RN : ScopedTypeRecovery Step Δ f (ProofShape.wrapForalls ds (B.liftN ds.length)))
    (hlen : images.length = ds.length) :
    ScopedTypeRecovery Step Δ (ProofShape.mkApps f images) B := by
  induction images generalizing ds f with
  | nil =>
    have E : ds = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ds
    simpa only [ProofShape.wrapForalls, List.foldr_nil, List.length_nil,
      ProofShape.liftN_zero, ProofShape.mkApps] using RN
  | cons x images ih =>
    cases ds with
    | nil => simp at hlen
    | cons A ds =>
      obtain ⟨es, hEs, E⟩ := inst_wrapForalls ds (B.liftN (ds.length+1)) x 0
      simp only [Nat.zero_add, inst_ignored_lift] at E
      have R := ScopedTypeRecovery.app (a := x) RN
      change ScopedTypeRecovery Step Δ (.app f x)
        ((ProofShape.wrapForalls ds (B.liftN (ds.length+1))).inst x) at R
      rw [E, ← hEs] at R
      exact ih R (by simpa only [List.length_cons, Nat.add_right_cancel_iff, hEs] using hlen)

/-- A selected header that computes to a literal ignored-field telescope
constructs exact recovery of its result after all raw arguments are supplied.
The direction is from the existing native output to the literal header; no
ancestry of other selected outputs, computation confluence, or native argument
premise is asserted. -/
theorem proofErase_native_selected_ignored_fields
    (hΓ : OnCtx Γ (env.IsType univs)) (hg : env.HasType univs Γ result (.sort u))
    (hctx : OnCtx (fields.reverse ++ Γ) (env.IsType univs))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) head T)
    (RH : ScopedCompute Step (proofEraseCtx Γ) T
      (proofErase Γ (VExpr.wrapForalls fields (result.liftN fields.length))))
    (hlen : images.length = fields.length) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (ProofShape.mkApps head images) (proofErase Γ result) := by
  have HW : Ctx.LiftN fields.length 0 Γ (fields.reverse ++ Γ) := .zero fields.reverse (by simp)
  obtain ⟨w, hPi⟩ := VExpr.wrapForalls_defeq hctx (hg.weakN henv HW)
  have RR := RN.convert RH
  rw [proofErase_wrapForalls_type hΓ ⟨w, hPi.hasType.1⟩,
    proofErase_liftN hΓ hctx HW hg, ← proofEraseDomains_length (Γ := Γ) (domains := fields)] at RR
  exact RR.supply_ignored_fields (by simpa only [proofEraseDomains_length] using hlen)

/-- A stored constant header may simplify to a literal ignored-field
telescope. The resulting constructor spine recovers the chosen result exactly,
for every raw argument vector of the right length. This is an existence result
for a selected recovery, not a path from the chosen result to all earlier native
outputs. The same statement applies to proof-valued raw constructor spines. -/
theorem proofErase_declared_selected_ignored_fields
    (hΓ : OnCtx Γ (env.IsType univs)) (hg : env.HasType univs Γ result (.sort u))
    (hc : env.constants ctor = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (hctx : OnCtx (fields.reverse ++ Γ) (env.IsType univs))
    (RH : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (ci.type.instL ls))
      (proofErase Γ (VExpr.wrapForalls fields (result.liftN fields.length))))
    (hlen : images.length = fields.length) :
    ScopedTypeRecovery Step (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ctor ls) images) (proofErase Γ result) := by
  have hfc : env.HasType univs [] (.const ctor ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨_, hT⟩ := hfc.isType henv (by trivial)
  have E := proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ
  apply proofErase_native_selected_ignored_fields hΓ hg hctx ?_ RH hlen
  rw [E]
  exact .const hc hw hl

end Lean4Lean.VEnv.Strengthening
