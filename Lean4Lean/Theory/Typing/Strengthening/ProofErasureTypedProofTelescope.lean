import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationEq
import Lean4Lean.Theory.Typing.Strengthening.SingletonTransportComparison

/-! # Computation chains through dependent proof telescopes

Every retained variable comes from the original context. Typed substitution
therefore gives identical erasures at any two witness lists, including for data
bodies. Ordinary proof irrelevance supplies the accompanying typed equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params SingletonLayout
variable {S : SingletonLayout}
variable [Params] {D : PureObservation.Definitions}

/-- A retained variable below a telescope of propositions comes from the
original context; every newly bound variable is a proof. -/
theorem proof_telescope_retained_lookup
    (H : PropTelescope env univs Γ ds) (hl : Lookup (ds.reverse ++ Γ) i A)
    (hn : ¬ IsProof (ds.reverse ++ Γ) (.bvar i)) : ds.length ≤ i := by
  induction H generalizing i A with
  | nil => exact Nat.zero_le _
  | snoc H hd ih =>
    simp only [List.reverse_append, List.reverse_singleton, List.cons_append, List.nil_append] at hl hn
    cases hl with
    | zero =>
      exact False.elim (hn ⟨_, .bvar .zero, hd.weakN henv.ordered Ctx.LiftN.one⟩)
    | succ hl =>
      have hh := ih hl (fun hp => hn (hp.lift' (Ctx.Lift'.skip .refl)))
      simp only [List.length_append, List.length_singleton]
      omega

/-- Any two typed instances of a proof telescope have literally identical
body erasures. Only retained-variable substitution agreement is needed. -/
theorem proof_telescope_instOuter_erasure
    (hΓ : OnCtx Γ (env.IsType univs)) (H : PropTelescope env univs Γ ds)
    (ha : TelInst env univs Γ ds args) (hb : TelInst env univs Γ ds args')
    (ht : env.HasType univs (ds.reverse ++ Γ) e T) :
    proofErase Γ (e.instOuter args) = proofErase Γ (e.instOuter args') := by
  simp only [instOuter_eq_subst]
  apply proofErase_template_congr hΓ hΓ (H.substEq henv hΓ ha ha) (H.substEq henv hΓ hb hb) ht
  intro i A hl hn
  have hi := proof_telescope_retained_lookup H hl hn
  simp only [Subst.ofList, ha.1, hb.1, dif_neg (Nat.not_lt.mpr hi)]

/-- Substituting any two typed witness lists into a typed body yields a chain.
The body and its type may contain arbitrary data; no ordinary-equality
completeness, native recovery or type-fork joining is assumed. -/
theorem proof_telescope_instOuter_chain
    (hΓ : OnCtx Γ (env.IsType univs)) (H : PropTelescope env univs Γ ds)
    (ha : TelInst env univs Γ ds args) (hb : TelInst env univs Γ ds args')
    (ht : env.HasType univs (ds.reverse ++ Γ) e T) :
    TypedComputationEq D Γ (e.instOuter args) (e.instOuter args') (T.instOuter args) := by
  exact .of_erasure_eq (H.instOuter_eq henv hΓ ha hb ht)
    (proof_telescope_instOuter_erasure hΓ H ha hb ht)

omit [Params] in
private theorem proof_telescope_getD_instOuter_map {xs : List VExpr} (hl : l < xs.length) :
    (xs.map (·.instOuter t)).getD l default = (xs.getD l default).instOuter t := by
  simp only [getD_of_lt (by simpa using hl : l < (xs.map (·.instOuter t)).length),
    List.getElem_map, getD_of_lt hl]

/-- Reconstructed fields have identical erasures at any two typed witness
lists, including dependent data fields and arbitrary requested indices. -/
theorem singleton_substHat_witness_erasure
    (heq : env.HasCanonicalEq)
    (T : S.Typed env univs params) (hΓ : OnCtx Γ (env.IsType univs))
    (hpa : TelInst env univs Γ params pa)
    (hia : TelInst env univs Γ (params ++ S.indices) (pa ++ ia))
    (hialen : ia.length = S.indices.length) (hi : i ≤ S.fields.length)
    (ht : TelInst env univs Γ (S.tel pa ia i).1 t)
    (ht' : TelInst env univs Γ (S.tel pa ia i).1 t') (hl : l < i) :
    proofErase Γ ((S.substHat pa ia i t).getD l default) =
      proofErase Γ ((S.substHat pa ia i t').getD l default) := by
  obtain ⟨_, hinst⟩ := tel_typed henv heq T hΓ hpa hia hialen i hi
  have hprop := tel_propTelescope henv heq T hΓ hpa hia hialen i hi
  have hv := hinst.getD (j := params.length + l) (by simp; omega)
  rw [getD_append_right' (by simp [hpa.1])] at hv
  simp only [List.length_map, hpa.1, Nat.add_sub_cancel_left] at hv
  have h := proof_telescope_instOuter_erasure hΓ hprop ht ht' hv
  have hscope := T.scope.mono_pa hpa.1
  have htl := ht.1.trans (S.tel_length pa ia i).1
  have htl' := ht'.1.trans (S.tel_length pa ia i).1
  rw [← tel_instOuter hscope hialen i t htl,
    ← tel_instOuter hscope hialen i t' htl',
    proof_telescope_getD_instOuter_map (by simpa only [(S.tel_length pa ia i).2] using hl),
    proof_telescope_getD_instOuter_map (by simpa only [(S.tel_length pa ia i).2] using hl)]
  exact h

/-- Changing the proof witnesses of a singleton cast telescope produces an
actual chain for each reconstructed field, including dependent data fields. -/
theorem singleton_substHat_witness_chain
    (heq : env.HasCanonicalEq)
    (T : S.Typed env univs params) (hΓ : OnCtx Γ (env.IsType univs))
    (hpa : TelInst env univs Γ params pa)
    (hia : TelInst env univs Γ (params ++ S.indices) (pa ++ ia))
    (hialen : ia.length = S.indices.length) (hi : i ≤ S.fields.length)
    (ht : TelInst env univs Γ (S.tel pa ia i).1 t)
    (ht' : TelInst env univs Γ (S.tel pa ia i).1 t') (hl : l < i) :
    ∃ A, TypedComputationEq D Γ ((S.substHat pa ia i t).getD l default)
      ((S.substHat pa ia i t').getD l default) A := by
  obtain ⟨A, HE⟩ := substHat_proof_irrel henv heq T hΓ hpa hia hialen hi ht ht' hl
  exact ⟨A, .of_erasure_eq HE
    (singleton_substHat_witness_erasure heq T hΓ hpa hia hialen hi ht ht' hl)⟩

end Lean4Lean.VEnv.Strengthening
