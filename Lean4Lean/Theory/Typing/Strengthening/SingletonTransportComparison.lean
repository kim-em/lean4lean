import Lean4Lean.Theory.Typing.Strengthening.ProofTelescopeIrrelevance

/-! # Comparing transported and aligned singleton reconstruction

Witnesses of the cast telescope are proofs. Any two typed witness lists therefore
produce definitionally equal reconstructed fields. At aligned occurrences this
identifies the new transported fields with the existing generated fields and
with any aligned constructor field instance.
-/
namespace Lean4Lean
open VExpr VEnv SingletonLayout

namespace SingletonLayout
variable {S : SingletonLayout}

private theorem getD_instOuter_map {xs : List VExpr} (hl : l < xs.length) :
    (xs.map (·.instOuter t)).getD l default = (xs.getD l default).instOuter t := by
  simp only [getD_of_lt (by simpa using hl : l < (xs.map (·.instOuter t)).length),
    List.getElem_map, getD_of_lt hl]

/-- The reconstructed fields do not depend definitionally on the chosen proofs
of the reconstruction telescope. Parameter and index providers remain fixed. -/
theorem substHat_proof_irrel (henv : env.WF) (heq : env.HasCanonicalEq)
    (T : S.Typed env U params) (hΓ : OnCtx Γ (env.IsType U))
    (hpa : TelInst env U Γ params pa)
    (hia : TelInst env U Γ (params ++ S.indices) (pa ++ ia))
    (hialen : ia.length = S.indices.length) (hi : i ≤ S.fields.length)
    (ht : TelInst env U Γ (S.tel pa ia i).1 t)
    (ht' : TelInst env U Γ (S.tel pa ia i).1 t') (hl : l < i) :
    env.IsDefEqU U Γ ((S.substHat pa ia i t).getD l default)
      ((S.substHat pa ia i t').getD l default) := by
  obtain ⟨_, hinst⟩ := tel_typed henv heq T hΓ hpa hia hialen i hi
  have hprop := tel_propTelescope henv heq T hΓ hpa hia hialen i hi
  have hv := hinst.getD (j := params.length + l) (by simp; omega)
  rw [getD_append_right' (by simp [hpa.1])] at hv
  simp only [List.length_map, hpa.1, Nat.add_sub_cancel_left] at hv
  have h := hprop.instOuter_eq henv hΓ ht ht' hv
  have hscope := T.scope.mono_pa hpa.1
  have htl := ht.1.trans (S.tel_length pa ia i).1
  have htl' := ht'.1.trans (S.tel_length pa ia i).1
  rw [← tel_instOuter hscope hialen i t htl,
    ← tel_instOuter hscope hialen i t' htl',
    getD_instOuter_map (by simpa only [(S.tel_length pa ia i).2] using hl),
    getD_instOuter_map (by simpa only [(S.tel_length pa ia i).2] using hl)]
  exact ⟨_, h⟩
end SingletonLayout

namespace PropElim
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- Wherever the old aligned extraction is typed, the transported field program
agrees with it. Its typing theorem itself needs no such alignment. -/
theorem transportedFields_eq_occ (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (hf : TelInst env U Γ (params ++ S.fields) (ps ++ f))
    (halign : ∀ l k, S.slot.getD l none = some k →
      env.IsDefEq U Γ (f.getD l default) (idx.getD k default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)))
    (hi : i ≤ S.fields.length) (hl : l < i) :
    env.IsDefEqU U Γ ((transportedFields S params E ps idx m i).getD l default)
      ((occ S params E ps idx m i).2.getD l default) := by
  obtain ⟨htOld, _, _, hOldCast⟩ := occ_typed params henv heq W hΓ hps hargs hf halign i hi
  have htNew := transportedWitnesses_typed henv heq W hps hargs i hi
  have hidx : idx.length = S.indices.length := by have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx) := by
    have := hargs.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using this
  have hpa : TelInst env U Γ params ps := by
    have := hia.take (doms := params) (more := S.indices)
    simpa [hps] using this
  have hfields := substHat_proof_irrel henv heq W.typed hΓ hpa hia hidx hi htNew htOld hl
  exact hfields.trans henv hΓ ⟨_, (hOldCast l hl).symm⟩

/-- The new program agrees with any aligned constructor-field instance, through
the checked comparison with the existing occurrence program. -/
theorem transportedFields_eq_aligned (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E]) (ps ++ idx ++ [m]))
    (hf : TelInst env U Γ (params ++ S.fields) (ps ++ f))
    (halign : ∀ l k, S.slot.getD l none = some k →
      env.IsDefEq U Γ (f.getD l default) (idx.getD k default)
        ((S.fields.getD l default).instOuter (ps ++ f.take l)))
    (hi : i ≤ S.fields.length) (hl : l < i) :
    env.IsDefEqU U Γ ((transportedFields S params E ps idx m i).getD l default)
      (f.getD l default) := by
  have h := transportedFields_eq_occ henv heq W hΓ hps hargs hf halign hi hl
  have hold := (occ_typed params henv heq W hΓ hps hargs hf halign i hi).2.2.1 l hl
  exact h.trans henv hΓ ⟨_, hold⟩

end PropElim
end Lean4Lean
