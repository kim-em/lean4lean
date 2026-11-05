import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistorySpinePivot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryPrimitiveSquare

/-! # Primitive squares from simultaneous native output transfer

A source with neither an opaque computational head nor a sort root has only
expansion primitives. A pivot recovering all its native outputs supplies the
guards before the remaining computation runs inside the expanded result.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private empty_compute_beta from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedComparison
variable [Params] {D : PureObservation.Definitions}

/-- Apart from opaque heads and universe sorts, only expansion primitives
remain. This classification includes an arbitrary lambda-headed spine. -/
theorem static_structure_nonopaque_primitive
    (hhead : ¬ PrimitiveHead source) (hsort : ∀ u, source ≠ .sort u)
    (RP : ErasedStaticStructureEtaExpansionUnion D Δ source expanded) :
    ConstantExpansion source expanded ∨
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded ∨
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded := by
  obtain ⟨stage, RP⟩ := RP
  induction stage with
  | zero =>
    rcases RP with (RP | RP) | RP
    · exact (hhead (erased_iota_primitive_head RP)).elim
    · cases RP with
      | sort => exact (hsort _ rfl).elim
      | const => exact (hhead trivial).elim
    · exact .inl RP
  | succ stage ih =>
    rcases RP with RP | RP | RP | RP | RP | RP
    · exact ih RP
    · exact (hhead RP.2.head).elim
    · exact (hhead RP.head).elim
    · exact .inr (.inl (RP.mono (fun H => ⟨stage, H⟩)))
    · exact .inr (.inr (.inl (RP.mono (fun H => ⟨stage, H⟩))))
    · exact .inr (.inr (.inr (RP.mono (fun H => ⟨stage, H⟩))))

/-- Transfer native guards to an intermediate pivot and then compute within
the expansion. The pivot need not compute to the uncontracted source, and the
common target need not recover any of the source's selected native outputs. -/
theorem native_pivot_primitive_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hhead : ¬ PrimitiveHead source) (hsort : ∀ u, source ≠ .sort u)
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ pivot target)
    (HN : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) Δ source pivot)
    (Rβ : ProofShape.BetaRed source target)
    (RP : ErasedStaticStructureEtaExpansionUnion D Δ source expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original shared ∧
      ProofShape.BetaRed expanded shared := by
  rcases static_structure_nonopaque_primitive hhead hsort RP with RC | RI | RE | RS
  · cases RC
    exact ⟨_, Rbefore.trans Rafter, (constantExpansion_beta _).trans Rβ⟩
  · cases RI with
    | intro _RN =>
      rename_i annotation
      have RIβ : ProofShape.BetaRed (.app (.lam annotation (.bvar 0)) source) source := by
        simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
          ProofShape.liftN_zero] using (ProofShape.BetaRed.beta (b := .bvar 0) (a := source))
      exact ⟨_, Rbefore.trans Rafter, RIβ.trans Rβ⟩
  · cases RE with
    | intro RN SD =>
      have RL := static_structure_compute_under_domain heq hs SD Rafter
      exact ⟨_, Rbefore.trans ((ScopedCompute.base
          (erased_static_structure_eta_expansion_union_eta (.intro (HN _ RN) SD))).trans
            (.lam .refl (.app RL .refl))),
        .lam .refl (.app Rβ.liftN .refl)⟩
  · cases RS with
    | intro hi hx ha hp RN =>
      refine ⟨_, Rbefore.trans ((ScopedCompute.base
        (erased_static_structure_eta_expansion_union_structure (.intro hi hx ha hp (HN _ RN)))).trans
          (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl)) Rafter)), ?_⟩
      apply empty_compute_beta
      exact (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl))
        (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := Δ) Rβ)).core_forget

end Lean4Lean.VEnv.Strengthening
