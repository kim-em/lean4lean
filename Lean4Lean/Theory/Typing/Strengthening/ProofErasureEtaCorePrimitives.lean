import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCorePatterns

/-! # Primitive simulation for arbitrary sorted eta origins

Target beta cleanup exposes the original pattern with paired captures. A whole
eta origin uses exact full-core simulation instead. Declaration, projection,
capture, template and universe primitives are all included.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_proj_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}
variable (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
include hs hΓ₀ hA hf hn

/-- Selector and capture-application steps simulate after exposing the exact
registered pattern. Its check is reused and its captures stay pointwise paired. -/
theorem sorted_eta_core_capture_primitive (R : CapturePrimitive a out)
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n out b' := by
  cases R with
  | select hp hc hm =>
    rcases sorted_eta_core_pattern_cleanup hs hΓ₀ hA hf hn hp hm V hΓ ht Ee W with
      ⟨b₀, caps', RB, HM, HC⟩ | HO
    · exact ⟨_, (Compute.beta RB).trans (.base (.inl (.inl (.inr (.select hp hc HM))))), HC _⟩
    · exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.base (.inl (.inl (.inr (.select hp hc hm)))))
  | apply hp hc hm =>
    rcases sorted_eta_core_pattern_cleanup hs hΓ₀ hA hf hn hp hm V hΓ ht Ee W with
      ⟨b₀, caps', RB, HM, HC⟩ | HO
    · exact ⟨_, (Compute.beta RB).trans (.base (.inl (.inl (.inr (.apply hp hc HM))))),
        .app (HC _) (HC _)⟩
    · exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.base (.inl (.inl (.inr (.apply hp hc hm)))))

/-- Arbitrary closed-template rules retain their original template and check;
only the pointwise paired capture vector changes after pattern exposure. -/
theorem sorted_eta_core_template_primitive (R : TemplatePrimitive a out)
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n out b' := by
  cases R with
  | intro hp hc hr hm =>
    rcases sorted_eta_core_pattern_cleanup hs hΓ₀ hA hf hn hp hm V hΓ ht Ee W with
      ⟨b₀, caps', RB, HM, HC⟩ | HO
    · refine ⟨_, (Compute.beta RB).trans (.base (.inl (.inr (.intro hp hc hr HM)))),
        AmbientVariant.refl.mkApps_pair ?_⟩
      apply List.forall₂_of_getElem (by simp)
      intro i hi hi'
      simp only [List.getElem_map]
      exact HC _
    · exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.base (.inl (.inr (.intro hp hc hr hm))))

/-- Delta and projection retain the eta-origin relation. Projection typing
excludes whole-function wrappers at the inspected constructor major. -/
theorem sorted_eta_core_declaration_projection (R : Primitive D a out)
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n out b' := by
  cases R with
  | delta HD =>
    cases V with
    | refl => exact ⟨_, .base (.inl (.inl (.inl (.delta HD)))), .refl⟩
    | origin HO => exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.base (.inl (.inl (.inl (.delta HD)))))
  | @projIota s info args i ls field hi hlen hget =>
    cases V with
    | refl => exact ⟨_, .base (.inl (.inl (.inl (.projIota hi hlen hget)))), .refl⟩
    | origin HO =>
      exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO
        (.base (.inl (.inl (.inl (.projIota hi hlen hget)))))
    | proj VM =>
      obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      have hpi : ∀ C E, ¬ env.HasType univs Γ m (.forallE C E) := by
        intro C E hPi
        obtain ⟨_, hFamily⟩ := hm.hasType.2.isType henv hΓ
        exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hFamily
          (hm.hasType.2.uniqU henv hΓ hPi)
      obtain ⟨args', RB, HA⟩ := sorted_eta_core_nonfunction_spine_cleanup hs hΓ₀ hA hf hn VM
        hΓ hm.hasType.2 hpi EM W
      obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
      have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
      refine ⟨args'[info.nparams + i]'hj', ?_, ?_⟩
      · exact (Compute.proj (.beta RB)).trans (.base (.inl (.inl (.inl
          (.projIota hi (HA.length_eq.symm.trans hlen) (List.getElem?_eq_getElem hj'))))))
      · rw [← HE]
        exact HA.getElem_of _ hj hj'

/-- Every full level-core primitive simulates at an arbitrary sorted eta
variant of an actual consumer. Pattern checks and universe lists stay exact;
no native certificate or semantic endpoint comparison is supplied. -/
theorem sorted_eta_core_primitive (R : ErasedLevelCore D a out)
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n out b' := by
  rcases R with ((R | R) | R) | R
  · exact sorted_eta_core_declaration_projection hs hΓ₀ hA hf hn R V hΓ ht Ee W
  · exact sorted_eta_core_capture_primitive hs hΓ₀ hA hf hn R V hΓ ht Ee W
  · exact sorted_eta_core_template_primitive hs hΓ₀ hA hf hn R V hΓ ht Ee W
  · cases R with
    | sort HE hw =>
      cases V with
      | refl => exact ⟨_, .base (.inr (.sort HE hw)), .refl⟩
      | origin HO => exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.base (.inr (.sort HE hw)))
    | const HE hw =>
      cases V with
      | refl => exact ⟨_, .base (.inr (.const HE hw)), .refl⟩
      | origin HO => exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.base (.inr (.const HE hw)))

end Lean4Lean.VEnv.Strengthening
