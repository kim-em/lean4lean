import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedHeadCommutation

/-! # Restore a constructor history inside retained application wrappers

The tracked application hole retains its exact telescope depth. Ordinary
equality recovers typing backwards through its applications and lambda bodies;
the guarded history itself moves forward by variable renaming only.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private equality_simAt
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private tracked_spine tracked_compose
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedPrefixOrigin
open private supply_head_image
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldRetainedProgress
variable [Params] {D : Definitions}

/-- Restore the original nonproof function inside a tracked spine/binder hole
at the exact type of an actual endpoint representative. Each retained binder
keeps its actual annotation and context. Only ordinary equality is reversed. -/
theorem SpineBinderHole.pi_inert_preimage {C : ScopedHole Ξ Δ}
    (HC : SpineBinderHole C) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ f) (hf : f ≠ .proof)
    (RF : ScopedCompute (PiInertStage D n) Δ f short)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Ξ)
    (ht : env.HasType univs Γ e T) (Ee : proofErase Γ e = C.plug short) :
    ∃ original, env.IsDefEq univs Γ e original T ∧
      proofErase Γ original = C.plug f := by
  induction HC generalizing Γ e T with
  | hole =>
    exact pi_inert_computed_head_spine_preimage heq hs HT hf RF hΓ EΓ ht Ee
      (args := [])
  | appFn HC ih =>
    obtain ⟨g, a, rfl, hn, Hg, Ha⟩ := erase_app_inv Ee
    obtain ⟨_, _, hg, _⟩ := ht.app_inv henv hΓ
    obtain ⟨g', HG, Eg⟩ := ih HT RF hΓ EΓ hg Hg
    have HH := SimAt.app henv.orderedStrong hΓ (equality_simAt hΓ HG) .refl T ht
    have hn' := mt (isProof_congr hΓ HH).2 hn
    exact ⟨.app g' a, HH, by simp only [proofErase, if_neg hn', Eg, Ha, ScopedHole.plug]⟩
  | lamBody HC ih =>
    obtain ⟨a, b, rfl, hn, Ha, Hb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, ha⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
    have EΓa : proofEraseCtx (a :: Γ) = proofErase Γ a :: proofEraseCtx Γ := rfl
    rw [Ha, EΓ] at EΓa
    obtain ⟨b', HB, Eb⟩ := ih HT RF hΓa EΓa hb Hb
    have HH := SimAt.lam henv.orderedStrong hΓ .refl
      (fun _ => equality_simAt hΓa HB) T ht
    have hn' := mt (isProof_congr hΓ HH).2 hn
    exact ⟨.lam a b', HH, by simp only [proofErase, if_neg hn', Ha, Eb, ScopedHole.plug]⟩

/-- A typed computed endpoint in a tracked hole supplies a typed source in
that same hole. No arbitrary-substitution stability of native guards is used. -/
theorem SpineBinderHole.pi_inert_typed_preimage {C : ScopedHole Ξ Δ}
    (HC : SpineBinderHole C) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ f) (hf : f ≠ .proof)
    (RF : ScopedCompute (PiInertStage D n) Δ f short)
    (HNext : TypedSource Ξ (C.plug short)) : TypedSource Ξ (C.plug f) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HNext
  obtain ⟨original, HE, EO⟩ := HC.pi_inert_preimage heq hs HT hf RF hΓ EΓ ht Ee
  exact ⟨Γ, original, T, hΓ, EΓ, HE.hasType.2, EO⟩

/-- Interpret a counted retained prefix under its next ordinary context map.
The target hole has exactly the recorded number of binders, and its inner map
is the literal lift of the same outer substitution by that depth. -/
theorem PiInertRetainedPrefixCount.substitution_hole
    (HP : PiInertRetainedPrefixCount D Δ Θ plug depth)
    (W : ContextSubstitution Θ Ξ τ) :
    ∃ telescope, telescope.length = depth ∧
      ∃ C : ScopedHole Ξ (telescope ++ Ξ), SpineBinderHole C ∧
        ContextSubstitution Δ (telescope ++ Ξ) (τ.liftN depth) ∧
        ∀ e, (plug e).subst τ = C.plug (e.subst (τ.liftN depth)) := by
  induction HP with
  | refl => exact ⟨[], rfl, .hole, .hole, W, fun _ => rfl⟩
  | @retained Δ A u n cd A' Θ plug depth args SD RD WI HP ih =>
    obtain ⟨telescope, hlen, C, HC, WS, EC⟩ := ih W
    let σ := τ.liftN depth
    have WB : ContextSubstitution (A :: Δ) (A'.subst σ :: (telescope ++ Ξ)) σ.lift := by
      intro Γ hΓ EΓ
      simpa only [ProofShape.Subst.id, ProofShape.subst] using
        (ContextSubstitution.comp WI (ContextSubstitution.cons (A := A') WS) hΓ EΓ)
    obtain ⟨B, HB, EB⟩ := tracked_spine
      (SpineBinderHole.lamBody (A := A'.subst σ) (.hole : SpineBinderHole
        (.hole : ScopedHole (A'.subst σ :: (telescope ++ Ξ)) (A'.subst σ :: (telescope ++ Ξ)))))
      (args.map (·.subst σ))
    obtain ⟨C', HC', EC'⟩ := tracked_compose HC HB
    refine ⟨A'.subst σ :: telescope, by simp only [List.length_cons, hlen], C', HC', WB, ?_⟩
    intro e
    rw [EC, EC', EB]
    simp only [ProofShape.subst_mkApps, ProofShape.subst, ScopedHole.plug, σ, ProofShape.Subst.liftN]

/-- Pending arguments enlarge the outer spine of the exact-depth retained
hole without changing its inner telescope or interpreted substitution. -/
theorem PiInertRetainedPrefixCount.application_hole
    (HP : PiInertRetainedPrefixCount D Δ Θ plug depth)
    (W : ContextSubstitution Θ Ξ τ) (pending : List ProofShape) :
    ∃ telescope, telescope.length = depth ∧
      ∃ C : ScopedHole Ξ (telescope ++ Ξ), SpineBinderHole C ∧
        ContextSubstitution Δ (telescope ++ Ξ) (τ.liftN depth) ∧
        ∀ e, ProofShape.mkApps ((plug e).subst τ) pending = C.plug (e.subst (τ.liftN depth)) := by
  obtain ⟨telescope, hlen, C, HC, WS, EC⟩ := HP.substitution_hole W
  obtain ⟨C', HC', EC'⟩ := tracked_spine HC pending
  exact ⟨telescope, hlen, C', HC', WS, fun e => by rw [EC, EC']⟩

/-- Replay an observer-scope constructor history inside an actual typed
application/binder hole. The target telescope supplies its own well-formed
renaming; the result restores typing of the constructor source and preserves
the exact primitive count and native stage through all wrappers. -/
theorem SpineBinderHole.pi_inert_lift_head {C : ScopedHole Ξ Λ}
    (HC : SpineBinderHole C) (EΛ : Λ = controls ++ Δ) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Δ (.const ctor levels))
    (RF : ScopedComputeCount (PiInertStage D n) cg Δ (.const ctor levels) short)
    (HNext : TypedSource Ξ (C.plug (ProofShape.mkApps (short.liftN controls.length) fields))) :
    TypedSource Ξ (C.plug (ProofShape.mkApps (.const ctor levels) fields)) ∧
      ScopedComputeCount (PiInertStage D n) cg Ξ
        (C.plug (ProofShape.mkApps (.const ctor levels) fields))
        (C.plug (ProofShape.mkApps (short.liftN controls.length) fields)) := by
  subst Λ
  have HU := C.typed HNext
  have RL : ScopedComputeCount (PiInertStage D n) cg (controls ++ Δ)
      (.const ctor levels) (short.liftN controls.length) := by
    simpa only [ProofShape.liftN] using pi_inert_lift_count_to_typed_context heq hs HU RF
  have HTctor : TypedSource (controls ++ Δ) (.const ctor levels) := by
    simpa only [ProofShape.subst] using
      HTlower.subst (TypedSource.telescope_renaming HU).interpretation
  obtain ⟨B, HB, EB⟩ := tracked_spine
    (.hole : SpineBinderHole (.hole : ScopedHole (controls ++ Δ) (controls ++ Δ))) fields
  obtain ⟨C', HC', EC⟩ := tracked_compose HC HB
  have E : ∀ e, C'.plug e = C.plug (ProofShape.mkApps e fields) := by
    intro e
    rw [EC, EB]
    rfl
  have HT := HC'.pi_inert_typed_preimage heq hs HTctor (by intro E; cases E) RL.forget
    (by simpa only [E] using HNext)
  exact ⟨by simpa only [E] using HT, by simpa only [E] using HC'.counted RL⟩

/-- Commute the reserved lower constructor history through any retained
prefix before an actual application above the distinguished field binder.
The new whole-source minimum begins at the constructor in those same wrappers.
Its unrestricted competitors are reconstructed using only the original
prefix and argument computation, so minimality does not assume the desired
commutation. Focusing this minimum removes the selected application frame. -/
theorem pi_inert_fresh_field_commute_retained_head_application
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Δ (.const ctor levels))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const ctor levels) short)
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) source
      (ProofShape.mkApps (.const ctor levels) args))
    (RX : ScopedArgumentsCount (PiInertStage D n) (controls ++ A :: Δ) ca args fields)
    (HP : PiInertRetainedPrefixCount D (controls ++ A :: Δ) (beforeControls ++ A :: Δ) plug depth)
    (hdepth : depth + beforeControls.length = controls.length)
    (W : PiInertEndpointMap (beforeControls ++ A :: Δ) (nextControls ++ A :: Δ) τ)
    (HNext : TypedSource (nextControls ++ A :: Δ) (ProofShape.mkApps
      ((plug (ProofShape.mkApps (short.liftN (controls.length+1)) fields)).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D suffixStage) cs (nextControls ++ A :: Δ)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (short.liftN (controls.length+1)) fields)).subst τ) pending) endpoint)
    (HK : PiInertFreshFieldRun D Δ family out A x nextControls K endpoint ck frames)
    (hcost : cp+ca+cg+cs+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      source tail → PiInertApplicationContinuation D (nextControls ++ A :: Δ) τ pending K (plug tail) k →
      cost ≤ j+k) :
    PiInertFreshFieldMinimum D Δ family out A x nextControls
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst τ) pending)
      (cg+cs+ck) frames := by
  obtain ⟨telescope, hlen, C, HC, WS, EC⟩ := HP.application_hole W.interpretation pending
  have EH := W.pending_head_transport (f := short) depth
  have EImage : (short.liftN (controls.length+1)).subst (τ.liftN depth) =
      short.liftN ((telescope ++ nextControls ++ [A]).length) := by
    simpa only [List.length_append, List.length_cons, List.length_nil, hlen, hdepth,
      Nat.add_assoc] using EH
  have HNext' : TypedSource (nextControls ++ A :: Δ)
      (C.plug (ProofShape.mkApps (short.liftN ((telescope ++ nextControls ++ [A]).length))
        (fields.map (·.subst (τ.liftN depth))))) := by
    simpa only [EC, ProofShape.subst_mkApps, EImage] using HNext
  have EΛ : telescope ++ (nextControls ++ A :: Δ) = (telescope ++ nextControls ++ [A]) ++ Δ := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨HTsource, RHead⟩ := HC.pi_inert_lift_head EΛ heq hs HTlower RF HNext'
  have ESource : ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst τ) pending =
      C.plug (ProofShape.mkApps (.const ctor levels) (fields.map (·.subst (τ.liftN depth)))) := by
    rw [EC, ProofShape.subst_mkApps]
    rfl
  have RHead' : ScopedComputeCount (PiInertStage D functionStage) cg (nextControls ++ A :: Δ)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst τ) pending)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (short.liftN (controls.length+1)) fields)).subst τ) pending) := by
    simpa only [ESource, EC, ProofShape.subst_mkApps, EImage] using RHead
  have RBody := (RHead'.mono (pi_inert_stage_mono (Nat.le_max_left functionStage suffixStage))).trans
    (RNext.mono (pi_inert_stage_mono (Nat.le_max_right functionStage suffixStage)))
  refine ⟨K, max functionStage suffixStage, cg+cs, ck, endpoint,
    by simpa only [ESource] using HTsource, RBody, HK, rfl, ?_⟩
  intro later j tail k RJ RK
  have RArgs := (ScopedComputeCount.beta (Step := PiInertStage D n)
    (BetaRed.refl (e := .const ctor levels))).mkApps RX
  have HH := HM n _ (ProofShape.mkApps (.const ctor levels) fields) (j+k) (RP.trans RArgs)
    ⟨later, j, tail, k, rfl, RJ, RK⟩
  omega

/-- Commute the lower constructor history through retained wrappers at the
distinguished supply itself. Its target is the observer scope, and the restored
whole-source minimum is an ordinary projection minimum. The function charge
is preserved, while all competing paths are tested against the original source. -/
theorem pi_inert_commute_retained_head_supply
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Δ (.const ctor levels))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const ctor levels) short)
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) source
      (ProofShape.mkApps (.const ctor levels) args))
    (RX : ScopedArgumentsCount (PiInertStage D n) (controls ++ A :: Δ) ca args fields)
    (HP : PiInertRetainedPrefixCount D (controls ++ A :: Δ) (A :: Δ) plug depth)
    (hdepth : depth = controls.length)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (HNext : TypedSource Δ (ProofShape.mkApps
      ((plug (ProofShape.mkApps (short.liftN (controls.length+1)) fields)).subst (ProofShape.Subst.one x)) pending))
    (RNext : ScopedComputeCount (PiInertStage D suffixStage) cs Δ
      (ProofShape.mkApps ((plug (ProofShape.mkApps (short.liftN (controls.length+1)) fields)).subst (ProofShape.Subst.one x)) pending) endpoint)
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K endpoint ck frames)
    (hcost : cp+ca+cg+cs+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      source tail → PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K (plug tail) k →
      cost ≤ j+k) :
    PiInertProjectionFrameMinimum D Δ family 0 out Δ
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst (ProofShape.Subst.one x)) pending)
      (cg+cs+ck) frames := by
  obtain ⟨telescope, hlen, C, HC, WS, EC⟩ := HP.application_hole W pending
  have EH := supply_head_image (f := short) (x := x) (depth := depth)
  have EImage : (short.liftN (controls.length+1)).subst ((ProofShape.Subst.one x).liftN depth) =
      short.liftN telescope.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil, hlen, hdepth,
      Nat.add_assoc] using EH
  have HNext' : TypedSource Δ
      (C.plug (ProofShape.mkApps (short.liftN telescope.length)
        (fields.map (·.subst ((ProofShape.Subst.one x).liftN depth))))) := by
    simpa only [EC, ProofShape.subst_mkApps, EImage] using HNext
  obtain ⟨HTsource, RHead⟩ := HC.pi_inert_lift_head rfl heq hs HTlower RF HNext'
  have ESource : ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst (ProofShape.Subst.one x)) pending =
      C.plug (ProofShape.mkApps (.const ctor levels) (fields.map (·.subst ((ProofShape.Subst.one x).liftN depth)))) := by
    rw [EC, ProofShape.subst_mkApps]
    rfl
  have RHead' : ScopedComputeCount (PiInertStage D functionStage) cg Δ
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ctor levels) fields)).subst (ProofShape.Subst.one x)) pending)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (short.liftN (controls.length+1)) fields)).subst (ProofShape.Subst.one x)) pending) := by
    simpa only [ESource, EC, ProofShape.subst_mkApps, EImage] using RHead
  have RBody := (RHead'.mono (pi_inert_stage_mono (Nat.le_max_left functionStage suffixStage))).trans
    (RNext.mono (pi_inert_stage_mono (Nat.le_max_right functionStage suffixStage)))
  refine ⟨K, max functionStage suffixStage, cg+cs, ck, endpoint,
    by simpa only [ESource] using HTsource, RBody, HK, rfl, ?_⟩
  intro later j tail k RJ RK
  have RArgs := (ScopedComputeCount.beta (Step := PiInertStage D n)
    (BetaRed.refl (e := .const ctor levels))).mkApps RX
  have HH := HM n _ (ProofShape.mkApps (.const ctor levels) fields) (j+k) (RP.trans RArgs)
    ⟨later, j, tail, k, rfl, RJ, RK⟩
  omega

end Lean4Lean.VEnv.Strengthening
