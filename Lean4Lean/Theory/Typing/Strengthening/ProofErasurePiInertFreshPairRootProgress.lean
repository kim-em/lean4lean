import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedConstructorProgress

/-! # Function-eta progress for marked full pairs

The empty prefix decreases continuation frames; the one-field prefix decreases
primitive cost. Both restore a full pair with the same distinguished field.
The remaining native structure root is recorded with its actual computation
and unrestricted minimum, so no function-root case is hidden in that boundary.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_pair_tail
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedConstructorProgress
variable [Params] {D : Definitions}

/-- An actual first structure expansion of a full fresh pair, followed by its
selected marked continuation. The root charge is included in the unrestricted
minimum. Reading this expansion through subsequent computations remains open. -/
def PiInertFreshPairStructureMinimum (D : Definitions) (Δ : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out A x : ProofShape)
    (controls : List ProofShape) (value : ProofShape) (cost frames : Nat) : Prop :=
  ∃ stage guardStage target endpoint ct ck K, guardStage < stage ∧
    TypedSource (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]) ∧
    PiInertStage D stage (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]) target ∧
    NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage)
      (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]) target ∧
    ScopedComputeCount (PiInertStage D stage) ct (controls ++ A :: Δ) target endpoint ∧
    PiInertFreshFieldRun D Δ family out A x controls K endpoint ck frames ∧ 1+ct+ck = cost ∧
    ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]) tail →
      K tail k → cost ≤ j+k

/-- Forgetting the selected structure root retains a genuine marked minimum
at its full-pair source, with the root charge still included. -/
theorem PiInertFreshPairStructureMinimum.minimum
    (H : PiInertFreshPairStructureMinimum D Δ family info out A x controls value cost frames) :
    PiInertFreshFieldMinimum D Δ family out A x controls
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]) cost frames := by
  obtain ⟨stage, guardStage, target, endpoint, ct, ck, K, hg, HT, HR, HE, RT, HK, hc, HM⟩ := H
  exact ⟨K, stage, 1+ct, ck, endpoint, HT, (ScopedComputeCount.base HR).trans RT, HK, hc, HM⟩

/-- The residual structure expansion has a strictly cheaper marked minimum
whose first field is the exact projection of its original full fresh pair.
The projection is sort-typed, and one ordinary iota selects the same fresh
variable. Replaying that selection through the remaining minimum is the
specific missing readout step; it is not assumed here. -/
theorem PiInertFreshPairStructureMinimum.projected_field_minimum
    (H : PiInertFreshPairStructureMinimum D Δ family info out A x controls value cost frames)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family []))) :
    let pair := ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]
    ControlTyping (controls ++ A :: Δ) (.proj family 0 pair) (.sort (.succ .zero)) ∧
    Primitive D (.proj family 0 pair) (.bvar controls.length) ∧
    ∃ nextValue smaller, smaller+1 = cost ∧ smaller < cost ∧
      PiInertFreshFieldMinimum D Δ family out A x controls
        (ProofShape.mkApps (.const info.ctorName []) [.proj family 0 pair, nextValue]) smaller frames := by
  obtain ⟨stage, guardStage, target, endpoint, ct, ck, K, hg, HT, HR, HE, RT, HK, hc, HM⟩ := H
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
  have HNative : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage)
      (proofEraseCtx Γ) (proofErase Γ m) target := by simpa only [EΓ, Em] using HE
  obtain ⟨HSort, HTtarget, nextValue, ETarget⟩ := proofErase_native_pair_structure_field D
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    hi hp hf hz hadm hshape hΓ hm HNative
  simp only [EΓ, Em] at HSort HTtarget ETarget
  refine ⟨HSort, .projIota hi (by simp [hp, hf]) (by simp [hp]), nextValue, ct+ck,
    by omega, by omega, ?_⟩
  have HTarget : PiInertFreshFieldMinimum D Δ family out A x controls target (ct+ck) frames := by
    refine ⟨K, stage, ct, ck, endpoint, HTtarget, RT, HK, rfl, ?_⟩
    intro later j tail k RJ RK
    have RAlt := (ScopedComputeCount.base
      (pi_inert_stage_mono (Nat.le_max_left stage later) HR)).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later)))
    have HH := HM _ _ tail k RAlt RK
    omega
  exact ETarget ▸ HTarget

private theorem fresh_pair_args
    (HA : ScopedArgumentsCount (PiInertStage D n) Ξ ca [.bvar i, value] fields) :
    ∃ slot, fields = [.bvar i, slot] := by
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RV last =>
      cases last
      exact ⟨_, by rw [RF.forget.pi_inert_bvar_fixed]⟩

private theorem closed_pair_no_function_eta
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HT : TypedSource Ξ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (RN : ScopedTypeRecovery Guard Ξ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) (.forallE C B)) : False := by
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
  obtain ⟨A, B, hmPi, _, _⟩ := proofErase_scoped_recovered_pi_descend
    hguard hΓ hΓ (Ctx.LiftN.zero []) hm
    (by simpa only [List.length_nil, ProofShape.liftN_zero, EΓ, Em] using RN)
  obtain ⟨u, hS⟩ := hm.isType henv hΓ
  exact IsDefEqU.rigidApp_forallE_inv (args := []) (ls := []) henv hΓ
    (henv.projectionRigid hi) hS (hm.uniqU henv hΓ hmPi)

/-- Every full fresh-pair minimum either activates its distinguished field,
progresses to another full fresh pair by a strict cost/frame decrease, or
reaches an actual saturated structure root. Both function-eta prefixes are
handled, including arbitrary retained wrappers before the next application.
The original observer-scope constructor recovery is kept fixed. -/
theorem PiInertFreshFieldMinimum.pair_root_progress
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HTlower : TypedSource Δ (.const info.ctorName []))
    (H : PiInertFreshFieldMinimum D Δ family out A x controls
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]) cost frames) :
    (∃ telescope nextValue smaller nextFrames, smaller ≤ cost ∧
      PiInertProjectionFrameMinimum D Δ family 0 out (telescope ++ Δ)
        (ProofShape.mkApps (.const info.ctorName []) [x.liftN telescope.length, nextValue]) smaller nextFrames) ∨
    (∃ nextControls nextValue smaller nextFrames,
      (smaller < cost ∨ smaller ≤ cost ∧ nextFrames < frames) ∧
      PiInertFreshFieldMinimum D Δ family out A x nextControls
        (ProofShape.mkApps (.const info.ctorName []) [.bvar nextControls.length, nextValue]) smaller nextFrames) ∨
    (∃ nextValue smaller, smaller ≤ cost ∧
      PiInertFreshPairStructureMinimum D Δ family info out A x controls nextValue smaller frames) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM⟩ := H
  rcases RB.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, values, ch, ca, hcounts, rfl, HL, _, HA⟩ |
    ⟨levels, pre, pending, target, cp, ct, ca, hcut, hca, HL, HA, RP, HR, HN, RT⟩
  · cases HL
    obtain ⟨slot, EValues⟩ := fresh_pair_args HA
    rw [EValues] at HA HK
    have RF : ScopedComputeCount (PiInertStage D n) 0 Δ
        (.const info.ctorName []) (.const info.ctorName []) := .beta BetaRed.refl
    rcases HK.constructor_head_next_minimum heq hs HTlower RF rfl
      (ScopedComputeCount.beta (Step := PiInertStage D n) BetaRed.refl) HA (cost := cost)
      (by omega) HM with
      ⟨telescope, σ, fields, smaller, nextFrames, hlen, WS, EF, hfields, hsmall, hbudget, hframes, HNext⟩ |
      ⟨nextControls, σ, fields, smaller, nextFrames, hlen, WS, EF, hfields, hsmall, hbudget, hframes, HNext⟩
    · have HTpair : TypedSource (telescope ++ Δ)
          (ProofShape.mkApps (.const info.ctorName []) (x.liftN telescope.length :: fields)) := by
        obtain ⟨_, _, _, _, _, HTpair, _⟩ := HNext
        exact HTpair
      obtain ⟨nextValue, rfl⟩ := typed_pair_tail hi hp hf hz HTpair hfields
      exact .inl ⟨telescope, nextValue, smaller, nextFrames, by omega, HNext⟩
    · have HTpair : TypedSource (nextControls ++ A :: Δ)
          (ProofShape.mkApps (.const info.ctorName []) (.bvar nextControls.length :: fields)) := by
        obtain ⟨_, _, _, _, _, HTpair, _⟩ := HNext
        exact HTpair
      obtain ⟨nextValue, rfl⟩ := typed_pair_tail hi hp hf hz HTpair hfields
      exact .inr (.inl ⟨nextControls, nextValue, smaller, nextFrames, .inr ⟨by omega, hframes⟩, HNext⟩)
  · cases HL
    obtain ⟨slot, EArgs⟩ := fresh_pair_args HA
    have HTwhole := HT.pi_inert_compute heq hs RP.forget
    have HSorted := HK.forget.forget.pair_sorted hi hu hp hshape
    obtain ⟨guardStage, hg, HE⟩ := pi_inert_sorted_frames_constructor_root heq hs
      (henv.projectionCtorRigid hi) hD HT RP HR HN RT HSorted hout hproj
      (cost := cost) (by omega) HM
    have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D guardStage) :=
      erased_static_structure_eta_expansion_stage_descent heq hs guardStage
    rcases HE with HE | HE
    · cases HE with
      | intro RN' SD' =>
        rename_i C E v
        cases pre with
        | nil =>
          simp only [List.nil_append] at EArgs
          subst pending
          rcases pi_inert_fresh_pair_empty_eta_constructor_progress heq hs hi hu hp hf hz
            hshape SD RN RN' SD' HTlower HTwhole RP HR RT HK (cost := cost) (by omega) HM with
            ⟨telescope, nextValue, smaller, nextFrames, hlen, hsmall, hframes, HNext⟩ |
            ⟨nextControls, nextValue, smaller, nextFrames, hlen, hsmall, hframes, HNext⟩
          · exact .inl ⟨telescope, nextValue, smaller, nextFrames, hsmall, HNext⟩
          · exact .inr (.inl ⟨nextControls, nextValue, smaller, nextFrames, .inr ⟨hsmall, hframes⟩, HNext⟩)
        | cons first rest =>
          have EFirst : first = .bvar controls.length := (List.cons.inj EArgs).1
          subst first
          have ERest : rest ++ pending = [slot] := (List.cons.inj EArgs).2
          cases rest with
          | nil =>
            have RP' := RP
            rw [ProofShape.mkApps_append] at RP'
            obtain ⟨smaller, hsmall, HNext⟩ := pi_inert_eta_fresh_field_descent heq hs hguard
              (by simpa only [ProofShape.mkApps_append] using HTwhole) RN' SD' RP' HR RT HK
              (cost := cost) (by omega) HM
            refine .inr (.inl ⟨C :: controls, etaArgument v, smaller, frames+1, .inl hsmall, ?_⟩)
            simpa only [ProofShape.mkApps, ProofShape.liftN, liftVar, Nat.not_lt_zero,
              ↓reduceIte, List.length_cons, Nat.add_comm] using HNext
          | cons second tail =>
            have ESecond : second = slot := (List.cons.inj ERest).1
            have ETail : tail ++ pending = [] := (List.cons.inj ERest).2
            have hlength := congrArg List.length ETail
            have ET : tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append, List.length_nil] at hlength; omega)
            have EP : pending = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_append, List.length_nil] at hlength; omega)
            subst second tail pending
            exact (closed_pair_no_function_eta hguard hi hp hf hz HTwhole RN').elim
    · have HTapp : TypedSource (controls ++ A :: Δ)
          (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
        simpa only [ProofShape.mkApps_append] using HTwhole
      have EP := TypedSource.structure_eta_pending_nil hguard HTapp HE
      subst pending
      simp only [List.append_nil] at EArgs
      subst pre
      refine .inr (.inr ⟨slot, 1+ct+ck, by omega, n, guardStage, target, endpoint, ct, ck, K,
        hg, HTwhole, HR, HE, RT, HK, rfl, ?_⟩)
      intro later j tail k RJ RK
      have RAlt := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
        (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
      have HH := HM _ _ tail k RAlt RK
      omega

/-- Eliminate every repeated function-eta case of a marked full-pair minimum
by well-founded induction on primitive cost, then continuation frames. The
result either activates the exact distinguished field or reaches an actual
full-pair structure expansion at no larger cost. There is no function-eta
alternative or caller-provided readout induction hypothesis. Structure readout
and activated minima under retained telescopes are still unresolved. -/
theorem PiInertFreshFieldMinimum.pair_function_eta_eliminate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HTlower : TypedSource Δ (.const info.ctorName []))
    (H : PiInertFreshFieldMinimum D Δ family out A x controls
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]) cost frames) :
    (∃ telescope nextValue smaller nextFrames, smaller ≤ cost ∧
      PiInertProjectionFrameMinimum D Δ family 0 out (telescope ++ Δ)
        (ProofShape.mkApps (.const info.ctorName []) [x.liftN telescope.length, nextValue]) smaller nextFrames) ∨
    (∃ nextControls nextValue smaller nextFrames, smaller ≤ cost ∧
      PiInertFreshPairStructureMinimum D Δ family info out A x nextControls nextValue smaller nextFrames) := by
  induction cost using Nat.strongRecOn generalizing controls value frames with
  | ind cost ihCost =>
    induction frames using Nat.strongRecOn generalizing controls value with
    | ind frames ihFrames =>
      rcases H.pair_root_progress heq hs hi hu hp hf hz hshape hD hout hproj SD RN HTlower with
        HActivated | ⟨nextControls, nextValue, smaller, nextFrames, hprogress, HNext⟩ |
        ⟨nextValue, smaller, hsmall, HStructure⟩
      · exact .inl HActivated
      · have hle : smaller ≤ cost := by rcases hprogress with h | ⟨h, _⟩ <;> omega
        have HNext' :
            (∃ telescope value' last lastFrames, last ≤ smaller ∧
              PiInertProjectionFrameMinimum D Δ family 0 out (telescope ++ Δ)
                (ProofShape.mkApps (.const info.ctorName []) [x.liftN telescope.length, value']) last lastFrames) ∨
            (∃ controls' value' last lastFrames, last ≤ smaller ∧
              PiInertFreshPairStructureMinimum D Δ family info out A x controls' value' last lastFrames) := by
          by_cases hsmall : smaller < cost
          · exact ihCost smaller hsmall HNext
          · have E : smaller = cost := by omega
            subst smaller
            have hframes : nextFrames < frames := by rcases hprogress with h | ⟨_, h⟩ <;> omega
            exact ihFrames nextFrames hframes HNext
        rcases HNext' with ⟨telescope, value', last, lastFrames, hlast, HM⟩ |
          ⟨controls', value', last, lastFrames, hlast, HM⟩
        · exact .inl ⟨telescope, value', last, lastFrames, by omega, HM⟩
        · exact .inr ⟨controls', value', last, lastFrames, by omega, HM⟩
      · exact .inr ⟨controls, nextValue, smaller, frames, hsmall, HStructure⟩

end Lean4Lean.VEnv.Strengthening
