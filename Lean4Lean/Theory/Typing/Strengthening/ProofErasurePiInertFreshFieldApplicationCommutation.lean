import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedHeadCommutation

/-! # Restore the constructor after an intervening fresh-field application

An empty-prefix eta in a marked full-pair minimum must retain its function.
Move that lower function history into the actual next application suffix.
The restored typed pair forbids pending arguments, and the resulting minimum
has the same fresh field and future supply with one fewer continuation frame.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- A retained empty-constructor eta followed immediately by an application
above the distinguished field binder restores a full constructor-pair minimum
in the application's target scope. Primitive cost cannot increase, the actual
application frame is removed, and the SAME future supply x is retained. The
entire function charge is moved into the actual suffix, not discarded. Extra
pending arguments are excluded by the restored pair's typing. Retained
wrappers before the next application still require a separate commutation. -/
theorem pi_inert_fresh_field_empty_eta_application_progress
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage)
      (controls ++ A :: Δ) (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (controls ++ A :: Δ) A' v)
    (HTlower : TypedSource Δ (.const info.ctorName []))
    (HT : TypedSource (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]))
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) source
      (ProofShape.mkApps (.const info.ctorName []) [.bvar controls.length, value]))
    (HR : PiInertStage D n (controls ++ A :: Δ) (.const info.ctorName [])
      (.lam A' (.app (.const info.ctorName []) (etaArgument v))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        [.bvar controls.length, value]) endpoint)
    (W : PiInertEndpointMap (controls ++ A :: Δ) (nextControls ++ A :: Δ) τ)
    (HNext : TypedSource (nextControls ++ A :: Δ) (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D suffixStage) cs (nextControls ++ A :: Δ)
      (ProofShape.mkApps (endpoint.subst τ) pending) major)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x nextControls K major ck frames)
    (hcost : cp+1+ct+cs+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ) source tail →
      PiInertApplicationContinuation D (nextControls ++ A :: Δ) τ pending K tail k → cost ≤ j+k) :
    pending = [] ∧ nextControls.length ≤ controls.length ∧
      ∃ nextValue smaller, smaller ≤ cost ∧
        PiInertFreshFieldMinimum D Ω Δ family out A x nextControls
          (ProofShape.mkApps (.const info.ctorName []) [.bvar nextControls.length, nextValue]) smaller frames := by
  have RBody := ((ScopedComputeCount.base HR).mkApps
    (ScopedArgumentsCount.refl (args := [.bvar controls.length, value]))).trans RT
  have HEndpoint := HT.pi_inert_compute heq hs RBody.forget
  have HFresh : PiInertFreshFieldRun D Ω Δ family out A x controls
      (PiInertApplicationContinuation D (nextControls ++ A :: Δ) τ pending K)
      endpoint (cs+ck) (frames+1) := .application HEndpoint W HNext RNext HK
  obtain ⟨short, domain, body, rest, cg, ca, HTshort, RShort, EL, E,
    RArgs, hsplit, hbound, hsmall, HMin⟩ :=
    pi_inert_fresh_field_empty_eta_retained_descent heq hs hi hu hshape SD RN RN' SD'
      HTlower HT RP HR RT HFresh (by omega) HM
  have hlen := RArgs.forget.length_eq
  simp only [List.length_cons, List.length_nil] at hlen
  have ERest : ∃ slot, rest = [slot] := by
    cases rest with
    | nil => simp at hlen
    | cons slot tail =>
      have ET : tail = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hlen
        omega)
      exact ⟨slot, by rw [ET]⟩
  obtain ⟨slot, rfl⟩ := ERest
  have HNew := pi_inert_fresh_field_commute_head_application heq hs HTlower RShort RP RArgs W
    (by simpa only [E] using HNext) (by simpa only [E] using RNext) HK (by omega) HM
  have EF := W.fresh_field
  change τ controls.length = .bvar nextControls.length at EF
  simp only [List.map_cons, List.map_nil, ProofShape.subst, EF] at HNew
  have HTall : TypedSource (nextControls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName [])
        ([.bvar nextControls.length, slot.subst τ] ++ pending)) := by
    obtain ⟨_, _, _, _, _, HTall, _⟩ := HNew
    exact HTall
  rw [ProofShape.mkApps_append] at HTall
  have HPair : TypedSource (nextControls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [.bvar nextControls.length, slot.subst τ]) :=
    typed_spine_head HTall
  obtain ⟨Γ, pair, hΓ, EΓ, hpair, Epair⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HPair
  have EP := TypedSource.closed_record_pending_nil hi hΓ EΓ hpair (by simpa only [Epair] using HTall)
  obtain ⟨hle, _⟩ := W.fresh_field_transport
  exact ⟨EP, hle, slot.subst τ, cg+cs+ck, by omega,
    by simpa only [EP, List.append_nil] using HNew⟩

end Lean4Lean.VEnv.Strengthening
