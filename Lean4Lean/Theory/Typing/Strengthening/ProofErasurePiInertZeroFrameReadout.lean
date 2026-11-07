import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstantReadout

/-! # Simultaneous stage-zero frame readout

Comparison and carrier premises are followed in the original inductive grammar.
The function clause retains framed lambda bodies, so application uses its own
function or argument induction hypothesis rather than an existential cut.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private sort_not_lam sort_not_constructor from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
open private type_not_family_carrier type_not_pi_carrier from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking
variable [Params] {D : Definitions}

private abbrev UnitHistory (D : Definitions) (stage : Nat) (Δ : List ProofShape) (C : ProofShape) :=
  ∀ left right, PiInertCarrierHistory D stage Δ C left right

private def TypeCase (D : Definitions) (stage : Nat) (family : Name)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∀ {Γ e f u v}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ e (.sort u) → env.HasType univs Γ f (.sort v) →
    proofEraseCtx Γ = Δ → proofErase Γ e = a → proofErase Γ f = b →
    RigidSortFrames family Δ a → UnitHistory D stage Δ b

private def FunctionCase (D : Definitions) (stage : Nat) (family : Name)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∀ {Γ A body f F G y T}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ (.lam A body) F → env.HasType univs Γ f G →
    env.HasType univs Γ (.app f y) T →
    proofEraseCtx Γ = Δ → proofErase Γ (.lam A body) = a → proofErase Γ f = b →
    RigidSortFrames family (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) body) →
    UnitHistory D stage Δ (proofErase Γ (.app f y))

private def CarrierCase (D : Definitions) (stage : Nat) (family : Name)
    (Δ : List ProofShape) (C a b : ProofShape) : Prop :=
  ∀ {Γ e f E u v}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ e (.sort u) → env.HasType univs Γ f (.sort v) →
    (env.HasType univs Γ e E ∨ env.HasType univs Γ f E) →
    proofEraseCtx Γ = Δ → proofErase Γ E = C → proofErase Γ e = a → proofErase Γ f = b →
    RigidSortFrames family Δ a → UnitHistory D stage Δ b

private def CheckCase (D : Definitions) (stage : Nat) (family : Name)
    (Δ : List ProofShape) (kind : JointCheckKind) (a b : ProofShape) : Prop :=
  match kind with
  | .compare mode => TypeCase D stage family Δ a b ∧ (mode = false → FunctionCase D stage family Δ a b)
  | .carrier C => CarrierCase D stage family Δ C a b

private theorem zero_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
  fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs 0
    hΓ hΓ' W ht HR.1

private theorem type_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hr : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (RA : ScopedCompute (PiInertStage D 0) Δ a a')
    (RB : ScopedCompute (PiInertStage D 0) Δ b b')
    (IH : TypeCase D stage family Δ a' b') : TypeCase D stage family Δ a b := by
  intro Γ e f u v hΓ he hf EΓ Ee Ef HF left right
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ he EΓ Ee RA
  obtain ⟨f', HF', Ef'⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ hf EΓ Ef RB
  have HK := IH hΓ HE.hasType.2 HF'.hasType.2 EΓ Ee' Ef'
    (HF.compute heq hs hr hD RA) left right
  exact PiInertCarrierHistory.carrier_prefix
    (PiInertEvidence.stage_zero heq hs hc ⟨Γ, f, _, hΓ, EΓ, hf, Ef⟩ RB) HK

private theorem function_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hr : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (RA : ScopedCompute (PiInertStage D 0) Δ a a')
    (RB : ScopedCompute (PiInertStage D 0) Δ b b')
    (IH : FunctionCase D stage family Δ a' b') : FunctionCase D stage family Δ a b := by
  intro Γ A body f F G y T hΓ hid hf happ EΓ Ei Ef HB left right
  obtain ⟨⟨w, hA⟩, B, hb⟩ := hid.lam_inv henv hΓ
  obtain ⟨u, hbu⟩ := HB.original_sort ⟨hΓ, w, hA⟩ hb
  have EL : proofErase Γ (.lam A body) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) body) :=
    if_neg (not_isProof_function_to_sort hΓ (.lam hA hbu))
  have HA : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) body)) a' := by simpa only [← EΓ, ← Ei, EL] using RA
  obtain ⟨rawA, rawb, Eout, HF⟩ := HB.lambda_compute heq hs hr hD HA
  obtain ⟨i', HI, Ei'⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ hid EΓ Ei RA
  obtain ⟨A', body', rfl, _, EA', EB'⟩ := erase_lam_inv (Ei'.trans Eout)
  obtain ⟨f', HE, Ef'⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ hf EΓ Ef RB
  obtain ⟨C, E, hfPi, hy⟩ := happ.app_inv henv hΓ
  have hfPi' := (HE.toU.of_l henv hΓ hfPi).hasType.2
  have HB' : RigidSortFrames family (proofEraseCtx (A' :: Γ)) (proofErase (A' :: Γ) body') := by
    simpa only [proofEraseCtx, EA', EB'] using HF
  have HK := IH hΓ HI.hasType.2 HE.hasType.2 (hfPi'.app hy) EΓ Ei' Ef' HB' left right
  have HP := pi_inert_zero_application_evidence (stage := stage) heq hs hc hΓ hfPi hfPi' hy
    (by simpa only [EΓ, Ef, Ef'] using RB)
  rw [EΓ] at HP
  exact PiInertCarrierHistory.carrier_prefix HP HK

private theorem type_refl
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) : TypeCase D stage family Δ a a := by
  intro Γ e f u v hΓ he hf EΓ Ee Ef HF left right
  exact HF.unit_history hs hc hi hp hx hfields hD

private theorem function_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (H : ComputedJointCompare (PiInertStage D 0) Δ false (.lam A b) (.lam C d))
    (K : TypeCase D stage family (A :: Δ) b d ∨ TypeCase D stage family (C :: Δ) b d ∨
      (EtaHead (.lam A b) (.lam C d) ∨ EtaHead (.lam C d) (.lam A b))) :
    FunctionCase D stage family Δ (.lam A b) (.lam C d) := by
  intro Γ A₀ body f F G y T hΓ hid hf happ EΓ Ei Ef HB left right
  obtain ⟨A₁, body₁, E, _, EA, Eb⟩ := erase_lam_inv Ei
  cases E
  obtain ⟨C₀, d₀, rfl, _, EC, Ed⟩ := erase_lam_inv Ef
  have HH : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A₀ body)) (proofErase Γ (.lam C₀ d₀)) := by simpa only [EΓ, Ei, Ef] using H
  obtain ⟨w, u, HAC, hb, hd⟩ := pi_inert_compared_lambda_body_typing heq hs hΓ hid hf HB HH
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, w, HAC.hasType.1⟩
  have hΓC : OnCtx (C₀ :: Γ) (env.IsType univs) := ⟨hΓ, w, HAC.hasType.2⟩
  obtain ⟨Y, E, hfPi, hy⟩ := happ.app_inv henv hΓ
  have hyC := argument_at_displayed_domain hΓ hfPi (.lam HAC.hasType.2 hd) hy
  rcases K with KL | KR | HE
  · have W : IsDefEqCtx env univs Γ (C₀ :: Γ) (A₀ :: Γ) := .succ .zero HAC.symm
    have hdA := hd.defeqDFC henv W
    have EdA := (proofErase_defeqCtx hΓC W hd).symm.trans Ed
    have HK := KL hΓA hb hdA (by simp only [proofEraseCtx, EA, EΓ]) Eb EdA
      (by simpa only [proofEraseCtx, EA, EΓ, Eb] using HB) (left.liftN 1) (right.liftN 1)
    have HK' : PiInertCarrierHistory D stage (proofEraseCtx (A₀ :: Γ))
        (proofErase (A₀ :: Γ) d₀) (left.liftN 1) (right.liftN 1) := by
      simpa only [proofEraseCtx, EA, EΓ, EdA] using HK
    simpa only [EΓ] using HK'.type_body_application hs hc hΓ HAC hd hyC
  · have W : IsDefEqCtx env univs Γ (A₀ :: Γ) (C₀ :: Γ) := .succ .zero HAC
    have hbC := hb.defeqDFC henv W
    have EbC := (proofErase_defeqCtx hΓA W hb).symm.trans Eb
    have HBC := HB.context (ContextSubstitution.of_defeqCtx hΓ W)
    rw [proofErase_defeqCtx hΓA W hb] at HBC
    have HK := KR hΓC hbC hd (by simp only [proofEraseCtx, EC, EΓ]) EbC Ed
      (by simpa only [proofEraseCtx, EC, EΓ, EbC] using HBC) (left.liftN 1) (right.liftN 1)
    have HK' : PiInertCarrierHistory D stage (proofEraseCtx (C₀ :: Γ))
        (proofErase (C₀ :: Γ) d₀) (left.liftN 1) (right.liftN 1) := by
      simpa only [proofEraseCtx, EC, EΓ, Ed] using HK
    simpa only [EΓ] using HK'.type_body_application hs hc hΓ HAC.hasType.2 hd hyC
  · have HE' : EtaHead (proofErase Γ (.lam A₀ body)) (proofErase Γ (.lam C₀ d₀)) ∨
        EtaHead (proofErase Γ (.lam C₀ d₀)) (proofErase Γ (.lam A₀ body)) := by
      simpa only [Ei, Ef] using HE
    have HD := (RigidSortFrames.typed_eta_pair_iff hΓ HAC hb hd HE').1 HB
    simpa only [EΓ] using HD.unit_application_history hs hc hi hp hx hfields hD hΓ hd hyC

private def ArgumentRecovery (D : Definitions) (Δ : List ProofShape) (f C : ProofShape) : Prop :=
  (∃ B, ScopedTypeRecovery (PiInertStage D 0) Δ f (.forallE C B)) ∨
    ∃ body, ScopedCompute (PiInertStage D 0) Δ f (.lam C body)

private theorem argument_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ArgumentRecovery D Δ rawf rawC)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.app f x) T)
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = rawf) :
    ∃ C, env.HasType univs Γ x C ∧ proofErase Γ C = rawC := by
  obtain ⟨A, B, hf, hx⟩ := ht.app_inv henv hΓ
  rcases R with ⟨rawB, R⟩ | ⟨body, R⟩
  · have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨C, E, hfC, EC, _⟩ := proofErase_scoped_recovered_pi_descend
      (zero_descent heq hs) hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero, EΓ, Ef] using R)
    exact ⟨C, argument_at_displayed_domain hΓ hf hfC hx, by simpa only [ProofShape.liftN_zero] using EC⟩
  · obtain ⟨f', HE, Ee⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ hf EΓ Ef R
    obtain ⟨C, d, rfl, _, EC, _⟩ := erase_lam_inv Ee
    obtain ⟨⟨_, hC⟩, E, hd⟩ := HE.hasType.2.lam_inv henv hΓ
    have hfC := (HE.toU.of_r henv hΓ (.lam hC hd)).hasType.1
    exact ⟨C, argument_at_displayed_domain hΓ hf hfC hx, EC⟩

private def ArgumentCase (D : Definitions) (stage : Nat) (family : Name)
    (Δ : List ProofShape) (f g x y : ProofShape) : Prop :=
  TypeCase D stage family Δ x y ∨
    ∃ C, CarrierCase D stage family Δ C x y ∧
      (ArgumentRecovery D Δ f C ∨ ArgumentRecovery D Δ g C)

private theorem type_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HF : ComputedJointCompare (PiInertStage D 0) Δ false f g)
    (IF : FunctionCase D stage family Δ f g)
    (IX : ArgumentCase D stage family Δ f g x y) :
    TypeCase D stage family Δ (.app f x) (.app g y) := by
  intro Γ e t u v hΓ he ht EΓ Ee Et HB left right
  obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨g₀, y₀, rfl, _, Eg, Ey⟩ := erase_app_inv Et
  obtain ⟨A₁, B₁, hf, hx⟩ := he.app_inv henv hΓ
  obtain ⟨C₁, E₁, hg, hy⟩ := ht.app_inv henv hΓ
  cases HB with
  | constant _ Hbody =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    have HB' : RigidSortFrames family (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) := by
      simpa only [proofEraseCtx, EΓ, EA, Eb] using Hbody
    simpa only [Et] using IF hΓ hf hg ht EΓ Ef Eg HB' left right
  | identity _ HX =>
    obtain ⟨A, b, rfl, _, _, Eb⟩ := erase_lam_inv Ef
    obtain rfl := erase_bvar_inv Eb
    obtain ⟨⟨w, hA⟩, _, _⟩ := hf.lam_inv henv hΓ
    have hxA := argument_at_displayed_domain hΓ hf (HasType.lam hA (.bvar .zero)) hx
    have HX' : RigidSortFrames family (proofEraseCtx Γ) (proofErase Γ x₀) := by
      simpa only [EΓ, Ex] using HX
    obtain ⟨z, hxz⟩ := HX'.original_sort hΓ hxA
    have HA := (hxA.uniqU henv hΓ hxz).of_l henv hΓ hA
    have hzero : env.HasType univs (A :: Γ) (.bvar 0) (.sort z) := (HA.weak henv).defeq (.bvar .zero)
    have HFG : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
        (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ g₀) := by
      simpa only [EΓ, Ef, Eg] using HF
    have hgPi := (pi_inert_zero_identity_lambda_cut heq hs hc hΓ hA hzero hg HFG).1
    have hyA := argument_at_displayed_domain hΓ hg hgPi hy
    have hyz := HA.defeq hyA
    have HY : PiInertCarrierHistory D stage Δ y left right := by
      rcases IX with IX | ⟨rawC, IX, RC⟩
      · exact IX hΓ hxz hyz EΓ Ex Ey HX left right
      · rcases RC with RC | RC
        · obtain ⟨C, hxC, EC⟩ := argument_carrier heq hs RC hΓ he EΓ Ef
          exact IX hΓ hxz hyz (.inl hxC) EΓ EC Ex Ey HX left right
        · obtain ⟨C, hyC, EC⟩ := argument_carrier heq hs RC hΓ ht EΓ Eg
          exact IX hΓ hxz hyz (.inr hyC) EΓ EC Ex Ey HX left right
    have HY' : PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ y₀) left right := by
      simpa only [EΓ, Ey] using HY
    simpa only [EΓ, Et] using HX'.compared_identity_application_history
      heq hs hc hΓ hA hxA hg hyA HFG HY'

private theorem type_no_frames (H : ¬ RigidSortFrames family Δ a) : TypeCase D stage family Δ a b := by
  intro Γ e f u v hΓ he hf EΓ Ee Ef HF
  exact (H HF).elim

private theorem type_no_lam_target : TypeCase D stage family Δ a (.lam C d) := by
  intro Γ e f u v hΓ he hf EΓ Ee Ef HF
  exact (sort_not_lam hΓ hf Ef).elim

private theorem function_no_lam (H : ∀ A b, a ≠ .lam A b) : FunctionCase D stage family Δ a b := by
  intro Γ A body f F G y T hΓ hid hf happ EΓ Ei Ef HB
  obtain ⟨⟨w, hA⟩, B, hb⟩ := hid.lam_inv henv hΓ
  obtain ⟨u, hbu⟩ := HB.original_sort ⟨hΓ, w, hA⟩ hb
  have EL : proofErase Γ (.lam A body) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) body) :=
    if_neg (not_isProof_function_to_sort hΓ (.lam hA hbu))
  exact (H _ _ (Ei.symm.trans EL)).elim

private theorem function_refl
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) : FunctionCase D stage family Δ a a := by
  intro Γ A body f F G y T hΓ hid hf happ EΓ Ei Ef HB left right
  obtain ⟨⟨w, hA⟩, B, hb⟩ := hid.lam_inv henv hΓ
  obtain ⟨u, hbu⟩ := HB.original_sort ⟨hΓ, w, hA⟩ hb
  have EL : proofErase Γ (.lam A body) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) body) :=
    if_neg (not_isProof_function_to_sort hΓ (.lam hA hbu))
  exact function_terminal heq hs hc hi hp hx hfields hD (.leaf .refl)
    (.inl (type_refl hs hc hi hp hx hfields hD)) hΓ hid hf happ EΓ EL
    (Ef.trans (Ei.symm.trans EL)) HB left right

private theorem type_const
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    TypeCase D stage family Δ (.const c ls) (.const c ls') := by
  intro Γ e f u v hΓ he hf EΓ Ee Ef HF left right
  cases HF with
  | const =>
    exact (RigidSortFrames.const ⟨Γ, f, hΓ, EΓ, hf, Ef⟩).unit_history hs hc hi hp hx hfields hD

private theorem type_eta_left (H : EtaHead a b) : TypeCase D stage family Δ a b := by
  intro Γ e f u v hΓ he hf EΓ Ee Ef HF
  obtain ⟨_, _, E, _⟩ := H.shape
  exact (sort_not_lam hΓ he (Ee.trans E)).elim

private theorem type_eta_right (H : EtaHead b a) : TypeCase D stage family Δ a b := by
  intro Γ e f u v hΓ he hf EΓ Ee Ef HF
  obtain ⟨_, _, E, _⟩ := H.shape
  exact (sort_not_lam hΓ hf (Ef.trans E)).elim

private theorem carrier_family (hi : env.projections c info) :
    CarrierCase D stage family Δ (ProofShape.mkApps (.const c ls) ps) a b := by
  intro Γ e f E u v hΓ he hf ht EΓ EC Ee Ef HF
  rcases ht with ht | ht
  · exact (type_not_family_carrier hΓ he ht hi EC).elim
  · exact (type_not_family_carrier hΓ hf ht hi EC).elim

private theorem carrier_pi : CarrierCase D stage family Δ (.forallE A B) a b := by
  intro Γ e f E u v hΓ he hf ht EΓ EC Ee Ef HF
  rcases ht with ht | ht
  · exact (type_not_pi_carrier hΓ he ht EC).elim
  · exact (type_not_pi_carrier hΓ hf ht EC).elim

private theorem carrier_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (PiInertStage D 0) Δ C E)
    (IH : CarrierCase D stage family Δ E a b) : CarrierCase D stage family Δ C a b := by
  intro Γ e f T u v hΓ he hf ht EΓ EC Ee Ef HF left right
  obtain ⟨w, hT⟩ := ht.elim (fun h => h.isType henv hΓ) (fun h => h.isType henv hΓ)
  obtain ⟨T', HE, ET⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ hT EΓ EC R
  exact IH hΓ he hf (ht.imp (fun h => HE.defeq h) (fun h => HE.defeq h))
    EΓ ET Ee Ef HF left right

private theorem carrier_reduce
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hr : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (RA : ScopedCompute (PiInertStage D 0) Δ a a')
    (RB : ScopedCompute (PiInertStage D 0) Δ b b')
    (IH : CarrierCase D stage family Δ C a' b') : CarrierCase D stage family Δ C a b := by
  intro Γ e f T u v hΓ he hf ht EΓ EC Ee Ef HF left right
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ he EΓ Ee RA
  obtain ⟨f', HF', Ef'⟩ := proofErase_scoped_compute_realize (zero_descent heq hs) hΓ hf EΓ Ef RB
  have ht' : env.HasType univs Γ e' T ∨ env.HasType univs Γ f' T :=
    ht.imp (fun h => (HE.toU.of_l henv hΓ h).hasType.2) (fun h => (HF'.toU.of_l henv hΓ h).hasType.2)
  have HK := IH hΓ HE.hasType.2 HF'.hasType.2 ht' EΓ EC Ee' Ef'
    (HF.compute heq hs hr hD RA) left right
  exact PiInertCarrierHistory.carrier_prefix
    (PiInertEvidence.stage_zero heq hs hc ⟨Γ, f, _, hΓ, EΓ, hf, Ef⟩ RB) HK

private theorem readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (H : ComputedJointCheck (PiInertStage D 0) Δ kind a b) :
    CheckCase D stage family Δ kind a b ∧ CheckCase D stage family Δ kind b a := by
  have hr := henv.projectionRigid hi
  induction H with
  | leaf H =>
    cases H with
    | refl =>
      exact ⟨⟨type_refl hs hc hi hp hx hfields hD,
          fun _ => function_refl heq hs hc hi hp hx hfields hD⟩,
        ⟨type_refl hs hc hi hp hx hfields hD,
          fun _ => function_refl heq hs hc hi hp hx hfields hD⟩⟩
    | sort =>
      exact ⟨⟨type_no_frames (by intro H; cases H), fun _ => function_no_lam (by intros; intro E; cases E)⟩,
        ⟨type_no_frames (by intro H; cases H), fun _ => function_no_lam (by intros; intro E; cases E)⟩⟩
    | const =>
      exact ⟨⟨type_const hs hc hi hp hx hfields hD, fun _ => function_no_lam (by intros; intro E; cases E)⟩,
        ⟨type_const hs hc hi hp hx hfields hD, fun _ => function_no_lam (by intros; intro E; cases E)⟩⟩
    | etaL H => exact ⟨⟨type_eta_left H, fun E => by cases E⟩, ⟨type_eta_right H, fun E => by cases E⟩⟩
    | etaR H => exact ⟨⟨type_eta_right H, fun E => by cases E⟩, ⟨type_eta_left H, fun E => by cases E⟩⟩
  | app HF HX ihf ihx =>
    exact ⟨⟨type_application heq hs hc HF (ihf.1.2 rfl) (.inl ihx.1.1),
        fun _ => function_no_lam (by intros; intro E; cases E)⟩,
      ⟨type_application heq hs hc HF.symm (ihf.2.2 rfl) (.inl ihx.2.1),
        fun _ => function_no_lam (by intros; intro E; cases E)⟩⟩
  | appCarrier R HF HX ihf ihx =>
    exact ⟨⟨type_application heq hs hc HF (ihf.1.2 rfl) (.inr ⟨_, ihx.1, .inl (.inl ⟨_, R⟩)⟩),
        fun _ => function_no_lam (by intros; intro E; cases E)⟩,
      ⟨type_application heq hs hc HF.symm (ihf.2.2 rfl) (.inr ⟨_, ihx.2, .inr (.inl ⟨_, R⟩)⟩),
        fun _ => function_no_lam (by intros; intro E; cases E)⟩⟩
  | appComputed R HF HX ihf ihx =>
    exact ⟨⟨type_application heq hs hc HF (ihf.1.2 rfl) (.inr ⟨_, ihx.1, .inl (.inr ⟨_, R⟩)⟩),
        fun _ => function_no_lam (by intros; intro E; cases E)⟩,
      ⟨type_application heq hs hc HF.symm (ihf.2.2 rfl) (.inr ⟨_, ihx.2, .inr (.inr ⟨_, R⟩)⟩),
        fun _ => function_no_lam (by intros; intro E; cases E)⟩⟩
  | proj | forallE | forallSorted =>
    exact ⟨⟨type_no_frames (by intro H; cases H), fun _ => function_no_lam (by intros; intro E; cases E)⟩,
      ⟨type_no_frames (by intro H; cases H), fun _ => function_no_lam (by intros; intro E; cases E)⟩⟩
  | lam HD HB ihd ihb =>
    refine ⟨⟨type_no_frames (by intro H; cases H), ?_⟩,
      ⟨type_no_frames (by intro H; cases H), ?_⟩⟩
    · intro E; cases E
      exact function_terminal heq hs hc hi hp hx hfields hD (.lam HD HB) (.inl ihb.1.1)
    · intro E; cases E
      exact function_terminal heq hs hc hi hp hx hfields hD (.symm (.lam HD HB)) (.inr (.inl ihb.2.1))
  | lamSorted SA SC HD HB ihd ihb =>
    refine ⟨⟨type_no_frames (by intro H; cases H), ?_⟩,
      ⟨type_no_frames (by intro H; cases H), ?_⟩⟩
    · intro E; cases E
      exact function_terminal heq hs hc hi hp hx hfields hD (.lamSorted SA SC HD HB) (.inl ihb.1.1)
    · intro E; cases E
      exact function_terminal heq hs hc hi hp hx hfields hD (.symm (.lamSorted SA SC HD HB)) (.inr (.inl ihb.2.1))
  | lamCommon =>
    exact ⟨⟨type_no_frames (by intro H; cases H), fun E => by cases E⟩,
      ⟨type_no_frames (by intro H; cases H), fun E => by cases E⟩⟩
  | etaBodyL => exact ⟨⟨type_no_frames (by intro H; cases H), fun E => by cases E⟩,
      ⟨type_no_lam_target, fun E => by cases E⟩⟩
  | etaBodyR => exact ⟨⟨type_no_lam_target, fun E => by cases E⟩,
      ⟨type_no_frames (by intro H; cases H), fun E => by cases E⟩⟩
  | structFields hi' hx' hp' hf' =>
    constructor <;> refine ⟨?_, fun E => by cases E⟩
    · intro Γ e f u v hΓ he hf EΓ Ee Ef HF
      exact (sort_not_constructor hΓ he hi' hx' hp' hf' Ee).elim
    · intro Γ e f u v hΓ he hf EΓ Ee Ef HF
      exact (sort_not_constructor hΓ hf hi' hx' hp' hf' Ef).elim
  | etaLams HD HE ih =>
    refine ⟨⟨type_no_frames (by intro H; cases H), ?_⟩,
      ⟨type_no_frames (by intro H; cases H), ?_⟩⟩
    · intro E; cases E
      exact function_terminal heq hs hc hi hp hx hfields hD (.etaLams HD HE) (.inr (.inr HE))
    · intro E; cases E
      exact function_terminal heq hs hc hi hp hx hfields hD (.symm (.etaLams HD HE)) (.inr (.inr HE.symm))
  | compute RA RB HC ih =>
    exact ⟨⟨type_compute heq hs hc hr hD RA RB ih.1.1,
        fun E => function_compute heq hs hc hr hD RA RB (ih.1.2 E)⟩,
      ⟨type_compute heq hs hc hr hD RB RA ih.2.1,
        fun E => function_compute heq hs hc hr hD RB RA (ih.2.2 E)⟩⟩
  | symm H ih => exact ih.symm
  | carrierIntro hi' | carrierNested hi' => exact ⟨carrier_family hi', carrier_family hi'⟩
  | carrierChecked H ih =>
    constructor
    · intro Γ e f E u v hΓ he hf ht EΓ EC Ee Ef HF
      exact ih.1.1 hΓ he hf EΓ Ee Ef HF
    · intro Γ e f E u v hΓ he hf ht EΓ EC Ee Ef HF
      exact ih.2.1 hΓ he hf EΓ Ee Ef HF
  | carrierSubsingleton H =>
    cases H with
    | unit hi' => exact ⟨carrier_family hi', carrier_family hi'⟩
    | forallE => exact ⟨carrier_pi, carrier_pi⟩
  | carrierFunction => exact ⟨carrier_pi, carrier_pi⟩
  | carrierSymm H ih => exact ih.symm
  | carrierCompute R H ih => exact ⟨carrier_compute heq hs R ih.1, carrier_compute heq hs R ih.2⟩
  | carrierReduce RA RB H ih => exact ⟨carrier_reduce heq hs hc hr hD RA RB ih.1,
      carrier_reduce heq hs hc hr hD RB RA ih.2⟩

/-- A raw stage-zero comparison against a unit-framed type constructs the
target's complete carrier history. Both checking modes, every recursive
application rule, all future substitutions and independent residuals are
covered. No pre-existing history for the target or comparison child is assumed. -/
theorem RigidSortFrames.zero_compared_history
    (HF : RigidSortFrames family (proofEraseCtx Γ) (proofErase Γ A))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ A) (proofErase Γ B)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ B) left right :=
  (readout heq hs hc hi hp hx hfields hD H).1.1 hΓ hA hB rfl rfl rfl HF left right

/-- The function clause of the simultaneous induction consumes the actual
body premises of lambda checking. A framed source body and raw stage-zero
inferred function comparison suffice for the original target application;
no recursive body-history premise or separate application-closure law remains. -/
theorem RigidSortFrames.zero_compared_function_application_history
    (HB : RigidSortFrames family (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A b) F) (hg : env.HasType univs Γ g G)
    (happ : env.HasType univs Γ (.app g y) T)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ g)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.app g y)) left right :=
  (readout heq hs hc hi hp hx hfields hD H).1.2 rfl hΓ hf hg happ rfl rfl rfl HB left right

/-- Carrier checking also supplies a complete unit history at the compared
type when both endpoints are independently sort typed and either has the
actual supplied carrier. The carrier and comparison clauses are proved in one
structural induction, rather than recursively calling a transformed certificate. -/
theorem RigidSortFrames.zero_carrier_compared_history
    (HF : RigidSortFrames family (proofEraseCtx Γ) (proofErase Γ A))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (ht : env.HasType univs Γ A C ∨ env.HasType univs Γ B C)
    (H : ComputedJointCarrierGuard (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ A) (proofErase Γ B)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ B) left right :=
  (readout heq hs hc hi hp hx hfields hD H).1 hΓ hA hB ht rfl rfl rfl rfl HF left right

/-- In particular, comparison with an actual nullary empty structure type at
stage zero supplies the whole target history at any requested stage. Expanded
constant/identity frames and carrier-checked arguments are allowed inside the
raw certificate; literal family-head preservation is not assumed. -/
theorem pi_inert_zero_compared_unit_carrier_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hT : env.HasType univs Γ T (.sort v))
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (.const family ls)) (proofErase Γ T)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ T) left right := by
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  have HF : RigidSortFrames family (proofEraseCtx Γ) (proofErase Γ (.const family ls)) := by
    rw [ES]
    exact .const ⟨Γ, _, hΓ, rfl, hS, ES⟩
  exact HF.zero_compared_history heq hs hc hi hp hx hfields hD hΓ hS hT H

end Lean4Lean.VEnv.Strengthening
