import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionCanonical

/-! # Return at a natively selected, convertible function domain

The retained function is demanded with an empty input-demand list. Its fresh
argument needs only ordinary unit typing, so a selected domain need not itself
compute to the literal unit type. Native replay and two ordinary Pi inversions
supply the fresh world's typing; no native recovery of its fresh variable at
Unit is required.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom)
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] [Atom]

/-- A chosen annotation determines the common family output. -/
def selectedCanonical (c r : Name) (A : ProofShape) : AtomicControl.ControlType → ProofShape
  | .sort _ => .app (.const r []) (.lam A (.const c []))
  | _ => .const c []

omit [Params] [Atom] in
/-- Closed selected annotations make the common output invariant under worlds. -/
theorem selectedCanonical_subst (hA : ∀ σ, A.subst σ = A) (t : AtomicControl.ControlType) :
    (selectedCanonical c r A t).subst σ = selectedCanonical c r A t := by
  cases t <;> simp only [selectedCanonical, ProofShape.subst, hA]

/-- Actual native selection plus ordinary assigned typing supplies all sorts
and fresh-variable typing needed to eta-expand the retained function. These
are ordinary conversions; no directed conversion to the unit annotation is asserted. -/
theorem selected_header_data
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HF : AtomicControl.ControlTyping Δ f (.arrow (.arrow .atom .atom) (.sort v)))
    (RN : ScopedTypeRecovery Step Δ f (.forallE (.forallE A B) C)) :
    DomainSort Δ (.forallE A B) (AtomicControl.ControlType.arrow .atom .atom).level ∧
    DomainSort Δ A AtomicControl.ControlType.atom.level ∧
    DomainSort (.forallE A B :: Δ) (A.liftN 1) AtomicControl.ControlType.atom.level ∧
    AtomicControl.ControlTyping (A :: Δ) (.bvar 0) .atom := by
  obtain ⟨Γ, f₀, hΓ, rfl, hf, Ef⟩ := HF
  have HW := (AtomicControl.ControlTyping.of_typed hΓ hf).wf
  obtain ⟨Q₀, C₀, hfQ, EQ, _⟩ := proofErase_scoped_recovered_pi_descend
    hstep hΓ hΓ (Ctx.LiftN.zero []) hf
    (by simpa only [List.length_nil, ProofShape.liftN_zero, Ef] using RN)
  simp only [List.length_nil, ProofShape.liftN_zero] at EQ
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv EQ
  obtain ⟨⟨_, HQ⟩, _⟩ := (hfQ.uniqU henv hΓ hf).forallE_inv henv hΓ
  have hQ := (AtomicControl.ControlType.typed HW.1).defeqU_l henv hΓ HQ.toU.symm
  obtain ⟨⟨_, HA⟩, _⟩ := HQ.toU.forallE_inv henv hΓ
  have hA := (AtomicControl.ControlType.typed HW.1.1).defeqU_l henv hΓ HA.toU.symm
  have hΓQ : OnCtx (VExpr.forallE A₀ B₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hx : env.HasType univs (A₀ :: Γ) (.bvar 0) AtomicControl.ControlType.atom.expr := by
    have H := (show env.HasType univs (A₀ :: Γ) (.bvar 0) A₀.lift from .bvar .zero).defeqU_r
      henv hΓA (HA.toU.weak henv)
    simpa only [(AtomicControl.ControlType.atom.closedN (k := 0)).lift_eq] using H
  refine ⟨⟨Γ, _, hΓ, rfl, hQ, EQ⟩, ⟨Γ, A₀, hΓ, rfl, hA, EA⟩, ?_, ?_⟩
  · refine ⟨_, A₀.lift, hΓQ, by simp only [proofEraseCtx, EQ], ?_, ?_⟩
    · exact hA.weak henv
    · rw [proofErase_liftN hΓ hΓQ Ctx.LiftN.one hA, EA]
  · exact ⟨_, .bvar 0, hΓA, by simp only [proofEraseCtx, EA], hx,
      if_neg (AtomicControl.ControlType.not_isProof hΓA hx)⟩

/-- A family's chosen native header realizes its demand even when the chosen
function domain is only ordinarily convertible to Unit. The fresh argument
has no computational obligation, exactly as required by the empty demand list. -/
theorem family_world_selected
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : AtomicControl.ControlTyping Δ (.const r []) (.arrow (.arrow .atom .atom) (.sort v)))
    (RN : ∀ {Δ}, AtomicControl.ControlTyping Δ (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) →
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ (.const r [])
        (.forallE (.forallE A B) C)) :
    WorldComputes (ErasedStaticStructureEtaExpansionUnion D) (selectedCanonical c r A) Δ
      (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) (.app [.app [] .pi] .pi) := by
  simp only [WorldComputes]
  intro Δ' τ W a HA ha
  have HF' : AtomicControl.ControlTyping Δ' (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) :=
    HF.subst W.interpretation
  have R := RN HF'
  obtain ⟨SQ, SA₀, SA, HX⟩ := selected_header_data
    (erased_static_structure_eta_expansion_union_descent heq hs) HF' R
  have hpos (t : AtomicControl.ControlType) : ¬ t.level ≈ .zero := by
    intro E
    exact t.level_ne_zero [] (congrFun E [])
  have HK := ha (.app [] .pi) (by simp)
  simp only [WorldComputes] at HK
  obtain ⟨Γ, a₀, hΓ, EΓ, _, _⟩ := HA
  obtain ⟨A₀, hA, EA⟩ := (EΓ.symm ▸ SA₀).realize hΓ
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have WA : ContextRenaming Δ' (A :: Δ') (fun i => .bvar (i+1)) := by
    have WW := ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one
    simpa only [proofEraseCtx, EA, EΓ, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using WW
  have KB := HK WA (.bvar 0) HX (by simp)
  have EL : a.subst (fun i => .bvar (i+1)) = a.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) a)
  rw [EL] at KB
  exact (static_structure_caller_argument_eta R SQ (hpos _) SA (hpos _)).trans
    (.app .refl (.lam .refl KB))

/-- A native header exposed at the closed family is itself closed. Native
replay recovers an actual empty-context type, rather than assuming a generic
closedness property of raw computation. -/
theorem closed_selected_header
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hf : env.HasType univs [] (.const r [])
      (AtomicControl.ControlType.arrow (.arrow .atom .atom) (.sort v)).expr)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r [])
      (.forallE (.forallE A B) C)) :
    (∀ σ, (ProofShape.forallE (.forallE A B) C).subst σ = .forallE (.forallE A B) C) ∧
    (∀ σ, A.subst σ = A) := by
  have EF : proofErase [] (.const r []) = .const r [] :=
    if_neg (AtomicControl.ControlType.not_isProof (by trivial) hf)
  obtain ⟨T, hT, ET⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) (by trivial) hf
    (by simpa only [EF, proofEraseCtx] using RN)
  obtain ⟨_, hTT⟩ := hT.isType henv (by trivial)
  have hclosed := hTT.closedN henv.ordered (by trivial)
  have HC (σ : ProofShape.Subst) : (ProofShape.forallE (.forallE A B) C).subst σ =
      .forallE (.forallE A B) C := by
    rw [← ET]
    exact proofErase_closed_subst hclosed
  refine ⟨HC, fun σ => ?_⟩
  exact (ProofShape.forallE.inj (ProofShape.forallE.inj (HC σ)).1).1

/-- One closed native exposure transports to every actual future world. Only
exact weakening is used; no type-conversion completeness premise appears. -/
theorem selected_family_native_world
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HC : ∀ σ, T.subst σ = T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const r []) T)
    (HF : AtomicControl.ControlTyping Δ (.const r []) (.arrow (.arrow .atom .atom) (.sort v))) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ (.const r []) T := by
  obtain ⟨Γ, f, hΓ, EΓ, _, _⟩ := HF
  have W : Ctx.LiftN Γ.length 0 [] Γ := by simpa using Ctx.LiftN.zero (Γ := []) Γ
  have R := RN.rename (union_world_rename heq hs) (ContextRenaming.of_liftN (by trivial) hΓ W)
  simpa only [HC, ProofShape.subst, EΓ] using R

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
