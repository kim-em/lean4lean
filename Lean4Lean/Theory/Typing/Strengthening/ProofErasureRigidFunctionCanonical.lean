import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionWorlds
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitFunctionParameter

/-! # Canonical interpretation of a family retaining unit endofunctions

The family's native header supplies the chosen lambda domain. The argument's
context-indexed demand supplies computation of its body at the fresh unit.
Native recovery of the argument at that selected Pi is never assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] [Atom]

omit [Atom] in
/-- Erasure of the closed unit-function type is literal in every context. -/
theorem unit_arrow_erasure
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (.forallE (.const s []) (.const s [])) = .forallE (.const s []) (.const s []) := by
  have hSΓ : env.HasType univs Γ (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (VExpr.const s [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have hSS : env.HasType univs (VExpr.const s [] :: Γ) (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ (.forallE hSΓ hSS))]
  rw [show proofErase Γ (.const s []) = .const s [] from if_neg (not_isProof_of_sort hΓ hSΓ),
    show proofErase (VExpr.const s [] :: Γ) (.const s []) = .const s [] from if_neg (not_isProof_of_sort hΓS hSS)]

/-- Unit results and family results have fixed, closed computational targets. -/
def canonical (c r s : Name) : AtomicControl.ControlType → ProofShape
  | .sort _ => .app (.const r []) (.lam (.const s []) (.const c []))
  | _ => .const c []

omit [Params] [Atom] in
/-- The canonical output never acquires a free variable under renaming. -/
theorem canonical_subst (t : AtomicControl.ControlType) : (canonical c r s t).subst σ = canonical c r s t := by
  cases t <;> rfl

omit [Atom] in
/-- Full enriched primitives transport under exact context renaming. -/
theorem union_world_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ErasedStaticStructureEtaExpansionUnion D Δ a b) (W : ContextRenaming Δ Δ' τ) :
    ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
  obtain ⟨n, H⟩ := H
  exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩

/-- A literal native unit-function header realizes its function demand in
all exact future worlds. Arguments need no native certificate. -/
theorem native_unit_function_world_of_target
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ e
      (.forallE (.const s []) (.const s [])))
    (HC : target .atom = .const info.ctorName []) :
    WorldComputes (ErasedStaticStructureEtaExpansionUnion D) target
      Δ e (.arrow .atom .atom) (.app keys .pi) := by
  simp only [WorldComputes]
  intro Δ' τ W a _ _
  have R := RN.rename (union_world_rename heq hs) W
  rw [HC]
  exact unit_native_compute hi hp hx hz (ScopedTypeRecovery.app R)

/-- A literal native unit-function header realizes its function demand in
all exact future worlds. Arguments need no native certificate. -/
theorem native_unit_function_world
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ e
      (.forallE (.const s []) (.const s []))) :
    WorldComputes (ErasedStaticStructureEtaExpansionUnion D) (canonical info.ctorName r s)
      Δ e (.arrow .atom .atom) (.app keys .pi) :=
  native_unit_function_world_of_target heq hs hi hp hx hz RN rfl

/-- The family constant realizes its higher-order input demand. The caller
selects the unit annotation; the argument is tested in that actual fresh world.
The supplied native family header is explicit and must be discharged separately. -/
theorem family_world
    (_hi : env.projections s info) (_hp : info.nparams = 0)
    (_hx : info.nindices = 0) (_hz : info.numFields = 0)
    (EA : Atom.type = .const s [])
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (RN : ∀ {Δ}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v))) :
    WorldComputes (ErasedStaticStructureEtaExpansionUnion D) (canonical info.ctorName r s) Δ
      (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) (.app [.app [] .pi] .pi) := by
  simp only [WorldComputes]
  intro Δ' τ W a HA ha
  have HK := ha (.app [] .pi) (by simp)
  simp only [WorldComputes] at HK
  obtain ⟨Γ, a₀, hΓ, EΓ, ha₀, Ea⟩ := HA
  have hSΓ : env.HasType univs Γ (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (VExpr.const s [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have ES : proofErase Γ (.const s []) = .const s [] := if_neg (not_isProof_of_sort hΓ hSΓ)
  have EΓS : proofEraseCtx (VExpr.const s [] :: Γ) = .const s [] :: Δ' := by simp only [proofEraseCtx, ES, EΓ]
  have hSS : env.HasType univs (VExpr.const s [] :: Γ) (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hQ := HasType.forallE hSΓ hSS
  have EQ : proofErase Γ (.forallE (.const s []) (.const s [])) = .forallE (.const s []) (.const s []) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ), ES]
    exact congrArg (ProofShape.forallE _) (if_neg (not_isProof_of_sort hΓS hSS))
  have SQ : DomainSort Δ' (.forallE (.const s []) (.const s [])) (.imax (.succ u) (.succ u)) :=
    ⟨Γ, _, hΓ, EΓ, hQ, EQ⟩
  have hΓQ : OnCtx (VExpr.forallE (.const s []) (.const s []) :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hSQ : env.HasType univs (VExpr.forallE (.const s []) (.const s []) :: Γ) (.const s []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have SA : DomainSort (.forallE (.const s []) (.const s []) :: Δ') ((ProofShape.const s []).liftN 1) (.succ u) :=
    ⟨_, _, hΓQ, by simp only [proofEraseCtx, EQ, EΓ], hSQ, if_neg (not_isProof_of_sort hΓQ hSQ)⟩
  have hpos : ¬ VLevel.imax (.succ u) (.succ u) ≈ .zero := by
    intro E; have E := congrFun E []; simp [VLevel.eval, Lean.Nat.imax] at E
  have hpos' : ¬ VLevel.succ u ≈ .zero := by
    intro E; have E := congrFun E []; simp [VLevel.eval] at E
  have WS : ContextRenaming Δ' (.const s [] :: Δ') (fun i => .bvar (i+1)) := by
    have WW := ContextRenaming.of_liftN hΓ hΓS Ctx.LiftN.one
    simpa only [EΓ, EΓS, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using WW
  have hx₀ : env.HasType univs (VExpr.const s [] :: Γ) (.bvar 0) (AtomicControl.ControlType.atom).expr := by
    rw [AtomicControl.ControlType.expr, EA]; exact .bvar .zero
  have HX : AtomicControl.ControlTyping (.const s [] :: Δ') (.bvar 0) .atom :=
    ⟨_, _, hΓS, EΓS, hx₀, if_neg (AtomicControl.ControlType.not_isProof hΓS hx₀)⟩
  have KB := HK WS (.bvar 0) HX (by simp)
  have EL : a.subst (fun i => .bvar (i+1)) = a.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using (subst_bvar_liftN (n := 1) (k := 0) a)
  rw [EL] at KB
  exact (static_structure_caller_argument_eta RN SQ hpos SA hpos').trans (.app .refl (.lam .refl KB))

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
