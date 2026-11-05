import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionRecordWorlds

/-! # Common outputs for the joint function-parameter observer

Constructor eta selects its actual literal parameter domain. Family eta selects
one actual closed native family domain, which may be ordinarily convertible.
Their input demands need no computation of the fresh argument's annotation.
-/
namespace Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets unitCarrier)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Separate value and native-family targets share the same unit function body. -/
def canonical (s uc c t : Name) (A : ProofShape) : Key → ProofShape
  | .unit => .const uc []
  | .record => .app (.const c []) (.lam (.const s []) (.const uc []))
  | .type .record => .app (.const t []) (.lam A (.const uc []))
  | _ => .proof

/-- A closed selected family annotation makes every canonical target closed. -/
theorem canonical_subst (HA : ∀ σ, A.subst σ = A) (key : Key) :
    (canonical s uc c t A key).subst σ = canonical s uc c t A key := by
  cases key with
  | unit | record | fn => rfl
  | type key => cases key <;> simp only [canonical, ProofShape.subst, HA]

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0
  [.forallE (.const s []) (.const s [])] t c))
variable (hF : env.HasType univs [] (.const t [])
  (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS hTag hF

/-- A native unit-function lookup realizes its empty-input demand in every
exact future world. The current raw argument does not need native recovery. -/
theorem native_function_world
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ e
      (.forallE (.const s []) (.const s []))) :
    WorldComputes U RT (ErasedStaticStructureEtaExpansionUnion D) (canonical s uc c t A)
      Δ e (.fn (.atom U) [] .unit) := by
  simp only [WorldComputes]
  intro Δ' τ W a _ _
  have R := RN.rename (RigidFunctionObservation.union_world_rename heq hs) W
  exact unit_native_compute hi rfl rfl rfl (ScopedTypeRecovery.app R)

/-- An actual caller selecting the literal unit-function domain can install
that annotation and compute the retained function body. The argument supplies
only the world demand and ordinary typing, not native recovery at the Pi. -/
theorem caller_function_return
    (HA : HeterogeneousControl.ControlTyping Δ a (.arrow (.atom U) (.atom U)))
    (HK : WorldComputes U RT (ErasedStaticStructureEtaExpansionUnion D) (canonical s uc c t A)
      Δ a (.fn (.atom U) [] .unit))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (.forallE (.const s []) (.const s [])) C)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f a)
      (.app f (.lam (.const s []) (.const uc []))) := by
  simp only [WorldComputes] at HK
  obtain ⟨Γ, a₀, hΓ, EΓ, _, _⟩ := HA
  have hSΓ : env.HasType univs Γ (.const s []) (.sort (.succ .zero)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (VExpr.const s [] :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have ES : proofErase Γ (.const s []) = .const s [] := if_neg (not_isProof_of_sort hΓ hSΓ)
  have EΓS : proofEraseCtx (VExpr.const s [] :: Γ) = .const s [] :: Δ := by simp only [proofEraseCtx, ES, EΓ]
  have hSS : env.HasType univs (VExpr.const s [] :: Γ) (.const s []) (.sort (.succ .zero)) := hS.weak0 henv.ordered
  have hQ := HasType.forallE hSΓ hSS
  have EQ := RigidFunctionObservation.unit_arrow_erasure hS hΓ
  have SQ : DomainSort Δ (.forallE (.const s []) (.const s [])) (.imax (.succ .zero) (.succ .zero)) :=
    ⟨Γ, _, hΓ, EΓ, hQ, EQ⟩
  have hΓQ : OnCtx (VExpr.forallE (.const s []) (.const s []) :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hSQ : env.HasType univs (VExpr.forallE (.const s []) (.const s []) :: Γ) (.const s []) (.sort (.succ .zero)) := hS.weak0 henv.ordered
  have SA : DomainSort (.forallE (.const s []) (.const s []) :: Δ) ((ProofShape.const s []).liftN 1) (.succ .zero) :=
    ⟨_, _, hΓQ, by simp only [proofEraseCtx, EQ, EΓ], hSQ, if_neg (not_isProof_of_sort hΓQ hSQ)⟩
  have hpos : ¬ VLevel.imax (.succ .zero) (.succ .zero) ≈ .zero := by
    intro E; have E := congrFun E []; simp [VLevel.eval, Lean.Nat.imax] at E
  have hpos' : ¬ VLevel.succ .zero ≈ .zero := by
    intro E; have E := congrFun E []; simp [VLevel.eval] at E
  have WS : ContextRenaming Δ (.const s [] :: Δ) (fun i => .bvar (i+1)) := by
    have WW := ContextRenaming.of_liftN hΓ hΓS Ctx.LiftN.one
    simpa only [EΓ, EΓS, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using WW
  have hx : env.HasType univs (VExpr.const s [] :: Γ) (.bvar 0) (HeterogeneousControl.ControlType.atom U).expr := .bvar .zero
  have HX : HeterogeneousControl.ControlTyping (.const s [] :: Δ) (.bvar 0) (.atom U) :=
    ⟨_, _, hΓS, EΓS, hx, if_neg (HeterogeneousControl.ControlType.not_isProof hΓS hx)⟩
  have KB := HK WS (.bvar 0) HX (by simp)
  have EL : a.subst (fun i => .bvar (i+1)) = a.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using (subst_bvar_liftN (n := 1) (k := 0) a)
  rw [EL] at KB
  exact (static_structure_caller_argument_eta RN SQ hpos SA hpos').trans (.app .refl (.lam .refl KB))

/-- Actual constructor metadata realizes the retained function demand. -/
theorem constructor_world
    (_HT : HeterogeneousControl.ControlTyping Δ (.const c []) (.arrow (.arrow (.atom U) (.atom U)) (.atom RT))) :
    WorldComputes U RT (ErasedStaticStructureEtaExpansionUnion D) (canonical s uc c t A) Δ (.const c [])
      (.fn (.arrow (.atom U) (.atom U)) [.fn (.atom U) [] .unit] .record) := by
  simp only [WorldComputes]
  intro Δ' τ W a HA ha
  exact caller_function_return hi hS hTag hF HA (ha _ (by simp)) (constructor_native hi hS hTag hF)

/-- The family realization reuses the selected-domain world theorem. Only the
unit-function demand is translated; record types keep their operational family
parameter and are never admitted from ordinary equality alone. -/
theorem family_world
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const t [])
      (.forallE (.forallE A B) C))
    (HT : HeterogeneousControl.ControlTyping Δ (.const t [])
      (.arrow (.arrow (.atom U) (.atom U)) (.sort (HeterogeneousControl.ControlType.atom RT).level))) :
    WorldComputes U RT (ErasedStaticStructureEtaExpansionUnion D) (canonical s uc c t A) Δ (.const t [])
      (.fn (.arrow (.atom U) (.atom U)) [.fn (.atom U) [] .unit] (.type .record)) := by
  letI := U
  have HF : AtomicControl.ControlTyping Δ (.const t []) (.arrow (.arrow .atom .atom) (.sort (.succ .zero))) := HT
  obtain ⟨HC, _⟩ := RigidFunctionObservation.closed_selected_header heq hs hF RF
  have HFworld := RigidFunctionObservation.family_world_selected (c := uc) heq hs HF
    (RigidFunctionObservation.selected_family_native_world heq hs HC RF)
  simp only [WorldComputes]
  intro Δ' τ W a HA ha
  simp only [RigidFunctionObservation.WorldComputes] at HFworld
  apply HFworld W a (show AtomicControl.ControlTyping Δ' a (.arrow .atom .atom) from HA)
  intro key hk
  obtain rfl := List.mem_singleton.1 hk
  simp only [RigidFunctionObservation.WorldComputes]
  intro Δ'' σ W' b HB _
  have HP := ha (.fn (.atom U) [] .unit) (by simp)
  simp only [WorldComputes] at HP
  exact HP W' b (show HeterogeneousControl.ControlTyping Δ'' b (.atom U) from HB) (by simp)

end Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
