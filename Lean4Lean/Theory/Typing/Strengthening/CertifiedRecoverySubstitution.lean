import Lean4Lean.Theory.Typing.Strengthening.RecoveredComparison
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalApplication

/-! # Substitution with a recovered argument type

Exact recovery is not preserved by arbitrary typed substitution. Supplying a
recovery certificate for the argument at the substituted declaration discharges
the variable case and preserves the full selected output type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- Substituting a recoverable argument into a lookup preserves its exact type.
The substituted occurrence uses that argument certificate; other occurrences
remain lookups, with the appropriate weakening under subsequent binders. -/
theorem TypeRecovery.lookup_instN
    (Rx : TypeRecovery D depth Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (h : Lookup Γ₁ i T) :
    TypeRecovery D depth Γ ((.bvar i : VExpr).inst x k) (T.inst x k) := by
  dsimp [inst]
  induction W generalizing i T with
  | zero =>
    cases h with simp [inst_lift]
    | zero => exact Rx
    | succ h => exact .bvar h
  | succ _ ih =>
    cases h with (simp; rw [Nat.add_comm, ← VExpr.liftN_instN_lo (hj := Nat.zero_le _)])
    | zero => exact .bvar .zero
    | succ h => exact TypeRecovery.weakN .one (ih h)

/-- Exact output preservation holds when the argument itself recovers the
source declaration type. Source well-formedness supplies the intermediate type
needed by substitution of certified K computations. -/
theorem TypeRecovery.instN_of_recovery (R : TypeRecovery D depth Γ₁ e T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecovery D depth Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ht : VExpr.WF env univs Γ₁ e) :
    TypeRecovery D depth Γ (e.inst x k) (T.inst x k) := by
  induction R generalizing k Γ with
  | sort hu => exact .sort hu
  | const hc hl hn =>
    rw [((henv.ordered.closedC hc).instL).instN_eq (Nat.zero_le _)]
    exact .const hc hl hn
  | bvar h => exact TypeRecovery.lookup_instN Rx W h
  | lam _ ih =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ₁
    exact .lam (ih ⟨hΓ₁, hA⟩ W.succ hb)
  | app _ ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ₁
    exact VExpr.inst_inst_hi .. ▸ TypeRecovery.app (ih hΓ₁ W ⟨_, hf⟩)
  | forallE hA hB => exact .forallE (hA.instN henv W hx) (hB.instN henv W.succ hx)
  | @proj s info Γs m ls args i F hi _ hF ih =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ₁ ht
    have hclosed := henv.ordered.closedC (henv.ordered.projectionConstructor hi)
    have hF' := VProjectionInfo.fieldType_inst_some info hclosed hF (value := x) (k := k)
    simp only [List.map_take] at hF'
    have hm' := ih hΓ₁ W ⟨_, hm.hasType.2⟩
    simp only [inst_mkApps, inst] at hm'
    exact TypeRecovery.proj hi hm' hF'
  | convert R RC ih =>
    have heT := TypeRecovery.hasType R heq hs hΓ₁ ht
    obtain ⟨_, hT⟩ := heT.isType henv hΓ₁
    exact .convert (ih hΓ₁ W ht) (RC.instN heq hs hΓ₁ hx W ⟨_, hT⟩)

/-- Both comparison modes survive homogeneous substitution with a recovered
argument type. This does not assert the heterogeneous or arbitrary-argument law
needed for every delayed beta comparison. -/
theorem RecoveredComparison.instN_of_recovery
    (H : RecoveredComparison D depth mode Γ₁ a b)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecovery D depth Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) :
    RecoveredComparison D depth mode Γ (a.inst x k) (b.inst x k) := by
  induction H generalizing k Γ with
  | base H => exact .base (H.instN hx W)
  | app hf hg ha hb _ _ ihf iha =>
    exact .app (hf.instN henv W hx) (hg.instN henv W hx) (ha.instN henv W hx)
      (hb.instN henv W hx) (ihf hΓ₁ W) (iha hΓ₁ W)
  | recover Ra Rb HT Hab ihT ihab =>
    obtain ⟨_, hab⟩ := Hab.defeq hΓ₁
    exact .recover (Ra.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.1⟩)
      (Rb.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.2⟩) (ihT hΓ₁ W) (ihab hΓ₁ W)
  | sameType Ra Rb Hab ih =>
    obtain ⟨_, hab⟩ := Hab.defeq hΓ₁
    exact .sameType (Ra.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.1⟩)
      (Rb.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.2⟩) (ih hΓ₁ W)

end Lean4Lean.VEnv.Strengthening
