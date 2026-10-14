import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureThinning

/-! # Contextual type recovery through arbitrary thinning

The typed oracle invariant tracks precisely the retained variable images. Its
binder extension admits convertible domain annotations on the two endpoints.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

private theorem erased_thinning_bvar_inv
    (H : (proofErase Γ e).lift' ρ = .bvar i) :
    ∃ j, e = .bvar j ∧ ρ.liftVar j = i := by
  cases e <;> simp only [proofErase] at H <;> split at H <;>
    simp_all [ProofShape.lift']

/-- An oracle may assign a convertible type instead of the literal lookup type.
Each retained entry must still have an original typed representative below. This
permits two different binder annotations during a compatible comparison. -/
def ErasedOracleThinning (Γ : List VExpr) (σ : ProofShape.TypeOracle) (ρ : Lift) : Prop :=
  ∀ {i T}, Lookup Γ i T → ∃ A, env.HasType univs Γ (.bvar i) A ∧
    (proofErase Γ A).lift' ρ = σ (ρ.liftVar i)

/-- Extend an oracle using a domain convertible to the actual new binder's
domain. The stored erased domains need not coincide syntactically. -/
theorem ErasedOracleThinning.cons_convert (H : ErasedOracleThinning Γ σ ρ)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hD : env.HasType univs Γ D (.sort v))
    (HAD : env.IsDefEqU univs Γ A D) :
    ErasedOracleThinning (A :: Γ) (σ.cons ((proofErase Γ D).lift' ρ)) ρ.cons := by
  intro i T hl
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  cases hl with
  | zero =>
    have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    refine ⟨D.lift, ((HAD.of_l henv hΓ hA).weak henv).defeq hx, ?_⟩
    simp only [Lift.liftVar, ProofShape.TypeOracle.cons,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hD]
    exact (ProofShape.lift'_liftN_one _).symm
  | succ hl =>
    rename_i i T
    obtain ⟨T', hx, ET⟩ := H hl
    obtain ⟨_, hT'⟩ := hx.isType henv hΓ
    have hx' : env.HasType univs (A :: Γ) (.bvar (i + 1)) T'.lift := by
      simpa only [HasType, lift, liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm]
        using (hx.weak henv (B := A))
    refine ⟨T'.lift, hx', ?_⟩
    simp only [Lift.liftVar, ProofShape.TypeOracle.cons, ← ET,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hT']
    exact (ProofShape.lift'_liftN_one _).symm

/-- The same-domain extension needs no conversion premise. -/
theorem ErasedOracleThinning.cons (H : ErasedOracleThinning Γ σ ρ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ErasedOracleThinning (A :: Γ) (σ.cons ((proofErase Γ A).lift' ρ)) ρ.cons :=
  H.cons_convert hΓ hA hA ⟨_, hA⟩

/-- Erased type recovery descends from source typing through arbitrary
thinning. Its whole output erasure is a lift of a reconstructed lower type,
even when it contains substituted proof markers or computed type expressions. -/
theorem proofErase_typeRecovery_thinning (hcompute : ErasedPrimitiveThinning (ProofShape.Compute Step))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (hσ : ErasedOracleThinning Γ σ ρ)
    (ht : env.HasType univs Γ e T)
    (R : ProofShape.TypeRecovery Step σ ((proofErase Γ e).lift' ρ) out) :
    ∃ A, env.HasType univs Γ e A ∧ (proofErase Γ A).lift' ρ = out := by
  generalize Ee : (proofErase Γ e).lift' ρ = source at R
  induction R generalizing Γ Γ' ρ e T with
  | bvar =>
    obtain ⟨i, rfl, rfl⟩ := erased_thinning_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    exact hσ hl
  | sort hu =>
    obtain rfl := erase_sort_inv (ProofShape.lift'_sort_inv Ee)
    refine ⟨_, .sort hu, ?_⟩
    rw [show proofErase Γ (.sort (.succ _)) = .sort (.succ _) from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .succ _) hu))]
    rfl
  | const hc hw hn =>
    obtain rfl := erase_const_inv (ProofShape.lift'_const_inv Ee)
    have hc0 := HasType.const (Γ := []) hc hw hn
    obtain ⟨_, hT⟩ := hc0.isType henv (by trivial)
    refine ⟨_, .const hc hw hn, ?_⟩
    rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ,
      ProofShape.lift'_eq_subst, proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
  | lam _ ih =>
    obtain ⟨_, _, Es, EA, Eb⟩ := ProofShape.lift'_lam_inv Ee
    obtain ⟨A, b, rfl, _, EAA, Ebb⟩ := erase_lam_inv Es
    rw [← EAA] at EA
    rw [← Ebb] at Eb
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weak' henv.ordered W⟩
    obtain ⟨B, hB, EB⟩ := ih hΓA hΓA' W.cons (EA ▸ hσ.cons hΓ hA) hb Eb
    refine ⟨.forallE A B, .lam hA hB, ?_⟩
    obtain ⟨_, hPi⟩ := (HasType.lam hA hB).isType henv hΓ
    simp only [proofErase, if_neg (not_isProof_of_sort hΓ hPi), ProofShape.lift', EA, EB]
  | app _ ih =>
    obtain ⟨_, _, Es, Ef, Ea⟩ := ProofShape.lift'_app_inv Ee
    obtain ⟨f, a, rfl, _, Eff, Eaa⟩ := erase_app_inv Es
    rw [← Eff] at Ef
    rw [← Eaa] at Ea
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨F, hfF, EF⟩ := ih hΓ hΓ' W hσ hf Ef
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.lift'_forallE_inv EF
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hCA⟩, _⟩ := (hf.uniqU henv hΓ hfF).forallE_inv henv hΓ
    have haA := hCA.defeq ha
    obtain ⟨⟨u, hA⟩, _, hB⟩ := (hfF.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    refine ⟨B.inst a, .app hfF haA, ?_⟩
    rw [proofErase_instN hΓA haA Ctx.InstN.zero hB]
    simpa only [EB, Ea] using
      (ProofShape.lift'_inst (ρ := ρ) (proofErase (A :: Γ) B) (proofErase Γ a))
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.lift'_forallE_inv Ee
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨S, hAu, ES⟩ := ihA hΓ hΓ' W hσ hA EA
    obtain rfl := erase_sort_inv (ProofShape.lift'_sort_inv ES)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hAu⟩
    have hΓA' : OnCtx (A.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', _, hAu.weak' henv.ordered W⟩
    obtain ⟨S, hBv, ES⟩ := ihB hΓA hΓA' W.cons (EA ▸ hσ.cons hΓ hAu) hB EB
    obtain rfl := erase_sort_inv (ProofShape.lift'_sort_inv ES)
    refine ⟨_, .forallE hAu hBv, ?_⟩
    rw [show proofErase Γ (.sort (.imax _ _)) = .sort (.imax _ _) from
      if_neg (not_isProof_of_sort hΓ
        (HasType.sort (l := .imax _ _) ⟨hAu.sort_r henv hΓ, hBv.sort_r henv hΓA⟩))]
    rfl
  | convert _ RC ih =>
    obtain ⟨A, heA, EA⟩ := ih hΓ hΓ' W hσ ht Ee
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    obtain ⟨A', HAA, EA'⟩ := hcompute hΓ hΓ' W hA (EA ▸ RC)
    exact ⟨A', HAA.defeq heA, EA'⟩

/-- An exposed recovered Pi reconstructs both original annotations below any
thinning, with their exact erasures under the respective binder maps. -/
theorem proofErase_recovered_pi_thinning
    (hcompute : ErasedPrimitiveThinning (ProofShape.Compute Step))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (hσ : ErasedOracleThinning Γ σ ρ)
    (hf : env.HasType univs Γ f T)
    (R : ProofShape.TypeRecovery Step σ ((proofErase Γ f).lift' ρ) (.forallE A B)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      (proofErase Γ D).lift' ρ = A ∧ (proofErase (D :: Γ) C).lift' ρ.cons = B := by
  obtain ⟨F, hfF, EF⟩ := proofErase_typeRecovery_thinning hcompute hΓ hΓ' W hσ hf R
  obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.lift'_forallE_inv EF
  obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Es
  exact ⟨D, C, hfF, by simpa only [← ED] using EA, by simpa only [← EC] using EB⟩

/-- A valid upper oracle supplies typed representatives of all retained entries. -/
theorem ErasedOracleValid.thinning (H : ErasedOracleValid Γ' σ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') : ErasedOracleThinning Γ σ ρ := by
  intro i A hl
  obtain ⟨_, hA⟩ := IsType.lookup henv hΓ hl
  exact ⟨A, .bvar hl, ((H (hl.weak' W)).trans (proofErase_lift' hΓ hΓ' W hA)).symm⟩

/-- The canonical context oracle recovers its entire output type below any
thinning, provided the computational stages admit typed replay. -/
theorem proofErase_context_typeRecovery_thinning
    (hcompute : ErasedPrimitiveThinning (ProofShape.Compute Step))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (ht : env.HasType univs Γ e T)
    (R : ProofShape.TypeRecovery Step (erasedTypeOracle Γ') (proofErase Γ' (e.lift' ρ)) out) :
    ∃ A, env.HasType univs Γ e A ∧ (proofErase Γ A).lift' ρ = out := by
  rw [proofErase_lift' hΓ hΓ' W ht] at R
  exact proofErase_typeRecovery_thinning hcompute hΓ hΓ' W
    (ErasedOracleValid.thinning (erasedTypeOracle_valid hΓ') hΓ hΓ' W) ht R

end Lean4Lean.VEnv.Strengthening
