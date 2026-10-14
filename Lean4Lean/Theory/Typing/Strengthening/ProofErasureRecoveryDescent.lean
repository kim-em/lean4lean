import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeRecovery

/-! # Erased type recovery below binder insertion

Recovery reconstructs its result type below from the original source typing.
Only the oracle entries for retained variables are needed. Hidden proof
arguments remain supplied by the source, including when they instantiate the
recovered result type. No inhabitant of a deleted binder is introduced.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv ProofShape.liftN_sort_inv ProofShape.liftN_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv ProofShape.liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

/-- Agreement of an upper oracle with the lower context at retained variables.
The oracle may have arbitrary entries for the removed binders. -/
def ErasedOracleAbove (Γ : List VExpr) (σ : ProofShape.TypeOracle) (n k : Nat) : Prop :=
  ∀ {i A}, Lookup Γ i A → σ (liftVar n i k) = (proofErase Γ A).liftN n k

/-- A valid upper context oracle has the required agreement after insertion. -/
theorem ErasedOracleValid.above (H : ErasedOracleValid Γ' σ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') : ErasedOracleAbove Γ σ n k := by
  intro i A hl
  obtain ⟨_, hA⟩ := IsType.lookup henv hΓ hl
  exact (H (hl.weakN W)).trans (proofErase_liftN hΓ hΓ' W hA)

/-- The retained-variable agreement extends under a retained typed binder. -/
theorem ErasedOracleAbove.cons (H : ErasedOracleAbove Γ σ n k)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ErasedOracleAbove (A :: Γ) (σ.cons ((proofErase Γ A).liftN n k)) n (k+1) := by
  intro i T hl
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  cases hl with
  | zero =>
    simp only [liftVar_lt (Nat.zero_lt_succ _), ProofShape.TypeOracle.cons,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hA]
    exact ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)
  | succ hl =>
    obtain ⟨_, hT⟩ := IsType.lookup henv hΓ hl
    simp only [liftVar_succ, ProofShape.TypeOracle.cons, H hl,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hT]
    exact ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)

private theorem erased_lift_bvar_inv
    (H : (proofErase Γ e).liftN n k = .bvar i) :
    ∃ j, e = .bvar j ∧ liftVar n j k = i := by
  cases e <;> simp only [proofErase] at H <;> split at H <;>
    simp_all [ProofShape.liftN]

/-- An oracle may assign a convertible type instead of the literal lookup type.
Each retained entry must still have an original typed representative below. This
permits two different binder annotations during a compatible comparison. -/
def ErasedOracleTyping (Γ : List VExpr) (σ : ProofShape.TypeOracle) (n k : Nat) : Prop :=
  ∀ {i T}, Lookup Γ i T → ∃ A, env.HasType univs Γ (.bvar i) A ∧
    (proofErase Γ A).liftN n k = σ (liftVar n i k)

/-- Exact lookup agreement is a special case of typed oracle agreement. -/
theorem ErasedOracleAbove.typing (H : ErasedOracleAbove Γ σ n k) :
    ErasedOracleTyping Γ σ n k :=
  fun hl => ⟨_, .bvar hl, (H hl).symm⟩

/-- Extend an oracle using a domain convertible to the actual new binder's
domain. The stored erased domains need not coincide syntactically. -/
theorem ErasedOracleTyping.cons_convert (H : ErasedOracleTyping Γ σ n k)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hD : env.HasType univs Γ D (.sort v))
    (HAD : env.IsDefEqU univs Γ A D) :
    ErasedOracleTyping (A :: Γ) (σ.cons ((proofErase Γ D).liftN n k)) n (k+1) := by
  intro i T hl
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  cases hl with
  | zero =>
    have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    refine ⟨D.lift, ((HAD.of_l henv hΓ hA).weak henv).defeq hx, ?_⟩
    simp only [liftVar_lt (Nat.zero_lt_succ _), ProofShape.TypeOracle.cons,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hD]
    exact (ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)).symm
  | succ hl =>
    rename_i i T
    obtain ⟨T', hx, ET⟩ := H hl
    obtain ⟨_, hT'⟩ := hx.isType henv hΓ
    have hx' : env.HasType univs (A :: Γ) (.bvar (i + 1)) T'.lift := by
      simpa only [HasType, lift, liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm]
        using (hx.weak henv (B := A))
    refine ⟨T'.lift, hx', ?_⟩
    simp only [liftVar_succ, ProofShape.TypeOracle.cons, ← ET,
      proofErase_liftN hΓ hΓA Ctx.LiftN.one hT']
    exact (ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)).symm

/-- The same-domain extension needs no conversion premise. -/
theorem ErasedOracleTyping.cons (H : ErasedOracleTyping Γ σ n k)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ErasedOracleTyping (A :: Γ) (σ.cons ((proofErase Γ A).liftN n k)) n (k+1) :=
  H.cons_convert hΓ hA hA ⟨_, hA⟩

/-- Erased type recovery descends from source typing through arbitrary block
insertion. Its whole output erasure is a lift of a reconstructed lower type,
even when it contains substituted proof markers or computed type expressions. -/
theorem proofErase_typeRecovery_descend_of_oracleTyping (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hσ : ErasedOracleTyping Γ σ n k)
    (ht : env.HasType univs Γ e T)
    (R : ProofShape.TypeRecovery Step σ ((proofErase Γ e).liftN n k) out) :
    ∃ A, env.HasType univs Γ e A ∧ (proofErase Γ A).liftN n k = out := by
  generalize Ee : (proofErase Γ e).liftN n k = source at R
  induction R generalizing Γ Γ' k e T with
  | bvar =>
    obtain ⟨i, rfl, rfl⟩ := erased_lift_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    exact hσ hl
  | sort hu =>
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv Ee)
    refine ⟨_, .sort hu, ?_⟩
    rw [show proofErase Γ (.sort (.succ _)) = .sort (.succ _) from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .succ _) hu))]
    rfl
  | const hc hw hn =>
    obtain rfl := erase_const_inv (ProofShape.liftN_const_inv Ee)
    have hc0 := HasType.const (Γ := []) hc hw hn
    obtain ⟨_, hT⟩ := hc0.isType henv (by trivial)
    refine ⟨_, .const hc hw hn, ?_⟩
    rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ,
      proofErase_closed_liftN ((henv.ordered.closedC hc).instL.mono (Nat.zero_le _))]
  | lam _ ih =>
    obtain ⟨_, _, Es, EA, Eb⟩ := ProofShape.liftN_lam_inv Ee
    obtain ⟨A, b, rfl, _, EAA, Ebb⟩ := erase_lam_inv Es
    rw [← EAA] at EA
    rw [← Ebb] at Eb
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨B, hB, EB⟩ := ih hΓA hΓA' W.succ (EA ▸ hσ.cons hΓ hA) hb Eb
    refine ⟨.forallE A B, .lam hA hB, ?_⟩
    obtain ⟨_, hPi⟩ := (HasType.lam hA hB).isType henv hΓ
    simp only [proofErase, if_neg (not_isProof_of_sort hΓ hPi), ProofShape.liftN, EA, EB]
  | app _ ih =>
    obtain ⟨_, _, Es, Ef, Ea⟩ := ProofShape.liftN_app_inv Ee
    obtain ⟨f, a, rfl, _, Eff, Eaa⟩ := erase_app_inv Es
    rw [← Eff] at Ef
    rw [← Eaa] at Ea
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨F, hfF, EF⟩ := ih hΓ hΓ' W hσ hf Ef
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hCA⟩, _⟩ := (hf.uniqU henv hΓ hfF).forallE_inv henv hΓ
    have haA := hCA.defeq ha
    obtain ⟨⟨u, hA⟩, _, hB⟩ := (hfF.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    refine ⟨B.inst a, .app hfF haA, ?_⟩
    rw [proofErase_instN hΓA haA Ctx.InstN.zero hB]
    simpa only [Nat.add_zero, EB, Ea] using
      (ProofShape.liftN_instN (proofErase (A :: Γ) B) (proofErase Γ a) n k 0)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv Ee
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨S, hAu, ES⟩ := ihA hΓ hΓ' W hσ hA EA
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv ES)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hAu⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hAu.weakN henv W⟩
    obtain ⟨S, hBv, ES⟩ := ihB hΓA hΓA' W.succ (EA ▸ hσ.cons hΓ hAu) hB EB
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv ES)
    refine ⟨_, .forallE hAu hBv, ?_⟩
    rw [show proofErase Γ (.sort (.imax _ _)) = .sort (.imax _ _) from
      if_neg (not_isProof_of_sort hΓ
        (HasType.sort (l := .imax _ _) ⟨hAu.sort_r henv hΓ, hBv.sort_r henv hΓA⟩))]
    rfl
  | proj hi HT hj hlen R ih =>
    rename_i s info ls doms result j argsRaw
    obtain ⟨_, Es, Em⟩ := ProofShape.liftN_proj_inv Ee
    obtain ⟨m, rfl, hn, Emm⟩ := erase_proj_inv Es
    rw [← Emm] at Em
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨F, hmF, EF⟩ := ih hΓ hΓ' W hσ hm.hasType.2 Em
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv EF
    obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv Es
    obtain ⟨hj', F, hproj, E⟩ := proofErase_projection_at_recovered_family hΓ hi HT ht hn hmF
    refine ⟨F, hproj, ?_⟩
    have E' : proofErase Γ F = ProofShape.projectionType s info doms j hj
        (args.map (proofErase Γ)) (proofErase Γ m) := by
      simpa only [ProofShape.projectionType, List.map_take] using E
    rw [E', ProofShape.projectionType_liftN HT hj (by
      have hh := congrArg List.length Eargs
      simp only [List.length_map] at hh ⊢
      omega), ← Eargs, Em]
  | convert _ RC ih =>
    obtain ⟨A, heA, EA⟩ := ih hΓ hΓ' W hσ ht Ee
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    obtain ⟨A', HAA, EA'⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W hA (EA ▸ RC)
    exact ⟨A', HAA.defeq heA, EA'⟩

/-- Exact oracle agreement retains the original recovery descent interface. -/
theorem proofErase_typeRecovery_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hσ : ErasedOracleAbove Γ σ n k)
    (ht : env.HasType univs Γ e T)
    (R : ProofShape.TypeRecovery Step σ ((proofErase Γ e).liftN n k) out) :
    ∃ A, env.HasType univs Γ e A ∧ (proofErase Γ A).liftN n k = out :=
  proofErase_typeRecovery_descend_of_oracleTyping hstep hΓ hΓ' W hσ.typing ht R

/-- Canonical erased context oracles instantiate the abstract retained-variable
agreement. The actual upper recovered type is reconstructed below. -/
theorem proofErase_context_typeRecovery_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (R : ProofShape.TypeRecovery Step (erasedTypeOracle Γ') (proofErase Γ' (e.liftN n k)) out) :
    ∃ A, env.HasType univs Γ e A ∧ (proofErase Γ A).liftN n k = out := by
  rw [proofErase_liftN hΓ hΓ' W ht] at R
  exact proofErase_typeRecovery_descend hstep hΓ hΓ' W
    (ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W) ht R

end Lean4Lean.VEnv.Strengthening
