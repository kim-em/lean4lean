import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStrongBounded

/-! # Additive bounds for substitution in strong derivations

The actual type-formation child of a variable supplies its substituted type.
Retaining that child avoids reconstructing typings from the target context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

private theorem inst_lookup (henv : Ordered env)
    (h₀ : StrongBounded env U m Γ₀ e₀ e₀ A₀)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h : Lookup Γ₁ i A) :
    (∃ j, (.bvar i : VExpr).inst e₀ k = .bvar j ∧ Lookup Γ j (A.inst e₀ k)) ∨
      StrongBounded env U m Γ ((VExpr.bvar i).inst e₀ k) ((VExpr.bvar i).inst e₀ k) (A.inst e₀ k) := by
  dsimp [inst]
  induction W generalizing i A with
  | zero =>
    cases h with simp [inst_lift]
    | zero => exact .inr h₀
    | succ h => exact .inl h
  | succ W ih =>
    cases h with (simp; rw [Nat.add_comm, ← liftN_instN_lo (hj := Nat.zero_le _)])
    | zero => exact .inl .zero
    | succ h =>
      rcases ih h with ⟨j, E, hj⟩ | H
      · exact .inl ⟨j+1, by simpa [inst, instVar, lift, liftN] using congrArg VExpr.lift E, .succ hj⟩
      · exact .inr (by simpa [inst, instVar] using H.weakN henv .one)

/-- Substituting a term of rank m into a derivation of rank n costs at most
m+n. All original premises are retained, so no target-context formation or
endpoint-typing reconstruction is needed, even underneath binders. -/
theorem StrongBounded.instN (henv : Ordered env)
    (h₀ : StrongBounded env U m Γ₀ e₀ e₀ A₀)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : StrongBounded env U n Γ₁ e1 e2 A) :
    StrongBounded env U (m+n) Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  induction H generalizing Γ k with
  | bvar hl hu hA ih =>
    rcases inst_lookup henv h₀ W hl with ⟨j, E, hj⟩ | H
    · simpa only [E, Nat.add_assoc] using (StrongBounded.bvar hj hu (ih W))
    · exact H.mono (by omega)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact (StrongBounded.sortDF (n := 0) h1 h2 h3).mono (by omega)
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ ih2 =>
    simp [(henv.closedC h1).instL.instN_eq (Nat.zero_le _)] at ih2 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 (h7.mono (Nat.le_add_left ..)) (ih2 W)
  | pat hp hm _ _ hr _ ihe ihred ihall =>
    have ihred := ihred W
    rw [Pattern.RHS.instN_apply] at ihred ⊢
    refine .pat hp (Pattern.matches_instN hm) (ihe W) ihred hr.map_instN ?_
    intro t ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    exact ihall t0 ht0 W
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact inst0_inst_hi .. ▸ .appDF h1 h2
      (ih1 W) (ih2 W.succ)
      (ih3 W) (ih4 W) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih5 W)
  | @projDF typeName info levels params index sourceMajor fieldType _ _ fieldLevel
      major indexArgs major' hinfo hlevels huvars hparams hindices hfield hwf
      _ _ _ hclosed hguard ihField ihLeft ihRight =>
    have hfield' := VProjectionInfo.fieldType_inst_some
      (typeName := typeName) (levels := levels) (params := params)
      (index := index) (major := sourceMajor) (result := fieldType)
      (value := e₀) (k := k) info hclosed hfield
    have hleft := ihLeft W
    have hright := ihRight W
    simp only [VExpr.inst_mkApps, List.map_append, VExpr.inst] at hleft hright
    simpa [VExpr.inst] using
      (.projDF (info := info) (params := params.map fun param => param.inst e₀ k)
        (indexArgs := indexArgs.map fun arg => arg.inst e₀ k)
        hinfo hlevels huvars (by simpa using hparams) (by simpa using hindices)
        hfield' hwf (ihField W) hleft hright hclosed hguard)
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W.succ) (ih5 W.succ)
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF h1 h2 (ih1 W)
      (ih2 W.succ) (ih3 W.succ)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W) (ih2 W)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    rw [inst0_inst_hi, inst0_inst_hi]; exact
      .beta h1 h2
        (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W)
        (inst0_inst_hi .. ▸ ih5 W) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih6 W)
  | eta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have :=
      StrongBounded.eta h1 h2 (ih1 W) (ih2 W.succ)
        (by
          have := ih3 W.succ.succ
          rwa [lift_instN_lo, liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
        (ih4 W)
        (by
          have := ih5 W.succ
          simp only [inst, ← lift_instN_lo] at this
          rwa [liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
        (by simpa [inst, ← lift_instN_lo] using ih6 W.succ)
    rw [lift, liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    simp [
      hA1.instL.instN_eq (Nat.zero_le _),
      hA2.instL.instN_eq (Nat.zero_le _),
      hA3.instL.instN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact .extra h1 h2 h3 h4 (h5.mono (Nat.le_add_left ..)) (h6.mono (Nat.le_add_left ..)) (h7.mono (Nat.le_add_left ..)) (ih4 W) (ih5 W)
  | projIota h1 _ h3 _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.inst_mkApps, VExpr.inst] at ih1 ⊢
    exact .projIota h1 ih1 (by simp [h3]) ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.inst_mkApps, VExpr.inst, List.map_append, List.map_map,
      Function.comp_def] at ih1 ih2 ⊢
    exact .structEta h1 (by simpa using h2) h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    have ih1 := ih1 W
    have ih2 := ih2 W
    simp only [VExpr.inst_mkApps, VExpr.inst] at ih1 ih2 ⊢
    exact .unitLike h1 (by simpa using h2) h3 h4 ih1 ih2
  | raise hlt H ih => exact (ih W).mono (by omega)

/-- Substitution shifts the parent and every retained conversion edge by the
same replacement rank. Thus each edge remains strictly below its transformed
parent, although it need not remain below the original parent's rank. -/
theorem BoundedTypeTrace.instN (henv : Ordered env)
    (h₀ : StrongBounded env U m Γ₀ e₀ e₀ A₀)
    (W : Ctx.InstN Γ₀ e₀ A₀ offset Γ₁ Γ) (H : BoundedTypeTrace env U n Γ₁ A B) :
    BoundedTypeTrace env U (m+n) Γ (A.inst e₀ offset) (B.inst e₀ offset) := by
  induction H with
  | refl => exact .refl
  | step hlt H HE ih => exact .step (Nat.add_lt_add_left hlt m) ih (StrongBounded.instN henv h₀ W HE)

/-- Forgetting the additive bound gives single-term substitution for the full
original strong judgment without separate context-well-formedness hypotheses.
The original derivation supplies all type-formation premises needed locally. -/
theorem strong_instN_without_contexts (henv : Ordered env)
    (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : env.IsDefEqStrong U Γ₁ e1 e2 A) :
    env.IsDefEqStrong U Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  obtain ⟨m, hm⟩ := strong_has_bound h₀
  obtain ⟨n, hn⟩ := strong_has_bound H
  exact (StrongBounded.instN henv hm W hn).strong

/-- Extracting both endpoint typings by symmetry and transitivity costs two
ranks. This records the cost instead of silently rebuilding an unranked proof. -/
theorem StrongBounded.hasType (H : StrongBounded env U n Γ a b A) :
    StrongBounded env U (n+2) Γ a a A ∧ StrongBounded env U (n+2) Γ b b A := by
  exact ⟨.trans (H.mono (by omega)) (.symm H), .trans (.symm H) (H.mono (by omega))⟩

/-- Converting one binder's domain using a rank-n equality adds at most n+4
to the body's rank. The universe validity is explicit; no context-formation
reconstruction or strengthening theorem is used. -/
theorem StrongBounded.defeqDF_l (henv : Ordered env) (hu : u.WF U)
    (hA : StrongBounded env U n Γ A A' (.sort u))
    (H : StrongBounded env U k (A::Γ) e1 e2 B) :
    StrongBounded env U ((n+4)+k) (A'::Γ) e1 e2 B := by
  have HA' := hA.hasType.2.weakN henv (Ctx.LiftN.one (A := A'))
  have hv : StrongBounded env U (n+3) (A'::Γ) (.bvar 0) (.bvar 0) A'.lift :=
    .bvar .zero hu HA'
  have ht : StrongBounded env U (n+3) (A'::Γ) A'.lift A.lift (.sort u) :=
    (StrongBounded.symm (hA.weakN henv (Ctx.LiftN.one (A := A')))).mono (by omega)
  have replacement : StrongBounded env U (n+4) (A'::Γ) (.bvar 0) (.bvar 0) A.lift :=
    .defeqDF hu ht hv
  simpa [VExpr.inst_liftN_bvar] using
    StrongBounded.instN henv replacement Ctx.InstN.zero
      (H.weakN henv (Ctx.LiftN.succ (Ctx.LiftN.one (A := A'))))

/-- Changing a binder shifts every edge and its parent by the same cost, so
strict trace bounds survive context conversion as well as substitution. -/
theorem BoundedTypeTrace.defeqDF_l (henv : Ordered env) (hu : u.WF U)
    (hA : StrongBounded env U m Γ A A' (.sort u))
    (H : BoundedTypeTrace env U n (A::Γ) X Y) :
    BoundedTypeTrace env U ((m+4)+n) (A'::Γ) X Y := by
  induction H with
  | refl => exact .refl
  | step hlt H HE ih =>
    exact .step (Nat.add_lt_add_left hlt (m+4)) ih (StrongBounded.defeqDF_l henv hu hA HE)

end Lean4Lean.VEnv.Strengthening
