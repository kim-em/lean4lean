import Lean4Lean.Theory.Typing.Strengthening.Klop.Env.EqDeclWF
import Lean4Lean.Theory.Typing.Strengthening.Klop.Derivation

/-! # The minimal Klop environment

`exists_minimalKlopEnv`: adding the six Klop declarations to `eqEnv` gives a well-formed
environment with canonical `Eq` and an exact inventory of its constants, definitional
equations, patterns and projection metadata (`KlopInventory`). The fundamental theorem is
proved for any environment with that inventory.
-/

namespace Lean4Lean
open VExpr

namespace VEnv.Strengthening

/-- The registered reduct and (trivial) side condition of the ι rule of `Eq.rec`: the
λ-template over `α`, `a`, the motive and the minor premise, with the canonical binder
domains, returning the minor premise. -/
def eqPatRHS : canonicalEqRecPattern.RHS × canonicalEqRecPattern.Check :=
  (SimplePattern.iotaRHS ``Eq.rec ``Eq.refl 2 1 1 1 2 0 eqRecRule.rhs eqRecRule_closed, .true)

/-- The projection metadata of `Eq`: two parameters, one index, constructor `Eq.refl`. -/
def eqProjInfo : VProjectionInfo :=
  { uvars := 1, nparams := 2, nindices := 1, resultLevel := .zero, ctorName := ``Eq.refl,
    ctorType := canonicalEqReflType }

/-- The inventory of the minimal Klop environment: besides the declarations of `KlopEnv`,
its constants are exactly `Eq`, `Eq.refl`, `Eq.rec` and the six Klop constants, its
definitional equations are exactly those of `C` and `Fix`, its only registered pattern is
the ι rule of `Eq.rec` with its registered reduct (`eqPatRHS`), and its only projection
metadata is the entry of `Eq` (`eqProjInfo`: one index, no field). -/
structure KlopInventory (env : VEnv) : Prop extends KlopEnv env where
  constants_only : ∀ n ci, env.constants n = some ci →
    n = ``Eq ∨ n = ``Eq.refl ∨ n = ``Eq.rec ∨ n = `Klop.T ∨ n = `Klop.E ∨ n = `Klop.P ∨
    n = `Klop.H ∨ n = `Klop.C ∨ n = `Klop.Fix
  defeqs_only : ∀ df, env.defeqs df →
    df = ⟨0, klopC, klopCBody, .forallE klopT klopT⟩ ∨
    df = ⟨0, klopFix, klopFixBody, .forallE klopP klopT⟩
  pats_only : ∀ p r, env.pats p r → ∃ h : p = canonicalEqRecPattern, h ▸ r = eqPatRHS
  projections_only : ∀ n info, env.projections n info → n = ``Eq ∧ info = eqProjInfo

theorem addConst_rest {env env' : VEnv} {n ci} (h : env.addConst n ci = some env') :
    env'.defeqs = env.defeqs ∧ env'.pats = env.pats ∧ env'.projections = env.projections := by
  unfold VEnv.addConst at h
  split at h <;> cases h
  exact ⟨rfl, rfl, rfl⟩

/-- `exists_axiom`, also tracking the other components of the environment. -/
theorem exists_axiom' {env : VEnv} (h : env.WF) (ci : VConstVal)
    (hw : ci.toVConstant.WF env) (hf : env.constants ci.name = none) :
    ∃ env', env'.WF ∧ env ≤ env' ∧ env'.constants ci.name = some ci.toVConstant ∧
      (∀ n, n ≠ ci.name → env'.constants n = env.constants n) ∧
      env'.defeqs = env.defeqs ∧ env'.pats = env.pats ∧ env'.projections = env.projections := by
  obtain ⟨env', a⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) hf
  obtain ⟨ds, h⟩ := h
  refine ⟨env', ⟨_, .decl (.axiom hw a) h⟩, VEnv.addConst_le a, VEnv.addConst_self a, ?_,
    addConst_rest a⟩
  intro n hn
  rw [VEnv.addConst_constants_eq a]
  simp [Ne.symm hn]

/-- `exists_mutualDef`, also tracking the other components of the environment. -/
theorem exists_mutualDef' {env : VEnv} (h : env.WF) (ci : VDefVal)
    (hty : ci.toVConstant.WF env) (hf : env.constants ci.name = none)
    (hval : ∀ env', env'.Ordered → env ≤ env' →
      env'.constants ci.name = some ci.toVConstant → ci.WF env') :
    ∃ env', env'.WF ∧ env ≤ env' ∧ env'.constants ci.name = some ci.toVConstant ∧
      env'.defeqs ci.toDefEq ∧ (∀ n, n ≠ ci.name → env'.constants n = env.constants n) ∧
      (∀ df, env'.defeqs df → df = ci.toDefEq ∨ env.defeqs df) ∧
      env'.pats = env.pats ∧ env'.projections = env.projections := by
  obtain ⟨e', a⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) hf
  have a' : env.addConsts [ci] = some e' := by simp [VEnv.addConsts, a]
  have ord' := VEnv.addConsts_ordered h.ordered (cis := [ci]) (by simpa using hty) a'
  have hv := hval e' ord' (VEnv.addConst_le a) (VEnv.addConst_self a)
  have W : VDecl.WF env (.mutualDef [ci]) (e'.addDefEqs [ci]) :=
    .mutualDef (by simpa using hty) a' (by simpa using hv)
  obtain ⟨hd, hp, hpr⟩ := addConst_rest a
  obtain ⟨ds, h⟩ := h
  refine ⟨e'.addDefEqs [ci], ⟨_, .decl W h⟩, (VEnv.addConst_le a).trans VEnv.addDefEq_le,
    VEnv.addDefEq_le.constants (VEnv.addConst_self a), .inl rfl, ?_, ?_, hp, hpr⟩
  · intro n hn
    show e'.constants n = _
    rw [VEnv.addConst_constants_eq a]
    simp [Ne.symm hn]
  · intro df hdf
    rcases hdf with rfl | hdf
    · exact .inl rfl
    · exact .inr (hd ▸ hdf)

theorem eqEnv_defeqs (df : VDefEq) : ¬ eqEnv.defeqs df := by
  simp [eqEnv, VEnv.addPat, eqRecsEnv, eqProjEnv, eqCtorsEnv]

theorem eqEnv_pats (p : Pattern) (r : p.RHS × p.Check) (h : eqEnv.pats p r) :
    ∃ h : p = canonicalEqRecPattern, h ▸ r = eqPatRHS := by
  rcases h with h | h
  · exact h
  · simp [eqRecsEnv, eqProjEnv, eqCtorsEnv] at h

theorem eqEnv_projections (n : Name) (info : VProjectionInfo) (h : eqEnv.projections n info) :
    n = ``Eq ∧ info = eqProjInfo := by
  have h' : (eqCtorsEnv.addProjections eqBlock.projections).projections n info := h
  rw [VEnv.addProjections_iff] at h'
  rcases h' with ⟨entry, hmem, rfl, rfl⟩ | h'
  · have hm : entry ∈ eqDecl.projectionEntries := hmem
    simp only [VInductDecl.projectionEntries, eqDecl, eqType, List.filterMap_cons,
      List.filterMap_nil, List.mem_singleton] at hm
    subst entry
    exact ⟨rfl, rfl⟩
  · exact (h' : False).elim

theorem eqEnv_fresh {n : Name} (h1 : ``Eq.rec ≠ n) (h2 : ``Eq.refl ≠ n) (h3 : ``Eq ≠ n) :
    eqEnv.constants n = none := by
  rw [eqEnv_constants]; simp [h1, h2, h3]

theorem eqEnv_constants_only {n : Name} {ci} (h : eqEnv.constants n = some ci) :
    n = ``Eq ∨ n = ``Eq.refl ∨ n = ``Eq.rec := by
  rw [eqEnv_constants] at h
  by_cases h1 : ``Eq.rec = n
  · exact .inr (.inr h1.symm)
  · by_cases h2 : ``Eq.refl = n
    · exact .inr (.inl h2.symm)
    · by_cases h3 : ``Eq = n
      · exact .inl h3.symm
      · simp [h1, h2, h3] at h

/-- **The minimal Klop environment exists**: it is well formed, has canonical `Eq`, and has
the Klop inventory. -/
theorem exists_minimalKlopEnv :
    ∃ env : VEnv, env.WF ∧ env.HasCanonicalEq ∧ KlopInventory env := by
  have hw : (VLevel.succ .zero).WF 0 := trivial
  have h₀ := eqEnv_wf
  have heq₀ := eqEnv_hasCanonicalEq
  -- T
  obtain ⟨e1, w1, l1, cT1, k1, d1, p1, r1⟩ := exists_axiom' h₀ ⟨⟨0, .sort (.succ .zero)⟩, `Klop.T⟩
    ⟨_, HasType.sort hw⟩ (eqEnv_fresh (by decide) (by decide) (by decide))
  -- E
  obtain ⟨e2, w2, l2, cE2, k2, d2, p2, r2⟩ := exists_axiom' w1 ⟨⟨0, klopT⟩, `Klop.E⟩
    ⟨_, hasT_of cT1⟩ (by
      rw [k1 _ (by decide)]; exact eqEnv_fresh (by decide) (by decide) (by decide))
  -- P
  obtain ⟨e3, w3, l3, cP3, k3, d3, p3, r3⟩ := exists_axiom' w2 ⟨⟨0, .sort .zero⟩, `Klop.P⟩
    ⟨_, HasType.sort (show VLevel.zero.WF 0 from trivial)⟩
    (by rw [k2 _ (by decide), k1 _ (by decide)]
        exact eqEnv_fresh (by decide) (by decide) (by decide))
  have cT3 := l3.constants (l2.constants cT1)
  have heq3 := heq₀.mono (l1.trans (l2.trans l3))
  -- H
  obtain ⟨e4, w4, l4, cH4, k4, d4, p4, r4⟩ := exists_axiom' w3
    ⟨⟨0, .forallE klopT (.forallE klopT
      (VExpr.eqApp (.succ .zero) klopT (.bvar 1) (.bvar 0)))⟩, `Klop.H⟩
    ⟨_, .forallE (hasT_of cT3) (.forallE (hasT_of cT3)
      (HasType.eqApp heq3 hw (hasT_of cT3) (.bvar (.succ .zero)) (.bvar .zero)))⟩
    (by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide)]
        exact eqEnv_fresh (by decide) (by decide) (by decide))
  have cT4 := l4.constants cT3
  have cE4 := l4.constants (l3.constants cE2)
  have heq4 := heq3.mono l4
  -- C
  obtain ⟨e5, w5, l5, cC5, dC5, k5, d5, p5, r5⟩ := exists_mutualDef' w4
    ⟨⟨⟨0, .forallE klopT klopT⟩, `Klop.C⟩, klopCBody⟩
    ⟨_, .forallE (hasT_of cT4) (hasT_of cT4)⟩
    (by rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide)]
        exact eqEnv_fresh (by decide) (by decide) (by decide))
    (fun e' ord' le' cC' => by
      have S : KlopSig e' := ⟨le'.constants cT4, le'.constants cE4, le'.constants cH4, cC'⟩
      have hx : e'.HasType 0 [klopT] (.bvar 0) klopT := .bvar .zero
      exact .lam S.hasT (S.hasD ord' (heq4.mono le') hx (S.hasCApp hx)
        (S.hasHApp hx (S.hasCApp hx))))
  have S5 : KlopSig e5 :=
    ⟨l5.constants cT4, l5.constants cE4, l5.constants cH4, cC5⟩
  have cP5 := l5.constants (l4.constants cP3)
  -- Fix
  obtain ⟨e6, w6, l6, cF6, dF6, k6, d6, p6, r6⟩ := exists_mutualDef' w5
    ⟨⟨⟨0, .forallE klopP klopT⟩, `Klop.Fix⟩, klopFixBody⟩
    ⟨_, .forallE (hasP_of cP5) S5.hasT⟩
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide),
          k1 _ (by decide)]
        exact eqEnv_fresh (by decide) (by decide) (by decide))
    (fun e' ord' le' cF' => by
      have S : KlopSig e' := ⟨le'.constants S5.T, le'.constants S5.E, le'.constants S5.H,
        le'.constants S5.C⟩
      have hx : e'.HasType 0 [klopP] (.bvar 0) klopP := .bvar .zero
      have hfx : e'.HasType 0 [klopP] (.app klopFix (.bvar 0)) klopT := by
        simpa [VExpr.inst] using (hasFix_of (U := 0) (Γ := [klopP]) cF').app hx
      exact .lam (hasP_of (le'.constants cP5)) (S.hasCApp hfx))
  have hCdef : e6.defeqs ⟨0, klopC, klopCBody, .forallE klopT klopT⟩ := by
    simpa [VDefVal.toDefEq, VLevel.params] using l6.defeqs dC5
  have hFdef : e6.defeqs ⟨0, klopFix, klopFixBody, .forallE klopP klopT⟩ := by
    simpa [VDefVal.toDefEq, VLevel.params] using dF6
  refine ⟨e6, w6, (heq4.mono l5).mono l6,
    ⟨⟨⟨l6.constants S5.T, l6.constants S5.E, l6.constants S5.H, l6.constants S5.C⟩,
      l6.constants cP5, cF6, hCdef, hFdef⟩, ?_, ?_, ?_, ?_⟩⟩
  · -- constants
    intro n ci hn
    by_cases n6 : n = `Klop.Fix
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr n6)))))))
    rw [k6 n n6] at hn
    by_cases n5 : n = `Klop.C
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl n5)))))))
    rw [k5 n n5] at hn
    by_cases n4 : n = `Klop.H
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl n4))))))
    rw [k4 n n4] at hn
    by_cases n3 : n = `Klop.P
    · exact .inr (.inr (.inr (.inr (.inr (.inl n3)))))
    rw [k3 n n3] at hn
    by_cases n2 : n = `Klop.E
    · exact .inr (.inr (.inr (.inr (.inl n2))))
    rw [k2 n n2] at hn
    by_cases n1 : n = `Klop.T
    · exact .inr (.inr (.inr (.inl n1)))
    rw [k1 n n1] at hn
    rcases eqEnv_constants_only hn with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · -- defeqs
    intro df hdf
    rcases d6 df hdf with rfl | hdf
    · exact .inr (by simp [VDefVal.toDefEq, VLevel.params])
    rcases d5 df hdf with rfl | hdf
    · exact .inl (by simp [VDefVal.toDefEq, VLevel.params])
    rw [d4, d3, d2, d1] at hdf
    exact (eqEnv_defeqs df hdf).elim
  · -- pats
    intro p r hp
    rw [p6, p5, p4, p3, p2, p1] at hp
    exact eqEnv_pats p r hp
  · -- projections
    intro n info hp
    rw [r6, r5, r4, r3, r2, r1] at hp
    exact eqEnv_projections n info hp

end VEnv.Strengthening
end Lean4Lean
