import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiHistoryObservation

/-! # Recursive observations retaining pending family arguments

Every Pi payload extends a telescope of arguments not yet supplied to the
family. At the terminal payload the whole family still has its native header
and a computation to the corresponding lambda telescope. This retains the
history needed to instantiate observations without substituting native guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation
variable [Params] {D : PureObservation.Definitions}

/-- A finite recursive Pi observation. `pending` records binders still
abstracted by the retained family, while `remaining` counts Pi payloads yet to
be observed. Only terminal payloads store computation, under all pending
binders; intermediate control frames retain ordinary typing. -/
def NativeFamilyPiObservation (D : PureObservation.Definitions) (Γ : List VExpr)
    (f : VExpr) (u : VLevel) : Nat → List VExpr → ProofShape → Prop
  | 0, pending, out => ∃ B, NativeFamilyPiHistory D Γ f u pending B ∧
      proofErase (pending.reverse ++ Γ) B = out
  | remaining + 1, pending, out => ∃ v,
      Obs (fun X Y => ∃ A B,
        env.IsType univs (pending.reverse ++ Γ) A ∧
        env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
        proofErase (pending.reverse ++ Γ) A = X ∧
        proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
        NativeFamilyPiObservation D Γ f u remaining (pending ++ [A]) Y)
        0 (proofEraseCtx (pending.reverse ++ Γ)) (fun _ _ _ => False) out (.sort v) .pi

private def PrefixPiCompute (D : PureObservation.Definitions) (Γ : List VExpr)
    (ds ds' : List VExpr) : Prop :=
  ∀ B v, env.HasType univs (ds.reverse ++ Γ) B (.sort v) →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) (proofErase Γ (VExpr.wrapForalls ds' B))

private theorem wrap_type
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hB : env.IsType univs (ds.reverse ++ Γ) B) :
    env.IsType univs Γ (VExpr.wrapForalls ds B) := by
  obtain ⟨v, HB⟩ := VExpr.wrapForalls_defeq hctx hB.choose_spec
  exact ⟨v, HB.hasType.1⟩

private theorem fixed_prefix_compute
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hB : env.IsType univs (ds.reverse ++ Γ) B)
    (hC : env.IsType univs (ds.reverse ++ Γ) C)
    (R : ScopedCompute Step (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) B) (proofErase (ds.reverse ++ Γ) C)) :
    ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) (proofErase Γ (VExpr.wrapForalls ds C)) := by
  induction ds generalizing Γ with
  | nil => exact R
  | cons A ds ih =>
    have hctx' : OnCtx (ds.reverse ++ A :: Γ) (env.IsType univs) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
    have hB' : env.IsType univs (ds.reverse ++ A :: Γ) B := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hB
    have hC' : env.IsType univs (ds.reverse ++ A :: Γ) C := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hC
    have hΓA := OnCtx.of_append hctx'
    have hT := wrap_type hctx hB
    have hT' := wrap_type hctx hC
    rw [show proofErase Γ (VExpr.wrapForalls (A :: ds) B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓA.1 hT.choose_spec),
      show proofErase Γ (VExpr.wrapForalls (A :: ds) C) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓA.1 hT'.choose_spec)]
    apply ScopedCompute.forallE .refl
    apply ih hctx' hB' hC'
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using R

private theorem PrefixPiCompute.snoc
    (R : PrefixPiCompute D Γ ds ds')
    (_hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hA : env.IsType univs (ds.reverse ++ Γ) A) :
    PrefixPiCompute D Γ (ds ++ [A]) (ds' ++ [A]) := by
  intro B v hB
  have hb : env.HasType univs (A :: (ds.reverse ++ Γ)) B (.sort v) := by
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons_append, List.nil_append] using hB
  have H := R (.forallE A B) _ (HasType.forallE hA.choose_spec hb)
  simpa only [EtaTelescope.wrapForalls_append_one] using H

/-- A directed computation of the pending telescope transports the recursive
observation. Context conversion changes ordinary control typings, while each
terminal family advances through the same directed prefix history. -/
theorem NativeFamilyPiObservation.convert_pending
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hctx' : OnCtx (ds'.reverse ++ Γ) (env.IsType univs))
    (hlen : ds.length = ds'.length)
    (HC : IsDefEqCtx env univs [] (ds.reverse ++ Γ) (ds'.reverse ++ Γ))
    (R : ∀ B v, env.HasType univs (ds.reverse ++ Γ) B (.sort v) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ds B)) (proofErase Γ (VExpr.wrapForalls ds' B)))
    (H : NativeFamilyPiObservation D Γ f u remaining ds out) :
    NativeFamilyPiObservation D Γ f u remaining ds' out := by
  induction remaining generalizing ds ds' out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    have hB' := HB.body.defeqDFC henv HC
    have E := proofErase_defeqCtx hctx HC HB.body
    exact ⟨B, HB.convert heq hs hΓ hlen (wrap_type hctx' ⟨u, hB'⟩)
      (R B u HB.body), E.symm.trans EB⟩
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    have W : ContextSubstitution (proofEraseCtx (ds.reverse ++ Γ))
        (proofEraseCtx (ds'.reverse ++ Γ)) ProofShape.Subst.id :=
      ContextSubstitution.of_defeqCtx (by trivial) HC
    have HT := HO.subst_lower (σ := ProofShape.Subst.id)
      (Q := fun X Y => ∃ A B, env.IsType univs (ds'.reverse ++ Γ) A ∧
        env.IsType univs (A :: (ds'.reverse ++ Γ)) B ∧
        proofErase (ds'.reverse ++ Γ) A = X ∧
        proofErase (A :: (ds'.reverse ++ Γ)) B = Y ∧
        NativeFamilyPiObservation D Γ f u remaining (ds' ++ [A]) Y) W (fun X Y HP => by
        obtain ⟨A, B, hA, hB, EA, EB, HR⟩ := HP
        have HC' := IsDefEqCtx.succ HC hA.choose_spec
        have hΓA : OnCtx (A :: (ds.reverse ++ Γ)) (env.IsType univs) := ⟨hctx, hA⟩
        have hΓA' : OnCtx (A :: (ds'.reverse ++ Γ)) (env.IsType univs) :=
          ⟨hctx', hA.defeqDFC henv HC⟩
        have RA : PrefixPiCompute D Γ (ds ++ [A]) (ds' ++ [A]) :=
          PrefixPiCompute.snoc R hctx hA
        have hlen' : (ds ++ [A]).length = (ds' ++ [A]).length := by simp [hlen]
        have HI := ih (ds := ds ++ [A]) (ds' := ds' ++ [A])
          (by simpa using hΓA) (by simpa using hΓA') hlen' (by simpa using HC') RA HR
        have EAA := proofErase_defeqCtx hctx HC hA.choose_spec
        have EBB := proofErase_defeqCtx hΓA HC' hB.choose_spec
        refine ⟨A, B, hA.defeqDFC henv HC, hB.defeqDFC henv HC', ?_, ?_, ?_⟩
        · simpa only [ProofShape.subst_id] using EAA.symm.trans EA
        · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id] using EBB.symm.trans EB
        · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id] using HI)
      (fun _ _ _ h => h.elim)
    exact ⟨v, by simpa only [ProofShape.Subst.liftN, ProofShape.subst_id] using HT⟩

/-- Every recursive observation has an ordinary type representative in its
actual pending context, including opaque control-frame outputs. -/
theorem NativeFamilyPiObservation.realize
    (hctx : OnCtx (pending.reverse ++ Γ) (env.IsType univs))
    (H : NativeFamilyPiObservation D Γ f u remaining pending out) :
    ∃ B v, env.HasType univs (pending.reverse ++ Γ) B (.sort v) ∧
      proofErase (pending.reverse ++ Γ) B = out := by
  cases remaining with
  | zero => obtain ⟨B, HB, EB⟩ := H; exact ⟨B, u, HB.body, EB⟩
  | succ n =>
    obtain ⟨v, HO⟩ := H
    obtain ⟨Δ, B, hΔ, EΔ, HB, EB⟩ := HO.typing
    have HC := proofEraseCtx_defeq hΔ hctx EΔ
    have EC := proofErase_defeqCtx hΔ HC HB
    exact ⟨B, v, HB.defeqDFC henv HC, EC.symm.trans EB⟩

private theorem last_prefix_compute
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (HA : env.IsDefEq univs (ds.reverse ++ Γ) A A' (.sort v))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (ds.reverse ++ Γ)) (proofErase (ds.reverse ++ Γ) A)
      (proofErase (ds.reverse ++ Γ) A')) :
    PrefixPiCompute D Γ (ds ++ [A]) (ds ++ [A']) := by
  intro B w hB
  have hb : env.HasType univs (A :: (ds.reverse ++ Γ)) B (.sort w) := by simpa using hB
  have hΓA : OnCtx (A :: (ds.reverse ++ Γ)) (env.IsType univs) := ⟨hctx, v, HA.hasType.1⟩
  have HC := IsDefEqCtx.succ (Γ₀ := ds.reverse ++ Γ) .zero HA
  have hb' := hb.defeqDFC henv HC
  have EB := proofErase_defeqCtx hΓA HC hb
  have hP := HasType.forallE HA.hasType.1 hb
  have hP' := HasType.forallE HA.hasType.2 hb'
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) (.forallE A B))
      (proofErase (ds.reverse ++ Γ) (.forallE A' B)) := by
    rw [show proofErase (ds.reverse ++ Γ) (.forallE A B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hctx hP),
      show proofErase (ds.reverse ++ Γ) (.forallE A' B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hctx hP'), ← EB]
    exact .forallE RA .refl
  simpa only [EtaTelescope.wrapForalls_append_one] using
    fixed_prefix_compute hctx ⟨_, hP⟩ ⟨_, hP'⟩ RP

/-- Arbitrary full-union computation preserves all recursive Pi layers.
Payload computation descends temporary controls, advances the inner
observation, and transports its pending domain along the selected domain
history. No hidden residual is beta-normalized. -/
theorem NativeFamilyPiObservation.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (pending.reverse ++ Γ) (env.IsType univs))
    (H : NativeFamilyPiObservation D Γ f u remaining pending source)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (pending.reverse ++ Γ)) source out) :
    NativeFamilyPiObservation D Γ f u remaining pending out := by
  induction remaining generalizing pending source out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    rw [← EB] at R
    obtain ⟨B', HE, EB'⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hctx HB.body rfl rfl R
    have RP := fixed_prefix_compute hctx ⟨u, HB.body⟩ ⟨u, HE.hasType.2⟩ (EB' ▸ R)
    exact ⟨B', HB.convert heq hs hΓ rfl (wrap_type hctx ⟨u, HE.hasType.2⟩) RP, EB'⟩
  | succ remaining ih =>
    obtain ⟨e, v, he, Ee⟩ := H.realize hctx
    obtain ⟨q, HO⟩ := H
    have HP : PiOriginComponentClosure (ErasedStaticStructureEtaExpansionUnion D)
        (pending.reverse ++ Γ)
        (fun X Y => ∃ A B, env.IsType univs (pending.reverse ++ Γ) A ∧
          env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
          proofErase (pending.reverse ++ Γ) A = X ∧
          proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
          NativeFamilyPiObservation D Γ f u remaining (pending ++ [A]) Y) := by
      intro Δ n X Y X' Y' hΔ W HX RX RY
      obtain ⟨A, B, ⟨a, hA⟩, ⟨b, hB⟩, rfl, rfl, HB⟩ := HX
      obtain ⟨X₁, Y₁, HX₁, EX, EY⟩ := static_structure_piOrigin_componentClosure
        heq hs hctx hΔ W (StaticStructurePiOrigin.refl (D := D) hA hB) RX RY
      obtain ⟨A₁, B₁, HA₁, hB₁, EA₁, EB₁, RA₁, RB₁⟩ := HX₁
      have hΓA : OnCtx (A :: (pending.reverse ++ Γ)) (env.IsType univs) := ⟨hctx, a, hA⟩
      have hΓA₁ : OnCtx (A₁ :: (pending.reverse ++ Γ)) (env.IsType univs) :=
        ⟨hctx, a, HA₁.hasType.2⟩
      have HI := ih (pending := pending ++ [A]) (by simpa using hΓA) HB
        (by simpa using RB₁)
      have HC : IsDefEqCtx env univs [] (A :: (pending.reverse ++ Γ))
          (A₁ :: (pending.reverse ++ Γ)) := .succ (.refl hctx) HA₁
      have RA : PrefixPiCompute D Γ (pending ++ [A]) (pending ++ [A₁]) :=
        last_prefix_compute hctx HA₁ (EA₁ ▸ RA₁)
      have HT := HI.convert_pending heq hs hΓ (by simpa using hΓA) (by simpa using hΓA₁)
        (by simp) (by simpa using HC) RA
      exact ⟨X₁, Y₁, ⟨A₁, B₁, ⟨a, HA₁.hasType.2⟩, ⟨b, hB₁⟩, EA₁, EB₁, HT⟩, EX, EY⟩
    have HT := proofErase_scoped_compute_controlObservation
      (erased_static_structure_eta_expansion_union_descent heq hs)
      (erased_static_structure_union_controlObservation heq hs) HP R hctx (Ctx.LiftN.zero [])
      he rfl Ee (fun _ _ _ h => h.elim) HO
    exact ⟨q, HT⟩

omit [Params] in
private theorem inst_domains_snoc (ds : List VExpr) (A x : VExpr) (k : Nat) :
    VExpr.instDomains (ds ++ [A]) x k = VExpr.instDomains ds x k ++ [A.inst x (k + ds.length)] := by
  induction ds generalizing k with
  | nil => rfl
  | cons B ds ih => simp only [List.cons_append, VExpr.instDomains, ih, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1]

omit [Params] in
private theorem pending_inst (ds : List VExpr) :
    Ctx.InstN Γ x A ds.length (ds.reverse ++ A :: Γ)
      ((VExpr.instDomains ds x 0).reverse ++ Γ) := by
  induction h : ds.length generalizing ds with
  | zero => rw [List.length_eq_zero_iff.mp h]; exact .zero
  | succ n ih =>
    rcases List.eq_nil_or_concat ds with rfl | ⟨ds, B, rfl⟩
    · simp at h
    rw [List.concat_eq_append] at h ⊢
    have hlen : ds.length = n := by simp at h; omega
    have HI := ih ds hlen
    simpa only [List.length_append, List.length_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.cons_append,
      inst_domains_snoc, Nat.zero_add, List.nil_append, hlen] using HI.succ (A := B)

private theorem inst_interpretation
    (hctx : OnCtx Δ (env.IsType univs)) (W : Ctx.InstN Γ x A k Δ Δ')
    (hx : env.HasType univs Γ x A) :
    ContextSubstitution (proofEraseCtx Δ) (proofEraseCtx Δ')
      ((ProofShape.Subst.one (proofErase Γ x)).liftN k) := by
  have hΔ' := (W.wf henv.ordered hx hctx).2
  apply ContextSubstitution.of_typed hΔ' (W.substEq hctx hx)
  intro i B hl hn
  have HE := proofErase_instN hctx hx W (show env.HasType univs Δ (.bvar i) B from .bvar hl)
  rw [show proofErase Δ (.bvar i) = .bvar i from if_neg hn] at HE
  simpa only [instN_eq, VExpr.subst, ProofShape.inst_eq_subst, ProofShape.subst] using HE

/-- Supplying the oldest pending argument preserves every recursive layer.
The argument needs only ordinary typing. Intermediate observations substitute
structurally, and terminal family computations run before argument supply. -/
theorem NativeFamilyPiObservation.supply
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx ((A :: pending).reverse ++ Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A)
    (H : NativeFamilyPiObservation D Γ f u remaining (A :: pending) out) :
    NativeFamilyPiObservation D Γ (.app f x) u remaining (VExpr.instDomains pending x 0)
      (out.inst (proofErase Γ x) pending.length) := by
  induction remaining generalizing pending out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    have hctx₀ : OnCtx (pending.reverse ++ A :: Γ) (env.IsType univs) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
    have hB : env.HasType univs (pending.reverse ++ A :: Γ) B (.sort u) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using HB.body
    refine ⟨B.inst x pending.length, HB.apply hΓ hx, ?_⟩
    rw [proofErase_instN hctx₀ hx (pending_inst pending) hB]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      congrArg (fun b => b.inst (proofErase Γ x) pending.length) EB
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    have hctx₀ : OnCtx (pending.reverse ++ A :: Γ) (env.IsType univs) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
    have WI := pending_inst (Γ := Γ) (A := A) (x := x) pending
    have W : ContextSubstitution (proofEraseCtx (pending.reverse ++ A :: Γ))
        (proofEraseCtx ((VExpr.instDomains pending x 0).reverse ++ Γ))
        ((ProofShape.Subst.one (proofErase Γ x)).liftN pending.length) :=
      inst_interpretation hctx₀ WI hx
    have HT := HO.subst_lower
      (σ := (ProofShape.Subst.one (proofErase Γ x)).liftN pending.length)
      (Q := fun X Y => ∃ C B,
        env.IsType univs ((VExpr.instDomains pending x 0).reverse ++ Γ) C ∧
        env.IsType univs (C :: ((VExpr.instDomains pending x 0).reverse ++ Γ)) B ∧
        proofErase ((VExpr.instDomains pending x 0).reverse ++ Γ) C = X ∧
        proofErase (C :: ((VExpr.instDomains pending x 0).reverse ++ Γ)) B = Y ∧
        NativeFamilyPiObservation D Γ (.app f x) u remaining
          (VExpr.instDomains pending x 0 ++ [C]) Y)
      (by
        intro Δ hΔ EΔ
        exact W hΔ (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using EΔ))
      (fun X Y HP => by
        obtain ⟨C, B, hC, hB, EC, EB, HR⟩ := HP
        have hC₀ : env.IsType univs (pending.reverse ++ A :: Γ) C := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hC
        have hB₀ : env.IsType univs (C :: (pending.reverse ++ A :: Γ)) B := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hB
        have hΓC : OnCtx (C :: (pending.reverse ++ A :: Γ)) (env.IsType univs) := ⟨hctx₀, hC₀⟩
        have HI := ih (pending := pending ++ [C]) (out := Y)
          (by simpa using hΓC) (by simpa only [List.cons_append] using HR)
        refine ⟨C.inst x pending.length, B.inst x (pending.length + 1),
          hC₀.instN henv.ordered WI hx, hB₀.instN henv.ordered WI.succ hx, ?_, ?_, ?_⟩
        · rw [proofErase_instN hctx₀ hx WI hC₀.choose_spec]
          have EE : proofErase (pending.reverse ++ A :: Γ) C = X := by
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using EC
          rw [EE, ProofShape.inst_eq_subst]
        · rw [proofErase_instN hΓC hx WI.succ hB₀.choose_spec]
          have EE : proofErase (C :: (pending.reverse ++ A :: Γ)) B = Y := by
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using EB
          rw [EE, ProofShape.inst_eq_subst]
          rfl
        · simpa only [inst_domains_snoc, Nat.zero_add, List.length_append, List.length_singleton,
            ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HI)
      (fun _ _ _ h => h.elim)
    exact ⟨v, by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HT⟩

omit [Params] in
private theorem wrap_append (ps ds : List VExpr) (B : VExpr) :
    VExpr.wrapForalls (ps ++ ds) B = VExpr.wrapForalls ps (VExpr.wrapForalls ds B) := by
  induction ps with
  | nil => rfl
  | cons A ps ih => exact congrArg (VExpr.forallE A) ih

/-- A literal family telescope starts a recursive observation at any chosen
split between already pending and still unobserved binders. -/
theorem NativeFamilyPiObservation.of_history
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativeFamilyPiHistory D Γ f u (pending ++ ds) B) :
    NativeFamilyPiObservation D Γ f u ds.length pending
      (proofErase (pending.reverse ++ Γ) (VExpr.wrapForalls ds B)) := by
  induction ds generalizing pending with
  | nil => exact ⟨B, by simpa only [List.append_nil] using H, rfl⟩
  | cons A ds ih =>
    have hfull := (H.typed.etaOpen_wf henv.ordered hΓ).1
    have hT := wrap_type hfull ⟨u, H.body⟩
    rw [wrap_append] at hT
    obtain ⟨hctx, v, hPi⟩ := IsType.wrapForalls_inv henv hΓ hT
    obtain ⟨hA, hB⟩ := (show env.IsType univs (pending.reverse ++ Γ)
      (.forallE A (VExpr.wrapForalls ds B)) from ⟨v, hPi⟩).forallE_inv henv.ordered
    have E : proofErase (pending.reverse ++ Γ) (VExpr.wrapForalls (A :: ds) B) =
        .forallE (proofErase (pending.reverse ++ Γ) A)
          (proofErase (A :: (pending.reverse ++ Γ)) (VExpr.wrapForalls ds B)) :=
      if_neg (not_isProof_of_sort hctx hPi)
    have HI := ih (pending := pending ++ [A])
      (by simpa only [List.append_assoc, List.singleton_append] using H)
    refine ⟨v, ?_⟩
    rw [E]
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero, ← E] using
          ControlTyping.of_typed (t := .sort v) hctx hPi)
        (show ∃ C T, env.IsType univs (pending.reverse ++ Γ) C ∧
          env.IsType univs (C :: (pending.reverse ++ Γ)) T ∧
          proofErase (pending.reverse ++ Γ) C = proofErase (pending.reverse ++ Γ) A ∧
          proofErase (C :: (pending.reverse ++ Γ)) T =
            proofErase (A :: (pending.reverse ++ Γ)) (VExpr.wrapForalls ds B) ∧
          NativeFamilyPiObservation D Γ f u ds.length (pending ++ [C])
            (proofErase (A :: (pending.reverse ++ Γ)) (VExpr.wrapForalls ds B)) from
          ⟨A, VExpr.wrapForalls ds B, hA, hB, rfl, rfl, by simpa using HI⟩))

/-- An observation retains some complete native family header. This witness
is used for ordinary domain conversion at a selected application; it does not
normalize the selected output or replace its computation history. -/
theorem NativeFamilyPiObservation.witness
    (H : NativeFamilyPiObservation D Γ f u remaining pending out) :
    ∃ ds B, ds.length = remaining ∧ NativeFamilyPiHistory D Γ f u (pending ++ ds) B := by
  induction remaining generalizing pending out with
  | zero => obtain ⟨B, HB, _⟩ := H; exact ⟨[], B, rfl, by simpa using HB⟩
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    obtain ⟨X, Y, ⟨A, B, _, _, _, _, HB⟩, _⟩ := HO.readout
    obtain ⟨ds, C, hlen, HC⟩ := ih HB
    exact ⟨A :: ds, C, congrArg Nat.succ hlen,
      by simpa only [List.append_assoc, List.singleton_append] using HC⟩

/-- A selected literal Pi exposes precisely its recursive payload, including
the observation of the codomain that may still be opaque. -/
theorem NativeFamilyPiObservation.selected_pi
    (H : NativeFamilyPiObservation D Γ f u (remaining + 1) pending (.forallE X Y)) :
    ∃ A B, env.IsType univs (pending.reverse ++ Γ) A ∧
      env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
      proofErase (pending.reverse ++ Γ) A = X ∧
      proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
      NativeFamilyPiObservation D Γ f u remaining (pending ++ [A]) Y := by
  obtain ⟨_, HO⟩ := H
  exact HO.literal_pi_payload

/-- Once all arguments have been supplied, the retained terminal family
computation reaches the selected output directly. -/
theorem NativeFamilyPiObservation.finish
    (H : NativeFamilyPiObservation D Γ f u 0 [] out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) out := by
  obtain ⟨B, HB, EB⟩ := H
  exact EB ▸ HB.finish

end Lean4Lean.VEnv.Strengthening
