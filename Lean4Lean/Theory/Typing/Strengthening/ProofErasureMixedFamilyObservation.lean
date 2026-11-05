import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFamilyFields

/-! # Parameter observations retaining an ignored-field suffix

Parameter Pi payloads extend the retained family's pending telescope. Once all
parameter layers have been observed, field observations preserve that family
below their own binders. Both phases retain arbitrary opaque control frames.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation
open private PrefixPiCompute PrefixPiCompute.snoc wrap_type fixed_prefix_compute
  last_prefix_compute pending_inst inst_interpretation inst_domains_snoc wrap_append
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation
variable [Params] {D : PureObservation.Definitions}

/-- A parameter observation with `fieldCount` ignored fields after its final
parameter layer. `pending` lists observed parameters not yet supplied to the
family, while `remaining` counts parameter Pi layers still to be observed. -/
def MixedFamilyPiObservation (D : PureObservation.Definitions) (Γ : List VExpr)
    (f : VExpr) (u : VLevel) (fieldCount : Nat) : Nat → List VExpr → ProofShape → Prop
  | 0, pending, out => NativeFamilyFieldObservation D Γ f u pending fieldCount [] out
  | remaining + 1, pending, out => ∃ v,
      Obs (fun X Y => ∃ A B,
        env.IsType univs (pending.reverse ++ Γ) A ∧
        env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
        proofErase (pending.reverse ++ Γ) A = X ∧
        proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
        MixedFamilyPiObservation D Γ f u fieldCount remaining (pending ++ [A]) Y)
        0 (proofEraseCtx (pending.reverse ++ Γ)) (fun _ _ _ => False) out (.sort v) .pi

/-- A directed computation of the pending telescope transports the recursive
observation. Context conversion changes ordinary control typings, while each
terminal family advances through the same directed prefix history. -/
theorem MixedFamilyPiObservation.convert_pending
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hctx' : OnCtx (ds'.reverse ++ Γ) (env.IsType univs))
    (hlen : ds.length = ds'.length)
    (HC : IsDefEqCtx env univs [] (ds.reverse ++ Γ) (ds'.reverse ++ Γ))
    (R : ∀ B v, env.HasType univs (ds.reverse ++ Γ) B (.sort v) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ds B)) (proofErase Γ (VExpr.wrapForalls ds' B)))
    (H : MixedFamilyPiObservation D Γ f u fieldCount remaining ds out) :
    MixedFamilyPiObservation D Γ f u fieldCount remaining ds' out := by
  induction remaining generalizing ds ds' out with
  | zero =>
    exact NativeFamilyFieldObservation.convert_parameters (ds := []) (ds' := [])
      heq hs hΓ hctx hctx' hctx hctx' hlen rfl HC HC R H
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
        MixedFamilyPiObservation D Γ f u fieldCount remaining (ds' ++ [A]) Y) W (fun X Y HP => by
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
theorem MixedFamilyPiObservation.realize
    (hctx : OnCtx (pending.reverse ++ Γ) (env.IsType univs))
    (H : MixedFamilyPiObservation D Γ f u fieldCount remaining pending out) :
    ∃ B v, env.HasType univs (pending.reverse ++ Γ) B (.sort v) ∧
      proofErase (pending.reverse ++ Γ) B = out := by
  cases remaining with
  | zero => exact NativeFamilyFieldObservation.realize (pending := []) hctx H
  | succ n =>
    obtain ⟨v, HO⟩ := H
    obtain ⟨Δ, B, hΔ, EΔ, HB, EB⟩ := HO.typing
    have HC := proofEraseCtx_defeq hΔ hctx EΔ
    have EC := proofErase_defeqCtx hΔ HC HB
    exact ⟨B, v, HB.defeqDFC henv HC, EC.symm.trans EB⟩

/-- Arbitrary full-union computation preserves all recursive Pi layers.
Payload computation descends temporary controls, advances the inner
observation, and transports its pending domain along the selected domain
history. No hidden residual is beta-normalized. -/
theorem MixedFamilyPiObservation.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (pending.reverse ++ Γ) (env.IsType univs))
    (H : MixedFamilyPiObservation D Γ f u fieldCount remaining pending source)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (pending.reverse ++ Γ)) source out) :
    MixedFamilyPiObservation D Γ f u fieldCount remaining pending out := by
  induction remaining generalizing pending source out with
  | zero => exact NativeFamilyFieldObservation.compute (pending := []) heq hs hΓ hctx H R
  | succ remaining ih =>
    obtain ⟨e, v, he, Ee⟩ := H.realize hctx
    obtain ⟨q, HO⟩ := H
    have HP : PiOriginComponentClosure (ErasedStaticStructureEtaExpansionUnion D)
        (pending.reverse ++ Γ)
        (fun X Y => ∃ A B, env.IsType univs (pending.reverse ++ Γ) A ∧
          env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
          proofErase (pending.reverse ++ Γ) A = X ∧
          proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
          MixedFamilyPiObservation D Γ f u fieldCount remaining (pending ++ [A]) Y) := by
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

/-- Supplying the oldest pending parameter preserves both observation phases.
The argument needs only ordinary typing. Parameter and field controls substitute
structurally, and retained family computations run before argument supply. -/
theorem MixedFamilyPiObservation.supply
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx ((A :: pending).reverse ++ Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A)
    (H : MixedFamilyPiObservation D Γ f u fieldCount remaining (A :: pending) out) :
    MixedFamilyPiObservation D Γ (.app f x) u fieldCount remaining (VExpr.instDomains pending x 0)
      (out.inst (proofErase Γ x) pending.length) := by
  induction remaining generalizing pending out with
  | zero => exact NativeFamilyFieldObservation.supply_parameter (ds := []) hΓ hctx hx H
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
        MixedFamilyPiObservation D Γ (.app f x) u fieldCount remaining
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

/-- An observation retains some complete native family header. This witness
is used for ordinary domain conversion at a selected application; it does not
normalize the selected output or replace its computation history. -/
theorem MixedFamilyPiObservation.witness
    (H : MixedFamilyPiObservation D Γ f u fieldCount remaining pending out) :
    ∃ ds B, ds.length = remaining ∧ NativeFamilyPiHistory D Γ f u (pending ++ ds) B := by
  induction remaining generalizing pending out with
  | zero =>
    obtain ⟨B, HB⟩ := NativeFamilyFieldObservation.witness H
    exact ⟨[], B, rfl, by simpa using HB⟩
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    obtain ⟨X, Y, ⟨A, B, _, _, _, _, HB⟩, _⟩ := HO.readout
    obtain ⟨ds, C, hlen, HC⟩ := ih HB
    exact ⟨A :: ds, C, congrArg Nat.succ hlen,
      by simpa only [List.append_assoc, List.singleton_append] using HC⟩

/-- A selected literal Pi exposes precisely its recursive payload, including
the observation of the codomain that may still be opaque. -/
theorem MixedFamilyPiObservation.selected_pi
    (H : MixedFamilyPiObservation D Γ f u fieldCount (remaining + 1) pending (.forallE X Y)) :
    ∃ A B, env.IsType univs (pending.reverse ++ Γ) A ∧
      env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
      proofErase (pending.reverse ++ Γ) A = X ∧
      proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
      MixedFamilyPiObservation D Γ f u fieldCount remaining (pending ++ [A]) Y := by
  obtain ⟨_, HO⟩ := H
  exact HO.literal_pi_payload

/-- Supplying every parameter exposes the exact remaining field observation.
The original applied family becomes its lower result origin. -/
theorem MixedFamilyPiObservation.finish_parameters
    (H : MixedFamilyPiObservation D Γ f u fieldCount 0 [] out) :
    IgnoredFieldPiObservation D Γ f u fieldCount [] out :=
  NativeFamilyFieldObservation.finish_parameters H

/-- A native parameter family and a well-formed dependent field suffix start
a mixed observation. The result ignores only the fields; it may depend on
every parameter. No literal residual telescope is required after this point. -/
theorem MixedFamilyPiObservation.of_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HF : NativeFamilyPiHistory D Γ f u (pending ++ ds) B)
    (hctx : OnCtx (fields.reverse ++ ((pending ++ ds).reverse ++ Γ)) (env.IsType univs)) :
    MixedFamilyPiObservation D Γ f u fields.length ds.length pending
      (proofErase (pending.reverse ++ Γ)
        (VExpr.wrapForalls ds (VExpr.wrapForalls fields (B.liftN fields.length)))) := by
  induction ds generalizing pending with
  | nil =>
    have HF' : NativeFamilyPiHistory D Γ f u pending B := by simpa using HF
    simpa only [MixedFamilyPiObservation, List.length_nil, VExpr.wrapForalls, List.foldr_nil,
      List.reverse_nil, List.nil_append, Nat.zero_add] using
      NativeFamilyFieldObservation.of_history (ds := []) heq hs hΓ HF' (by simpa using hctx)
  | cons A ds ih =>
    have hps := (HF.typed.etaOpen_wf henv.ordered hΓ).1
    have W : Ctx.LiftN fields.length 0 ((pending ++ A :: ds).reverse ++ Γ)
        (fields.reverse ++ ((pending ++ A :: ds).reverse ++ Γ)) :=
      Ctx.LiftN.zero fields.reverse (by simp)
    have hfields := wrap_type hctx ⟨u, HF.body.weakN henv W⟩
    have hT := wrap_type hps hfields
    rw [wrap_append] at hT
    obtain ⟨hpending, v, hPi⟩ := IsType.wrapForalls_inv henv hΓ hT
    obtain ⟨hA, hB⟩ := (show env.IsType univs (pending.reverse ++ Γ)
      (.forallE A (VExpr.wrapForalls ds (VExpr.wrapForalls fields (B.liftN fields.length))))
      from ⟨v, hPi⟩).forallE_inv henv.ordered
    have E : proofErase (pending.reverse ++ Γ)
        (VExpr.wrapForalls (A :: ds) (VExpr.wrapForalls fields (B.liftN fields.length))) =
        .forallE (proofErase (pending.reverse ++ Γ) A)
          (proofErase (A :: (pending.reverse ++ Γ))
            (VExpr.wrapForalls ds (VExpr.wrapForalls fields (B.liftN fields.length)))) :=
      if_neg (not_isProof_of_sort hpending hPi)
    have HI := ih (pending := pending ++ [A])
      (by simpa only [List.append_assoc, List.singleton_append] using HF)
      (by simpa only [List.append_assoc, List.singleton_append] using hctx)
    refine ⟨v, ?_⟩
    rw [E]
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero, ← E] using
          ControlTyping.of_typed (t := .sort v) hpending hPi)
        (show ∃ C T, env.IsType univs (pending.reverse ++ Γ) C ∧
          env.IsType univs (C :: (pending.reverse ++ Γ)) T ∧
          proofErase (pending.reverse ++ Γ) C = proofErase (pending.reverse ++ Γ) A ∧
          proofErase (C :: (pending.reverse ++ Γ)) T =
            proofErase (A :: (pending.reverse ++ Γ))
              (VExpr.wrapForalls ds (VExpr.wrapForalls fields (B.liftN fields.length))) ∧
          MixedFamilyPiObservation D Γ f u fields.length ds.length (pending ++ [C])
            (proofErase (A :: (pending.reverse ++ Γ))
              (VExpr.wrapForalls ds (VExpr.wrapForalls fields (B.liftN fields.length)))) from
          ⟨A, _, hA, hB, rfl, rfl, by simpa using HI⟩))

end Lean4Lean.VEnv.Strengthening
