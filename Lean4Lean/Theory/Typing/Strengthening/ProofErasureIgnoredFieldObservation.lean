import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativePiSupply

/-! # Native type histories through ignored field telescopes

Terminal payloads retain a lower-context computation, lifted past all pending
fields. Certificate descent preserves that independence under computation;
supplying any ordinarily typed field leaves the lower history unchanged.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation
open private pending_inst inst_interpretation inst_domains_snoc wrap_type wrap_append
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation
open private raw_liftN_subst_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiHistoryObservation
variable [Params] {D : PureObservation.Definitions}

/-- Recursive Pi observations whose terminal output computes from a fixed type
below every pending field. This stores independence as a lower computation,
not merely as ordinary equality or absence of free variables. -/
def IgnoredFieldPiObservation (D : PureObservation.Definitions) (Γ : List VExpr)
    (origin : VExpr) (u : VLevel) : Nat → List VExpr → ProofShape → Prop
  | 0, pending, out => ∃ B, env.HasType univs Γ B (.sort u) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ origin) (proofErase Γ B) ∧
      (proofErase Γ B).liftN pending.length = out
  | remaining + 1, pending, out => ∃ v,
      Obs (fun X Y => ∃ A B,
        env.IsType univs (pending.reverse ++ Γ) A ∧
        env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
        proofErase (pending.reverse ++ Γ) A = X ∧
        proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
        IgnoredFieldPiObservation D Γ origin u remaining (pending ++ [A]) Y)
        0 (proofEraseCtx (pending.reverse ++ Γ)) (fun _ _ _ => False) out (.sort v) .pi

/-- Pending-domain conversion changes only ordinary observation typings.
The retained lower computation depends on neither the domains nor their values. -/
theorem IgnoredFieldPiObservation.convert_pending
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hctx' : OnCtx (ds'.reverse ++ Γ) (env.IsType univs))
    (hlen : ds.length = ds'.length)
    (HC : IsDefEqCtx env univs [] (ds.reverse ++ Γ) (ds'.reverse ++ Γ))
    (H : IgnoredFieldPiObservation D Γ f u remaining ds out) :
    IgnoredFieldPiObservation D Γ f u remaining ds' out := by
  induction remaining generalizing ds ds' out with
  | zero =>
    obtain ⟨B, HB, RB, EB⟩ := H
    exact ⟨B, HB, RB, by simpa only [← hlen] using EB⟩
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
        IgnoredFieldPiObservation D Γ f u remaining (ds' ++ [A]) Y) W (fun X Y HP => by
        obtain ⟨A, B, hA, hB, EA, EB, HR⟩ := HP
        have HC' := IsDefEqCtx.succ HC hA.choose_spec
        have hΓA : OnCtx (A :: (ds.reverse ++ Γ)) (env.IsType univs) := ⟨hctx, hA⟩
        have hΓA' : OnCtx (A :: (ds'.reverse ++ Γ)) (env.IsType univs) :=
          ⟨hctx', hA.defeqDFC henv HC⟩
        have hlen' : (ds ++ [A]).length = (ds' ++ [A]).length := by simp [hlen]
        have HI := ih (ds := ds ++ [A]) (ds' := ds' ++ [A])
          (by simpa using hΓA) (by simpa using hΓA') hlen' (by simpa using HC') HR
        have EAA := proofErase_defeqCtx hctx HC hA.choose_spec
        have EBB := proofErase_defeqCtx hΓA HC' hB.choose_spec
        refine ⟨A, B, hA.defeqDFC henv HC, hB.defeqDFC henv HC', ?_, ?_, ?_⟩
        · simpa only [ProofShape.subst_id] using EAA.symm.trans EA
        · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id] using EBB.symm.trans EB
        · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id] using HI)
      (fun _ _ _ h => h.elim)
    exact ⟨v, by simpa only [ProofShape.Subst.liftN, ProofShape.subst_id] using HT⟩

/-- Every observation layer retains an ordinary type representative in the
actual pending context, including opaque control-frame outputs. -/
theorem IgnoredFieldPiObservation.realize
    (hctx : OnCtx (pending.reverse ++ Γ) (env.IsType univs))
    (H : IgnoredFieldPiObservation D Γ f u remaining pending out) :
    ∃ B v, env.HasType univs (pending.reverse ++ Γ) B (.sort v) ∧
      proofErase (pending.reverse ++ Γ) B = out := by
  cases remaining with
  | zero =>
    obtain ⟨B, HB, _, EB⟩ := H
    have hΓ : OnCtx Γ (env.IsType univs) := OnCtx.of_append hctx
    have W : Ctx.LiftN pending.length 0 Γ (pending.reverse ++ Γ) :=
      Ctx.LiftN.zero pending.reverse (by simp)
    exact ⟨B.liftN pending.length, u, HB.weakN henv W,
      (proofErase_liftN hΓ hctx W HB).trans EB⟩
  | succ n =>
    obtain ⟨v, HO⟩ := H
    obtain ⟨Δ, B, hΔ, EΔ, HB, EB⟩ := HO.typing
    have HC := proofEraseCtx_defeq hΔ hctx EΔ
    have EC := proofErase_defeqCtx hΔ HC HB
    exact ⟨B, v, HB.defeqDFC henv HC, EC.symm.trans EB⟩

/-- Full-union computation preserves lower terminal histories. At a terminal
layer, certificate descent removes every pending field binder; at a Pi layer,
the inner observation computes and follows the selected domain conversion. -/
theorem IgnoredFieldPiObservation.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (pending.reverse ++ Γ) (env.IsType univs))
    (H : IgnoredFieldPiObservation D Γ f u remaining pending source)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (pending.reverse ++ Γ)) source out) :
    IgnoredFieldPiObservation D Γ f u remaining pending out := by
  induction remaining generalizing pending source out with
  | zero =>
    obtain ⟨B, HB, RB, EB⟩ := H
    rw [← EB] at R
    have W : Ctx.LiftN pending.length 0 Γ (pending.reverse ++ Γ) :=
      Ctx.LiftN.zero pending.reverse (by simp)
    obtain ⟨B', HE, RC, EC⟩ := proofErase_scoped_compute_certificate_descend
      (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
      hΓ hctx W HB rfl R
    exact ⟨B', HE.hasType.2, RB.trans RC, EC⟩
  | succ remaining ih =>
    obtain ⟨e, v, he, Ee⟩ := H.realize hctx
    obtain ⟨q, HO⟩ := H
    have HP : PiOriginComponentClosure (ErasedStaticStructureEtaExpansionUnion D)
        (pending.reverse ++ Γ)
        (fun X Y => ∃ A B, env.IsType univs (pending.reverse ++ Γ) A ∧
          env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
          proofErase (pending.reverse ++ Γ) A = X ∧
          proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
          IgnoredFieldPiObservation D Γ f u remaining (pending ++ [A]) Y) := by
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
      have HT := HI.convert_pending (ds' := pending ++ [A₁]) (by simpa using hΓA) (by simpa using hΓA₁)
        (by simp) (by simpa using HC)
      exact ⟨X₁, Y₁, ⟨A₁, B₁, ⟨a, HA₁.hasType.2⟩, ⟨b, hB₁⟩, EA₁, EB₁, HT⟩, EX, EY⟩
    have HT := proofErase_scoped_compute_controlObservation
      (erased_static_structure_eta_expansion_union_descent heq hs)
      (erased_static_structure_union_controlObservation heq hs) HP R hctx (Ctx.LiftN.zero [])
      he rfl Ee (fun _ _ _ h => h.elim) HO
    exact ⟨q, HT⟩

omit [Params] in
private theorem ignored_field_lift_inst (b x : ProofShape) (n : Nat) :
    (b.liftN (n + 1)).inst x n = b.liftN n := by
  rw [ProofShape.inst_eq_subst, Nat.add_comm n 1, ← ProofShape.liftN_add,
    raw_liftN_subst_liftN, ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]

/-- Supplying the oldest pending field preserves all remaining observations.
The terminal output is lifted from below the fields, so instantiation removes
one unused binder and leaves its lower computation unchanged. -/
theorem IgnoredFieldPiObservation.supply
    (_hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx ((A :: pending).reverse ++ Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A)
    (H : IgnoredFieldPiObservation D Γ f u remaining (A :: pending) out) :
    IgnoredFieldPiObservation D Γ f u remaining (VExpr.instDomains pending x 0)
      (out.inst (proofErase Γ x) pending.length) := by
  induction remaining generalizing pending out with
  | zero =>
    obtain ⟨B, HB, RB, EB⟩ := H
    refine ⟨B, HB, RB, ?_⟩
    rw [← EB, VExpr.instDomains_length]
    exact (ignored_field_lift_inst (proofErase Γ B) (proofErase Γ x) pending.length).symm
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
        IgnoredFieldPiObservation D Γ f u remaining
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

/-- A selected literal Pi exposes its exact codomain observation, preserving
the selected domain and every remaining opaque field layer. -/
theorem IgnoredFieldPiObservation.selected_pi
    (H : IgnoredFieldPiObservation D Γ f u (remaining + 1) pending (.forallE X Y)) :
    ∃ A B, env.IsType univs (pending.reverse ++ Γ) A ∧
      env.IsType univs (A :: (pending.reverse ++ Γ)) B ∧
      proofErase (pending.reverse ++ Γ) A = X ∧
      proofErase (A :: (pending.reverse ++ Γ)) B = Y ∧
      IgnoredFieldPiObservation D Γ f u remaining (pending ++ [A]) Y := by
  obtain ⟨_, HO⟩ := H
  exact HO.literal_pi_payload

/-- Once all fields have been supplied, their selected result computes
from the original lower type directly. -/
theorem IgnoredFieldPiObservation.finish
    (H : IgnoredFieldPiObservation D Γ f u 0 [] out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) out := by
  obtain ⟨B, _, RB, EB⟩ := H
  simp only [List.length_nil, ProofShape.liftN_zero] at EB
  exact EB ▸ RB

/-- Any well-formed dependent field telescope whose result ignores all its
fields starts an observation with a reflexive history below those fields. -/
theorem IgnoredFieldPiObservation.of_telescope
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : env.HasType univs Γ g (.sort u))
    (hctx : OnCtx ((pending ++ fields).reverse ++ Γ) (env.IsType univs)) :
    IgnoredFieldPiObservation D Γ g u fields.length pending
      (proofErase (pending.reverse ++ Γ)
        (VExpr.wrapForalls fields (g.liftN (pending.length + fields.length)))) := by
  induction fields generalizing pending with
  | nil =>
    have hctx' : OnCtx (pending.reverse ++ Γ) (env.IsType univs) := by simpa using hctx
    have W : Ctx.LiftN pending.length 0 Γ (pending.reverse ++ Γ) :=
      Ctx.LiftN.zero pending.reverse (by simp)
    refine ⟨g, hg, .refl, ?_⟩
    simpa only [List.length_nil, Nat.add_zero, VExpr.wrapForalls, List.foldr_nil] using
      (proofErase_liftN hΓ hctx' W hg).symm
  | cons A fields ih =>
    have W : Ctx.LiftN (pending ++ A :: fields).length 0 Γ
        ((pending ++ A :: fields).reverse ++ Γ) :=
      Ctx.LiftN.zero (pending ++ A :: fields).reverse (by simp; omega)
    have hbody := hg.weakN henv W
    have hT := wrap_type hctx ⟨u, hbody⟩
    rw [wrap_append] at hT
    obtain ⟨hpending, v, hPi⟩ := IsType.wrapForalls_inv henv hΓ hT
    have hPi' : env.HasType univs (pending.reverse ++ Γ)
        (.forallE A (VExpr.wrapForalls fields (g.liftN (pending.length + (A :: fields).length))))
        (.sort v) := by simpa only [List.length_append, VExpr.wrapForalls, List.foldr_cons] using hPi
    obtain ⟨hA, hB⟩ := (show env.IsType univs (pending.reverse ++ Γ)
      (.forallE A (VExpr.wrapForalls fields (g.liftN (pending.length + (A :: fields).length))))
      from ⟨v, hPi'⟩).forallE_inv henv.ordered
    have HI := ih (pending := pending ++ [A])
      (by simpa only [List.append_assoc, List.singleton_append] using hctx)
    have E : proofErase (pending.reverse ++ Γ)
        (VExpr.wrapForalls (A :: fields) (g.liftN (pending.length + (A :: fields).length))) =
        .forallE (proofErase (pending.reverse ++ Γ) A)
          (proofErase (A :: (pending.reverse ++ Γ))
            (VExpr.wrapForalls fields (g.liftN (pending.length + (A :: fields).length)))) :=
      if_neg (not_isProof_of_sort hpending hPi')
    have HT : ControlTyping (proofEraseCtx (pending.reverse ++ Γ))
        (proofErase (pending.reverse ++ Γ)
          (VExpr.wrapForalls (A :: fields) (g.liftN (pending.length + (A :: fields).length))))
        (.sort v) := by
      apply ControlTyping.of_typed
      · exact hpending
      · change env.HasType univs (pending.reverse ++ Γ)
          (.forallE A (VExpr.wrapForalls fields (g.liftN (pending.length + (A :: fields).length)))) (.sort v)
        exact hPi'
    rw [E] at HT
    refine ⟨v, ?_⟩
    rw [E]
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero] using HT)
        (show ∃ C T, env.IsType univs (pending.reverse ++ Γ) C ∧
          env.IsType univs (C :: (pending.reverse ++ Γ)) T ∧
          proofErase (pending.reverse ++ Γ) C = proofErase (pending.reverse ++ Γ) A ∧
          proofErase (C :: (pending.reverse ++ Γ)) T =
            proofErase (A :: (pending.reverse ++ Γ))
              (VExpr.wrapForalls fields (g.liftN (pending.length + (A :: fields).length))) ∧
          IgnoredFieldPiObservation D Γ g u fields.length (pending ++ [C])
            (proofErase (A :: (pending.reverse ++ Γ))
              (VExpr.wrapForalls fields (g.liftN (pending.length + (A :: fields).length)))) from
          ⟨A, _, hA, hB, rfl, rfl, by simpa [Nat.add_assoc, Nat.add_comm 1] using HI⟩))

end Lean4Lean.VEnv.Strengthening
