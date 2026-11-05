import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredFieldSupply

/-! # Native families retained below ignored field telescopes

Terminal payloads retain the native parameter family below all pending fields.
Field computations descend to the parameter context and advance the retained
family before any parameter is supplied.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation
open private pending_inst inst_interpretation inst_domains_snoc wrap_type wrap_append fixed_prefix_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation
open private raw_liftN_subst_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiHistoryObservation
variable [Params] {D : PureObservation.Definitions}

/-- Recursive field observations with a retained native parameter family.
Each terminal output is the family's current body lifted past the pending
fields; its family path and exact native parameter header remain available. -/
def NativeFamilyFieldObservation (D : PureObservation.Definitions) (Γ : List VExpr)
    (origin : VExpr) (u : VLevel) (ps : List VExpr) : Nat → List VExpr → ProofShape → Prop
  | 0, pending, out => ∃ B, NativeFamilyPiHistory D Γ origin u ps B ∧
      (proofErase (ps.reverse ++ Γ) B).liftN pending.length = out
  | remaining + 1, pending, out => ∃ v,
      Obs (fun X Y => ∃ A B,
        env.IsType univs (pending.reverse ++ (ps.reverse ++ Γ)) A ∧
        env.IsType univs (A :: (pending.reverse ++ (ps.reverse ++ Γ))) B ∧
        proofErase (pending.reverse ++ (ps.reverse ++ Γ)) A = X ∧
        proofErase (A :: (pending.reverse ++ (ps.reverse ++ Γ))) B = Y ∧
        NativeFamilyFieldObservation D Γ origin u ps remaining (pending ++ [A]) Y)
        0 (proofEraseCtx (pending.reverse ++ (ps.reverse ++ Γ))) (fun _ _ _ => False) out (.sort v) .pi

/-- Field-domain conversion changes only ordinary observation typings.
The retained family below those fields and its parameter header stay fixed. -/
theorem NativeFamilyFieldObservation.convert_pending
    (hctx : OnCtx (ds.reverse ++ (ps.reverse ++ Γ)) (env.IsType univs))
    (hctx' : OnCtx (ds'.reverse ++ (ps.reverse ++ Γ)) (env.IsType univs))
    (hlen : ds.length = ds'.length)
    (HC : IsDefEqCtx env univs [] (ds.reverse ++ (ps.reverse ++ Γ)) (ds'.reverse ++ (ps.reverse ++ Γ)))
    (H : NativeFamilyFieldObservation D Γ f u ps remaining ds out) :
    NativeFamilyFieldObservation D Γ f u ps remaining ds' out := by
  induction remaining generalizing ds ds' out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    exact ⟨B, HB, by simpa only [← hlen] using EB⟩
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    have W : ContextSubstitution (proofEraseCtx (ds.reverse ++ (ps.reverse ++ Γ)))
        (proofEraseCtx (ds'.reverse ++ (ps.reverse ++ Γ))) ProofShape.Subst.id :=
      ContextSubstitution.of_defeqCtx (by trivial) HC
    have HT := HO.subst_lower (σ := ProofShape.Subst.id)
      (Q := fun X Y => ∃ A B, env.IsType univs (ds'.reverse ++ (ps.reverse ++ Γ)) A ∧
        env.IsType univs (A :: (ds'.reverse ++ (ps.reverse ++ Γ))) B ∧
        proofErase (ds'.reverse ++ (ps.reverse ++ Γ)) A = X ∧
        proofErase (A :: (ds'.reverse ++ (ps.reverse ++ Γ))) B = Y ∧
        NativeFamilyFieldObservation D Γ f u ps remaining (ds' ++ [A]) Y) W (fun X Y HP => by
        obtain ⟨A, B, hA, hB, EA, EB, HR⟩ := HP
        have HC' := IsDefEqCtx.succ HC hA.choose_spec
        have hΓA : OnCtx (A :: (ds.reverse ++ (ps.reverse ++ Γ))) (env.IsType univs) := ⟨hctx, hA⟩
        have hΓA' : OnCtx (A :: (ds'.reverse ++ (ps.reverse ++ Γ))) (env.IsType univs) :=
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
theorem NativeFamilyFieldObservation.realize
    (hctx : OnCtx (pending.reverse ++ (ps.reverse ++ Γ)) (env.IsType univs))
    (H : NativeFamilyFieldObservation D Γ f u ps remaining pending out) :
    ∃ B v, env.HasType univs (pending.reverse ++ (ps.reverse ++ Γ)) B (.sort v) ∧
      proofErase (pending.reverse ++ (ps.reverse ++ Γ)) B = out := by
  cases remaining with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    have hps : OnCtx (ps.reverse ++ Γ) (env.IsType univs) := OnCtx.of_append hctx
    have W : Ctx.LiftN pending.length 0 (ps.reverse ++ Γ) (pending.reverse ++ (ps.reverse ++ Γ)) :=
      Ctx.LiftN.zero pending.reverse (by simp)
    exact ⟨B.liftN pending.length, u, HB.body.weakN henv W,
      (proofErase_liftN hps hctx W HB.body).trans EB⟩
  | succ n =>
    obtain ⟨v, HO⟩ := H
    obtain ⟨Δ, B, hΔ, EΔ, HB, EB⟩ := HO.typing
    have HC := proofEraseCtx_defeq hΔ hctx EΔ
    have EC := proofErase_defeqCtx hΔ HC HB
    exact ⟨B, v, HB.defeqDFC henv HC, EC.symm.trans EB⟩

/-- Full-union computation preserves the retained family. At a terminal layer,
certificate descent removes every field binder, and the resulting body path
advances the parameter family. Pi layers follow their selected domain histories. -/
theorem NativeFamilyFieldObservation.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (pending.reverse ++ (ps.reverse ++ Γ)) (env.IsType univs))
    (H : NativeFamilyFieldObservation D Γ f u ps remaining pending source)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (pending.reverse ++ (ps.reverse ++ Γ))) source out) :
    NativeFamilyFieldObservation D Γ f u ps remaining pending out := by
  induction remaining generalizing pending source out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    rw [← EB] at R
    have W : Ctx.LiftN pending.length 0 (ps.reverse ++ Γ) (pending.reverse ++ (ps.reverse ++ Γ)) :=
      Ctx.LiftN.zero pending.reverse (by simp)
    obtain ⟨B', HE, RC, EC⟩ := proofErase_scoped_compute_certificate_descend
      (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
      (OnCtx.of_append hctx) hctx W HB.body rfl R
    have hps : OnCtx (ps.reverse ++ Γ) (env.IsType univs) := OnCtx.of_append hctx
    have RP := fixed_prefix_compute hps ⟨u, HB.body⟩ ⟨u, HE.hasType.2⟩ RC
    exact ⟨B', HB.convert heq hs hΓ rfl (wrap_type hps ⟨u, HE.hasType.2⟩) RP, EC⟩
  | succ remaining ih =>
    obtain ⟨e, v, he, Ee⟩ := H.realize hctx
    obtain ⟨q, HO⟩ := H
    have HP : PiOriginComponentClosure (ErasedStaticStructureEtaExpansionUnion D)
        (pending.reverse ++ (ps.reverse ++ Γ))
        (fun X Y => ∃ A B, env.IsType univs (pending.reverse ++ (ps.reverse ++ Γ)) A ∧
          env.IsType univs (A :: (pending.reverse ++ (ps.reverse ++ Γ))) B ∧
          proofErase (pending.reverse ++ (ps.reverse ++ Γ)) A = X ∧
          proofErase (A :: (pending.reverse ++ (ps.reverse ++ Γ))) B = Y ∧
          NativeFamilyFieldObservation D Γ f u ps remaining (pending ++ [A]) Y) := by
      intro Δ n X Y X' Y' hΔ W HX RX RY
      obtain ⟨A, B, ⟨a, hA⟩, ⟨b, hB⟩, rfl, rfl, HB⟩ := HX
      obtain ⟨X₁, Y₁, HX₁, EX, EY⟩ := static_structure_piOrigin_componentClosure
        heq hs hctx hΔ W (StaticStructurePiOrigin.refl (D := D) hA hB) RX RY
      obtain ⟨A₁, B₁, HA₁, hB₁, EA₁, EB₁, RA₁, RB₁⟩ := HX₁
      have hΓA : OnCtx (A :: (pending.reverse ++ (ps.reverse ++ Γ))) (env.IsType univs) := ⟨hctx, a, hA⟩
      have hΓA₁ : OnCtx (A₁ :: (pending.reverse ++ (ps.reverse ++ Γ))) (env.IsType univs) :=
        ⟨hctx, a, HA₁.hasType.2⟩
      have HI := ih (pending := pending ++ [A]) (by simpa using hΓA) HB
        (by simpa using RB₁)
      have HC : IsDefEqCtx env univs [] (A :: (pending.reverse ++ (ps.reverse ++ Γ)))
          (A₁ :: (pending.reverse ++ (ps.reverse ++ Γ))) := .succ (.refl hctx) HA₁
      have HT := HI.convert_pending (ds' := pending ++ [A₁]) (by simpa using hΓA) (by simpa using hΓA₁)
        (by simp) (by simpa using HC)
      exact ⟨X₁, Y₁, ⟨A₁, B₁, ⟨a, HA₁.hasType.2⟩, ⟨b, hB₁⟩, EA₁, EB₁, HT⟩, EX, EY⟩
    have HT := proofErase_scoped_compute_controlObservation
      (erased_static_structure_eta_expansion_union_descent heq hs)
      (erased_static_structure_union_controlObservation heq hs) HP R hctx (Ctx.LiftN.zero [])
      he rfl Ee (fun _ _ _ h => h.elim) HO
    exact ⟨q, HT⟩


/-- Directed parameter-domain conversion transports the retained native family
at every terminal field payload. Field domains can also change by ordinary
context conversion; their lengths, but not their computations, are retained. -/
theorem NativeFamilyFieldObservation.convert_parameters
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hps : OnCtx (ps.reverse ++ Γ) (env.IsType univs))
    (hps' : OnCtx (ps'.reverse ++ Γ) (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ (ps.reverse ++ Γ)) (env.IsType univs))
    (hctx' : OnCtx (ds'.reverse ++ (ps'.reverse ++ Γ)) (env.IsType univs))
    (hp : ps.length = ps'.length) (hd : ds.length = ds'.length)
    (HP : IsDefEqCtx env univs [] (ps.reverse ++ Γ) (ps'.reverse ++ Γ))
    (HC : IsDefEqCtx env univs [] (ds.reverse ++ (ps.reverse ++ Γ))
      (ds'.reverse ++ (ps'.reverse ++ Γ)))
    (R : ∀ B v, env.HasType univs (ps.reverse ++ Γ) B (.sort v) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ps B)) (proofErase Γ (VExpr.wrapForalls ps' B)))
    (H : NativeFamilyFieldObservation D Γ f u ps remaining ds out) :
    NativeFamilyFieldObservation D Γ f u ps' remaining ds' out := by
  induction remaining generalizing ds ds' out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    have hB' := HB.body.defeqDFC henv HP
    have E := proofErase_defeqCtx hps HP HB.body
    exact ⟨B, HB.convert heq hs hΓ hp (wrap_type hps' ⟨u, hB'⟩)
      (R B u HB.body), by simpa only [← E, ← hd] using EB⟩
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    have W : ContextSubstitution (proofEraseCtx (ds.reverse ++ (ps.reverse ++ Γ)))
        (proofEraseCtx (ds'.reverse ++ (ps'.reverse ++ Γ))) ProofShape.Subst.id :=
      ContextSubstitution.of_defeqCtx (by trivial) HC
    have HT := HO.subst_lower (σ := ProofShape.Subst.id)
      (Q := fun X Y => ∃ A B, env.IsType univs (ds'.reverse ++ (ps'.reverse ++ Γ)) A ∧
        env.IsType univs (A :: (ds'.reverse ++ (ps'.reverse ++ Γ))) B ∧
        proofErase (ds'.reverse ++ (ps'.reverse ++ Γ)) A = X ∧
        proofErase (A :: (ds'.reverse ++ (ps'.reverse ++ Γ))) B = Y ∧
        NativeFamilyFieldObservation D Γ f u ps' remaining (ds' ++ [A]) Y) W (fun X Y HXY => by
        obtain ⟨A, B, hA, hB, EA, EB, HR⟩ := HXY
        have HC' := IsDefEqCtx.succ HC hA.choose_spec
        have hΓA : OnCtx (A :: (ds.reverse ++ (ps.reverse ++ Γ))) (env.IsType univs) := ⟨hctx, hA⟩
        have hΓA' : OnCtx (A :: (ds'.reverse ++ (ps'.reverse ++ Γ))) (env.IsType univs) :=
          ⟨hctx', hA.defeqDFC henv HC⟩
        have HI := ih (ds := ds ++ [A]) (ds' := ds' ++ [A])
          (by simpa using hΓA) (by simpa using hΓA') (by simp [hd]) (by simpa using HC') HR
        have EAA := proofErase_defeqCtx hctx HC hA.choose_spec
        have EBB := proofErase_defeqCtx hΓA HC' hB.choose_spec
        refine ⟨A, B, hA.defeqDFC henv HC, hB.defeqDFC henv HC', ?_, ?_, ?_⟩
        · simpa only [ProofShape.subst_id] using EAA.symm.trans EA
        · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id] using EBB.symm.trans EB
        · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id] using HI)
      (fun _ _ _ h => h.elim)
    exact ⟨v, by simpa only [ProofShape.Subst.liftN, ProofShape.subst_id] using HT⟩

omit [Params] in
private theorem inst_domains_append (ps ds : List VExpr) (x : VExpr) (k : Nat) :
    VExpr.instDomains (ps ++ ds) x k =
      VExpr.instDomains ps x k ++ VExpr.instDomains ds x (k + ps.length) := by
  induction ps generalizing k with
  | nil => simp only [List.nil_append, VExpr.instDomains, List.length_nil, Nat.add_zero]
  | cons A ps ih => simp only [List.cons_append, VExpr.instDomains, ih, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1]

omit [Params] in
private theorem raw_subst_liftN_add (σ : ProofShape.Subst) (m n : Nat) :
    σ.liftN (m + n) = (σ.liftN m).liftN n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg ProofShape.Subst.lift ih

/-- Supply a parameter beneath every pending field. Terminal family paths run
before application, while ordinary control observations substitute structurally.
Neither the parameter value nor a computed lambda needs a native certificate. -/
theorem NativeFamilyFieldObservation.supply_parameter
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ ((A :: ps).reverse ++ Γ)) (env.IsType univs))
    (hx : env.HasType univs Γ x A)
    (H : NativeFamilyFieldObservation D Γ f u (A :: ps) remaining ds out) :
    NativeFamilyFieldObservation D Γ (.app f x) u (VExpr.instDomains ps x 0) remaining
      (VExpr.instDomains ds x ps.length)
      (out.inst (proofErase Γ x) (ps.length + ds.length)) := by
  induction remaining generalizing ds out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    have hps : OnCtx (ps.reverse ++ A :: Γ) (env.IsType univs) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        (OnCtx.of_append hctx)
    have hB : env.HasType univs (ps.reverse ++ A :: Γ) B (.sort u) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using HB.body
    refine ⟨B.inst x ps.length, HB.apply hΓ hx, ?_⟩
    rw [proofErase_instN hps hx (pending_inst ps) hB, VExpr.instDomains_length, ← EB]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
      ProofShape.inst_eq_subst, raw_subst_liftN_add, raw_liftN_subst_liftN]
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    have hctx₀ : OnCtx ((ps ++ ds).reverse ++ A :: Γ) (env.IsType univs) := by
      simpa only [List.reverse_append, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hctx
    have WI := pending_inst (Γ := Γ) (A := A) (x := x) (ps ++ ds)
    have W : ContextSubstitution (proofEraseCtx (ds.reverse ++ ((A :: ps).reverse ++ Γ)))
        (proofEraseCtx ((VExpr.instDomains ds x ps.length).reverse ++
          ((VExpr.instDomains ps x 0).reverse ++ Γ)))
        ((ProofShape.Subst.one (proofErase Γ x)).liftN (ps.length + ds.length)) := by
      intro Δ hΔ EΔ
      have W₀ : ContextSubstitution (proofEraseCtx ((ps ++ ds).reverse ++ A :: Γ))
          (proofEraseCtx ((VExpr.instDomains (ps ++ ds) x 0).reverse ++ Γ))
          ((ProofShape.Subst.one (proofErase Γ x)).liftN (ps ++ ds).length) :=
        inst_interpretation hctx₀ WI hx
      have HW := W₀ hΔ (by simpa only [List.reverse_append, List.reverse_cons,
        List.append_assoc, List.singleton_append] using EΔ)
      simpa only [inst_domains_append, Nat.zero_add, List.length_append, List.reverse_append,
        List.append_assoc] using HW
    have HT := HO.subst_lower
      (σ := (ProofShape.Subst.one (proofErase Γ x)).liftN (ps.length + ds.length))
      (Q := fun X Y => ∃ C B,
        env.IsType univs ((VExpr.instDomains ds x ps.length).reverse ++
          ((VExpr.instDomains ps x 0).reverse ++ Γ)) C ∧
        env.IsType univs (C :: ((VExpr.instDomains ds x ps.length).reverse ++
          ((VExpr.instDomains ps x 0).reverse ++ Γ))) B ∧
        proofErase ((VExpr.instDomains ds x ps.length).reverse ++
          ((VExpr.instDomains ps x 0).reverse ++ Γ)) C = X ∧
        proofErase (C :: ((VExpr.instDomains ds x ps.length).reverse ++
          ((VExpr.instDomains ps x 0).reverse ++ Γ))) B = Y ∧
        NativeFamilyFieldObservation D Γ (.app f x) u (VExpr.instDomains ps x 0) remaining
          (VExpr.instDomains ds x ps.length ++ [C]) Y) W
      (fun X Y HP => by
        obtain ⟨C, B, hC, hB, EC, EB, HR⟩ := HP
        have hC₀ : env.IsType univs ((ps ++ ds).reverse ++ A :: Γ) C := by
          simpa only [List.reverse_append, List.reverse_cons, List.append_assoc,
            List.singleton_append] using hC
        have hB₀ : env.IsType univs (C :: ((ps ++ ds).reverse ++ A :: Γ)) B := by
          simpa only [List.reverse_append, List.reverse_cons, List.append_assoc,
            List.singleton_append] using hB
        have hΓC : OnCtx (C :: ((ps ++ ds).reverse ++ A :: Γ)) (env.IsType univs) := ⟨hctx₀, hC₀⟩
        have HI := ih (ds := ds ++ [C]) (out := Y) (by simpa using hΓC) HR
        refine ⟨C.inst x (ps.length + ds.length), B.inst x (ps.length + ds.length + 1),
          ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [inst_domains_append, Nat.zero_add, List.length_append, List.reverse_append,
            List.append_assoc] using hC₀.instN henv.ordered WI hx
        · simpa only [inst_domains_append, Nat.zero_add, List.length_append, List.reverse_append,
            List.append_assoc] using hB₀.instN henv.ordered WI.succ hx
        · have EE := proofErase_instN hctx₀ hx WI hC₀.choose_spec
          simp only [inst_domains_append, Nat.zero_add, List.length_append, List.reverse_append,
            List.append_assoc] at EE
          rw [EE]
          have E : proofErase (ds.reverse ++ (ps.reverse ++ A :: Γ)) C = X := by
            simpa only [List.reverse_append, List.reverse_cons, List.append_assoc,
              List.singleton_append] using EC
          rw [E, ProofShape.inst_eq_subst]
        · have EE := proofErase_instN hΓC hx WI.succ hB₀.choose_spec
          simp only [inst_domains_append, Nat.zero_add, List.length_append, List.reverse_append,
            List.append_assoc] at EE
          rw [EE]
          have E : proofErase (C :: (ds.reverse ++ (ps.reverse ++ A :: Γ))) B = Y := by
            simpa only [List.reverse_append, List.reverse_cons, List.append_assoc,
              List.singleton_append] using EB
          rw [E, ProofShape.inst_eq_subst]
          rfl
        · rw [inst_domains_snoc] at HI
          have E : ps.length + (ds ++ [C]).length = (ps.length + ds.length) + 1 := by simp; omega
          rw [E, ProofShape.inst_eq_subst] at HI
          exact HI)
      (fun _ _ _ h => h.elim)
    exact ⟨v, by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HT⟩

private theorem map_payload (H : Obs P n Δ S e t o)
    (h : ∀ A B, P A B → Q A B) : Obs Q n Δ S e t o := by
  induction H with
  | var HT HD hi => exact .var HT HD hi
  | payload HT HP => exact .payload HT (h _ _ HP)
  | app HT _ _ ihf iha => exact .app HT ihf iha
  | lam HT HK _ ih => exact .lam HT HK ih

/-- Attach a retained native parameter family to an ignored-field history
of its body. Each terminal lower computation advances that original family,
so no substituted native guard is required later. -/
theorem IgnoredFieldPiObservation.attach_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HF : NativeFamilyPiHistory D Γ f u ps B)
    (H : IgnoredFieldPiObservation D (ps.reverse ++ Γ) B u remaining ds out) :
    NativeFamilyFieldObservation D Γ f u ps remaining ds out := by
  induction remaining generalizing ds out with
  | zero =>
    obtain ⟨C, HC, RC, EC⟩ := H
    have hps := (HF.typed.etaOpen_wf henv.ordered hΓ).1
    have RP := fixed_prefix_compute hps ⟨u, HF.body⟩ ⟨u, HC⟩ RC
    exact ⟨C, HF.convert heq hs hΓ rfl (wrap_type hps ⟨u, HC⟩) RP, EC⟩
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    exact ⟨v, map_payload HO (fun _ _ ⟨A, C, hA, hC, EA, EC, HR⟩ =>
      ⟨A, C, hA, hC, EA, EC, ih HR⟩)⟩

/-- A retained native family starts an observation beneath any well-formed
field telescope whose result ignores those fields. -/
theorem NativeFamilyFieldObservation.of_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HF : NativeFamilyPiHistory D Γ f u ps B)
    (hctx : OnCtx ((ds ++ fields).reverse ++ (ps.reverse ++ Γ)) (env.IsType univs)) :
    NativeFamilyFieldObservation D Γ f u ps fields.length ds
      (proofErase (ds.reverse ++ (ps.reverse ++ Γ))
        (VExpr.wrapForalls fields (B.liftN (ds.length + fields.length)))) :=
  (IgnoredFieldPiObservation.of_telescope
    (HF.typed.etaOpen_wf henv.ordered hΓ).1 HF.body hctx).attach_family heq hs hΓ HF

/-- After all parameters have been supplied, the original applied family is
itself the lower result origin for the remaining field observations. -/
theorem NativeFamilyFieldObservation.finish_parameters
    (H : NativeFamilyFieldObservation D Γ f u [] remaining ds out) :
    IgnoredFieldPiObservation D Γ f u remaining ds out := by
  induction remaining generalizing ds out with
  | zero =>
    obtain ⟨B, HB, EB⟩ := H
    exact ⟨B, HB.body, HB.finish, EB⟩
  | succ remaining ih =>
    obtain ⟨v, HO⟩ := H
    exact ⟨v, map_payload HO (fun _ _ ⟨A, C, hA, hC, EA, EC, HR⟩ =>
      ⟨A, C, hA, hC, EA, EC, ih HR⟩)⟩

/-- Field observations retain the original family at the pending parameter
header, even when their selected result is hidden inside control frames. -/
theorem NativeFamilyFieldObservation.witness
    (H : NativeFamilyFieldObservation D Γ f u ps remaining ds out) :
    ∃ B, NativeFamilyPiHistory D Γ f u ps B := by
  induction remaining generalizing ds out with
  | zero => obtain ⟨B, HB, _⟩ := H; exact ⟨B, HB⟩
  | succ remaining ih =>
    obtain ⟨_, HO⟩ := H
    obtain ⟨_, _, ⟨_, _, _, _, _, _, HR⟩, _⟩ := HO.readout
    exact ih HR

end Lean4Lean.VEnv.Strengthening
