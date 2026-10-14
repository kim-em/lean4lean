import Lean4Lean.Theory.Typing.Strengthening.ProofTelescopeIrrelevance
import Lean4Lean.Theory.Typing.Strengthening.SingletonFamilyTransport

/-! # Singleton reconstruction with propositional indices

Proof irrelevance aligns an entire dependent index telescope after fixed
parameters. This removes family transport from reconstructed singleton proofs.
-/
namespace Lean4Lean.VEnv
open VExpr

/-- Instances of a propositional suffix agree after the same parameter instance.
The source parameter context is closed; the target context is arbitrary. -/
theorem PropTelescope.substEq_suffix (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hP : OnCtx params.reverse (env.IsType U))
    (H : PropTelescope env U params.reverse ds) (hps : ps.length = params.length)
    (ha : TelInst env U Γ (params ++ ds) (ps ++ args))
    (hb : TelInst env U Γ (params ++ ds) (ps ++ args')) :
    Ctx.SubstEq env U Γ (Subst.ofList (ps ++ args)) (Subst.ofList (ps ++ args'))
      (params ++ ds).reverse := by
  induction H generalizing args args' with
  | nil =>
    have h1 : args = [] := by have := ha.1; simp only [List.length_append] at this; apply List.eq_nil_of_length_eq_zero; simp at this; omega
    have h2 : args' = [] := by have := hb.1; simp only [List.length_append] at this; apply List.eq_nil_of_length_eq_zero; simp at this; omega
    subst args; subst args'
    simp only [List.append_nil] at ha hb ⊢
    exact substEq_ofTel hP ha.1 hb.1 (fun j hj _ hd => ha.2 j hj hd)
  | @snoc ds d H hd ih =>
    obtain ⟨as, a, rfl⟩ : ∃ as a, args = as ++ [a] := by
      rcases List.eq_nil_or_concat args with rfl | ⟨as, a, h⟩
      · have := ha.1; simp only [List.length_append, List.length_singleton, List.length_nil] at this; omega
      · exact ⟨as, a, by simpa using h⟩
    obtain ⟨bs, b, rfl⟩ : ∃ bs b, args' = bs ++ [b] := by
      rcases List.eq_nil_or_concat args' with rfl | ⟨bs, b, h⟩
      · have := hb.1; simp only [List.length_append, List.length_singleton, List.length_nil] at this; omega
      · exact ⟨bs, b, by simpa using h⟩
    have hla : (ps ++ as).length = (params ++ ds).length := by have := ha.1; simp_all only [List.length_append, List.length_singleton]; omega
    have hlb : (ps ++ bs).length = (params ++ ds).length := by have := hb.1; simp_all only [List.length_append, List.length_singleton]; omega
    rw [← List.append_assoc] at ha hb
    have ha0 : TelInst env U Γ (params ++ ds) (ps ++ as) := by
      have := ha.take (doms := params ++ ds) (more := [d])
      simpa only [← List.append_assoc, List.take_left' hla] using this
    have hb0 : TelInst env U Γ (params ++ ds) (ps ++ bs) := by
      have := hb.take (doms := params ++ ds) (more := [d])
      simpa only [← List.append_assoc, List.take_left' hlb] using this
    have W := ih ha0 hb0
    have hctx : OnCtx (params ++ ds).reverse (env.IsType U) := by simpa using H.wf hP
    have hd' : env.HasType U (params ++ ds).reverse d (.sort .zero) := by simpa using hd
    have hdd := IsDefEq.substDF henv.orderedStrong hctx hΓ W hd'
    simp only [← instOuter_eq_subst, instOuter_sort] at hdd
    have hat : env.HasType U Γ a (d.instOuter (ps ++ as)) := by
      have := ha.getD (j := (params ++ ds).length) (by simp)
      simp only [← List.append_assoc] at this
      rw [getD_append_right' (by omega), getD_append_right' (Nat.le_refl _),
        show (params ++ ds).length - (ps ++ as).length = 0 by omega,
        Nat.sub_self, List.getD_cons_zero, List.take_left' hla] at this
      exact this
    have hbt : env.HasType U Γ b (d.instOuter (ps ++ bs)) := by
      have := hb.getD (j := (params ++ ds).length) (by simp)
      simp only [← List.append_assoc] at this
      rw [getD_append_right' (by omega), getD_append_right' (Nat.le_refl _),
        show (params ++ ds).length - (ps ++ bs).length = 0 by omega,
        Nat.sub_self, List.getD_cons_zero, List.take_left' hlb] at this
      exact this
    simp only [← List.append_assoc, List.reverse_append, List.reverse_singleton,
      List.cons_append, List.nil_append]
    apply Ctx.SubstEq.cons
    · simpa only [Subst.ofList_snoc_tail, List.reverse_append] using W
    · exact hd
    · simpa only [Subst.ofList_snoc_head, Subst.ofList_snoc_tail, ← instOuter_eq_subst] using
        IsDefEq.proofIrrel hdd.hasType.1 hat (hdd.symm.defeq hbt)

/-- Substitution of two proof-index lists into a typed expression agrees. -/
theorem PropTelescope.instOuter_eq_suffix (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hP : OnCtx params.reverse (env.IsType U))
    (H : PropTelescope env U params.reverse ds) (hps : ps.length = params.length)
    (ha : TelInst env U Γ (params ++ ds) (ps ++ args))
    (hb : TelInst env U Γ (params ++ ds) (ps ++ args'))
    (he : env.HasType U (params ++ ds).reverse e T) :
    env.IsDefEq U Γ (e.instOuter (ps ++ args)) (e.instOuter (ps ++ args'))
      (T.instOuter (ps ++ args)) := by
  have hctx : OnCtx (params ++ ds).reverse (env.IsType U) := by simpa using H.wf hP
  simpa only [← instOuter_eq_subst] using IsDefEq.substDF henv.orderedStrong hctx hΓ
    (H.substEq_suffix henv hΓ hP hps ha hb) he

/-- A closed context instance specializes every term in another closed telescope. -/
theorem TelInst.closed_instOuter (henv : env.WF) (hΔ : OnCtx Δ.reverse (env.IsType U))
    (H : TelInst env U Δ.reverse doms args)
    (hcl : ∀ j (hj : j < doms.length), doms[j].ClosedN j)
    (ht : TelInst env U Γ Δ t) :
    TelInst env U Γ doms (args.map (·.instOuter t)) := by
  refine ⟨by simpa using H.1, ?_⟩
  intro j hj hd
  have hja : j < args.length := by simpa using hj
  have h := HasType.closed_instOuter henv hΔ (H.2 j hja hd) ht
  rw [instOuter_instOuter _ _ _ (by simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hja)] using hcl j hd)] at h
  simpa only [List.getElem_map, List.map_take] using h

/-- A closed telescope substitution exposes equality at every argument position. -/
theorem Ctx.SubstEq.ofList_getD (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (W : Ctx.SubstEq env U Γ (Subst.ofList args) (Subst.ofList args') doms.reverse)
    (ha : TelInst env U Γ doms args) (hb : args'.length = doms.length)
    (hj : j < doms.length) :
    env.IsDefEq U Γ (args.getD j default) (args'.getD j default)
      ((doms.getD j default).instOuter (args.take j)) := by
  have hla := ha.1
  have hn : doms.length - 1 - j < doms.reverse.length := by simp; omega
  obtain ⟨T, hT⟩ := Lookup.ofLt hn
  have h := W.lookup hT
  rw [Subst.ofList_lt _ (by omega), Subst.ofList_lt _ (by omega)] at h
  have hja : args.length - 1 - (doms.length - 1 - j) = j := by omega
  have hjb : args'.length - 1 - (doms.length - 1 - j) = j := by omega
  simp only [hja, hjb] at h
  have hu : env.IsDefEqU U Γ (args.getD j default) (args'.getD j default) := by
    rw [getD_of_lt (by omega), getD_of_lt (by omega)]
    exact ⟨_, h⟩
  exact hu.of_l henv hΓ (ha.getD hj)

end Lean4Lean.VEnv

namespace Lean4Lean.PropElim
open VExpr VEnv SingletonLayout
variable {S : SingletonLayout} {params : List VExpr} {E : PropElim}

/-- Constructor indices specialize to a typed index instance after any typed
field instance, with the original parameter values. -/
theorem WF.specializedCtorIndices (henv : env.WF) (W : E.WF S params env U)
    (hps : ps.length = params.length)
    (hf : TelInst env U Γ (params ++ S.fields) (ps ++ f)) :
    TelInst env U Γ (params ++ S.indices)
      (ps ++ E.ctorIndices.map (·.instOuter (ps ++ f))) := by
  have hctx : OnCtx (params ++ S.fields).reverse (env.IsType U) := by
    simpa using W.typed.fieldsCtx S.fields.length (Nat.le_refl _)
  have h := W.ctorIndices_typed.closed_instOuter henv hctx
    (W.typed.prefix_closed (fun l hl => W.typed.scope.indices l hl)) hf
  have hlen : (ps ++ f).length = params.length + S.fields.length := by simpa using hf.1
  simp only [List.map_append, branchPa] at h
  rw [instOuter_bvarRange _ _ _ (by omega) (by rw [hlen]; exact Nat.le_refl _), hlen,
    Nat.sub_self, List.drop_zero, List.take_left' hps] at h
  exact h

/-- Propositional indices force the reconstructed and requested family to agree.
This discharges the family-conversion obstruction for the entire dependent
proof-index fragment, without an assumed aligned field instance. -/
theorem proof_indices_family_conversion (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hindices : PropTelescope env U params.reverse S.indices)
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.IsDefEq U Γ (transportedFamily S params E ps idx m)
      (mkApps E.family (ps ++ idx)) (.sort .zero) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx) := by
    have := hargs.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using this
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  have hci := W.specializedCtorIndices henv hps hf
  have hP : OnCtx params.reverse (env.IsType U) := by
    simpa using W.typed.indicesCtx 0 (Nat.zero_le _)
  have h := hindices.instOuter_eq_suffix henv hΓ hP hps hci hia W.majorTy_typed
  rw [majorTy_at W hps (by simpa using W.ctorIndices_length), majorTy_at W hps hidx,
    instOuter_sort] at h
  have hlen : (ps ++ transportedFields S params E ps idx m S.fields.length).length =
      params.length + S.fields.length := by simpa using hf.1
  unfold transportedFamily branchFamily
  simp only [instOuter_mkApps, instOuter_closed0 W.family_closed, List.map_append, branchPa]
  rw [instOuter_bvarRange _ _ _ (by omega) (by rw [hlen]; exact Nat.le_refl _), hlen,
    Nat.sub_self, List.drop_zero, List.take_left' hps]
  exact h

/-- A singleton with a dependent telescope of proof indices exposes its bare
reconstructed constructor at every typed occurrence. -/
theorem proof_indices_bare_constructor (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hindices : PropTelescope env U params.reverse S.indices)
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.IsDefEqU U Γ m (transportedCtor S params E ps idx m) :=
  (bare_constructor_iff_family_conversion henv heq W hΓ hps hargs).2
    (proof_indices_family_conversion henv heq W hΓ hindices hps hargs)

/-- Any two typed index instances agree componentwise when all index domains
are propositions, including dependency on earlier index proofs. -/
theorem proof_indices_eq (henv : env.WF) (W : E.WF S params env U)
    (hΓ : OnCtx Γ (env.IsType U))
    (hindices : PropTelescope env U params.reverse S.indices)
    (hps : ps.length = params.length)
    (hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx))
    (hf : TelInst env U Γ (params ++ S.fields) (ps ++ f))
    (hk : k < S.indices.length) :
    env.IsDefEq U Γ (idx.getD k default)
      ((E.ctorIndices.getD k default).instOuter (ps ++ f))
      ((S.indices.getD k default).instOuter (ps ++ idx.take k)) := by
  have hci := W.specializedCtorIndices henv hps hf
  have hP : OnCtx params.reverse (env.IsType U) := by
    simpa using W.typed.indicesCtx 0 (Nat.zero_le _)
  have hs := hindices.substEq_suffix henv hΓ hP hps hia hci
  have h := hs.ofList_getD henv hΓ hia hci.1 (j := params.length + k) (by simp; omega)
  rw [getD_append_right' (by omega), getD_append_right' (by omega),
    getD_append_right' (by omega), List.take_append, List.take_of_length_le (by omega),
    hps, Nat.add_sub_cancel_left] at h
  rw [getD_of_lt (l := E.ctorIndices.map (·.instOuter (ps ++ f))) (by simpa [W.ctorIndices_length] using hk), List.getElem_map,
    ← getD_of_lt (d := (default : VExpr)) (by simpa [W.ctorIndices_length] using hk)] at h
  exact h

/-- The original generated singleton reconstruction is valid for proof indices.
The slot bound is the ordinary layout condition satisfied by registered
singletons; neither aligned fields nor ambient index equations are assumed. -/
theorem proof_indices_singleton_eta (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : E.WF S params env U) (hΓ : OnCtx Γ (env.IsType U))
    (hindices : PropTelescope env U params.reverse S.indices)
    (hslot : ∀ l k, S.slot.getD l none = some k → l < S.fields.length)
    (hps : ps.length = params.length)
    (hargs : TelInst env U Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    env.IsDefEq U Γ m
      (mkApps E.ctor (ps ++ (occ S params E ps idx m S.fields.length).2))
      ((majorTy S params E).instOuter (ps ++ idx)) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hia : TelInst env U Γ (params ++ S.indices) (ps ++ idx) := by
    have := hargs.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using this
  let f := transportedFields S params E ps idx m S.fields.length
  have hf : TelInst env U Γ (params ++ S.fields) (ps ++ f) := by
    simpa [f] using transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  have hfl : f.length = S.fields.length := by
    have := hf.1; simp only [List.length_append] at this; omega
  have hix := fun k hk => proof_indices_eq henv W hΓ hindices hps hia hf (k := k) hk
  apply singleton_eta params henv heq W hΓ hps hargs hf ?_ hix
  intro l k hs
  have hl := hslot l k hs
  have hk := W.typed.scope.slot_lt l k hs
  have h := (hix k hk).symm
  rw [W.slot_literal l k hs, instOuter_bvar _ (by simp [hps, hfl]; omega)] at h
  have he : (ps ++ f)[(ps ++ f).length - 1 - (S.fields.length - 1 - l)]'(by simp only [List.length_append]; omega) = f.getD l default := by
    rw [List.getElem_append_right (by simp [hfl]; omega), getD_of_lt (by omega)]
    congr 1
    simp only [List.length_append]
    omega
  rw [he] at h
  have ht := hf.getD (j := params.length + l) (by simp; omega)
  rw [getD_append_right' (by omega), getD_append_right' (by omega), List.take_append,
    List.take_of_length_le (by omega), hps, Nat.add_sub_cancel_left] at ht
  exact (show env.IsDefEqU U Γ (f.getD l default) (idx.getD k default) from ⟨_, h⟩).of_l henv hΓ ht

end Lean4Lean.PropElim
