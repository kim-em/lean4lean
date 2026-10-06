import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.Injectivity

/-! Source-universe normalization of checked positive constructor fields.
The output retains the exact recursive-head universe spine. Uniformity of that
spine is a separate fact supplied by the executable inductive-application check.
-/

namespace Lean4Lean
namespace VInductDecl

/-- A normalized positive field is either free of current inductive constants,
or a telescope of such domains ending in a fully applied current family. -/
def FieldNormalForm (decl : VInductDecl) (depth : Nat) (e : VExpr) : Prop :=
  e.SourceConstFree (decl.types.map (·.name)) ∨
  ∃ domains result, e = VExpr.wrapForalls domains result ∧
    (∀ domain ∈ domains, domain.SourceConstFree (decl.types.map (·.name))) ∧
    decl.ValidIndAppAt none (depth + domains.length) result

private theorem normalize_positive {env : VEnv} {decl : VInductDecl}
    (henv : env.WF) : ∀ {ctx depth e}, decl.Positive env ctx depth e →
    OnCtx ctx (env.IsType decl.uvars) → env.IsType decl.uvars ctx e →
    ∃ normalized, env.IsDefEqU decl.uvars ctx e normalized ∧
      decl.FieldNormalForm depth normalized := by
  intro ctx depth e H
  refine Positive.rec
    (motive_1 := fun ctx depth e _ =>
      OnCtx ctx (env.IsType decl.uvars) → env.IsType decl.uvars ctx e →
      ∃ normalized, env.IsDefEqU decl.uvars ctx e normalized ∧
        decl.FieldNormalForm depth normalized)
    (motive_2 := fun ctx depth e _ =>
      OnCtx ctx (env.IsType decl.uvars) → env.IsType decl.uvars ctx e →
      ∃ normalized, env.IsDefEqU decl.uvars ctx e normalized ∧
        decl.FieldNormalForm depth normalized)
    ?_ ?_ ?_ ?_ H
  · intro ctx e exposed type depth hdef _ ih hctx he
    have hexposed : env.IsType decl.uvars ctx exposed :=
      he.defeqU_l henv hctx ⟨_, hdef⟩
    obtain ⟨normalized, hn, hs⟩ := ih hctx hexposed
    exact ⟨normalized, (VEnv.IsDefEqU.trans henv hctx ⟨_, hdef⟩ hn), hs⟩
  · intro ctx depth e hfree hctx he
    exact ⟨e, (let ⟨u, hu⟩ := he; ⟨_, hu⟩), .inl hfree⟩
  · intro ctx dom checkedDom domLevel body checkedBody bodyType depth hfree hdom hbody _ ih hctx he
    have htypes := he.forallE_inv henv.ordered
    have hdomctx : OnCtx (dom :: ctx) (env.IsType decl.uvars) := ⟨hctx, htypes.1⟩
    have hcheckedctx : OnCtx (checkedDom :: ctx) (env.IsType decl.uvars) :=
      ⟨hctx, _, hdom.hasType.2⟩
    have hctxeq : env.IsDefEqCtx decl.uvars ctx (dom :: ctx) (checkedDom :: ctx) :=
      .succ .zero hdom
    have hchecked : env.IsType decl.uvars (checkedDom :: ctx) checkedBody :=
      (htypes.2.defeqU_l henv hdomctx ⟨_, hbody⟩).defeqDFC henv.ordered hctxeq
    obtain ⟨normalized, hn, hs⟩ := ih hcheckedctx hchecked
    have hback := hn.defeqDFC henv.ordered (hctxeq.symm henv.ordered)
    have hnorm : env.IsDefEqU decl.uvars (dom :: ctx) body normalized :=
      VEnv.IsDefEqU.trans henv hdomctx ⟨_, hbody⟩ hback
    obtain ⟨v, hv⟩ := htypes.2
    have hnormSort := hnorm.of_l henv hdomctx hv
    refine ⟨.forallE dom normalized, ⟨_, .forallEDF hdom.hasType.1 hnormSort⟩, ?_⟩
    rcases hs with hfreeBody | ⟨domains, result, rfl, hdomains, hresult⟩
    · exact .inl (.forallE hfree hfreeBody)
    · refine .inr ⟨dom :: domains, result, rfl, ?_, ?_⟩
      · intro domain hmem
        rcases List.mem_cons.mp hmem with rfl | hm
        · exact hfree
        · exact hdomains domain hm
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
  · intro depth e ctx happ hctx he
    exact ⟨e, (let ⟨u, hu⟩ := he; ⟨_, hu⟩), .inr ⟨[], e, rfl, by simp, by simpa using happ⟩⟩

/-- Normalize the actual checked field by typed equality, without identifying
independently chosen translations of projections. -/
theorem Positive.normalForm {env : VEnv} {decl : VInductDecl}
    (H : decl.Positive env ctx depth e) (henv : env.WF)
    (hctx : OnCtx ctx (env.IsType decl.uvars)) (he : env.IsType decl.uvars ctx e) :
    ∃ normalized, env.IsDefEqU decl.uvars ctx e normalized ∧
      decl.FieldNormalForm depth normalized :=
  normalize_positive henv H hctx he


/-- A field retains its declared domain together with a normalized positive
shape at the original declaration universes. Unsafe blocks do not require
positivity. -/
def NormalizedField (env : VEnv) (decl : VInductDecl)
    (ctx : List VExpr) (depth : Nat) (domain : VExpr) : Prop :=
  decl.isUnsafe = true ∨ ∃ normalized,
    env.IsDefEqU decl.uvars ctx domain normalized ∧
      decl.FieldNormalForm depth normalized

/-- Explicit constructor telescope with source-universe positive-field data.
The stored domains remain the domains used to generate constructor minors;
their normalized recursive shapes are recorded separately. -/
inductive NormalizedCtorTail (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) : List VExpr → Nat → VExpr → Prop
  | result : decl.ValidIndAppAt (some target.name) depth result →
    NormalizedCtorTail env decl target ctx depth result
  | field : env.IsType decl.uvars ctx domain →
    NormalizedField env decl ctx depth domain →
    NormalizedCtorTail env decl target (domain :: ctx) (depth + 1) body →
    NormalizedCtorTail env decl target ctx depth (.forallE domain body)

theorem NormalizedField.defeqCtx
    (H : NormalizedField env decl ctx₁ depth domain)
    (henv : env.Ordered) (hctx : env.IsDefEqCtx decl.uvars base ctx₁ ctx₂) :
    NormalizedField env decl ctx₂ depth domain := by
  rcases H with hunsafe | ⟨normalized, hnorm, hshape⟩
  · exact .inl hunsafe
  · exact .inr ⟨normalized, hnorm.defeqDFC henv hctx, hshape⟩

theorem NormalizedCtorTail.defeqCtx
    (H : NormalizedCtorTail env decl target ctx₁ depth tail)
    (henv : env.Ordered) (hctx : env.IsDefEqCtx decl.uvars base ctx₁ ctx₂) :
    NormalizedCtorTail env decl target ctx₂ depth tail := by
  induction H generalizing ctx₂ with
  | result hresult => exact .result hresult
  | field htype hfield _ ih =>
    obtain ⟨u, hu⟩ := htype
    exact .field ⟨u, hu.defeqDFC henv hctx⟩
      (hfield.defeqCtx henv hctx) (ih (.succ hctx hu))

/-- Extract the explicit field list with each field certified in precisely
its parameter-and-prior-field context. -/
theorem NormalizedCtorTail.telescope
    (H : NormalizedCtorTail env decl target ctx depth tail) :
    ∃ fields result, tail = VExpr.wrapForalls fields result ∧
      decl.ValidIndAppAt (some target.name) (depth + fields.length) result ∧
      ∀ i (hi : i < fields.length),
        env.IsType decl.uvars ((fields.take i).reverse ++ ctx) fields[i] ∧
        NormalizedField env decl ((fields.take i).reverse ++ ctx)
          (depth + i) fields[i] := by
  induction H with
  | result hresult =>
    exact ⟨[], _, rfl, by simpa using hresult, by intro i hi; simp at hi⟩
  | @field ctx domain depth body htype hfield _ ih =>
    obtain ⟨fields, result, rfl, hresult, hfields⟩ := ih
    refine ⟨domain :: fields, result, rfl, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
    · intro i hi
      cases i with
      | zero => simpa using And.intro htype hfield
      | succ i =>
        have hi' : i < fields.length := by simpa using hi
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfields i hi'

/-- Interpret every checked constructor field before adding the recursor
universe. This keeps the original domain and relates its recursive normal
form by typed equality, including when projection desugaring changes syntax. -/
theorem CtorTailWF.normalForm
    (H : decl.CtorTailWF env target ctx depth tail)
    (henv : env.WF) (hctx : OnCtx ctx (env.IsType decl.uvars))
    (htail : env.IsType decl.uvars ctx tail) :
    ∃ normalized, env.IsDefEqU decl.uvars ctx tail normalized ∧
      NormalizedCtorTail env decl target ctx depth normalized := by
  induction H with
  | result hresult hdef =>
    exact ⟨_, ⟨_, hdef⟩, .result hresult⟩
  | @field ctx dom fieldLevel depth checkedDom checkedLevel body checkedBody bodyType
      hdom hlevel hpositive hdomEq hbodyEq htailwf ih =>
    have htypes := htail.forallE_inv henv.ordered
    have hdomctx : OnCtx (dom :: ctx) (env.IsType decl.uvars) := ⟨hctx, htypes.1⟩
    have hcheckedctx : OnCtx (checkedDom :: ctx) (env.IsType decl.uvars) :=
      ⟨hctx, _, hdomEq.hasType.2⟩
    have hctxeq : env.IsDefEqCtx decl.uvars ctx
        (dom :: ctx) (checkedDom :: ctx) := .succ .zero hdomEq
    have hchecked : env.IsType decl.uvars (checkedDom :: ctx) checkedBody :=
      (htypes.2.defeqU_l henv hdomctx ⟨_, hbodyEq⟩).defeqDFC henv.ordered hctxeq
    obtain ⟨normalized, hn, hs⟩ := ih hcheckedctx hchecked
    have hback := hn.defeqDFC henv.ordered (hctxeq.symm henv.ordered)
    have hnorm : env.IsDefEqU decl.uvars (dom :: ctx) body normalized :=
      VEnv.IsDefEqU.trans henv hdomctx ⟨_, hbodyEq⟩ hback
    obtain ⟨v, hv⟩ := htypes.2
    have hnormSort := hnorm.of_l henv hdomctx hv
    refine ⟨.forallE dom normalized, ⟨_, .forallEDF hdom hnormSort⟩,
      .field ⟨_, hdom⟩ ?_ (hs.defeqCtx henv.ordered (hctxeq.symm henv.ordered))⟩
    rcases hpositive with hunsafe | hpositive
    · exact .inl hunsafe
    · exact .inr (hpositive.normalForm henv hctx ⟨_, hdom⟩)


theorem UniformFieldNormalForm.forgetLevels {decl : VInductDecl}
    (H : decl.UniformFieldNormalForm levels depth e) :
    decl.FieldNormalForm depth e := by
  rcases H with hfree | ⟨domains, result, heq, hdomains, hresult, _⟩
  · exact .inl hfree
  · exact .inr ⟨domains, result, heq, hdomains, hresult⟩

theorem UniformFieldNormalForm.forallE {decl : VInductDecl} {domain : VExpr}
    (hdom : domain.SourceConstFree (decl.types.map (·.name)))
    (H : decl.UniformFieldNormalForm levels (depth + 1) body) :
    decl.UniformFieldNormalForm levels depth (.forallE domain body) := by
  rcases H with hfree | ⟨domains, result, rfl, hdomains, hresult, hhead⟩
  · exact .inl (.forallE hdom hfree)
  · refine .inr ⟨domain :: domains, result, rfl, ?_, ?_, hhead⟩
    · intro field hfield
      rcases List.mem_cons.mp hfield with rfl | hfield
      · exact hdom
      · exact hdomains field hfield
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult

/-- The literal checked constructor telescope, with field classification
attached to the actual domain and prefix context. This certificate is produced
by replaying constructor checks, without selecting independent field targets. -/
inductive UniformCtorTail (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) (levels : List VLevel) : List VExpr → Nat → VExpr → Prop
  | result : decl.ValidIndAppAt (some target.name) depth result →
    result.getAppFnArgs.1 = .const target.name levels →
    UniformCtorTail env decl target levels ctx depth result
  | field : env.IsType decl.uvars ctx domain →
    (decl.isUnsafe = true ∨ ∃ normalized,
      env.IsDefEqU decl.uvars ctx domain normalized ∧
      decl.UniformFieldNormalForm levels depth normalized) →
    UniformCtorTail env decl target levels (domain :: ctx) (depth + 1) body →
    UniformCtorTail env decl target levels ctx depth (.forallE domain body)

theorem UniformCtorTail.forgetLevels
    (H : UniformCtorTail env decl target levels ctx depth tail) :
    NormalizedCtorTail env decl target ctx depth tail := by
  induction H with
  | result hresult _ => exact .result hresult
  | field htype hfield _ ih =>
    apply NormalizedCtorTail.field htype _ ih
    rcases hfield with hunsafe | ⟨normalized, hnorm, hshape⟩
    · exact .inl hunsafe
    · exact .inr ⟨normalized, hnorm, hshape.forgetLevels⟩

/-- Every field of the literal source telescope has its own classification
under exactly the preceding fields and parameters; recursive levels remain
uniform across the whole constructor. -/
theorem UniformCtorTail.telescope
    (H : UniformCtorTail env decl target levels ctx depth tail) :
    ∃ fields result, tail = VExpr.wrapForalls fields result ∧
      decl.ValidIndAppAt (some target.name) (depth + fields.length) result ∧
      result.getAppFnArgs.1 = .const target.name levels ∧
      ∀ i (hi : i < fields.length),
        env.IsType decl.uvars ((fields.take i).reverse ++ ctx) fields[i] ∧
        (decl.isUnsafe = true ∨ ∃ normalized,
          env.IsDefEqU decl.uvars ((fields.take i).reverse ++ ctx) fields[i] normalized ∧
          decl.UniformFieldNormalForm levels (depth + i) normalized) := by
  induction H with
  | result hresult hhead =>
    exact ⟨[], _, rfl, by simpa using hresult, hhead, by intro i hi; simp at hi⟩
  | @field ctx domain depth body htype hfield _ ih =>
    obtain ⟨fields, result, rfl, hresult, hhead, hfields⟩ := ih
    refine ⟨domain :: fields, result, rfl, ?_, hhead, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult
    · intro i hi
      cases i with
      | zero => simpa using And.intro htype hfield
      | succ i =>
        have hi' : i < fields.length := by simpa using hi
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfields i hi'

end VInductDecl
end Lean4Lean
