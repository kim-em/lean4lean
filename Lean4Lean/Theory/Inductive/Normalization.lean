import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.Injectivity

/-! Source-universe normalization of checked positive constructor fields.
The output retains the exact recursive-head universe spine. Uniformity of that
spine is a separate fact supplied by the executable inductive-application check.
-/

namespace Lean4Lean
namespace VInductDecl

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
