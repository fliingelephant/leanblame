/-
Proof erasure (docs/03-trust-model.md, "The hash, precisely"): every subterm of
a type or a definition body whose type is a proposition is replaced by a marker
before hashing.

"Is this subterm a proof?" is `Lean.Meta.isProof`, asked in the environment
`Load` builds from the export. The answer errs on one side only: when inference
fails, the subterm is kept and hashed. Keeping a proof costs a spurious hash
change; erasing a non-proof would hide a change of meaning.
-/
import Lean.Meta.InferType

namespace LeanBlame.Erase

open Lean Meta

/-- The marker that replaces an erased proof. Never occurs in exported terms. -/
def proofMarker : Expr := .mvar ⟨`_leanblame_erased_proof⟩

def isProofMarker (e : Expr) : Bool := e == proofMarker

/-- Whether `e` (closed but for locals) is a proof. Failures answer `false`: keep it. -/
def isProof (e : Expr) : MetaM Bool :=
  tryCatchRuntimeEx (withTransparency .all (Meta.isProof e)) fun _ => pure false

/--
Replace every proof subterm by `proofMarker`, outermost first. Locals are declared with the
original binder types, so inference under a binder never meets a marker. Terms reach here closed
but for locals, so the result depends on the term alone and is cached: shared subterms are erased
once.
-/
partial def erase (e : Expr) : MonadCacheT Expr Expr MetaM Expr :=
  checkCache e fun _ => do
    if ← isProof e then return proofMarker
    match e with
    | .app .. => return mkAppN (← erase e.getAppFn) (← e.getAppArgs.mapM erase)
    | .lam n d b bi =>
      let d' ← erase d
      withLocalDecl n bi d fun x => return .lam n d' ((← erase (b.instantiate1 x)).abstract #[x]) bi
    | .forallE n d b bi =>
      let d' ← erase d
      withLocalDecl n bi d fun x =>
        return .forallE n d' ((← erase (b.instantiate1 x)).abstract #[x]) bi
    | .letE n t v b nd =>
      let t' ← erase t
      let v' ← erase v
      withLetDecl n t v fun x => return .letE n t' v' ((← erase (b.instantiate1 x)).abstract #[x]) nd
    | .proj s i st => return .proj s i (← erase st)
    | .mdata _ b => erase b
    | _ => return e

/-- Erase the proofs in a closed term: a type or a definition body. -/
def eraseProofs (e : Expr) : MetaM Expr := (erase e).run

end LeanBlame.Erase
