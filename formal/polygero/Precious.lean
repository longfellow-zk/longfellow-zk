import Lean

/-! Persistent markers and signature checks for the precious Polygero API.
The marker permits declarations from imported modules, so the protected surface
can be maintained in one manifest without modifying mathematical source files.
-/

namespace RecursivePolygero.StableAPI
open Lean Elab Command

initialize preciousExtension : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries =>
      entries.foldl (fun acc names => names.foldl NameSet.insert acc) {}
    addEntryFn := fun names name => names.insert name
    toArrayFn := fun names => names.toArray.qsort Name.quickLt
  }

/-- True exactly when a declaration belongs to the protected API in this environment. -/
def isPrecious (env : Environment) (name : Name) : Bool :=
  (preciousExtension.getState env).contains name

private def markPrecious (name : Name) : CoreM Unit := do
  unless (← getEnv).contains name do
    throwError "Unknown precious declaration: {name}"
  modifyEnv fun env => preciousExtension.addEntry env name

/-- Binder names are presentation only; retain all binder types, order,
implicitness, universe parameters, and constants in the fingerprint. -/
private partial def eraseBinderNames : Expr → Expr
  | .app f a => .app (eraseBinderNames f) (eraseBinderNames a)
  | .lam _ d b bi => .lam .anonymous (eraseBinderNames d) (eraseBinderNames b) bi
  | .forallE _ d b bi => .forallE .anonymous (eraseBinderNames d) (eraseBinderNames b) bi
  | .letE _ t v b nondep =>
      .letE .anonymous (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) nondep
  | .mdata data e => .mdata data (eraseBinderNames e)
  | .proj name idx e => .proj name idx (eraseBinderNames e)
  | e => e

/-- Stable under alpha-renaming of binders, including Lean-generated names. -/
def signatureFingerprint (info : ConstantInfo) : UInt64 :=
  hash (info.levelParams, reprStr (eraseBinderNames info.type))

run_cmd do
  let nat := mkConst ``Nat
  let body := Expr.app (mkConst ``Nat.succ) (.bvar 0)
  let left := Expr.forallE `x nat body .default
  let renamed := Expr.forallE `y nat body .default
  let implicit := Expr.forallE `x nat body .implicit
  let differentDomain := Expr.forallE `x (mkConst ``Bool) body .default
  unless eraseBinderNames left == eraseBinderNames renamed do
    throwError "Signature normalization is sensitive to binder names"
  if reprStr (eraseBinderNames left) == reprStr (eraseBinderNames implicit) then
    throwError "Signature normalization erased binder implicitness"
  if reprStr (eraseBinderNames left) == reprStr (eraseBinderNames differentDomain) then
    throwError "Signature normalization erased binder types"

initialize registerBuiltinAttribute {
  name := `precious
  descr := "Stable API until explicit further user order; preserve name and contract."
  add := fun name stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do throwAttrMustBeGlobal `precious kind
    markPrecious name
  erase := fun name => throwError "Precious API protection requires explicit further user order: {name}"
}

/-- Mark a declaration precious and check its frozen universe parameters and type.
Proof bodies are deliberately excluded, so proofs may be improved freely.
-/
elab "precious_api " decl:ident fingerprint:num : command => do
  let name ← resolveGlobalConstNoOverload decl
  let info ← getConstInfo name
  let actual := signatureFingerprint info
  unless actual.toNat == fingerprint.getNat do
    throwErrorAt decl "Precious API signature changed for {name}; explicit further user order is required"
  modifyEnv fun env => preciousExtension.addEntry env name

end RecursivePolygero.StableAPI
