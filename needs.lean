import Lean
/-!
Prints, for every module below a given root, which other modules it references directly:
through the constants in its compiled declarations and through the extra module uses that Lean
records during elaboration (notation, tactics, attributes, ...).

Output (tab separated):
  M <module>
  C <used module> <exported 0/1> <meta 0/1> <#distinct constants> <using decl> <used decl>
  X <used module> <exported 0/1> <meta 0/1>          (recorded extra use)
  I <module> <decl>   (module that put an attribute on a used declaration; weak hint)
  Q <module> <decl>   (a syntax quotation in this module names `decl` of `module`: a macro
                       or notation whose expansion refers to it; the quotation resolves the
                       name where it is written, so this module must keep seeing `decl`)
At the end, for every loaded module:
  N <namespace> <module>   (the module registers the namespace)
-/
open Lean

def isDeclMeta' (env : Environment) (declName : Name) : Bool :=
  let inferFor :=
    if declName.isStr && (declName.getString!.startsWith "match_" || declName.getString! == "_unsafe_rec")
    then declName.getPrefix else declName
  isMarkedMeta env inferFor || isDeclMeta env inferFor

structure Use where
  consts : Std.HashSet Name := {}
  useDecl : Name := .anonymous
  defDecl : Name := .anonymous

abbrev Uses := Std.HashMap (Nat × Bool × Bool) Use

def addUse (u : Uses) (key : Nat × Bool × Bool) (useDecl defDecl : Name) : Uses :=
  u.alter key fun o =>
    let x := o.getD {}
    let better := x.consts.isEmpty ||
      (useDecl.toString.length + defDecl.toString.length <
        x.useDecl.toString.length + x.defDecl.toString.length)
    some { consts := x.consts.insert defDecl
           useDecl := if better then useDecl else x.useDecl
           defDecl := if better then defDecl else x.defDecl }

/-- The name denoted by a closed `Name` expression, as produced by quoting a name
(`Name.anonymous`, `Name.str`, `Name.num`, `Name.mkStr`, `Name.mkStr1` ... `Name.mkStr8`). -/
partial def nameLit? (e : Expr) : Option Name := do
  let str? (e : Expr) : Option String := match e.consumeMData with
    | .lit (.strVal s) => some s
    | _ => none
  let nat? (e : Expr) : Option Nat := match e.consumeMData with
    | .lit (.natVal n) => some n
    | e => if e.isAppOfArity ``OfNat.ofNat 3 then
        (match e.appFn!.appArg!.consumeMData with | .lit (.natVal n) => some n | _ => none)
      else none
  let e := e.consumeMData
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Lean.Name.anonymous => guard args.isEmpty; return .anonymous
  | some ``Lean.Name.str | some ``Lean.Name.mkStr =>
    guard (args.size == 2); return .str (← nameLit? args[0]!) (← str? args[1]!)
  | some ``Lean.Name.num | some ``Lean.Name.mkNum =>
    guard (args.size == 2); return .num (← nameLit? args[0]!) (← nat? args[1]!)
  | some c =>
    guard (c.getPrefix == ``Lean.Name && c.isStr && c.getString!.startsWith "mkStr" &&
      (c.getString!.drop 5).toString.toNat?.isSome && !args.isEmpty)
    args.foldlM (init := Name.anonymous) fun n a => return .str n (← str? a)
  | none => none

/-- Declarations named by the syntax quotations in `e`: every quoted identifier carries the
global declarations it resolved to where the quotation was written
(`Syntax.Preresolved.decl n _`). -/
unsafe def quotedDecls (e : Expr) : IO (Array Name) := do
  let r ← IO.mkRef (#[] : Array Name)
  e.forEachWhere (·.isAppOfArity ``Lean.Syntax.Preresolved.decl 2) fun d => do
    if let some n := nameLit? d.appFn!.appArg! then r.modify (·.push n)
  r.get

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let root := args.head!.toName
  let imps : Array Import := #[{ module := root }]
  let (_, s) ← importModulesCore imps (isExported := true) |>.run
  let s := s.markAllExported
  let mut env ← finalizeImport s (isModule := true) imps {} (leakEnv := true) (loadExts := false)
  let is := indirectModUseExt.toEnvExtension.getState env
  let newState ← indirectModUseExt.addImportedFn is.importedEntries { env := env, opts := {} }
  env := indirectModUseExt.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }
  let indirect : Std.HashMap Name (Array ModuleIdx) := indirectModUseExt.getState env
  let mut reserved : Std.HashSet Name := {}
  for (c, _) in env.constants do
    if isReservedName env c then reserved := reserved.insert c
  let names := env.header.moduleNames
  let out ← IO.getStdout
  for i in [0:names.size] do
    unless root.isPrefixOf names[i]! do continue
    let mut uses : Uses := {}
    let mut ind : Std.HashMap Nat Name := {}
    let mut quoted : Std.HashMap Name Nat := {}
    for ci in env.header.moduleData[i]!.constants do
      if let some v := ci.value? (allowOpaque := true) then
        for n in ← quotedDecls v do
          if let some (j : Nat) := env.getModuleIdxFor? n then
            if j != i then quoted := quoted.insert n j
      let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
      let k0 : Bool × Bool := (pubCI?.isSome, isDeclMeta' env ci.name)
      let mut exprs : Array (Bool × Bool × Expr) := #[(k0.1, k0.2, ci.type)]
      if let some e := ci.value? (allowOpaque := true) then
        let k := if k0.2 then k0 else
          (pubCI?.any (·.hasValue (allowOpaque := true)), false)
        exprs := exprs.push (k.1, k.2, e)
      for (exp, isMeta, e) in exprs do
        uses := Lean.Expr.foldConsts e uses fun c uses => Id.run do
          let mut uses := uses
          if reserved.contains c then return uses
          let c := if c.isStr && c.getString!.startsWith "_simp_" then c.getPrefix else c
          if let some (j : Nat) := env.getModuleIdxFor? c then
            let m := isMeta && !isDeclMeta' env c
            if j != i then
              uses := addUse uses (j, exp, m) ci.name c
          return uses
        ind := Lean.Expr.foldConsts e ind fun c ind => Id.run do
          let mut ind := ind
          if reserved.contains c then return ind
          let c := if c.isStr && c.getString!.startsWith "_simp_" then c.getPrefix else c
          for (indMod : Nat) in indirect[c]?.getD #[] do
            if indMod != i then
              ind := ind.insert indMod c
          return ind
    out.putStrLn s!"M\t{names[i]!}"
    for ((j, exp, m), u) in uses do
      out.putStrLn s!"C\t{names[j]!}\t{exp.toNat}\t{m.toNat}\t{u.consts.size}\t{u.useDecl}\t{u.defDecl}"
    for (j, c) in ind do
      out.putStrLn s!"I\t{names[j]!}\t{c}"
    for (n, j) in quoted do
      out.putStrLn s!"Q\t{names[j]!}\t{n}"
    for use in getExtraModUses env i do
      out.putStrLn s!"X\t{use.module}\t{use.isExported.toNat}\t{use.isMeta.toNat}"
  -- which modules register which namespaces (for `open N` failing with "unknown namespace")
  -- (`namespacesExt` is private, so it is looked up in the registry by its private name)
  let isNsExt := fun (n : Name) => privateToUserName n == `Lean.namespacesExt
  if let some ext := (← persistentEnvExtensionsRef.get).find? (isNsExt ·.name) then
    for i in [0:names.size] do
      for e in ext.getModuleEntries env i do
        let ns : Name := unsafeCast e
        out.putStrLn s!"N\t{ns}\t{names[i]!}"
  out.flush
