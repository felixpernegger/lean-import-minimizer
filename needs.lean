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
    for ci in env.header.moduleData[i]!.constants do
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
