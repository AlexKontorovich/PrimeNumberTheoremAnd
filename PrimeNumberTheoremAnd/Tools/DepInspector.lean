import Lean

open Lean Meta Elab Command

namespace DepInspector

/-- Strip metadata nodes (so pattern matching is easier). -/
partial def consumeMData : Expr → Expr
  | .mdata _ e => consumeMData e
  | e          => e

/-- Collect all constants appearing in an expression. -/
partial def usedConstsAux (e : Expr) (s : Std.HashSet Name) : Std.HashSet Name :=
  match consumeMData e with
  | .const n _        => s.insert n
  | .app f a          => usedConstsAux a (usedConstsAux f s)
  | .lam _ t b _      => usedConstsAux b (usedConstsAux t s)
  | .forallE _ t b _  => usedConstsAux b (usedConstsAux t s)
  | .letE _ t v b _   => usedConstsAux b (usedConstsAux v (usedConstsAux t s))
  | .proj _ _ b       => usedConstsAux b s
  | .mdata _ b        => usedConstsAux b s
  | _                 => s

def usedConsts (e : Expr) : Std.HashSet Name :=
  usedConstsAux e {}

/-- Turn a HashSet into a deterministically-sorted array (by `toString`). -/
def sortedNames (s : Std.HashSet Name) : Array Name :=
  let xs : List Name := s.fold (init := []) (fun acc n => n :: acc)
  xs.toArray.qsort (fun a b => a.toString < b.toString)

/-- Direct (one-hop) deps from the *type* of a declaration. -/
def oneHopTypeDeps (decl : ConstantInfo) : Std.HashSet Name :=
  usedConsts decl.type

/-- Direct (one-hop) deps from the *value/proof term* of a declaration. -/
def oneHopValueDeps (decl : ConstantInfo) : Std.HashSet Name :=
  match decl.value? with
  | some v => usedConsts v
  | none   => {}

/-- Pretty-print a list of names as newline-separated text. -/
def formatNameList (title : String) (xs : Array Name) : String :=
  let lines := xs.toList.map (fun n => s!"  {n}")
  s!"{title} ({xs.size}):\n" ++ String.intercalate "\n" lines

/-- Get the binder list of a constant type (names + binder-info), in order. -/
partial def getForallBinders (ty : Expr) : Array (Name × BinderInfo) :=
  go (consumeMData ty) #[] where
    go (t : Expr) (acc : Array (Name × BinderInfo)) : Array (Name × BinderInfo) :=
      match consumeMData t with
      | .forallE n _ body bi => go body (acc.push (n, bi))
      | _                    => acc

/-- Decompose an application into (function, args) with args in left-to-right order. -/
def getAppFnArgs : Expr → Expr × Array Expr
  | .app f a =>
      let (fn, args) := getAppFnArgs f
      (fn, args.push a)
  | .mdata _ e =>
      getAppFnArgs e
  | e =>
      (e, #[])


/--
Traverse `e` under binder context, calling `k` on every subexpression.
We keep binder context readable by replacing bvars with local fvars via `withLocalDecl` / `withLetDecl`.
-/
partial def traverseWithCtx (e : Expr) (k : Expr → MetaM Unit) : MetaM Unit := do
  let e := consumeMData e
  k e
  match e with
  | .app f a =>
      traverseWithCtx f k
      traverseWithCtx a k
  | .lam n t b bi =>
      traverseWithCtx t k
      withLocalDecl n bi t fun x =>
        traverseWithCtx (b.instantiate1 x) k
  | .forallE n t b bi =>
      traverseWithCtx t k
      withLocalDecl n bi t fun x =>
        traverseWithCtx (b.instantiate1 x) k
  | .letE n t v b _ =>
      traverseWithCtx t k
      traverseWithCtx v k
      withLetDecl n t v fun x =>
        traverseWithCtx (b.instantiate1 x) k
  | .mdata _ b =>
      traverseWithCtx b k
  | .proj _ _ b =>
      traverseWithCtx b k
  | _ =>
      pure ()

/-- Command: print one-hop dependencies of a constant (type deps + value deps + union). -/
syntax (name := oneHopDepsCmd) "#one_hop_deps" ident : command

elab_rules : command
  | `(#one_hop_deps $id:ident) => do
      let rootName ← resolveGlobalConstNoOverload id
      liftTermElabM do
        let decl ← getConstInfo rootName

        let typeDeps := oneHopTypeDeps decl
        let valDeps  := oneHopValueDeps decl
        let mut all  := typeDeps
        all := valDeps.fold (init := all) (fun acc n => acc.insert n)
        all := all.erase rootName

        let typeArr := sortedNames (typeDeps.erase rootName)
        let valArr  := sortedNames (valDeps.erase rootName)
        let allArr  := sortedNames all

        logInfo m!"#one_hop_deps {rootName}\n\
          {formatNameList "Type deps" typeArr}\n\n\
          {formatNameList "Value/proof deps" valArr}\n\n\
          {formatNameList "Union" allArr}"

/-- Command: show how `dep` is applied inside the proof term of `root`. -/
syntax (name := showAppsCmd) "#show_apps" ident ident : command

elab_rules : command
  | `(#show_apps $rootId:ident $depId:ident) => do
      let rootName ← resolveGlobalConstNoOverload rootId
      let depName  ← resolveGlobalConstNoOverload depId
      liftTermElabM do
        let rootDecl ← getConstInfo rootName
        let depDecl  ← getConstInfo depName

        logInfo m!"#show_apps root={rootName} dep={depName}"

        match rootDecl.value? with
        | none =>
            logInfo m!"(root has no value/proof term; maybe it's an axiom?)"
        | some v =>
            let depBinders := getForallBinders depDecl.type

            logInfo m!"Declaration type of {depName}:\n  {← ppExpr depDecl.type}"

            let mut count : Nat := 0

            traverseWithCtx v (fun e => do
              let (fn, args) := getAppFnArgs e
              match consumeMData fn with
              | .const n _ =>
                  if n == depName then
                    count := count + 1
                    let ty ← inferType e
                    logInfo m!"\nOccurrence #{count}:\n  term: {← ppExpr e}\n  term type: {← ppExpr ty}"

                    -- Print explicit args (BinderInfo.default) paired with binder names when available.
                    let k := Nat.min depBinders.size args.size
                    if k > 0 then
                      logInfo m!"  explicit args:"
                      for i in [:k] do
                        let (bn, bi) := depBinders[i]!
                        if bi == BinderInfo.default then
                          logInfo m!"    {bn} := {← ppExpr args[i]!}"
              | _ => pure ()
            )

            if count == 0 then
              logInfo m!"No applications of {depName} found inside the proof term of {rootName}."
            else
              logInfo m!"\nTotal occurrences: {count}"

end DepInspector
