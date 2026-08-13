/-
Generator for `INDEX.tsv`, a flat searchable list of every declaration in this project.

Run it with `make index`, never by hand — it needs the library built, because the types come
from the compiled environment rather than from the sources.

Imported from the first attempt on 2026-08-13 and adapted. Four changes, all so that it runs
before there is any Lean: `import Lean` instead of the project's own modules; `modRoots` and
the stripped prefixes point at this project; the row list is only appended when it is
non-empty, so an empty index has no trailing blank line; and the header says what is going on
when the count is zero.

**How it indexes anything.** `collect` walks the compiled environment and keeps the
declarations whose defining module starts with one of `modRoots`. A module is in that
environment only if this file imports it, so the import list below is what the index covers:
add a line when a new module root lands, and the same root to `modRoots`.

`modRoots` is a list rather than one prefix because this project has no single module prefix
over its two halves: the specification is rooted at `Spec` and the analysis at `Analysis`.
Missing a root here is silent — its declarations are simply absent from the index.

Not part of any `lean_lib`, so `lake build` never sees it. Self-contained by the usual rule for
independent attempts: a project that wants an index should copy this and let the copy disagree,
rather than sharing it.
-/
import Lean

-- One line per module root the index should cover, and one entry per root in `modRoots`
-- below. Each is a library root that imports its own half, so this list stays two lines as
-- files are added under either.
import Spec
import Analysis

open Lean Lean.Meta

namespace Decoupled.DeclIndex

/-- Where the index is written, relative to the repository root. -/
def outPath : System.FilePath := "INDEX.tsv"

/-- Only modules under one of these roots are indexed. One entry per `lean_lib` root; see the
    file header on why this is a list. -/
def modRoots : List String := ["Spec", "Analysis"]

/-- Name fragments that only ever occur in declarations the elaborator generated. -/
def noiseFragments : List String :=
  [".proof_", ".eq_", ".match_", ".sizeOf_spec", ".injEq", ".noConfusion",
   ".casesOn", ".recOn", ".brecOn", ".below", ".ibelow", ".rec", ".mk.inj",
   ".ofNat", ".toCtorIdx", "._", ".eq_def", ".induct", ".fun_cases",
   ".ctorIdx", ".congr_simp", ".congr", ".sizeOf", ".toString", ".beq",
   ".decEq", ".repr", ".hash", "instDecidable", ".unfold"]

def isNoise (n : Name) : Bool :=
  n.isInternal ||
    noiseFragments.any (fun s => decide (((toString n).splitOn s).length > 1))

/-- Collapse every run of whitespace to one space, and drop the namespaces a reader of
    this file always supplies from context. Collapsing is what makes a tab safe as the
    field separator: no field can then contain one. -/
def tidy (s : String) : String :=
  let s := s.replace "Decoupled." "" |>.replace "Framework.StsMultisetLog." ""
             |>.replace "Execution." ""
  let s := s.replace "\n" " " |>.replace "\t" " "
  String.intercalate " " ((s.splitOn " ").filter (· != ""))

/-- Binders no row should carry: instances and type variables are the same on every
    declaration, so printing them is noise that buries the rest.

    Inherited from the first attempt, whose declarations all carried a `Schedule` binder.
    Revisit it against this project's own statements rather than assuming it still fits. -/
def suppressed (bi : BinderInfo) (ty : String) : Bool :=
  bi == .instImplicit || ty == "Type" || ty == "Prop"
    || ty.startsWith "Schedule " || ty.startsWith "outParam"

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "rec"

/-- One row: kind, name, location, conclusion, hypotheses.

    For a theorem the binders worth listing are its hypotheses, so only the
    propositional ones are kept; a `def`'s signature is the whole point of the row, so
    its data binders stay. -/
def row (n : Name) (ci : ConstantInfo) (loc : String) : MetaM (Option String) := do
  forallTelescope ci.type fun xs concl => do
    let isThm := ci matches .thmInfo _
    let mut hyps : Array String := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let ty := tidy (toString (← ppExpr d.type))
      let keep ← if isThm then isProp d.type else pure true
      if keep && !suppressed d.binderInfo ty then
        hyps := hyps.push ty
    let concl := tidy (toString (← ppExpr concl))
    let hypStr := String.intercalate " | " hyps.toList
    -- inaccessible names (`✝`) appear only in machine-generated statements
    if concl.any (· == '✝') || hypStr.any (· == '✝') then return none
    let short := (toString n).replace "Decoupled." ""
    return some s!"{kindOf ci}\t{short}\t{loc}\t{concl}\t{hypStr}"

def collect : MetaM (Array String) := do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if isNoise n then continue
    if ci matches .ctorInfo _ | .recInfo _ | .quotInfo _ then continue
    if env.isProjectionFn n then continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    -- An explicit lambda, not `.startsWith` partially applied: `String.startsWith` takes a
    -- pattern with an instance argument, so the point-free form does not unify with
    -- `String → Bool`.
    unless modRoots.any (fun r => (toString modName).startsWith r) do continue
    let loc ← match ← findDeclarationRanges? n with
      | some r => pure s!"{modName}:{r.range.pos.line}"
      | none => pure (toString modName)
    match ← row n ci loc with
    | some s => out := out.push s
    | none => pure ()
  return out.qsort (fun a b =>
    (a.splitOn "\t").getD 1 "" < (b.splitOn "\t").getD 1 "")

def header (count : Nat) : String :=
  "# Every declaration in THIS project, one per line, sorted by name.\n" ++
  "# GENERATED — do not edit. Regenerate with `make index`.\n" ++
  s!"# {count} declarations.\n" ++
  (if count == 0 then
     "#\n" ++
     "# Zero because this file indexes only the modules it imports, and only those whose\n" ++
     "# name starts with one of its `modRoots`. Check both lists at the top of\n" ++
     "# `tools/decl_index.lean`.\n"
   else "") ++
  "#\n" ++
  "# Fields, tab-separated: kind, name, file:line, conclusion, hypotheses.\n" ++
  "# Hypotheses are ` | `-separated; for a theorem they are its propositional binders,\n" ++
  "# for a def its whole signature.\n" ++
  "#\n" ++
  "# Dropped, because every declaration carries the same ones and they bury the rest:\n" ++
  "# instance binders, bare type variables, and the schedule. The `Decoupled.` and\n" ++
  "# `Framework.StsMultisetLog.` prefixes are stripped. So a row is a search key, not a\n" ++
  "# statement you can paste into Lean.\n" ++
  "#\n" ++
  "# Looking for a lemma whose *statement* you know but whose name you do not? Prefer\n" ++
  "# `exact?` on the goal — it matches up to unification, which grep cannot.\n" ++
  "#\n" ++
  "# An earlier formalization of the same paper has its own index of 975 declarations.\n" ++
  "# It is not in this repository and no path to it is recorded here.\n"

end Decoupled.DeclIndex

open Decoupled.DeclIndex in
#eval show CoreM Unit from do
  let rows ← MetaM.run' collect
  -- No trailing blank line when there are no rows.
  let body := if rows.isEmpty then "" else String.intercalate "\n" rows.toList ++ "\n"
  IO.FS.writeFile outPath (header rows.size ++ body)
  IO.println s!"wrote {outPath} — {rows.size} declarations"
