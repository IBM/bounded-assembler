import ParserAlpha.Parsing
import Std.Data.HashMap
import Std.Data.HashSet
import ParserAlpha.Basic


-- Extracts the formula at the end of the pipe
def extractLastLine (file : System.FilePath) : IO Formula := do
  let contents : String <- IO.FS.readFile file
  match contents.revFind (. == '|') with
    | some ⟨idx⟩ => return extractPipedFormula (contents.drop (idx))
    | none => return Formula.ERROR "No Conclusion in this import!"


--def mergeHashMapsNoDuplicates (hm1 : Std.HashMap String Formula) (hm2 : Std.HashMap String Formula) : Std.HashMap String Formula :=


-- Main recursive function to collect imports and return a hashmap id2formula of an initial namespace
--TODO: Update after implementing the def command to also return hashmap of defined funcs and preds.

-- partial def gatherImports (file : String) : IO (Std.HashMap String Formula) := do



--     let rec helper (counter : Nat) (f : String) : IO (Std.HashMap String Formula) :=

--       match counter with
--         | 0 => pure ((Std.HashMap.emptyWithCapacity : Std.HashMap String Formula))
--         | n + 1 =>
--           let imprtXsubfile : Option (String × String) := parseImportLine f
--           match imprtXsubfile with
--             -- If parseImportLine gives none, then we stop
--             | none => pure (Std.HashMap.emptyWithCapacity : Std.HashMap String Formula)

--             -- Recurse on an import. Need IO here
--             | some (fname, subfile) => do
--               if
--               let file_contents <- readFile fname
--               let prev <- (helper file_contents.length file_contents)
--               let prevNamespace := (prev.insert fname (extractLastLine file_contents))

--               -- Recurse on next line in the file
--                pure Std.HashMap.union prevNamespace (helper n subfile)
--     let f <- file
--     helper f.length f

open System

def moduleToPath (mod : String) : FilePath :=
  (mod.splitOn ".").foldl (· / ·) ("." : FilePath) |>.withExtension "pv"


def parseImports (contents : String) : List String :=
  contents.splitOn "\n"
  |>.takeWhile (·.trim.startsWith "import ")
  |>.map (fun line =>
    line.trim.drop 7 |>.trim)  -- remove "import " and trim whitespace

partial def gatherImports (start : FilePath) (seen : IO.Ref (Std.HashSet FilePath)) : IO (List FilePath) := do
  let canonical ← IO.FS.realPath start
  --let canonical := start
  let alreadySeen ← seen.get
  if alreadySeen.contains canonical then
    return []
  else
    seen.modify (·.insert canonical)

  let contents ← IO.FS.readFile canonical
  let imports := parseImports contents
  let baseDir := System.FilePath.parent canonical -- directory of current file

  let mut allDeps := [canonical]
  for imp in imports do
    let depFile := baseDir.get! / (moduleToPath imp)
    let recDeps ← gatherImports depFile seen
    allDeps := allDeps ++ recDeps
  return allDeps

def extractName (f : FilePath) : String :=
  match f.fileName with
    | some name => name.replace "/" "" |>.dropRight 3
    | none => ""

def removeImports (file : String) : String :=
  (file.splitOn "\n").foldr (λ a b => if a.startsWith "import " then b else a.append "\n" |>.append b) ""


def collectImportedFormulas (entry : FilePath) :  IO ((Std.HashMap String Formula) × String) := do
  let seen ← IO.mkRef ({} : Std.HashSet FilePath)
  let importFiles ← (gatherImports entry seen)
  let mut formulas : Std.HashMap String Formula := Std.HashMap.emptyWithCapacity
  for file in importFiles do
    let form <- extractLastLine file
    if file != entry then
      formulas := formulas.insert (extractName file) (form)
  let mainPf <- IO.FS.readFile entry
  return (formulas, (removeImports mainPf))
