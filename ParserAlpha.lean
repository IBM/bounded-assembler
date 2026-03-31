import ParserAlpha.Basic
import ParserAlpha.Parsing
import Std.Data.HashMap

--open ParserAlpha.Parsing

def mergeListsNoDuplicates (l1 : List String) (l2 : List String) : List String :=
  l1.foldr (λ a b => (b.insert a)) l2


def allIDsInHashMap (ids : List String) (hm : Std.HashMap String Formula) : Bool :=
  ids.foldr (λ id truth => truth && hm.contains id) true





-- Extract if a term or formula "let formula|term ... be ..." command
-- False is formula and True is term
def formulaOrTermLet (line : String) : Bool :=
  let termPos := line.findSubstring "term"
  let formPos := line.findSubstring "formula"
  if termPos < line.length && formPos < line.length then

    if termPos < formPos then true else false

  else if (termPos < line.length) then
    true
  else
    false

-- Check piped formula equals rule output

def pipeCheck (f_output : Formula) (f_pipe : String) : Bool :=
  let piped_form := newFormula f_pipe
  piped_form == f_output && (match piped_form with | Formula.ERROR _ => false | _ => true)

--#eval extractCommand "aef. assume sdf"

-- #eval newTerm "(f (g x y) y)"
-- #eval (newFormula "(ForAll X (= X X))")

-- Strategy: Search for the 2nd command and backtrack. Remove new line characters from there.

def extractNextLine (file : String) : String × String :=
  if (file.split (.== '.')).length < 3 then -- last line!
    (file, "")
  else -- Multiple lines
    let removedFirstDot := (file.dropWhile (. != '.')).drop 1
    let dotPos := posToNat (removedFirstDot.find (.=='.'))
    -- First line extracted by reverse find of new line.
    let lastNewLineIndex : Nat := match (removedFirstDot.take dotPos).revPosOf '\n' with | some ⟨n⟩ => n | none => 0
    let untrimmedLine := file.take ((file.length - removedFirstDot.length) + lastNewLineIndex)
    ((untrimmedLine.replace "\n" " ").trim, file.drop (untrimmedLine.length + 1))

-- #eval extractNextLine "this. is a line\n  blah  \nmore stuff on this line\n  line2. sdfdf\n\nsdfds\n"
-- #eval extractNextLine "this. is a line"
-- #eval extractCommand "sdfdsfkkkk. sdfsdf vvvvvsdfsdf"

-- From a line, parse the arguments and return a list.
-- Params will be of form {formula} or {term}

def extractCommandParams (line : String) : List String :=
  let rec helper (line : String) (stored : String) (inParam : Bool) (params : List String) (counter : Nat) : List String :=
    match counter with
      | 0 => params
      | n + 1 => if line.get! ⟨0⟩ == '{' then
      helper (line.drop 1) "" true params (n)
    else if line.get! ⟨0⟩ == '}' then
      helper (line.drop 1) "" false (params.append [stored]) (n)
    else if inParam then
      helper (line.drop 1) (stored.append (line.take 1)) true params (n)
    else
      helper (line.drop 1) stored false params (n)

  helper line "" false [] line.length

def extractAxiomSubstParams (line : String) : List String :=
  if !line.contains '/' then [] -- no substitutions
  else
    let rec helper (line : String) (stored : String) (inParam : Bool) (params : List String) (counter : Nat) : List String :=
    match counter with
      | 0 => params
      | n + 1 => if line.get! ⟨0⟩ == '[' then
      helper (line.drop 1) "" true params (n)
    else if line.get! ⟨0⟩ == ']' then
      helper (line.drop 1) "" false (params.append [stored]) (n)
    else if inParam then
      helper (line.drop 1) (stored.append (line.take 1)) true params (n)
    else
      helper (line.drop 1) stored false params (n)

    let substParams := (helper line "" false [] line.length)
    let split : List (List String) := substParams.map (λ a => a.split (.=='/'))
    match split with
      | [_, xname] :: [] => [xname.trim]
      | [x, xname] :: [_, yname] :: [] => if x.trim == "x" then [xname.trim, yname.trim] else [yname.trim, xname.trim]
      | _ => []

--#eval extractAxiomSubstParams "1234. axiom 1 [x  / α] [y/ β]"
--#eval (("10. mark 1234 5678 | 23423".drop ("10. mark 1234 5678 | 23423".findSubstring "mark"+5)).split (.==' '))[0]!

-- Parse line into the appropriate operation
-- Note: "let" produces either a formula × formula pair or a term × term pair (alias, actual)
--       "assume" produces a formula
--       "mark" produces a marked formula
--       "axiom" produces a formula
--       all others produce an NDRule
--       Every response additionally returns a list of assumptions for the output formula. This list is empty for let...be, and for axiom
def extractOperation (line : String) (id2fmla : Std.HashMap String Formula) (id2marked_fmla : Std.HashMap String MarkedFormula) (id2assump : Std.HashMap String (List String)) : ((NDRule ⊕ Formula) ⊕ (MarkedFormula ⊕ ((Formula × Formula) ⊕ (Term × Term)))) × (List String) :=
  let lineID := line.trim.extract ⟨0⟩ ⟨line.trim.findSubstring "."⟩
  let linePostID := line.extract ⟨((line.findSubstring ".") + 1)⟩ line.endPos
  let linePrePipe := line.extract ⟨0⟩ ⟨line.findSubstring "|"⟩
  match extractCommand line with
    | "assume" =>  -- assume [formula_raw]
                    match extractCommandParams line with
                      | f :: [] =>
                                  (Sum.inl (Sum.inr (newFormula f)), [lineID])
                      | _ => (Sum.inl (Sum.inr (Formula.ERROR "Bad assume command!")),[])

    -- | "let" => -- let formula|term [formula|term] be [alias]
    --             match extractCommandParams line with
    --               | ft1 :: ft2 :: [] => if (formulaOrTermLet line) then
    --                                       Sum.inr (Sum.inr (Sum.inr ((newTerm ft1), (newTerm ft2))))
    --                                     else Sum.inr (Sum.inr (Sum.inl ((newFormula ft1), (newFormula ft2))))
    --               | _ => Sum.inl (Sum.inr (Formula.ERROR "Bad let command!"))

    | "axiom" => -- axiom [nat] [substitution1 (optional)] [substitution2 (optional)]
                let substs := extractAxiomSubstParams line
                let axiomId := match substs with | [] => (line.extract ⟨line.findSubstring "axiom" + 5⟩ ⟨line.length⟩).trim.toNat!
                                                 | _ => (line.extract ⟨line.findSubstring "axiom" + 5⟩ (line.find (.=='['))).trim.toNat!
                let genAxiom : Formula := newAxiom axiomId
                if substs.length == 0 then ((Sum.inl (Sum.inr genAxiom)),[]) -- No substitutions to make
                else if substs.length == 1 then (Sum.inl (Sum.inr (genAxiom.subAndReplace (Term.var substs.head!) (Term.var "x"))), []) -- x substitution
                else (Sum.inl (Sum.inr ((genAxiom.subAndReplace (Term.var substs.head!) (Term.var "x")).subAndReplace (Term.var substs.tail.head!) (Term.var "y"))), []) -- x and y substitution

    | "mark" =>
                if line.contains '{' then
                  let forms := (extractCommandParams line)
                  let id_of_marked : String := ((line.drop (line.findSubstring "mark"+5)).split (.==' '))[0]!.trim
                  if forms.length == 1 then
                    let gen_fmla := newMarkedFormula forms[0]!
                    if id2fmla.contains id_of_marked then
                      let curr_fmla : Formula := (id2fmla[id_of_marked]!)
                      if (some gen_fmla.toUnlabeled) == curr_fmla then
                        (Sum.inr (Sum.inl (gen_fmla)),id2assump[id_of_marked]!)
                      else
                        (Sum.inl (Sum.inr (Formula.ERROR "Bad mark command! The marked formula doesn't match the original")),[])
                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad mark command! The id of the original line doesn't exist!")),[])
                  else (Sum.inl (Sum.inr (Formula.ERROR "Bad mark command! Incorrect number of arguments")),[])
                else
                  (Sum.inl (Sum.inr (Formula.ERROR "Bad mark command! Incorrect number of arguments")),[])

       | "andI" =>
                  -- Grab two prev formula ids
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "andI") + 5⟩ ⟨line.findSubstring "|"⟩).split (.==' '))
                  if ids.length == 2 && id2fmla.contains ids[0]! && id2fmla.contains ids[1]! then
                    let new_assumps : List String := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                    let A := id2fmla[ids[0]!]!
                    let B := id2fmla[ids[1]!]!
                    ((Sum.inl (Sum.inl (NDRule.AndIntro A B))), new_assumps)
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad andI command! Incorrect number of arguments, or incorrect line identifiers")),[])



       | "andE-left" => -- andE-left [formula_id]
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "andE-left") + 10⟩ ⟨line.findSubstring "|"⟩).split (.==' '))
                  if ids.length == 1 && id2fmla.contains ids[0]! then
                    let new_assumps : List String := id2assump[ids[0]!]!
                    let AandB := id2fmla[ids[0]!]!
                    ((Sum.inl (Sum.inl (NDRule.AndElimLeft AandB))), new_assumps)
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad andE-left command! Incorrect number of arguments, or incorrect line identifiers")),[])
        | "andE-right" => -- andE-right [formula_id]
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "andE-right") + 11⟩ ⟨line.findSubstring "|"⟩).split (.==' '))
                  if ids.length == 1 && id2fmla.contains ids[0]! then
                    let new_assumps : List String := id2assump[ids[0]!]!
                    let AandB := id2fmla[ids[0]!]!
                    ((Sum.inl (Sum.inl (NDRule.AndElimRight AandB))), new_assumps)
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad andE-left command! Incorrect number of arguments, or incorrect line identifiers")),[])

       | "orI-left" => -- orI-left [formula_id] [formula_id|formula_raw]

                if line.findSubstring "{" < line.findSubstring "|" then
                  let id := (line.extract ⟨(line.findSubstring "orI-left") + 9⟩ ⟨line.findSubstring "{"⟩).trim
                  if !id2fmla.contains id then
                  (Sum.inl (Sum.inr (Formula.ERROR "Bad orI-left command! Identifier doesn't exist")),[])
                  else
                    let A := id2fmla[id]!
                    let new_assumps := id2assump[id]!
                    let fmla := newFormula (extractCommandParams line)[0]!
                    ((Sum.inl (Sum.inl (NDRule.OrIntroLeft A fmla))), new_assumps)
                else
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "orI-left") + 9⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length != 2 || !id2fmla.contains ids[0]! || !id2fmla.contains ids[1]! then (Sum.inl (Sum.inr (Formula.ERROR "Bad orI-left command! Incorrect number of arguments, or bad identifiers!")),[])
                  else
                  let A := id2fmla[ids[0]!]!
                  let B := id2fmla[ids[1]!]!
                  let new_assumps := id2assump[ids[0]!]!
                  ((Sum.inl (Sum.inl (NDRule.OrIntroLeft A B))), new_assumps)
       | "orI-right" => -- orI-right [formula_id] [formula_id|formula_raw]

                if line.findSubstring "{" < line.findSubstring "|" then
                  let id := (line.extract ⟨(line.findSubstring "orI-right") + 10⟩ ⟨line.findSubstring "{"⟩).trim
                  if !id2fmla.contains id then
                  (Sum.inl (Sum.inr (Formula.ERROR "Bad orI-left command! Identifier doesn't exist")),[])
                  else
                    let A := id2fmla[id]!
                    let new_assumps := id2assump[id]!
                    let fmla := newFormula (extractCommandParams line)[0]!
                    ((Sum.inl (Sum.inl (NDRule.OrIntroRight A fmla))), new_assumps)
                else
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "orI-left") + 9⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length != 2 || !id2fmla.contains ids[0]! || !id2fmla.contains ids[1]! then (Sum.inl (Sum.inr (Formula.ERROR "Bad orI-left command! Incorrect number of arguments, or bad identifiers!")),[])
                  else
                  let A := id2fmla[ids[0]!]!
                  let B := id2fmla[ids[1]!]!
                  let new_assumps := id2assump[ids[0]!]!
                  ((Sum.inl (Sum.inl (NDRule.OrIntroRight A B))), new_assumps)


       | "orE" => -- orE [formula_id] [formula_id] [formula_id] [formula_id] [formula_id] (AorB  A B C C)
                let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "orE") + 4⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                if ids.length == 5 then
                  if allIDsInHashMap ids id2fmla then
                    let AorB := id2fmla[ids[0]!]!
                    let A := id2fmla[ids[1]!]!
                    let B := id2fmla[ids[2]!]!
                    let C1 := id2fmla[ids[3]!]!
                    let C2 := id2fmla[ids[4]!]!

                    if C1 == C2 && id2assump[ids[3]!]!.contains ids[1]! && id2assump[ids[4]!]!.contains ids[2]! then
                      let new_assumps := (mergeListsNoDuplicates (id2assump[ids[0]!]!)
                       (mergeListsNoDuplicates (id2assump[ids[3]!]!) (id2assump[ids[4]!]!))).filter (λ a => a != ids[1]! && a != ids[2]!)

                      ((Sum.inl (Sum.inl (NDRule.OrElim AorB A B C1))), new_assumps)
                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad orE command! Assumption IDs are wrong!")),[])
                  else
                   (Sum.inl (Sum.inr (Formula.ERROR "Bad orE command! Some IDs don't exist!")),[])

                else
                  (Sum.inl (Sum.inr (Formula.ERROR "Bad orE command! Incorrect number of arguments!")),[])

       | "impliesI" =>
                    let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "impliesI") + 9⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                    if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let A := id2fmla[ids[0]!]!
                      let B := id2fmla[ids[1]!]!

                      if id2assump[ids[1]!]!.contains ids[0]! then
                        let new_assumps := id2assump[ids[1]!]!.filter (λ a => a != ids[0]!)
                        ((Sum.inl (Sum.inl (NDRule.ImplIntro A B))), new_assumps)
                      else
                        (Sum.inl (Sum.inr (Formula.ERROR "Bad impliesI command! Invalid assumption!")),[])
                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad impliesI command! Incorrect number of arguments, or invalid identifiers!")),[])

        | "iffI" =>
                    let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "iffI") + 5⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                    if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let AimB := id2fmla[ids[0]!]!
                      let BimA := id2fmla[ids[1]!]!
                      let new_assumps := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.IffIntro AimB BimA))), new_assumps)

                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad iffI command! Incorrect number of arguments, or invalid identifiers!")),[])

       | "impliesE" =>
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "impliesE") + 9⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let A := id2fmla[ids[0]!]!
                      let AimplB := id2fmla[ids[1]!]!
                      let new_assumps := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.ImplElim A AimplB))), new_assumps)
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad impliesI command! Incorrect number of arguments, or invalid identifiers!")),[])

       | "iffE-left" =>
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "iffE-left") + 10⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let A := id2fmla[ids[0]!]!
                      let AiffB := id2fmla[ids[1]!]!
                      let new_assumps := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.IffElimLeft A AiffB))), new_assumps)
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad iffE-left command! Incorrect number of arguments, or invalid identifiers!")),[])

       | "iffE-right" =>
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "iffE-right") + 11⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let B := id2fmla[ids[0]!]!
                      let AiffB := id2fmla[ids[1]!]!
                      let new_assumps := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.IffElimLeft B AiffB))), new_assumps)
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad iffE-left command! Incorrect number of arguments, or invalid identifiers!")),[])

       | "notI" =>

                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "notI") + 5⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))

                  if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let A := id2fmla[ids[0]!]!
                      let Bot := id2fmla[ids[1]!]!
                      if id2assump[ids[1]!]!.contains ids[0]! then
                        let new_assumps := id2assump[ids[1]!]!.filter  (λ a => a != ids[0]!)
                        ((Sum.inl (Sum.inl (NDRule.NotIntro A Bot))), new_assumps)
                      else
                         (Sum.inl (Sum.inr (Formula.ERROR "Bad notI command! Incorrect assumption!")),[])
                  else
                     (Sum.inl (Sum.inr (Formula.ERROR "Bad notI command! Incorrect number of arguments, or invalid identifiers!")),[])
       | "notE" =>
                 let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "notE") + 5⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let A := id2fmla[ids[0]!]!
                      let nA := id2fmla[ids[1]!]!
                      let new_assumps := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.ImplElim A nA))), new_assumps)
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad notE command! Incorrect number of arguments, or invalid identifiers!")),[])

       | "falseI" =>
                  if line.findSubstring "{" < line.findSubstring "|" then
                  let id := (line.extract ⟨(line.findSubstring "falseI") + 7⟩ ⟨line.findSubstring "{"⟩).trim
                  if !id2fmla.contains id then
                  (Sum.inl (Sum.inr (Formula.ERROR "Bad falseI command! Identifier doesn't exist")),[])
                  else
                    let flse := id2fmla[id]!
                    let new_assumps := id2assump[id]!
                    let fmla := newFormula (extractCommandParams line)[0]!
                    ((Sum.inl (Sum.inl (NDRule.FalseIntro flse fmla))), new_assumps)
                else
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "falseI") + 7⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length != 2 || !id2fmla.contains ids[0]! || !id2fmla.contains ids[1]! then (Sum.inl (Sum.inr (Formula.ERROR "Bad falseI command! Incorrect number of arguments, or bad identifiers!")),[])
                  else
                  let flse := id2fmla[ids[0]!]!
                  let B := id2fmla[ids[1]!]!
                  let new_assumps := id2assump[ids[0]!]!
                  ((Sum.inl (Sum.inl (NDRule.FalseIntro flse B))), new_assumps)

       | "falseE" =>
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "falseE") + 7⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))

                  if ids.length == 2 && allIDsInHashMap ids id2fmla then
                      let nA := id2fmla[ids[0]!]!
                      let Bot := id2fmla[ids[1]!]!
                      if id2assump[ids[1]!]!.contains ids[0]! then
                        let new_assumps := id2assump[ids[1]!]!.filter  (λ a => a != ids[0]!)
                        ((Sum.inl (Sum.inl (NDRule.NotIntro nA Bot))), new_assumps)
                      else
                         (Sum.inl (Sum.inr (Formula.ERROR "Bad falseE command! Incorrect assumption!")),[])
                  else
                     (Sum.inl (Sum.inr (Formula.ERROR "Bad falseE command! Incorrect number of arguments, or invalid identifiers!")),[])
       | "forAllI" =>
                    let ids_vars := removeEmptyEntries ((line.extract ⟨(line.findSubstring "forAllI") + 8⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids_vars.length == 3 && id2fmla.contains ids_vars[0]! then
                      let A := id2fmla[ids_vars[0]!]!
                      let freevar := ids_vars[1]!
                      let boundvar := ids_vars[2]!
                      if A.varIsFree (newTerm freevar) then
                        let new_assumps := id2assump[ids_vars[0]!]!
                        ((Sum.inl (Sum.inl (NDRule.ForAllIntro A freevar boundvar))), new_assumps)
                      else
                         (Sum.inl (Sum.inr (Formula.ERROR "Bad forAllI command! This variable is not free!")),[])
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad forAllI command! Incorrect number of arguments, or invalid identifiers!")),[])

       | "existsI" =>
                    let var_label := removeEmptyEntries ((line.extract ⟨(line.findSubstring "}") + 1⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                    let fmla_id := (line.extract ⟨(line.findSubstring "existsI") + 8⟩ ⟨line.findSubstring "{" ⟩).trim
                    let term := newTerm (line.extract ⟨(line.findSubstring "{")+1⟩ ⟨(line.findSubstring "}")⟩).trim
                    if id2fmla.contains fmla_id then
                      let fmla := id2fmla[fmla_id]!
                      if !(fmla.containsTerm term) then
                        (Sum.inl (Sum.inr (Formula.ERROR "Bad existsI command! Term provided is not in the formula!")),[])
                      else
                        let new_assumps := id2assump[fmla_id]!

                        ((Sum.inl (Sum.inl (NDRule.ExistsIntro fmla term var_label[0]!))), new_assumps)

                    else if id2marked_fmla.contains fmla_id then
                      let fmla := id2marked_fmla[fmla_id]!
                      if !(fmla.toUnlabeled.containsTerm term) then
                        (Sum.inl (Sum.inr (Formula.ERROR "Bad existsI command! Term provided is not in the formula!")),[])
                      else
                        let new_assumps := id2assump[fmla_id]!

                        ((Sum.inl (Sum.inl (NDRule.ExistsIntroMarked fmla term var_label[0]! var_label[1]!))), new_assumps)

                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad existsI command! Invalid identifier!")),[])

       | "forAllE" =>
                     if line.findSubstring "{" < line.findSubstring "|" then
                        let id := (line.extract ⟨(line.findSubstring "forAllE") + 8⟩ ⟨line.findSubstring "{"⟩).trim
                        if !id2fmla.contains id then
                        (Sum.inl (Sum.inr (Formula.ERROR "Bad forAllE command! Identifier doesn't exist")),[])
                        else
                          let A := id2fmla[id]!
                          let new_assumps := id2assump[id]!
                          let t := newTerm (extractCommandParams line)[0]!
                          ((Sum.inl (Sum.inl (NDRule.ForAllElim A t))), new_assumps)
                     else (Sum.inl (Sum.inr (Formula.ERROR "Bad forAllE command! No term provided!")),[])
       | "existsE" =>
                      let idExA := removeEmptyEntries ((line.extract ⟨(line.findSubstring "existsE") + 8⟩ ⟨line.findSubstring "{"⟩).trim.split (.==' '))
                      let ids := idExA.append (removeEmptyEntries ((line.extract ⟨(line.findSubstring "}") + 1⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' ')))
                      let params := extractCommandParams linePrePipe
                      if ids.length == 3 then
                        if allIDsInHashMap ids id2fmla then
                          let ExistsA := id2fmla[ids[0]!]!

                          let A := id2fmla[ids[1]!]!
                          let C := id2fmla[ids[2]!]!
                          if params.length != 1 then
                            (Sum.inl (Sum.inr (Formula.ERROR "Bad existsE command! No Term provided!")),[])
                          else

                          let t := newTerm params[0]!

                          if id2assump[ids[2]!]!.contains ids[1]! then
                            let new_assumps := mergeListsNoDuplicates id2assump[ids[0]!]! (id2assump[ids[2]!]!.filter (.!=ids[1]!))

                            ((Sum.inl (Sum.inl (NDRule.ExistsElim ExistsA t A C))), new_assumps)
                          else
                            (Sum.inl (Sum.inr (Formula.ERROR "Bad existsE command! Assumption IDs are wrong!")),[])
                        else
                        (Sum.inl (Sum.inr (Formula.ERROR "Bad existsE command! Some IDs don't exist!")),[])

                      else
                        (Sum.inl (Sum.inr (Formula.ERROR "Bad existsE command! Incorrect number of arguments!")),[])

       | "=Refl" =>
                  let terms := extractCommandParams linePrePipe
                  if terms.length == 1 then
                    let t := newTerm terms[0]!
                    ((Sum.inl (Sum.inl (NDRule.Refl t))), [])
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad =Refl command! Incorrect number of arguments!")),[])

       | "=Symm" =>
                  let fmlas := removeEmptyEntries ((line.extract ⟨(line.findSubstring "=Symm") + 6⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if fmlas.length == 1 then
                    let fmla := fmlas[0]!
                    if id2fmla.contains fmla then
                      let sEQt := id2fmla[fmla]!
                      ((Sum.inl (Sum.inl (NDRule.Symm sEQt))), id2assump[fmla]!)

                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad =Symm command! No such identifier exists!")),[])

                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad =Symm command! Incorrect number of arguments!")),[])



       | "=Trans" =>
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "=Trans") + 7⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length == 2 then

                    if allIDsInHashMap ids id2fmla then

                      let rEQs := id2fmla[ids[0]!]!
                      let sEQt := id2fmla[ids[1]!]!
                      let new_assump := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.Trans rEQs sEQt))), new_assump)

                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad =Trans command! An identifier doesn't exists!")),[])

                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad =Trans command! Incorrect number of arguments!")),[])

       | "=Subst" =>
                  let ids := removeEmptyEntries ((line.extract ⟨(line.findSubstring "=Subst") + 7⟩ ⟨line.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length == 2 then -- unlabeled

                    if allIDsInHashMap ids id2fmla then

                      let sEQt := id2fmla[ids[0]!]!
                      let A := id2fmla[ids[1]!]!
                      let new_assump := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.Subst sEQt A))), new_assump)

                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad =Subst command! An identifier doesn't exists!")),[])

                  else if ids.length == 3 then
                    if allIDsInHashMap (ids.take 1) id2fmla && id2marked_fmla.contains ids.tail!.head! then
                      let sEQt := id2fmla[ids[0]!]!
                      let A := id2marked_fmla[ids[1]!]!
                      let label := ids[2]!
                      let new_assump := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.SubstMarked sEQt A label))), new_assump)

                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad =Subst command! An identifier doesn't exists!")),[])
                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad =Subst command! Incorrect number of arguments!")),[])
      | "induct" =>
                  let ids := removeEmptyEntries ((linePostID.extract ⟨(linePostID.findSubstring "induct") + 7⟩ ⟨linePostID.findSubstring "|"⟩).trim.split (.==' '))
                  if ids.length == 2 then

                    if allIDsInHashMap ids id2fmla then

                      let base := id2fmla[ids[0]!]!
                      let hyp := id2fmla[ids[1]!]!
                      let new_assump := mergeListsNoDuplicates id2assump[ids[0]!]! id2assump[ids[1]!]!
                      ((Sum.inl (Sum.inl (NDRule.Ind base hyp))), new_assump)

                    else
                      (Sum.inl (Sum.inr (Formula.ERROR "Bad induct command! An identifier doesn't exists!")),[])

                  else
                    (Sum.inl (Sum.inr (Formula.ERROR "Bad induct command! Incorrect number of arguments!")),[])
    | _ => (Sum.inl (Sum.inr (Formula.ERROR "Bad Command!")),[])

--#eval extractOperation "1337. axiom 2 [x / t] [y/m]"
--#eval extractOperation "1337. mark 1 {(= /sum(S (0)) (S (0)))}" (Std.HashMap.emptyWithCapacity.insert "1" (newFormula "(= (S (0)) (S (0)))") : Std.HashMap String Formula) (Std.HashMap.emptyWithCapacity : Std.HashMap String MarkedFormula) ((Std.HashMap.emptyWithCapacity).insert "1" ["abc"] : Std.HashMap String (List String))

--#eval extractOperation "1337. andI 1 2 | {(And True True)}" ((Std.HashMap.emptyWithCapacity.insert "1" (newFormula "(= (S (0)) (S (0)))")).insert "2" (newFormula "(= (0) (0))") : Std.HashMap String Formula) (Std.HashMap.emptyWithCapacity : Std.HashMap String MarkedFormula)(((Std.HashMap.emptyWithCapacity).insert "1" ["abc"]).insert "2" [""] : Std.HashMap String (List String))
