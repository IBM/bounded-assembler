import ParserAlpha.Basic

def posToNat (s : String.Pos) : Nat :=
  match s with
    | ⟨n⟩ => n

-- Custom find a substring position function (since Lean's string library is atrocious and doesn't have one)
def String.findSubstring (big sub : String) : Nat :=
  let bigLen := big.length
  let subLen := sub.length
  if subLen == 0 then 0 else
    let rec helper (counter : Nat) (matchLength : Nat) : Nat :=
      match counter with
        | 0 => if matchLength == subLen then (bigLen - counter) - matchLength else bigLen
        | n + 1 => if matchLength == subLen then (bigLen - counter) - matchLength
                    else if (big.get! ⟨bigLen - counter⟩) == (sub.get! ⟨matchLength⟩) then helper n (matchLength + 1)
                    else helper n 0
    helper bigLen 0

-- TODO: Make Safe!
def extractCommand (line : String) : String :=
  let dotIndex := (line.posOf '.')
  let droppedIdentifier := (line.drop (posToNat (dotIndex) + 1)).trim
  let cmdEnd := (droppedIdentifier.posOf ' ')
  let cmd := (droppedIdentifier.take (posToNat (cmdEnd) + 1)).trim
  cmd

-- Extract the formula after a pipe
def extractPipedFormula (line : String) : Formula :=
  newFormula (((((line.extract ⟨(line.findSubstring "|") +  1⟩ line.endPos).dropRightWhile (.!='}')).dropRight 1).dropWhile (.!='{')).drop 1).trim

--def line := "| {(Or  (= (0) x) (Not (= y (1))) )}"
--#eval extractPipedFormula "| {(Or  (= (0) x) (Not (= y (1))) )}"
--#eval (((((line.extract ⟨(line.findSubstring "|") +  1⟩ line.endPos).dropRightWhile (.!='}')).dropRight 1).dropWhile (.!='{')).drop 1).trim
--#eval newFormula "(Or  (= x x) True )"
