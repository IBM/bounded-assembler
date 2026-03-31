-- Here, we define our Term and Formula types

inductive Term  : Type
  | func : String -> List Term -> Term --function, args
  | plus : Term -> Term -> Term
  | times : Term -> Term -> Term
  | succ : Term -> Term
  | len : Term -> Term
  | smash : Term -> Term -> Term
  | var : String -> Term --var name
  | zero : Term
  -- | one : Term
  -- | two : Term
  | bitshift : Term -> Term -> Term
  | ERROR : String -> Term
deriving Repr, BEq


inductive MarkedTerm : Type
  | func : String -> String -> List MarkedTerm -> MarkedTerm --function, args
  | plus : String -> MarkedTerm -> MarkedTerm -> MarkedTerm
  | times : String -> MarkedTerm -> MarkedTerm -> MarkedTerm
  | succ : String -> MarkedTerm -> MarkedTerm
  | len : String -> MarkedTerm -> MarkedTerm
  | smash : String -> MarkedTerm -> MarkedTerm -> MarkedTerm
  | var : String -> String -> MarkedTerm --var name
  | zero : String -> MarkedTerm
  -- | one : Term
  -- | two : Term
  | bitshift : String -> MarkedTerm -> MarkedTerm -> MarkedTerm
  | ERROR : String -> MarkedTerm
deriving Repr, BEq

inductive Formula : Type
  | And : Formula -> Formula -> Formula -- Left, Right
  | Or : Formula -> Formula -> Formula -- Left, Right
  | Not : Formula -> Formula
  | ForAll : String -> Formula -> Formula -- Bound Var Name, Formula in scope
  | Exists : String -> Formula -> Formula -- Bound Var Name, Formula in scope
  -- | BoundedForAll : String -> Term -> Formula -> Formula -- Bound Var Name, Bounding Term, Formula in scope
  -- | BoundedExists : String -> Term -> Formula -> Formula -- Bound Var Name, Bounding Term, ormula in scope
  | Equals : Term -> Term -> Formula -- Left, Right
  | LEQ : Term -> Term -> Formula -- <=
  | LT : Term -> Term -> Formula -- <
  | True
  | False
  | Pred : String -> List Term -> Formula -- Arbitrary Predicate
  | Implies : Formula -> Formula -> Formula -- Cedent, Antecedent
  | Iff : Formula -> Formula -> Formula
  | ERROR : String -> Formula
deriving Repr, BEq

instance : Inhabited Formula where
  default := Formula.ERROR "Something weird has happened"

inductive MarkedFormula : Type
  | And : MarkedFormula -> MarkedFormula -> MarkedFormula -- Left, Right
  | Or : MarkedFormula -> MarkedFormula -> MarkedFormula -- Left, Right
  | Not : MarkedFormula -> MarkedFormula
  | ForAll : String -> MarkedFormula -> MarkedFormula -- Bound Var Name, Formula in scope
  | Exists : String -> MarkedFormula -> MarkedFormula -- Bound Var Name, Formula in scope
  -- | BoundedForAll : String -> MarkedTerm -> MarkedFormula -> MarkedFormula -- Bound Var Name, Label × Bounding Term, Formula in scope
  -- | BoundedExists : String -> MarkedTerm -> MarkedFormula -> MarkedFormula -- Bound Var Name, Label × Bounding Term, ormula in scope
  | Equals : MarkedTerm -> MarkedTerm -> MarkedFormula -- Left, Right
  | LEQ : MarkedTerm -> MarkedTerm -> MarkedFormula
  | LT : MarkedTerm -> MarkedTerm -> MarkedFormula
  | True
  | False
  | Pred : String -> List MarkedTerm -> MarkedFormula -- Arbitrary Predicate
  | Implies : MarkedFormula -> MarkedFormula -> MarkedFormula -- Cedent, Antecedent
  | Iff : MarkedFormula -> MarkedFormula -> MarkedFormula -- Cedent, Antecedent
  | ERROR : String -> MarkedFormula
deriving Repr, BEq

instance : Inhabited MarkedFormula where
  default := MarkedFormula.ERROR "Something weird has happened"

inductive NDRule : Type
  | AndIntro : Formula -> Formula -> NDRule
  | AndElimLeft : Formula -> NDRule
  | AndElimRight : Formula -> NDRule
  | OrIntroLeft : Formula -> Formula -> NDRule
  | OrIntroRight : Formula -> Formula -> NDRule
  | OrElim : Formula -> Formula -> Formula -> Formula -> NDRule -- A or B, A, B, C are args.
  | ImplIntro : Formula -> Formula -> NDRule -- Assumption A, implied formula B
  | ImplElim : Formula -> Formula -> NDRule -- A, A-> B
  | IffIntro : Formula -> Formula -> NDRule -- A -> B, B -> A
  | IffElimLeft : Formula -> Formula -> NDRule -- A, A <--> B
  | IffElimRight : Formula -> Formula -> NDRule -- B, A <--> B
  | NotIntro : Formula -> Formula -> NDRule -- A, 2nd arg should be False
  | NotElim : Formula -> Formula -> NDRule
  | FalseIntro : Formula -> Formula -> NDRule -- False, D
  | FalseImpl : Formula -> Formula -> NDRule -- Assumption not A, False
  | ForAllIntro : Formula -> String -> String -> NDRule -- Formula, free var name, bounded var name
  | ExistsIntro : Formula -> Term -> String -> NDRule
  | ExistsIntroMarked : MarkedFormula -> Term -> String -> String -> NDRule -- Marked Formula, identified term, label to find, bounded var name
  | ForAllElim : Formula -> Term -> NDRule
  | ExistsElim : Formula  -> Term -> Formula -> Formula -> NDRule -- Exists x Ax , t,  A(t), C
  | Refl : Term -> NDRule
  | Symm : Formula -> NDRule
  | Trans : Formula -> Formula -> NDRule
  | Subst : Formula -> Formula -> NDRule -- Substitute everywhere: s=t, At
  | SubstMarked : Formula -> MarkedFormula -> String -> NDRule -- s=t, At, identifier
  | Ind : Formula -> Formula -> NDRule -- Phi(0), ForAlln Phi(n) -> Phi(n+1)
deriving Repr, BEq

def possibleCommands : List String := ["assume", "def", "axiom", "andI", "andE-left", "andE-right", "orI-left", "orI-right", "orE",
    "impliesI", "impliesE", "iffI", "iffE-left", "iffE-right", "notI", "notE", "falseI", "falseE", "forAllI", "existsI", "forAllE", "existsE", "=Refl", "=Symm", "=Trans",
    "=Subst", "induct", "mark" ]

-- String and List helper functions

def removeEmptyEntries (x : List String) : (List String) :=
  match x with
    | "" :: rest => removeEmptyEntries rest
    | [] => []
    | head :: rest => head :: removeEmptyEntries rest

def Formula.Predicates : List String := []

--def Term.Functions : List String := ["+", "×"]

def Term.containsVar (t : Term) (s : String) : Bool :=
  match t with
    | Term.var name => name == s
    | Term.func _ args => args.foldr (λ a b => (a.containsVar s) || b) false
    | Term.plus t1 t2 => t1.containsVar s || t2.containsVar s
    | Term.times t1 t2 => t1.containsVar s || t2.containsVar s
    | Term.smash t1 t2 => t1.containsVar s || t2.containsVar s
    | Term.succ t1 => t1.containsVar s
    | Term.len t1 => t1.containsVar s
    -- | Term.one => false
    | Term.zero => false
    -- | Term.two => false
    | Term.bitshift t1 t2 => t1.containsVar s || t2.containsVar s
    | _ => false


def Term.containsTerm (t : Term) (searchTerm : Term) : Bool :=
  if t==searchTerm then true
  else
  match t with
    | Term.func _ args => args.foldr (λ a b => (a.containsTerm searchTerm) || b) false
    | Term.plus t1 t2 => t1.containsTerm searchTerm || t2.containsTerm searchTerm
    | Term.times t1 t2 => t1.containsTerm searchTerm || t2.containsTerm searchTerm
    | Term.smash t1 t2 => t1.containsTerm searchTerm || t2.containsTerm searchTerm
    | Term.succ t1 => t1.containsTerm searchTerm
    | Term.len t1 => t1.containsTerm searchTerm
    | Term.bitshift t1 t2 => t1.containsTerm searchTerm || t2.containsTerm searchTerm
    | _ => false

def Formula.containsTerm (f : Formula) (searchTerm : Term) : Bool :=
  match f with
    | Formula.And f1 f2 => f1.containsTerm searchTerm || f2.containsTerm searchTerm
    | Formula.Or f1 f2 => f1.containsTerm searchTerm || f2.containsTerm searchTerm
    | Formula.Not f1 =>  f1.containsTerm searchTerm
    | Formula.ForAll _ f => f.containsTerm searchTerm
    | Formula.Exists _ f => f.containsTerm searchTerm
    -- | Formula.BoundedForAll s t f => t.innerTermError.append f.innerFormulaError
    -- | Formula.BoundedExists s t f => t.innerTermError.append f.innerFormulaError
    | Formula.Equals t1 t2 => t1.containsTerm searchTerm || t2.containsTerm searchTerm
    | Formula.LEQ t1 t2 => t1.containsTerm searchTerm || t2.containsTerm searchTerm
    | Formula.True => false
    | Formula.False => false
    | Formula.Pred _ params => (params.foldl (λ val trm => val || trm.containsTerm searchTerm ) false)
    | Formula.Implies f1 f2 => f1.containsTerm searchTerm || f2.containsTerm searchTerm
    | Formula.Iff f1 f2 => f1.containsTerm searchTerm || f2.containsTerm searchTerm
    | Formula.LT t1 t2 => t1.containsTerm searchTerm || t2.containsTerm searchTerm
    | Formula.ERROR _ => false

-- Convert a MarkedTerm into an unlabeled Term
def MarkedTerm.toUnlabeled : MarkedTerm -> Term
  | MarkedTerm.func _ fname params => Term.func fname (params.map (λ trm => trm.toUnlabeled))
  | MarkedTerm.plus _ t1 t2 => Term.plus (t1.toUnlabeled) (t2.toUnlabeled)
  | MarkedTerm.times _ t1 t2 =>  Term.times (t1.toUnlabeled) (t2.toUnlabeled)
  | MarkedTerm.succ _ t1 => Term.succ (t1.toUnlabeled)
  | MarkedTerm.len _ t1 => Term.len (t1.toUnlabeled)
  | MarkedTerm.smash _ t1 t2 =>  Term.smash (t1.toUnlabeled) (t2.toUnlabeled)
  | MarkedTerm.var _ name => Term.var name
  | MarkedTerm.zero _ => Term.zero
  -- | one : Term
  -- | two : Term
  | MarkedTerm.bitshift _ t1 t2 => Term.bitshift (t1.toUnlabeled) (t2.toUnlabeled)
  | MarkedTerm.ERROR msg => Term.ERROR msg

def MarkedFormula.toUnlabeled : MarkedFormula -> Formula
  | MarkedFormula.And f1 f2 => Formula.And f1.toUnlabeled f2.toUnlabeled
  | MarkedFormula.Or f1 f2 => Formula.Or f1.toUnlabeled f2.toUnlabeled
  | MarkedFormula.Not f1 => Formula.Not f1.toUnlabeled
  | MarkedFormula.ForAll s f => Formula.ForAll s f.toUnlabeled
  | MarkedFormula.Exists s f => Formula.Exists s f.toUnlabeled
  -- | MarkedFormula.BoundedForAll s t f =>
  -- | MarkedFormula.BoundedExists s t f =>
  | MarkedFormula.Equals t1 t2 => Formula.Equals t1.toUnlabeled t2.toUnlabeled
  | MarkedFormula.LEQ t1 t2 => Formula.LEQ t1.toUnlabeled t2.toUnlabeled
  | MarkedFormula.True => Formula.True
  | MarkedFormula.False => Formula.False
  | MarkedFormula.Pred f params => Formula.Pred f (params.map (λ t => t.toUnlabeled))
  | MarkedFormula.Implies f1 f2 => Formula.Implies f1.toUnlabeled f2.toUnlabeled
  | MarkedFormula.Iff f1 f2 => Formula.Iff f1.toUnlabeled f2.toUnlabeled
  | MarkedFormula.LT t1 t2 => Formula.LT t1.toUnlabeled t2.toUnlabeled
  | MarkedFormula.ERROR s => Formula.ERROR s

-- Returns [] if no subterm is an error, or returns the error messages otherwise
def Term.innerTermError : Term -> List String
  | Term.func _ params =>  (params.foldl (λ val trm => val.append trm.innerTermError ) [])
  | Term.plus t1 t2 => (t1.innerTermError).append t2.innerTermError
  | Term.times t1 t2 =>  (t1.innerTermError).append t2.innerTermError
  | Term.succ t1 => (t1.innerTermError)
  | Term.len t1 => (t1.innerTermError)
  | Term.smash t1 t2 =>  (t1.innerTermError).append t2.innerTermError
  | Term.var _ => []
  | Term.zero => []
  -- | one : Term
  -- | two : Term
  | Term.bitshift t1 t2 => (t1.innerTermError).append t2.innerTermError
  | Term.ERROR msg => [msg]


-- Returns [] if no subterm is an error, or returns the error messages otherwise
def MarkedTerm.innerMarkedTermError : MarkedTerm -> List String
  | MarkedTerm.func _ _ params => (params.foldl (λ val trm => val.append trm.innerMarkedTermError ) [])
  | MarkedTerm.plus _  t1 t2 => (t1.innerMarkedTermError).append t2.innerMarkedTermError
  | MarkedTerm.times _ t1 t2 =>  (t1.innerMarkedTermError).append t2.innerMarkedTermError
  | MarkedTerm.succ _ t1 => (t1.innerMarkedTermError)
  | MarkedTerm.len _ t1 => (t1.innerMarkedTermError)
  | MarkedTerm.smash _ t1 t2 =>  (t1.innerMarkedTermError).append t2.innerMarkedTermError
  | MarkedTerm.var _ _ => []
  | MarkedTerm.zero _ => []
  | MarkedTerm.bitshift _ t1 t2 => (t1.innerMarkedTermError).append t2.innerMarkedTermError
  | MarkedTerm.ERROR msg => [msg]

-- Returns "" if no subformula/term is an error, or returns the error message otherwise
def Formula.innerFormulaError : Formula -> List String
  | Formula.And f1 f2 => (f1.innerFormulaError).append f2.innerFormulaError
  | Formula.Or f1 f2 => (f1.innerFormulaError).append f2.innerFormulaError
  | Formula.Not f1 => (f1.innerFormulaError)
  | Formula.ForAll _ f => (f.innerFormulaError)
  | Formula.Exists _ f => (f.innerFormulaError)
  -- | Formula.BoundedForAll s t f => t.innerTermError.append f.innerFormulaError
  -- | Formula.BoundedExists s t f => t.innerTermError.append f.innerFormulaError
  | Formula.Equals t1 t2 => t1.innerTermError.append t2.innerTermError
  | Formula.LEQ t1 t2 => t1.innerTermError.append t2.innerTermError
  | Formula.True => []
  | Formula.False => []
  | Formula.Pred _ params => (params.foldl (λ val trm => val.append trm.innerTermError ) [])
  | Formula.Implies f1 f2 => (f1.innerFormulaError).append f2.innerFormulaError
  | Formula.Iff f1 f2 => (f1.innerFormulaError).append f2.innerFormulaError
  | Formula.LT t1 t2 => t1.innerTermError.append t2.innerTermError
  | Formula.ERROR s => [s]

-- Returns "" if no subformula/term is an error, or returns the error message otherwise
def MarkedFormula.innerMarkedFormulaError : MarkedFormula -> List String
  | MarkedFormula.And f1 f2 => (f1.innerMarkedFormulaError).append f2.innerMarkedFormulaError
  | MarkedFormula.Or f1 f2 => (f1.innerMarkedFormulaError).append f2.innerMarkedFormulaError
  | MarkedFormula.Not f1 => (f1.innerMarkedFormulaError)
  | MarkedFormula.ForAll _ f => (f.innerMarkedFormulaError)
  | MarkedFormula.Exists _ f => (f.innerMarkedFormulaError)
  -- | MarkedFormula.BoundedForAll s t f => t.innerMarkedTermError.append f.innerMarkedFormulaError
  -- | MarkedFormula.BoundedExists s t f => t.innerMarkedTermError.append f.innerMarkedFormulaError
  | MarkedFormula.Equals t1 t2 => t1.innerMarkedTermError.append t2.innerMarkedTermError
  | MarkedFormula.LEQ t1 t2 => t1.innerMarkedTermError.append t2.innerMarkedTermError
  | MarkedFormula.True => []
  | MarkedFormula.False => []
  | MarkedFormula.Pred _ params => (params.foldl (λ val trm => val.append trm.innerMarkedTermError ) [])
  | MarkedFormula.Implies f1 f2 => (f1.innerMarkedFormulaError).append f2.innerMarkedFormulaError
  | MarkedFormula.Iff f1 f2 => (f1.innerMarkedFormulaError).append f2.innerMarkedFormulaError
  | MarkedFormula.LT t1 t2 => t1.innerMarkedTermError.append t2.innerMarkedTermError
  | MarkedFormula.ERROR s => [s]


-- Function to check if a variable guaranteed to be in a formula is free
def Formula.varIsFree (F : Formula) (var : Term) : Bool :=
  match var with
  | Term.var name =>
    match F with
      | Formula.And f1 f2 => f1.varIsFree var && f2.varIsFree var
      | Formula.Or f1 f2 => f1.varIsFree var && f2.varIsFree var
      | Formula.Not f1 => f1.varIsFree var
      | Formula.ForAll s f => s == name && f.varIsFree var
      | Formula.Exists s f => !(s == name) && f.varIsFree var
      -- | Formula.BoundedForAll s _ f => !(s == name) && f.varIsFree var
      -- | Formula.BoundedExists s _ f => !(s == name) && f.varIsFree var
      | Formula.Equals _ _ => true
      | Formula.LEQ _ _ => true
      | Formula.True => true
      | Formula.False => true
      | Formula.Pred _ _ => true
      | Formula.Implies f1 f2 => f1.varIsFree var && f2.varIsFree var
      | Formula.Iff f1 f2 => f1.varIsFree var && f2.varIsFree var
      | Formula.LT _ _ => true
      | Formula.ERROR _ => false

  | _ => false

--def extractBoundingTerm (line : String) : Term :=



-- If I have "(f (g x y) (h x (l y)))", the output is ["(g x y)", "(h x (l y))"]
def grabInnerTermsOrFormulas (s : String) : List String :=
  let opened : String := (((s.trim.dropWhile (.!='(')).drop 1).dropRight 1).trim
  let len : Nat := opened.length
  let rec helper (counter : Nat) (t : String) (i : Nat) (depth : Nat) (params : List (Nat × Nat)) : List (Nat × Nat) :=
    match counter with
      | n + 1 =>
        let curr : Char := t.get! ⟨i⟩
        let next : Char := t.get! ⟨i+1⟩
        match curr, next, depth with
          | _, '(', 0 => helper (n) t (i+1) (depth+1) (params.append [(i+1, 0)])
          | _, '(', k+1 => helper (n) t (i+1) (depth + 1)  params
          | _, ')', 1 => helper (n) t (i+1) (0) (match params.getLast! with | (j, _) => params.dropLast.append [(j, i+1)])
          | _, ')', k+1 => helper (n) t (i+1) (k) params
          | ' ', '/', 0 => helper (n) t (i+1) 0 params -- Case where a label is encountered
          | ' ', ' ', _ => helper (n) t (i+1) depth params
          | ' ', '\n', _ => helper (n) t (i+1) depth params
          | ' ', _, 0 => helper (n) t (i+1) 0  (params.append [(i,0)]) -- beginning of variable param (implies in the Predicate case)
          | _, ' ', 0 => match params.length with
            | 0 => helper (n) t (i + 1) 0  params
            | _ => helper (n) t (i+1) 0
               (match params.getLast! with | (j, _) => params.dropLast.append [(j, i+1)]) -- end of variable param
          | _, _, _ => helper (n) t (i+1) depth params
      | 0 => match depth, params.getLast! with
        | 0, ((j, 0) : Nat × Nat) => params.dropLast.append [(j, t.length)]
        | _, _ => params
  termination_by counter

  (helper (len - 1) opened 0 0 ([] : List (Nat × Nat))).map (λ (a,b) => (opened.extract ⟨a⟩ ⟨b+1⟩).trim)
--#eval (grabInnerTermsOrFormulas "(>> /asd(a) b)")
--#eval grabInnerTermsOrFormulas "/asd(>> a b)"
--#eval grabInnerTermsOrFormulas "(= /asd(S 0) (0))"
-- Term structure:  (f_name param1 param2 ... paramk), where each param is a term
def newTerm (t : String) : Term :=
  let rec helper (q : String) (num_paren_upper_bound : Nat) : Term :=
    let varOrFun : Bool := q.contains '('
    match num_paren_upper_bound, varOrFun with
      | _, false => Term.var q.trim
      | n + 1, true =>
        let fun_and_params : List String :=  (removeEmptyEntries (((q.trim.drop 1).dropRight 1).split (. == ' ')))
        let args := if fun_and_params.length > 1 then grabInnerTermsOrFormulas q else []
        match fun_and_params.head! with
          | "1" => Term.succ (Term.zero)
          | "0" => Term.zero
          | "2" => Term.succ (Term.succ Term.zero)
          | "+" => if args.length == 2 then (Term.plus (helper args[0]! n) (helper args[1]! n)) else Term.ERROR "Bad Addition! Two arguments not found!"
          | "*" => if args.length == 2 then (Term.times (helper args[0]! n) (helper args[1]! n)) else Term.ERROR "Bad Multiplication! Two arguments not found!"
          | "S" => if args.length == 1 then (Term.succ (helper args[0]! n)) else Term.ERROR "Bad Successor! One argument not found!"
          | "Len" => if args.length == 1 then (Term.len (helper args[0]! n)) else Term.ERROR "Bad length! One argument not found!"
          | "#" => if args.length == 2 then (Term.smash (helper args[0]! n) (helper args[1]! n)) else Term.ERROR "Bad Multiplication! Two arguments not found!"
          | ">>" => if args.length == 2 then (Term.bitshift (helper args[0]! n) (helper args[1]! n)) else Term.ERROR "Bad Bitshift! Two arguments not found!"
          | _ => Term.func (fun_and_params.head!) (args.map (λ s => helper s (n)))
      | 0, true => Term.ERROR "Bad Atomic Term"-- This case should never happen! num_paren_upper_bound is always positive if varOrFun is true
  helper t t.length
--#eval newTerm "2)"


--#eval newTerm "(>> (1) (0))"
def grabTermLabel (term : String) : String :=
  let subIdx := term.find (.=='/')
  if subIdx == term.endPos then ""
  else
    let parenIdx :=  (term.find (.=='('))
    if parenIdx > ( subIdx) then
    (term.extract (term.next subIdx) parenIdx).trim
    else
      ""

-- Given a marked term, like /first(+ /zero(0) (S 0)), extract the labels of the **inner terms**.
-- Assumes the term input is in parentheses
-- Example: Input: "/first(+ /zero(0) (S 0))"   Output: ["/zero", ""]
def grabInnerTermLabels (s : String) : List String :=

  let opened : String := (((s.trim.dropWhile (.!='(')).drop 1).dropRight 1).trim
  let len : Nat := opened.length
  let rec helper (counter : Nat) (t : String) (i : Nat) (depth : Nat) (params : List (Nat × Nat)) : List (Nat × Nat) :=
    match counter with
      | n + 1 =>
        let curr : Char := t.get!  ⟨i⟩
        let next : Char := t.get! ⟨i+1⟩
        match curr, next, depth with
          | '/', _, 0 => helper n t (i+1) (depth) (params.append [(i, 0)])
          | _, '(', 0 => if params.length > 0 then
                            match params.getLast! with
                              | (j, 0) => (helper n t (i+1) 1 (params.dropLast.append [(j,i+1)]))
                              | _ => (helper n t (i+1) 1 (params.append [(1,1)]))
                          else (helper n t (i+1) 1 (params.append [(1,1)]))
          | _, ')', d+1 => helper n t (i+1) d params
          | _, '(', d+1 => helper n t (i+1) (d+2) params
          | _, _, _ => helper n t (i+1) depth params
      | 0 => params
  (helper (len-1) opened 0 0 []).map (λ (a,b) => opened.extract ⟨a⟩ ⟨b⟩)

--#eval grabTermLabel "/abc (/(sdf)"
--#eval grabInnerTermLabels "/dfs(+ /abc(S 0) (+ /blah(0) (0)))"

def padEmptyLabels (terms : List String) (labels : List String) : List String :=
  let len := terms.length
  let rec helper (counter : Nat) (numEmpties : Nat) (newLabels : List String) : List String :=
    match counter with
      | 0 => newLabels
      | n + 1 => if !terms[len-counter]!.contains '(' then --is variable
                    helper n (numEmpties+1) (newLabels.append [""])
                  else
                    helper n numEmpties (newLabels.append [labels[len-counter-numEmpties]!])
  helper len 0 []

--#eval padEmptyLabels ["(a", "b", "d","(c"] ["a", "c"]

def newMarkedTerm (t : String) : MarkedTerm :=
  let rec helper (q : String) (num_paren_upper_bound : Nat) : MarkedTerm :=
    let varOrFun : Bool := q.contains '(' -- for marked terms, this just distinguishes between unlabeled vars vs everything else (including labeled vars)
    match num_paren_upper_bound, varOrFun with
      | _, false => MarkedTerm.var "" q.trim
      | n + 1, true =>
        let fun_and_params : List String :=  (removeEmptyEntries ((((q.trim.dropWhile (.!='(')).drop 1).dropRight 1).split (. == ' ')))
        let label := grabTermLabel q
        let args := if fun_and_params.length > 1 then grabInnerTermsOrFormulas q else []
        let arg_labels_v1 : List String := if fun_and_params.length > 1 then (grabInnerTermLabels q) else []
        --if args.length== 1 then MarkedTerm.zero "" else
        -- If some arguments are unlabeled variables, the list lengths will differ. We must add in a correctly indexed empty label per unlabeled variable
        let arg_labels := padEmptyLabels args arg_labels_v1

        if args.length == arg_labels.length then
          match fun_and_params.head! with
            | "1" => MarkedTerm.succ label (MarkedTerm.zero "")
            | "0" => MarkedTerm.zero label
            | "2" => MarkedTerm.succ label (MarkedTerm.succ "" (MarkedTerm.zero ""))
            | "+" => if args.length == 2 then (MarkedTerm.plus label (helper (arg_labels[0]!.append args[0]!) n) (helper (arg_labels[1]!.append args[1]!) n)) else MarkedTerm.ERROR "Bad Addition! Two arguments not found!"
            | "*" => if args.length == 2 then (MarkedTerm.times label (helper (arg_labels[0]!.append args[0]!) n) (helper (arg_labels[1]!.append args[1]!) n)) else MarkedTerm.ERROR "Bad Multiplication! Two arguments not found!"
            | "S" => if args.length == 1 then (MarkedTerm.succ label (helper (arg_labels[0]!.append args[0]!) n)) else MarkedTerm.ERROR "Bad Successor! One argument not found!"
            | "Len" => if args.length == 1 then (MarkedTerm.len label (helper (arg_labels[0]!.append args[0]!) n)) else MarkedTerm.ERROR "Bad length! One argument not found!"
            | "#" => if args.length == 2 then (MarkedTerm.smash label (helper (arg_labels[0]!.append args[0]!) n) (helper (arg_labels[1]!.append args[1]!) n)) else MarkedTerm.ERROR "Bad Multiplication! Two arguments not found!"
            | ">>" => if args.length == 2 then (MarkedTerm.bitshift label (helper (arg_labels[0]!.append args[0]!) n) (helper (arg_labels[1]!.append args[1]!) n)) else MarkedTerm.ERROR "Bad Bitshift! Two arguments not found!"
            | _ => if args.length > 0 then MarkedTerm.func label (fun_and_params.head!) ((arg_labels.zip args).map (λ (lbl, s) => helper (lbl.append s) (n))) else MarkedTerm.var label fun_and_params.head! -- TODO: Make robust to adding 0-ary aliases when we add let ... be ... commands
          else
            MarkedTerm.ERROR "Mismatch of label and parameter numbers!"
      | 0, true => MarkedTerm.ERROR "Bad Atomic Term"-- This case should never happen! num_paren_upper_bound is always positive if varOrFun is true
  helper t t.length
def q := "(>> a b)"
-- #eval (removeEmptyEntries ((((q.trim.dropWhile (.!='(')).drop 1).dropRight 1).split (. == ' ')))
-- #eval (grabInnerTermsOrFormulas "(>> /asd(a) b)")

-- #eval padEmptyLabels (grabInnerTermsOrFormulas q) (grabInnerTermLabels "(>> a b)")
--#eval newMarkedTerm "/asd(>> /var(a) b)"
--#eval newMarkedTerm "(3)"
-- Define parsing function of a formula
def newFormula (s : String) : Formula :=
  let rec helper (q : String) (num_paren_upper_bound : Nat) : Formula :=
    let constOrConnective : Bool := q.contains '('
    match num_paren_upper_bound, constOrConnective with
      | _, false => match q with | "True" => Formula.True | "False" => Formula.False | _ => Formula.ERROR "Bad Atomic Formula"
      | n+1, true => -- Extract connective and params
        let name : String :=  (removeEmptyEntries (((q.trim.drop 1).dropRight 1).split (. == ' '))).head!.trim
        let params : List String := grabInnerTermsOrFormulas q
        match name with
          | "And" => match params with | p1 :: p2 :: [] => Formula.And (helper p1 n) (helper p2 n) | _ => Formula.ERROR "Bad And"
          | "Or" => match params with | p1 :: p2 :: [] => Formula.Or (helper p1 n) (helper p2 n) | _ => Formula.ERROR "Bad Or"
          | "Not" => match params with | form :: [] => Formula.Not (helper form n) | _ => Formula.ERROR "Bad Not"
          | "ForAll" => match params with | varname :: form :: [] => Formula.ForAll varname (helper form n) | _ => Formula.ERROR "Bad For All quantifier"
          | "Exists" => match params with | varname :: form :: [] => Formula.Exists varname (helper form n) | _ => Formula.ERROR "Bad Existential quantifier"
          | "=" => match params with | a :: b :: [] => Formula.Equals (newTerm a) (newTerm b) | _ => Formula.ERROR "Bad Equality"
          | "<=" => match params with | a :: b :: [] => Formula.LEQ (newTerm a) (newTerm b) | _ => Formula.ERROR "Bad Inequality"
          | "<" => match params with | a :: b :: [] => Formula.LT (newTerm a) (newTerm b) | _ => Formula.ERROR "Bad Inequality"

          | "->" =>
            match params with
              | a :: b :: [] => Formula.Implies (helper a n) (helper b n)
              | _ => Formula.ERROR "Bad Implication"

          | "<-->" =>
            match params with
              | a :: b :: [] => Formula.Iff (helper a n) (helper b n)
              | _ => Formula.ERROR "Bad Implication"

          | _ => Formula.ERROR "Bad Connective or Predicate"
      | 0, true => Formula.ERROR "Bad Atomic Formula"
  helper s s.length

-- Parsing function for a marked formula
def newMarkedFormula (s : String) : MarkedFormula :=
  let rec helper (q : String) (num_paren_upper_bound : Nat) : MarkedFormula :=
    let constOrConnective : Bool := q.contains '('
    match num_paren_upper_bound, constOrConnective with
      | _, false => match q with | "True" => MarkedFormula.True | "False" => MarkedFormula.False | _ => MarkedFormula.ERROR "Bad Atomic Formula"
      | n+1, true => -- Extract connective and params
        let name : String :=  (removeEmptyEntries ((((q.trim.dropWhile (.!='(')).drop 1).dropRight 1).split (. == ' '))).head!
        let params : List String := grabInnerTermsOrFormulas q
        match name with
          | "And" => match params with | p1 :: p2 :: [] => MarkedFormula.And (helper p1 n) (helper p2 n) | _ => MarkedFormula.ERROR "Bad And"
          | "Or" => match params with | p1 :: p2 :: [] => MarkedFormula.Or (helper p1 n) (helper p2 n) | _ => MarkedFormula.ERROR "Bad Or"
          | "Not" => match params with | form :: [] => MarkedFormula.Not (helper form n) | _ => MarkedFormula.ERROR "Bad Not"
          | "ForAll" => match params with | varname :: form :: [] => MarkedFormula.ForAll varname (helper form n) | _ => MarkedFormula.ERROR "Bad For All quantifier"
          | "Exists" => match params with | varname :: form :: [] => MarkedFormula.Exists varname (helper form n) | _ => MarkedFormula.ERROR "Bad Existential quantifier"
          | "=" =>
                  let arg_labels_v1 : List String :=  (grabInnerTermLabels q)
                  let arg_labels := padEmptyLabels params arg_labels_v1
                  match params with | a :: b :: [] => MarkedFormula.Equals (newMarkedTerm (arg_labels[0]!.append a)) (newMarkedTerm (arg_labels[1]!.append b)) | _ => MarkedFormula.ERROR "Bad Equality"

          | "<=" => match params with | a :: b :: [] =>
                                                    let arg_labels_v1 : List String :=  (grabInnerTermLabels q)
                                                    let arg_labels := padEmptyLabels params arg_labels_v1

                                                    MarkedFormula.LEQ (newMarkedTerm (arg_labels[0]!.append a)) (newMarkedTerm (arg_labels[1]!.append b)) | _ => MarkedFormula.ERROR "Bad Inequality"
          | "<" => match params with | a :: b :: [] =>
                                                    let arg_labels_v1 : List String :=  (grabInnerTermLabels q)
                                                    let arg_labels := padEmptyLabels params arg_labels_v1


                                                    MarkedFormula.LT (newMarkedTerm (arg_labels[0]!.append a)) (newMarkedTerm (arg_labels[1]!.append b)) | _ => MarkedFormula.ERROR "Bad Inequality"

          | "->" =>
            match params with
              | a :: b :: [] => MarkedFormula.Implies (helper a n) (helper b n)
              | _ => MarkedFormula.ERROR "Bad Implication"

          | "<-->" =>
            match params with
              | a :: b :: [] => MarkedFormula.Iff (helper a n) (helper b n)
              | _ => MarkedFormula.ERROR "Bad Implication"

          | _ => MarkedFormula.ERROR "Bad Connective or Predicate"
      | 0, true => MarkedFormula.ERROR "Bad Atomic Formula"
  helper s s.length
-- #eval newMarkedTerm "(+ (S (0)) (0))"
-- #eval newMarkedFormula "(= /abc(S (0)) /sdf(1))"
-- #eval grabInnerTermsOrFormulas "(+ (S (0) ) (1) )"
-- #eval newMarkedFormula "(And True (= /abc(S (0)) (1)))"
-- AXIOMS: A function that on input an axiom number, outputs a formula of the corresponding axiom

-- TODO: Infix <-> Prefix converter. Use infix here in s-expressions.
def newAxiom (n : Nat) : Formula :=
  match n with
    | 1 => newFormula "(= (+ x (0)) x)" -- x + 0 = x
    | 2 => newFormula "(= (+ x (S y)) (S (+ x y)))" -- x + Sy = S(x+y)
    | 3 => newFormula "(= (* x 0) (0))" -- x*0 = 0
    | 4 => newFormula "(= (* x (S y)) (+ (* x y) x))" -- x*Sy = x*y + x
    | 5 => newFormula "(<= 0 x)" -- 0 <= x
    | 6 => newFormula "(<--> (<= (S y) x) (< y x))" -- Sy ≤ x <--> y < x
    | 7 => newFormula "(= (>> x 0) x)" -- x >> 0 = x
    | 8 => newFormula "(Or
                          (= (>> x y) (* (2) (>> x (S y))))
                          (= (>> x y) (S (* (2) (>> x (S y)))))
                        )" -- x >> y = 2*(x >> Sy) or x >> y = S(2*(x >> Sy))
    | 9 => newFormula "(= (Len (0)) (0))" -- |0| = 0
    | 10 => newFormula "(-> (Not (= x (0))) (= (Len x) (S (Len (>> x (1))))))" -- x ≠ 0 ⊇ |x| = S(|x/2|)
    | 11 => newFormula "(= (# (0) (1)) (1))" -- 0 # 1 = 1
    | 12 => newFormula "(->
                          (Not (= x (0)))
                          (And
                            (= (# x (1)) (* (2) (# (>> x (1)) (1))))

                            (= (# y x)

                               (*
                                  (# y (1))
                                  (# y (>> x (1)))
                               )
                            )
                          )

                        )" -- x ≠ 0 ⊇ ( x # 1 = 2*( (x >> 1) # 1) )  ∧  ( y # x = (y # 1)*( y # (x >> 1)) )
    | _ => Formula.ERROR "No axiom of that number!"

-- SUBSTITUTION FUNCTIONS

-- Subsitute variable in a term with a term
-- params: t the Term to substitute into,  var the *name* of the variable to sub into, sub the *term* to put in
def Term.subAndReplace (T : Term) (t : Term) (x : Term) : Term :=
  if T == x then t else
  match T with
  | Term.func fname params => Term.func fname (params.map (λ trm => trm.subAndReplace t x))
  | Term.plus t1 t2 => Term.plus (t1.subAndReplace t x) (t2.subAndReplace t x)
  | Term.times t1 t2 =>  Term.times (t1.subAndReplace t x) (t2.subAndReplace t x)
  | Term.succ t1 => Term.succ (t1.subAndReplace t x)
  | Term.len t1 => Term.len (t1.subAndReplace t x)
  | Term.smash t1 t2 =>  Term.smash (t1.subAndReplace t x) (t2.subAndReplace t x)
  | Term.var name => Term.var name
  | Term.zero => Term.zero
  -- | one : Term
  -- | two : Term
  | Term.bitshift t1 t2 => Term.bitshift (t1.subAndReplace t x) (t2.subAndReplace t x)
  | Term.ERROR msg => Term.ERROR msg

def MarkedTerm.subAndReplace (T : MarkedTerm) (label : String) (t : Term) (x : Term) : Term :=
  match T with
  | MarkedTerm.func mark fname params => if T.toUnlabeled == x && mark == label then t else Term.func fname (params.map (λ trm => trm.subAndReplace label t x))
  | MarkedTerm.plus mark t1 t2 => if T.toUnlabeled == x && mark == label then t else Term.plus (t1.subAndReplace label t x) (t2.subAndReplace label t x)
  | MarkedTerm.times mark t1 t2 =>  if T.toUnlabeled == x && mark == label then t else Term.times (t1.subAndReplace label t x) (t2.subAndReplace label t x)
  | MarkedTerm.succ mark t1 => if T.toUnlabeled == x && mark == label then t else Term.succ (t1.subAndReplace label t x)
  | MarkedTerm.len mark t1 => if T.toUnlabeled == x && mark == label then t else Term.len (t1.subAndReplace label t x)
  | MarkedTerm.smash mark t1 t2 =>  if T.toUnlabeled == x && mark == label then t else Term.smash (t1.subAndReplace label t x) (t2.subAndReplace label t x)
  | MarkedTerm.var mark name => if T.toUnlabeled == x && mark == label then t else Term.var name
  | MarkedTerm.zero mark => if T.toUnlabeled == x && mark == label then t else Term.zero
  -- | one : Term
  -- | two : Term
  | MarkedTerm.bitshift mark t1 t2 => if T.toUnlabeled == x && mark == label then t else Term.bitshift (t1.subAndReplace label t x) (t2.subAndReplace label t x)
  | MarkedTerm.ERROR msg => Term.ERROR msg

-- Unmarked substitution (substitute everywhere possible)
def Formula.subAndReplace (F : Formula) (t: Term) (x: Term) : Formula :=
  match F with
    | Formula.And A B => Formula.And (subAndReplace A t x) (subAndReplace B t x)
    | Formula.Or A B => Formula.Or (subAndReplace A t x) (subAndReplace B t x)
    | Formula.Not A => Formula.Not (subAndReplace A t x)
    | Formula.ForAll s A => Formula.ForAll s (subAndReplace A t x)
    | Formula.Exists s A => Formula.Exists s (subAndReplace A t x)
    -- | Formula.BoundedForAll s bt A => Formula.BoundedForAll s (bt.subAndReplace t x) (subAndReplace A t x)
    -- | Formula.BoundedExists s bt A => Formula.BoundedExists s (bt.subAndReplace t x) (subAndReplace A t x)
    | Formula.Equals t1 t2 =>  Formula.Equals (t1.subAndReplace t x) (t2.subAndReplace t x)
    | Formula.LEQ t1 t2 => Formula.LEQ (t1.subAndReplace t x) (t2.subAndReplace t x)
    | Formula.True => Formula.True
    | Formula.False => Formula.True
    | Formula.Pred s args => Formula.Pred s (args.map λ term => term.subAndReplace t x)
    | Formula.Implies A B => Formula.Implies (subAndReplace A t x) (subAndReplace B t x)
    | Formula.LT t1 t2 => Formula.LT (t1.subAndReplace t x) (t2.subAndReplace t x)
    | _ => Formula.ERROR "Bad substitution"

-- Marked substitution

def MarkedFormula.subAndReplace (F : MarkedFormula) (t: Term) (label : String) (x: Term) : Formula :=
  match F with
    | MarkedFormula.And A B => Formula.And (subAndReplace A t label x) (subAndReplace B t label x)
    | MarkedFormula.Or A B => Formula.Or (subAndReplace A t label x) (subAndReplace B t label x)
    | MarkedFormula.Not A => Formula.Not (subAndReplace A t label x)
    | MarkedFormula.ForAll s A => Formula.ForAll s (subAndReplace A t label x)
    | MarkedFormula.Exists s A => Formula.Exists s (subAndReplace A t label x)
    -- | MarkedFormula.BoundedForAll s bt A => if (t.containsVar s) then Formula.ERROR "Bad substitution into bounding term!" else Formula.BoundedForAll s (bt.subAndReplace label t x)  (subAndReplace A t label x)
    -- | MarkedFormula.BoundedExists s bt A => if (t.containsVar s) then Formula.ERROR "Bad substitution into bounding term!" else Formula.BoundedExists s (bt.subAndReplace label t x) (subAndReplace A t label x)
    | MarkedFormula.Equals (t1) (t2) => Formula.Equals (t1.subAndReplace label t x) (t2.subAndReplace label t x)
    | MarkedFormula.LEQ t1 t2 => Formula.LEQ (t1.subAndReplace label t x) (t2.subAndReplace label t x)
    | MarkedFormula.True => Formula.True
    | MarkedFormula.False => Formula.True
    | MarkedFormula.Pred s args => Formula.Pred s (args.map λ term => term.subAndReplace label t x)
    | MarkedFormula.Implies A B => Formula.Implies (subAndReplace A t label x) (subAndReplace B t label x)
    | MarkedFormula.LT t1 t2 => Formula.LT (t1.subAndReplace label t x) (t2.subAndReplace label t x)
    | _ => Formula.ERROR "Bad substitution"

-- APPLY RULES

-- TODO: Add **Bounded** versions of quantifier rules. Not done yet.
def NDRule.apply (rule : NDRule) : Formula :=
  match rule with
    | NDRule.AndIntro A B => Formula.And A B
    | NDRule.AndElimLeft AandB => match AandB with | Formula.And A _ => A | _ => Formula.ERROR "Bad And Elimination!"
    | NDRule.AndElimRight AandB => match AandB with | Formula.And _ B => B | _ => Formula.ERROR "Bad And Elimination!"
    | NDRule.OrIntroLeft A B => Formula.Or A B
    | NDRule.OrIntroRight A B => Formula.Or B A
    | NDRule.OrElim AorB A B C => match AorB, A, B with | (Formula.Or a b), _, _ => if a == A && b == B then C else Formula.ERROR "Bad OrElim" | _, _, _ => Formula.ERROR "Bad Or Elimination"
    | NDRule.ImplIntro A B => Formula.Implies A B
    | NDRule.ImplElim A AimB => match AimB with | Formula.Implies a b => if a == A then b else Formula.ERROR "Bad ImplElim" | _ => Formula.ERROR "Bad ImplElim"
    | NDRule.IffIntro AimB BimA => match AimB, BimA with | Formula.Implies a1 b1, Formula.Implies b2 a2 => if a1 == a2 && b1 == b2 then Formula.Iff a1 b1 else Formula.ERROR "Bad IffIntro: Implication mismatch." | _, _ => Formula.ERROR "Bad IffIntro: One or both arguments are not implications."
    | NDRule.IffElimLeft A AiffB => match AiffB with | Formula.Iff A' B => if A == A' then B else Formula.ERROR "Bad IffElimLeft. Formulas do not match." | _ => Formula.ERROR "Bad IffElimLeft. Iff not provided."
    | NDRule.IffElimRight B AiffB => match AiffB with | Formula.Iff A B' => if B == B' then A else Formula.ERROR "Bad IffElimRight. Formulas do not match." | _ => Formula.ERROR "Bad IffElimRight. Iff not provided."
    | NDRule.NotIntro A F => match F with | Formula.False => Formula.Not A | _ => Formula.ERROR "Bad NotIntro. False not implied"
    | NDRule.NotElim A nA => match nA with | Formula.Not a => if a == A then Formula.False else Formula.ERROR "Bad Not Elimination" | _ => Formula.ERROR "Bad Not Elimination"
    | NDRule.FalseIntro F A => match F with | Formula.False => A | _ => Formula.ERROR "Bad False Intro"
    | NDRule.FalseImpl nA F => match nA, F with | Formula.Not A, Formula.False => A | _, _ => Formula.ERROR "Bad False Implication"
    | NDRule.ForAllIntro A c bvname => Formula.ForAll bvname (Formula.subAndReplace A (Term.var c) (Term.var bvname))
    | NDRule.ForAllElim faA t => match faA with | Formula.ForAll bv A => Formula.subAndReplace A t (Term.var bv) | _ => Formula.ERROR "Bad ForAllElim"
    | NDRule.ExistsIntro F t s => if !t.containsVar s then  Formula.Exists s (Formula.subAndReplace F (Term.var s) t) else Formula.ERROR "Bad Exists Introduction! Violated Eigenvariable condition"
    | NDRule.ExistsIntroMarked F t label bvname => if !t.containsVar bvname then
      let new_formula := MarkedFormula.subAndReplace F (Term.var bvname) label t
      Formula.Exists bvname new_formula
      else
        Formula.ERROR "Bad Exists Introduction. Variable contained in term"
    | NDRule.ExistsElim ExAx t At C => match ExAx with | Formula.Exists s As => if (Formula.subAndReplace As t (Term.var s)) == At then C else Formula.ERROR "Bad Exists Elimination!" | _ => Formula.ERROR "Bad Exists Elimination!"
    | NDRule.Refl t => Formula.Equals t t
    | NDRule.Symm F => match F with | Formula.Equals t1 t2 => Formula.Equals t2 t1 | _ => Formula.ERROR "Bad Equality Symmetry!"
    | NDRule.Trans F1 F2 => match F1, F2 with | Formula.Equals s t1, Formula.Equals t2 r => if t1 == t2 then Formula.Equals s r else Formula.ERROR "Bad Equality Transitivity!" | _, _ => Formula.ERROR "Bad Equality Transitivity"
    | NDRule.Subst sEQt At => match sEQt with | Formula.Equals s t => Formula.subAndReplace At s t | _ => Formula.ERROR "Bad Equality substitution!"
    | NDRule.SubstMarked sEQt At label => match sEQt with | Formula.Equals s t => MarkedFormula.subAndReplace At s label t | _ => Formula.ERROR "Bad Marked Equality Substitution!"
    | NDRule.Ind φ0 φnTOsn => match φnTOsn with | Formula.ForAll n (Formula.Implies φn φsuccn) => if ((Formula.subAndReplace φn (Term.plus (Term.var n) (Term.succ Term.zero)) (Term.var n)) == φsuccn || (Formula.subAndReplace φn (Term.succ (Term.var n)) (Term.var n)) == φsuccn) && (Formula.subAndReplace φn Term.zero (Term.var n)) == φ0 then Formula.ForAll n φn else Formula.ERROR "Bad Induction!" | _ => Formula.ERROR "Bad Induction!"

--#eval grabInnerTermsOrFormulas "(ForAll (x h) y (a b c) )"
