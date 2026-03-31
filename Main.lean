import ParserAlpha
import ParserAlpha.ParserImports
-- Read the proof line by line. Keep track of assumptions per line.

def verifyProof (pf : String) (imports : Std.HashMap String Formula) : String :=

 --let rec parseImports (counter : Nat) (subPf : String) (id2fmla : Std.HashMap String Formula) (id2marked_fmla : Std.HashMap String MarkedFormula) (id2assump : Std.HashMap String (List String)) : Std.HashMap String Formula := panic!

  let rec main_loop (counter : Nat) (subPf : String) (id2fmla : Std.HashMap String Formula) (id2marked_fmla : Std.HashMap String MarkedFormula) (id2assump : Std.HashMap String (List String)) : String :=
    match counter, subPf with
      | 0, _ => "Proof must end in a Natural Deduction Rule!"
      | n+1, _ =>
        -- Read a line of input
        let (line, subsubPf) := extractNextLine subPf
        let line_id : String :=  line.trim.extract ⟨0⟩ ⟨line.trim.findSubstring "."⟩
        if id2fmla.contains line_id || id2marked_fmla.contains line_id || id2assump.contains line_id then
          s!"On {line_id}: This line identifier is a duplicate!!"
        else
        -- Extract Operation
        let (operation, new_assumps) := extractOperation line id2fmla id2marked_fmla id2assump

        match operation with
          | (Sum.inl (Sum.inl ndr)) =>
            let new_fmla := ndr.apply
            let possible_errors := new_fmla.innerFormulaError
            if possible_errors != [] then
              let errors := possible_errors.foldr (λ a b => (b.append " ").append a) s!"On {line_id}: "
              errors
            else if new_fmla != extractPipedFormula line then
              s!"On {line_id}: Pipe Mismatch! The actual formula is\n{repr new_fmla}\n and the formula you piped is \n {repr (extractPipedFormula line)}"

            else if !subsubPf.contains '.' && new_assumps == [] then "Verified!" -- Proofs always end with an NDRule
            else if !subsubPf.contains '.' && new_assumps != [] then s!"You have finished the proof with uncancelled assumptions: {new_assumps}"

            else
              main_loop n subsubPf (id2fmla.insert line_id new_fmla) id2marked_fmla (id2assump.insert line_id new_assumps)

          | (Sum.inl (Sum.inr fmla)) =>
            let possible_errors := fmla.innerFormulaError
            if possible_errors != [] then
              let errors := possible_errors.foldr (λ a b => (b.append " ").append a) s!"On {line_id}: "
              errors
            else
              match extractCommand line with
                | "assume" => main_loop n subsubPf (id2fmla.insert line_id fmla) id2marked_fmla (id2assump.insert line_id new_assumps)

                | "axiom" => main_loop n subsubPf (id2fmla.insert line_id fmla) id2marked_fmla (id2assump.insert line_id new_assumps)

                | _ => s!"On {line_id}: Something weird has happened!"

          | (Sum.inr (Sum.inl mkd_fmla)) =>
              let possible_errors := mkd_fmla.innerMarkedFormulaError
              if possible_errors != [] then
                let errors := possible_errors.foldr (λ a b => (b.append " ").append a) s!"On {line_id}: "
                errors
              else
                main_loop n subsubPf id2fmla (id2marked_fmla.insert line_id mkd_fmla) (id2assump.insert line_id new_assumps)

          -- TODO: Implement cases for let...be...
          | _ => s!"On {line_id}, an invalid command was given"

  -- give empty assumptions for all imported formulas
  let assums : Std.HashMap String (List String) := imports.fold (init := Std.HashMap.emptyWithCapacity) (λ a k _ => a.insert k ([] : List String))
  main_loop pf.length pf imports (Std.HashMap.emptyWithCapacity : Std.HashMap String MarkedFormula) assums


def main : IO Unit := do
  let (proof_namespace, proof) <- collectImportedFormulas "draft-proof.pv"

  IO.println s!"{verifyProof proof proof_namespace}"
