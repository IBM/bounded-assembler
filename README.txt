# Bounded Assembler

This document defines a first-order theory of bounded arithmetic called $T^0_2$ (which is equivalent to PV1, but easier to axiomatize).  We begin by specifying a first-order language, starting with a list of the symbols in that language and their intended interpretations. First define some auxiliary sets of strings using eBNF notation.  The <id> strings will be used to identify sub-terms and sub-formulas of the language.  The <var> strings are the allowed names for variables.

\begin{grammar}
  <pad> := `\_' | `-'
  
  <digit> ::= `0' .. `9'
  
  <alpha> ::= `a' .. `z' | `A' .. `Z'

  <id> ::= ( <alpha> | <digit> | <pad> )$^+$

  <var> ::= `a' .. `z'
\end{grammar}

We specify the syntax of $T^0_2$ starting with \emph{terms} --- expressions that evaluate to an object.

\begin{grammar}
  <function0> ::= `0' | `1' | `2'

  <function1> := `S' | `Len' | `C_0' | `C_1'
  
  <function2> := `+' | `*' | `#' | `\>\,\>'

  <term> := <var>
  \alt `(' <function0> `)'
  \alt `(' <function1> <term> `)'
  \alt `(' <function2> <term> <term> `)'
\end{grammar}

For example, the intended evaluation of \texttt{(* (S 1) (S 2))} is 6.  Notice there is no symbol for 6 but $T^0_2$ can refer to it using both the given expression and \texttt{(S(S(S(S(S(S 0))))))}.

To write down proofs in $T^0_2$, we must refer to sub-terms.  \emph{Marked terms} use identifiers to name part of a term.  Formally, they are defined recursively using terms according to the following grammar.

\begin{grammar}
  <m-term> := `/' <id> <term>
  \alt `(' <function1> <m-term> `)'
  \alt `(' <function2> <term> <m-term> `)'
  \alt `(' <function2> <m-term> <term> `)'
  \alt `(' <function2> <m-term> <m-term> `)'
  %% inner mark
  \alt `/' <id> `(' <function1> <m-term> `)'
  \alt `/' <id> `(' <function2> <term> <m-term> `)'
  \alt `/' <id> `(' <function2> <m-term> <term> `)'
  \alt `/' <id> `(' <function2> <m-term> <m-term> `)'
  %% outer mark
\end{grammar}

For example, the marked term \texttt{(* (S 1) /three(S 2))} uses the identifier ``\texttt{three}'' to refer to the sub-term \texttt{(S 2)}.

We continue to specify the syntax of $T^0_2$ by defining \emph{formulas} --- expressions that evaluate to true or false.

\begin{grammar}
  <connective1> := `Not'
  
  <connective2> := `And' | `Or' | `->'
  
  <predicate> := `=' | `<' | `<='

  <quantifier> := `ForAll' | `Exists'

  <formula> := `True' | `False'
  \alt `(' <predicate> <term> <term> `)'
  \alt `(' <connective1> <formula> `)'
  \alt `(' <connective2> <formula> <formula> `)'
  \alt `(' <quantifier> <var> <formula> `)'
\end{grammar}

For example, the formula \texttt{(= 1 (S 0))} is intended to evaluate to \emph{true}.

To write down proofs in $T^0_2$ we must refer to sub-formulas.  \emph{Marked formulas} use identifiers to name part of a formula.   Formally, they are defined recursively using formulas according to the following grammar.

\begin{grammar}
  <m-formula> := `(' <predicate> <term> <m-term> `)'
  \alt `(' <predicate> <m-term> <term> `)'
  \alt `(' <predicate> <m-term> <m-term> `)'
  \alt `(' <connective1> <m-formula> `)'
  \alt `(' <connective2> <formula> <m-formula> `)'
  \alt `(' <connective2> <m-formula> <formula> `)'
  \alt `(' <connective2> <m-formula> <m-formula> `)'
  \alt `(' <quantifier> <var> <m-formula> `)'
\end{grammar}

The language of $T^0_2$ is the set $\langle formula \rangle \cup \langle m -formula\rangle$.
