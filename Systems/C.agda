module Systems.C where

open import Math.Type

postulate
  -- C semantics are defined in terms of traces, which is a partially-ordered
  -- set of volatile memory accesses. The partial order is "program order" or
  -- "sequenced-before order".
  Trace : Type₀

  -- C expressions, statements, and functions
  Expr : Type₀
  Stmt : Type₀
  Func : Type₀

  -- "Executions" of each element
  Eval : Expr → Type₀
  Exec : Stmt → Type₀
  Call : Func → Type₀

  -- TODO: expressions have types; evaluations have values
  -- TODO: functions have signatures; calls have argument and return values

  -- The semantics.
  evalTrace : {e : Expr} → Eval e → Trace
  execTrace : {s : Stmt} → Exec s → Trace
  callTrace : {f : Func} → Call f → Trace
