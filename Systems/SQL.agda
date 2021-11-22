module Systems.SQL where

open import Math.Type

postulate
  Value : Type₀
  Expr : Type₀
  Column : Type₀

data StmtSyntax : Type₁ where
  SELECT : StmtSyntax
  -- INSERT INTO table VALUES
  --   (v1, v2, ...);
  INSERT : (Column → Value) → StmtSyntax
  -- UPDATE table
  -- SET col = expr
  -- WHERE condition
  UPDATE : Column → Expr → Expr → StmtSyntax

postulate
  Stmt : Type₀
  _<_ : Stmt → Stmt → Type₀
  stmtSyntax : Stmt → StmtSyntax

InsertedRow : Stmt → Type₀
InsertedRow s with stmtSyntax s
... | SELECT = ⊥
... | INSERT _ = ⊤
... | UPDATE _ _ _ = ⊥

Row : Type₀
Row = Σ[ s ∈ Stmt ] InsertedRow s

-- A row r is visible to s if r was inserted before s
IsVisible : Stmt → Row → Type₀
IsVisible s r = fst r < s

VisibleRow : Stmt → Type₀
VisibleRow s = Σ[ r ∈ Row ] IsVisible s r

eval : (s : Stmt) → VisibleRow s → Expr → Value
eval = {!!}  -- use evalColumn

evalColumn : (s : Stmt) → VisibleRow s → Column → Value
evalColumn = {!!}

Write : Stmt → Type₀
Write s with stmtSyntax s
... | SELECT = ⊥
... | INSERT _ = Column
... | UPDATE _ _ _ = VisibleRow s

writeRow : (s : Stmt) → Write s → Row
writeRow s with stmtSyntax s
writeRow s | SELECT = {!!}
writeRow s | INSERT _ = λ c → s , {!!}
writeRow s | UPDATE _ _ _ = {!!}

writeColumn : (s : Stmt) → Write s → Column
writeColumn = {!!}

writeValue : (s : Stmt) → Write s → Value
writeValue = {!!}
