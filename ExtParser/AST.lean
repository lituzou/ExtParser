import ExtParser.CoreParser

namespace AST
  open CoreParser

  inductive PreAST' (n : Nat) (b : Nat) where
    | skip (s e : Fin b) (G : PEG n)
    | ε (s e : Fin b)
    | any (s e : Fin b) (x : Char)
    | terminal (s e : Fin b) (a x : Char)
    | nonTerminal (s e : Fin b) (A : Fin n) (T : PreAST' n b)
    | seq (s e : Fin b) (T1 T2 : PreAST' n b)
    | prior (s e : Fin b) (T1 T2 : PreAST' n b)
    | star (s e : Fin b) (T0 TS : PreAST' n b)
    | notP (s e : Fin b) (T : PreAST' n b)
  
  inductive SkipPreAST' {n : Nat} {b : Nat} : PreAST' n b → Prop where
    | mk : ∀ {s e : Fin b} {G : PEG n}, SkipPreAST' (PreAST'.skip s e G)
  
  inductive StarPreAST' {n : Nat} {b : Nat} : PreAST' n b → Prop where
    | mk : ∀ {s e : Fin b} {T0 TS : PreAST' n b}, StarPreAST' (PreAST'.star s e T0 TS)
  
  inductive PreAST (n : Nat) (b : Nat) where
    | skip (s e : Fin b) (G : PEG n)
    | ε (s e : Fin b)
    | any (s e : Fin b) (x : Char)
    | terminal (s e : Fin b) (a x : Char)
    | nonTerminal (s e : Fin b) (A : Fin n) (T : PreAST' n b) (not_skip : ¬SkipPreAST' T)
    | seq (s e : Fin b) (T1 T2 : PreAST' n b) (not_skip_t1 : ¬SkipPreAST' T1)
    | star (s e : Fin b) (T0 TS : PreAST' n b) (skip_t1 : SkipPreAST' T1) (skip_or_star_t2 : SkipPreAST' T2 ∨ StarPreAST' T2)
    | notP (s e : Fin b) (T : PreAST' n b) (not_skip : ¬SkipPreAST' T)

end AST