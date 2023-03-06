import ExtParser.CoreParser

namespace AST
  open CoreParser

  mutual
  inductive PreAST (n : Nat) (b : Nat) where
    | skip (s e : Fin b) (G : PEG n)
    | ε (s e : Fin b)
    | any (s e : Fin b) (x : Char)
    | terminal (s e : Fin b) (a x : Char)
    | nonTerminal (s e : Fin b) (A : Fin n) (T : PreAST n b)
    | seq (s e : Fin b) (T1 T2 : PreAST n b)
    | prior (s e : Fin b) (T1 T2 : PreAST n b)
    | star (s e : Fin b) (T0 TS : PreAST n b)
    | notP (s e : Fin b) (T : PreAST n b)

  end
  
end AST