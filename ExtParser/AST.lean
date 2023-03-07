import ExtParser.CoreParser

namespace AST
  open CoreParser

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

  inductive SkipPreAST : PreAST n b → Prop where
    | skip : SkipPreAST (.skip s e G)

  inductive StarPreAST : PreAST n b → Prop where
    | star : StarPreAST (.star s e T0 TS)

  inductive PreAST.wellFormed : PreAST n b → Prop where
    | skip : wellFormed (.skip s e G)
    | ε : wellFormed (.ε s e)
    | any : wellFormed (.any s e x)
    | terminal : wellFormed (.terminal s e a x)
    | nonTerminal : ¬SkipPreAST T → wellFormed (.nonTerminal s e A T)
    | seq : ¬SkipPreAST T1 →  wellFormed (.seq s e T1 T2)
    | prior : ¬SkipPreAST T1 →  wellFormed (.prior s e T1 T2)
    | star : ¬SkipPreAST T0 → (SkipPreAST TS ∨ StarPreAST TS) → wellFormed (.star s e T0 TS)
    | notP : ¬SkipPreAST T → wellFormed (.notP s e T) 
  
end AST