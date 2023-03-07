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

  inductive SkipPreAST' : PreAST' n b → Prop where
    | skip : SkipPreAST' (.skip s e G)

  inductive StarPreAST' : PreAST' n b → Prop where
    | star : StarPreAST' (.star s e T0 TS)

  inductive PreAST'.Wellformed : PreAST' n b → Prop where
    | skip : Wellformed (.skip s e G)
    | ε : Wellformed (.ε s e)
    | any : Wellformed (.any s e x)
    | terminal : Wellformed (.terminal s e a x)
    | nonTerminal : ¬SkipPreAST' T → Wellformed (.nonTerminal s e A T)
    | seq : ¬SkipPreAST' T1 →  Wellformed (.seq s e T1 T2)
    | prior : ¬SkipPreAST' T1 →  Wellformed (.prior s e T1 T2)
    | star : ¬SkipPreAST' T0 → (SkipPreAST' TS ∨ StarPreAST' TS) → Wellformed (.star s e T0 TS)
    | notP : ¬SkipPreAST' T → Wellformed (.notP s e T)
  
  structure PreAST (n : Nat) (b : Nat) where
    T : PreAST' n b
    wf_T : PreAST'.Wellformed T
  
end AST