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

  inductive PreAST.SkipPreAST : PreAST n b → Prop where
    | skip : SkipPreAST (.skip s e G)

  inductive PreAST.StarPreAST : PreAST n b → Prop where
    | star : StarPreAST (.star s e T0 TS)

  inductive PreAST.IsValid : PreAST n b → Prop where
    | skip : IsValid (.skip s e G)
    | ε : IsValid (.ε s e)
    | any : IsValid (.any s e x)
    | terminal : IsValid (.terminal s e a x)
    | nonTerminal : IsValid sub_T → ¬SkipPreAST sub_T → IsValid (.nonTerminal s e A sub_T)
    | seq : IsValid T1 → IsValid T2 → ¬SkipPreAST T1 → IsValid (.seq s e T1 T2)
    | prior : IsValid T1 → IsValid T2 → ¬SkipPreAST T1 → IsValid (.prior s e T1 T2)
    | star : IsValid T0 → IsValid TS → ¬SkipPreAST T0 → (SkipPreAST TS ∨ StarPreAST TS) → IsValid (.star s e T0 TS)
    | notP : IsValid sub_T → ¬SkipPreAST sub_T → IsValid (.notP s e sub_T)

  def PreAST.size (T : PreAST n b) : Nat :=
    match T with
    | .skip _ _ _ => 0
    | .ε _ _ => 0
    | .any _ _ _ => 0
    | .terminal _ _ _ _ => 0
    | .nonTerminal _ _ _ T => T.size + 1
    | .seq _ _ T1 T2 => T1.size + T2.size + 1
    | .prior _ _ T1 T2 => T1.size + T2.size + 1
    | .star _ _ T0 TS => T0.size + TS.size + 1
    | .notP _ _ T => T.size + 1
  
  def PreAST.start (T : PreAST n b) : Fin b :=
    match T with
    | .skip s _ _             => s
    | .ε s _                  => s
    | .any s _ _              => s
    | .terminal s _ _ _       => s
    | .nonTerminal s _ _ _    => s
    | .seq s _ _ _            => s
    | .prior s _ _ _          => s
    | .star s _ _ _           => s
    | .notP s _ _             => s

  def PreAST.end (T : PreAST n b) : Fin b :=
    match T with
    | .skip _ e _             => e
    | .ε _ e                  => e
    | .any _ e _              => e
    | .terminal _ e _ _       => e
    | .nonTerminal _ e _ _    => e
    | .seq _ e _ _            => e
    | .prior _ e _ _          => e
    | .star _ e _ _           => e
    | .notP _ e _             => e

  mutual

  inductive PreAST.SuccessAST : PreAST n b → Prop where
    | ε : s = e → SuccessAST (.ε s e)
    | any : s.inbound_succ h = e → SuccessAST (.any s e x)
    | terminal : s.inbound_succ h = e → a = x → SuccessAST (.terminal s e a x)
    | nonTerminal : SuccessAST T → SuccessAST (.nonTerminal s e A T)
    | seq : SuccessAST T1 → SuccessAST T2 → SuccessAST (.seq s e T1 T2)
    | prior_S : SuccessAST T1 → SuccessAST (.prior s e T1 T2)
    | prior_FS : FailureAST T1 → SuccessAST T2 → SuccessAST (.prior s e T1 T2)
    | star_F : FailureAST T0 → SuccessAST (.star s e T0 TS)
    | star_SS : SuccessAST T0 → SuccessAST TS → SuccessAST (.star s e T0 TS)
    | notP : FailureAST T → SuccessAST (.notP s e T)

  inductive PreAST.FailureAST : PreAST n b → Prop where
    | any : s = e → Fin.IsMax e → FailureAST (.any s e x)
    | terminal_mismatch : s.inbound_succ h = e → a ≠ x → FailureAST (.terminal s e a x)
    | terminal_empty : s = e → Fin.IsMax e → FailureAST (.terminal s e a x)
    | nonTerminal : FailureAST T → FailureAST (.nonTerminal s e A T)
    | seq_F : FailureAST T1 → FailureAST (.seq s e T1 T2)
    | seq_SF : SuccessAST T1 → FailureAST T2 → FailureAST (.seq s e T1 T2)
    | prior : FailureAST T1 → FailureAST T2 → FailureAST (.prior s e T1 T2)
    | notP : SuccessAST T → FailureAST (.notP s e T)

  end

  theorem PreAST.SuccessAST.ne_failure : ∀ {T : PreAST n b}, PreAST.IsValid T → SuccessAST T → ¬FailureAST T := by
    intro T valid_T hs hf;
    match T with
      | .skip _ _ _ => cases hs;
      | .ε _ _ => cases hf;
      | .any _ _ _ => cases hs; cases hf; apply absurd (by assumption); apply Fin.ne_of_val_ne; apply Nat.ne_of_lt; apply Fin.lt_from_inbound_succ; assumption;
      | .terminal s e a x => cases hs; cases hf; contradiction; apply absurd (by assumption); apply Fin.ne_of_val_ne; apply Nat.ne_of_lt; apply Fin.lt_from_inbound_succ; assumption;
      | .nonTerminal s e A _ => match hs with
        | .nonTerminal (T := Ts) st =>
          {
            match hf with
            | .nonTerminal (T := Ts) ft => 
              {
                apply absurd ft; apply ne_failure; cases valid_T; assumption; assumption;
              }
          }
      | .seq s e _ _ => match hs with
        | .seq (T1 := T1) (T2 := T2) st1 st2 =>
          {
            match hf with
              | .seq_F (T1 := T1) (T2 := T2) ft1 =>
                {
                  apply absurd ft1; apply ne_failure; cases valid_T; assumption; assumption;
                }
              | .seq_SF (T1 := T1) (T2 := T2) _ ft2 =>
                {
                  apply absurd ft2; apply ne_failure; cases valid_T; assumption; assumption;
                }
          }
      | .prior s e _ _ => match hf with
        | .prior (T1 := T1) (T2 := T2) ft1 ft2 =>
          {
            match hs with
              | .prior_S (T1 := T1) (T2 := T2) st1 =>
                {
                  apply absurd ft1; apply ne_failure; cases valid_T; assumption; assumption;
                }
              | .prior_FS (T1 := T1) (T2 := T2) _ st2 =>
                {
                  apply absurd ft2; apply ne_failure; cases valid_T; assumption; assumption;
                }
          }
      | .star s e _ _ => cases hf;
      | .notP s e _ => match hs with
        | .notP (T := T) ft =>
          {
            match hf with
              | .notP (T := T) st =>
                {
                  apply absurd ft; apply ne_failure; cases valid_T; assumption; assumption;
                }
          }

  theorem PreAST.FailureAST.ne_success : ∀ {T : PreAST n b}, PreAST.IsValid T → FailureAST T → ¬SuccessAST T := by
    intro T valid_T hf hs;
    exact SuccessAST.ne_failure valid_T hs hf;

  theorem PreAST.PreAST.star_cannot_fail : ∀ {T : PreAST n b}, StarPreAST T → ¬FailureAST T := by
    intro T h_star h_fail;
    cases h_star; cases h_fail;
  
  def PreAST.IsMeaningful (T : PreAST n b) : Prop := SuccessAST T ∨ FailureAST T

  inductive PreAST.IsWellformed : PreAST n b → Prop where
    | ε :           IsMeaningful (.ε (n := n) (b := b) s e)
                    → IsWellformed (.ε (n := n) (b := b) s e)
    | any :         IsMeaningful (.any (n := n) (b := b) s e x)
                    → IsWellformed (.any (n := n) (b := b) s e x)
    | terminal :    IsMeaningful (.terminal (n := n) (b := b) s e a x)
                    → IsWellformed (.terminal (n := n) (b := b) s e a x)
    | nonTerminal : ∀ {sub_T : PreAST n b},
                    s = sub_T.start → e = sub_T.end 
                    → IsWellformed sub_T 
                    → IsWellformed (.nonTerminal s e A sub_T)
    | seq_F :       ∀ {T1 T2 : PreAST n b},
                    s = T1.start → T1.end = T2.start → e = T2.end → T2.start = T2.end
                    → IsWellformed T1 → FailureAST T1 → SkipPreAST T2
                    → IsWellformed (.seq s e T1 T2)
    | seq_S :       ∀ {T1 T2 : PreAST n b},
                    s = T1.start → T1.end = T2.start → e = T2.end 
                    → IsWellformed T1 → SuccessAST T1 → IsWellformed T2
                    → IsWellformed (.seq s e T1 T2)
    | prior_S :     ∀ {T1 T2 : PreAST n b},
                    s = T1.start → s = T2.start → s = T2.end → e = T1.end 
                    → IsWellformed T1 → SuccessAST T1 → SkipPreAST T2
                    → IsWellformed (.prior s e T1 T2)
    | prior_F :     ∀ {T1 T2 : PreAST n b},
                    s = T1.start → s = T2.start → e = T2.end 
                    → IsWellformed T1 → FailureAST T1 → IsWellformed T2
                    → IsWellformed (.prior s e T1 T2)
    | star_S :      ∀ {T0 TS : PreAST n b},
                    s = T0.start → T0.end = TS.start → e = TS.end
                    → IsWellformed T0 → SuccessAST T0 → IsWellformed TS
                    → IsWellformed (.star s e T0 TS)
    | star_F :      ∀ {T0 TS : PreAST n b},
                    s = T0.start → T0.end = TS.start → TS.start = TS.end → s = e
                    → IsWellformed T0 → FailureAST T0 → SkipPreAST TS
                    → IsWellformed (.star s e T0 TS)
    | notP :        ∀ {sub_T : PreAST n b},
                    s = e → s = sub_T.start
                    → IsWellformed sub_T 
                    → IsWellformed (.notP s e sub_T)

  theorem PreAST.skip_is_not_wellformed : ∀ {T : PreAST n b}, SkipPreAST T → ¬IsWellformed T := by
    intro T hskip hwf;
    cases hskip; cases hwf;

  theorem PreAST.valid_and_wellformed_implies_meaningful : ∀ {T : PreAST n b}, IsValid T → IsWellformed T → IsMeaningful T := by
    intro T h_valid hwf;
    match hwf with
    | .ε _ => assumption;
    | .any _ => assumption;
    | .terminal _ => assumption;
    | .nonTerminal _ _ hwfT =>
      {
        cases h_valid; cases valid_and_wellformed_implies_meaningful (by assumption) hwfT;
        apply Or.inl; constructor <;> assumption;
        apply Or.inr; constructor <;> assumption;
      }
    | .seq_F _ _ _ _ _ hf1 hskip2 =>
      {
        cases h_valid; apply Or.inr;
        apply FailureAST.seq_F <;> assumption;
      }
    | .seq_S _ _ _ _ hs1 hwf2 =>
      {
        cases h_valid; cases valid_and_wellformed_implies_meaningful (by assumption) hwf2;
        apply Or.inl; constructor <;> assumption;
        apply Or.inr; apply FailureAST.seq_SF <;> assumption;
      }
    | .prior_S _ _ _ _ _ hs1 hskip2 =>
      {
        cases h_valid; apply Or.inl;
        apply SuccessAST.prior_S <;> assumption;
      }
    | .prior_F _ _ _ _ hf1 hwf2 =>
      {
        cases h_valid; cases valid_and_wellformed_implies_meaningful (by assumption) hwf2;
        apply Or.inl; apply SuccessAST.prior_FS <;> assumption;
        apply Or.inr; constructor <;> assumption;
      }
    | .star_S (TS := TS) _ _ _ _ hs0 hwfS =>
      {
        match h_valid with
        | PreAST.IsValid.star _ _ _ svs => 
          match svs with
          | Or.inl hskip =>
            {
              apply absurd hwfS;
              apply skip_is_not_wellformed; assumption;
            }
          | Or.inr hstar =>
            {
              apply Or.inl; apply SuccessAST.star_SS;
              assumption;
              match valid_and_wellformed_implies_meaningful (by assumption) hwfS with
              | Or.inl _ => assumption
              | Or.inr hf => cases hstar; cases hf;
            }
        
      }
    | .star_F _ _ _ _ _ hf0 hskipS =>
      {
        cases h_valid; apply Or.inl;
        apply SuccessAST.star_F <;> assumption;
      }
    | .notP _ _ hwfT =>
      {
        cases h_valid; cases valid_and_wellformed_implies_meaningful (by assumption) hwfT;
        apply Or.inr; constructor <;> assumption;
        apply Or.inl; constructor <;> assumption;
      }
  
  theorem PreAST.valid_and_wellformed_implies_start_le_end : ∀ {T : PreAST n b}, IsValid T → IsWellformed T → T.start ≤ T.end := by
    intro T h_valid hwf;
    match hwf with
    | .ε hm =>
      {
        simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        match hm with
        | Or.inl hs => cases hs; apply Nat.le_of_eq; apply Fin.val_eq_of_eq; assumption;
      }
    | .any hm =>
      {
        simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        match hm with
        | Or.inl hs => cases hs; apply Nat.le_of_lt; apply Fin.lt_from_inbound_succ; assumption;
        | Or.inr hf => cases hf; apply Nat.le_of_eq; apply Fin.val_eq_of_eq; assumption;
      }
    | .terminal hm =>
      {
        simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        match hm with
        | Or.inl hs => cases hs; apply Nat.le_of_lt; apply Fin.lt_from_inbound_succ; assumption;
        | Or.inr hf => cases hf; apply Nat.le_of_lt; apply Fin.lt_from_inbound_succ; assumption; apply Nat.le_of_eq; apply Fin.val_eq_of_eq; assumption;
      }
    | .nonTerminal hssT heeT hwfT =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hssT, heeT];
        apply valid_and_wellformed_implies_start_le_end <;> assumption;
      }
    | .seq_F hss1 he1s2 hee2 hs2e2 hwf1 _ hskip2 =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hss1, hee2, ←hs2e2, ←he1s2]
        apply valid_and_wellformed_implies_start_le_end <;> assumption;
      }
    | .seq_S hss1 he1s2 hee2 hwf1 _ hwf2 =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hss1, hee2];
        apply Nat.le_trans;
        apply valid_and_wellformed_implies_start_le_end (by assumption) hwf1;
        rw [he1s2];
        apply valid_and_wellformed_implies_start_le_end (by assumption) hwf2;
      }
    | .prior_S hss1 _ _ hee1 hwf1 _ hskip2 =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hss1, hee1];
        apply valid_and_wellformed_implies_start_le_end (by assumption) hwf1;
      }
    | .prior_F _ hss2 hee2 _ _ hwf2 =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hss2, hee2];
        apply valid_and_wellformed_implies_start_le_end (by assumption) hwf2;
      }
    | .star_S (TS := TS) hss0 he0sS heeS hwf0 _ hwfS =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hss0, heeS];
        apply Nat.le_trans;
        apply valid_and_wellformed_implies_start_le_end (by assumption) hwf0;
        rw [he0sS];
        apply valid_and_wellformed_implies_start_le_end (by assumption) hwfS;
      }
    | .star_F _ _ _ hse _ _ hskipS =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hse];
        apply Nat.le_refl;
      }
    | .notP hse _ hwfT =>
      {
        cases h_valid; simp [PreAST.start, PreAST.end, PreAST.start, PreAST.end];
        rw [hse];
        apply Nat.le_refl;
      }

  structure AST (n : Nat) (b : Nat) where
    T : PreAST n b
    valid_T : PreAST.IsValid T
    wf_T : PreAST.IsWellformed T
  
  def AST.size (T : AST n b) : Nat := T.T.size
  def AST.start (T : AST n b) : Fin b := T.T.start
  def AST.end (T : AST n b) : Fin b := T.T.end

  theorem AST.meaningful (T : AST n b) : PreAST.IsMeaningful T.T := PreAST.valid_and_wellformed_implies_meaningful T.valid_T T.wf_T
  theorem AST.start_le_end (T : AST n b) : T.start ≤ T.end := by
    rw [AST.start, AST.end];
    apply PreAST.valid_and_wellformed_implies_start_le_end T.valid_T T.wf_T;

end AST