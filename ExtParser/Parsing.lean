import ExtParser.AST
namespace Parsing
  open AST
  open CoreParser

  inductive PreAST.TrueToGrammar : PreAST n b → GProd n → PEG n → Prop where
    | skip : TrueToGrammar (.skip s e G) Pexp G
    | ε : TrueToGrammar (.ε s e) Pexp .ε
    | any : TrueToGrammar (.any s e x) Pexp .any
    | terminal : TrueToGrammar (.terminal s e a x) Pexp (.terminal x)
    | nonTerminal : TrueToGrammar T Pexp (Pexp.f A) → TrueToGrammar (.nonTerminal s e A T) Pexp (.nonTerminal A)
    | seq : TrueToGrammar T1 Pexp e1 → TrueToGrammar T2 Pexp e2 → TrueToGrammar (.seq s e T1 T2) Pexp (.seq e1 e2)
    | prior : TrueToGrammar T1 Pexp e1 → TrueToGrammar T2 Pexp e2 → TrueToGrammar (.prior s e T1 T2) Pexp (.prior e1 e2)
    | star : TrueToGrammar T0 Pexp e0 → TrueToGrammar TS Pexp (.star e0) → TrueToGrammar (.star s e T0 TS) Pexp (.star e0)
    | notP : TrueToGrammar T Pexp e0 → TrueToGrammar (.notP s e T) Pexp (.notP e0)

  def AST.TrueToGrammar : AST n b → GProd n → PEG n → Prop := fun T => PreAST.TrueToGrammar T.T

  theorem PreAST.unique_grammar : ∀ {T : PreAST n b} {G1 G2 : PEG n} {Pexp : GProd n}, TrueToGrammar T Pexp G1 → TrueToGrammar T Pexp G2 → G1 = G2 := by
    intro T G1 G2 Pexp h1 h2;
    cases T;
    {cases h1; cases h2; rfl}
    {cases h1; cases h2; rfl}
    {cases h1; cases h2; rfl}
    {cases h1; cases h2; rfl}
    {cases h1; cases h2; rfl}
    {
      match h1, h2 with
      | .seq h11 h12, .seq h21 h22 => rw [unique_grammar h11 h21, unique_grammar h12 h22];
    }
    {
      match h1, h2 with
      | .prior h11 h12, .prior h21 h22 => rw [unique_grammar h11 h21, unique_grammar h12 h22];
    }
    {
      match h1, h2 with
      | .star h11 _, .star h21 h22 => rw [unique_grammar h11 h21];
    }
    {
      match h1, h2 with
      | .notP h11, .notP h21 => rw [unique_grammar h11 h21];
    }
  
  theorem AST.unique_grammar : ∀ {T : AST n b} {G1 G2 : PEG n} {Pexp : GProd n}, TrueToGrammar T Pexp G1 → TrueToGrammar T Pexp G2 → G1 = G2 := by
    intro T;
    exact PreAST.unique_grammar (T := T.T);
  
  def Input (b : Nat) := Fin b → Char

  inductive PreAST.TrueToInput : PreAST n b → (inp : Input b) → Prop where
    | skip : TrueToInput (.skip s e G) inp
    | ε : TrueToInput (.ε s e) inp
    | any : inp s = x → TrueToInput (.any s e x) inp
    | terminal : inp s = x → TrueToInput (.terminal s e a x) inp
    | nonTerminal : TrueToInput T inp → TrueToInput (.nonTerminal s e A T) inp
    | seq : TrueToInput T1 inp → TrueToInput T2 inp → TrueToInput (.seq s e T1 T2) inp
    | prior : TrueToInput T1 inp → TrueToInput T2 inp → TrueToInput (.prior s e T1 T2) inp
    | star : TrueToInput T0 inp → TrueToInput TS inp → TrueToInput (.star s e T0 TS) inp
    | notP : TrueToInput T inp → TrueToInput (.notP s e T) inp

  def AST.TrueToInput : AST n b → Input b → Prop := fun T => PreAST.TrueToInput T.T

  theorem AST.unique_input : ∀ {T : AST n b} {inp1 inp2 : Input b}, TrueToInput T inp1 → TrueToInput T inp2 → T.start ≤ i → i < T.end → inp1 i = inp2 i := by
    intro (.mk T valid_T wf_T) inp1 inp2 h1 h2 hstart hend;
    match T with
    | .skip _ _ _ => cases wf_T
    | .ε _ _ => match wf_T with
      | .ε (Or.inl (.ε h)) =>
        {
          simp [AST.start, PreAST.start, AST.end, PreAST.end] at hstart hend;
          rw [h] at hstart; have g : i < i := Nat.lt_of_lt_of_le hend hstart; 
          apply absurd g (Nat.lt_irrefl i);
        }
    | .any s e x => match h1, h2 with
      | .any heq1, .any heq2 =>
        {
          simp [AST.start, PreAST.start, AST.end, PreAST.end] at hstart hend;
          match wf_T with
          | .any (Or.inl (.any h)) =>
            {
              match Nat.eq_or_lt_of_le hstart with
              | Or.inl g => simp [←Fin.eq_of_val_eq g, heq1, heq2];
              | Or.inr g =>
                {
                  apply absurd (Fin.val_eq_of_eq h);
                  simp [Fin.inbound_succ];
                  apply Nat.ne_of_lt;
                  exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ g) hend;
                }
            }
          | .any (Or.inr (.any h)) =>
            {
              rw [h] at hstart;
              apply absurd hstart;
              exact Nat.not_le_of_gt hend;
            }

        }
    | .terminal s e a x => match h1, h2 with
      | .terminal (s := s) (e := e) heq1, .terminal heq2 =>
        {
          simp [AST.start, PreAST.start, AST.end, PreAST.end] at hstart hend;
          match wf_T with
          | .terminal (Or.inl (.terminal h _)) =>
            {
              match Nat.eq_or_lt_of_le hstart with
              | Or.inl g => simp [←Fin.eq_of_val_eq g, heq1, heq2];
              | Or.inr g =>
                {
                  apply absurd (Fin.val_eq_of_eq h);
                  simp [Fin.inbound_succ];
                  apply Nat.ne_of_lt;
                  exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ g) hend;
                }
            }
          | .terminal (Or.inr (.terminal_mismatch h _)) =>
            {
              match Nat.eq_or_lt_of_le hstart with
              | Or.inl g => simp [←Fin.eq_of_val_eq g, heq1, heq2];
              | Or.inr g =>
                {
                  apply absurd (Fin.val_eq_of_eq h);
                  simp [Fin.inbound_succ];
                  apply Nat.ne_of_lt;
                  exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ g) hend;
                }
            }
          | .terminal (Or.inr (.terminal_empty h)) =>
            {
              rw [h] at hstart;
              apply absurd hstart;
              exact Nat.not_le_of_gt hend;
            }
        }
    | .nonTerminal s e A sub_T => match h1, h2 with
      | .nonTerminal (T := sub_T) h1, .nonTerminal h2 =>
        {
          match valid_T, wf_T with
          | .nonTerminal hv _, .nonTerminal hssT heeT hwf =>
            {
              let T' := AST.mk sub_T hv hwf;
              apply unique_input (T := T') h1 h2;
              rw [AST.start, ←hssT]; exact hstart;
              rw [AST.end, ←heeT]; exact hend;
            }
        }
    | .seq s e T1 T2 => match h1, h2 with
      | .seq h11 h12, .seq h21 h22 =>
        {
          simp [AST.start, PreAST.start, AST.end, PreAST.end] at hstart hend;
          match valid_T, wf_T with
          | .seq hv1 _ _, .seq_F hss1 he1s2 hee2 hs2e2 hwf1 _ _ =>
            {
              let T' := AST.mk T1 hv1 hwf1;
              apply unique_input (T := T') h11 h21;
              rw [AST.start, ←hss1]; exact hstart;
              rw [AST.end, he1s2, hs2e2, ←hee2]; exact hend;
            }
          | .seq hv1 hv2 _, .seq_S hss1 he1s2 hee2 hwf1 _ hwf2 =>
            {
              let T1' := AST.mk T1 hv1 hwf1;
              let T2' := AST.mk T2 hv2 hwf2;
              match Nat.lt_or_ge i (T1.end) with
              | Or.inl g =>
                {
                  apply unique_input (T := T1') h11 h21;
                  simp [AST.start, ←hss1]; exact hstart;
                  exact g;
                }
              | Or.inr g =>
                {
                  apply unique_input (T := T2') h12 h22;
                  simp [AST.start, ←he1s2]; exact g;
                  simp [AST.end, ←hee2]; exact hend;
                }
            }
        }
    | .prior s e T1 T2 => match h1, h2 with
      | .prior h11 h12, .prior h21 h22 =>
        {
          simp [AST.start, PreAST.start, AST.end, PreAST.end] at hstart hend;
          match valid_T, wf_T with
          | .prior hv1 _ _, .prior_S hss1 _ _ hee1 hwf1 _ _ =>
            {
              let T' := AST.mk T1 hv1 hwf1;
              apply unique_input (T := T') h11 h21;
              simp [AST.start, ←hss1]; exact hstart;
              simp [AST.end, ←hee1]; exact hend;
            }
          | .prior _ hv2 _, .prior_F _ hss2 hee2 _ _ hwf2 =>
            {
              let T' := AST.mk T2 hv2 hwf2;
              apply unique_input (T := T') h12 h22;
              simp [AST.start, ←hss2]; exact hstart;
              simp [AST.end, ←hee2]; exact hend;
            }
        }
    | .star s e T0 TS => match h1, h2 with
      | .star h10 h1S, .star h20 h2S =>
        {
          simp [AST.start, PreAST.start, AST.end, PreAST.end] at hstart hend;
          match valid_T, wf_T with
          | .star hv1 hv2 _ _, .star_F _ _ _ hse _ _ _ =>
            {
              rw [hse] at hstart;
              have g : e < e := Nat.lt_of_le_of_lt hstart hend;
              apply absurd g (Nat.lt_irrefl e);
            }
          | .star hv0 hvS _ _, .star_S hss0 he0sS heeS hwf0 _ hwfS =>
            {
              let T0' := AST.mk T0 hv0 hwf0;
              let TS' := AST.mk TS hvS hwfS;
              match Nat.lt_or_ge i (T0.end) with
              | Or.inl g =>
                {
                  apply unique_input (T := T0') h10 h20;
                  simp [AST.start, ←hss0]; exact hstart;
                  exact g;
                }
              | Or.inr g =>
                {
                  apply unique_input (T := TS') h1S h2S;
                  simp [AST.start, ←he0sS]; exact g;
                  simp [AST.end, ←heeS]; exact hend;
                }
            }
        }
    | .notP s e T => match h1, h2 with
      | .notP (T := sub_T) h1, .notP h2 =>
        {
          simp [AST.start, PreAST.start, AST.end, PreAST.end] at hstart hend;
          match valid_T, wf_T with
          | .notP hv _, .notP hse _ _ =>
            {
              rw [hse] at hstart;
              have g : e < e := Nat.lt_of_le_of_lt hstart hend;
              apply absurd g (Nat.lt_irrefl e);
            }
        }

end Parsing