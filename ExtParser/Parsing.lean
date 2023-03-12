import ExtParser.AST
namespace Parsing
  open AST
  open Grammar

  inductive PreAST.TrueToGrammar : PreAST n b → GProd n → PEG n → Prop where
    | skip : TrueToGrammar (.skip s e G) Pexp G
    | ε : TrueToGrammar (.ε s e) Pexp .ε
    | any : TrueToGrammar (.any s e x) Pexp .any
    | terminal : TrueToGrammar (.terminal s e a x) Pexp (.terminal a)
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
          | .any (Or.inr (.any h _)) =>
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
          | .terminal (Or.inr (.terminal_empty h _)) =>
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


  theorem AST.unique_tree : ∀ {T1 T2 : AST n b} {inp : Input b} {G : PEG n} {Pexp : GProd n}, 
                            AST.TrueToInput T1 inp → AST.TrueToInput T2 inp → 
                            AST.TrueToGrammar T1 Pexp G → AST.TrueToGrammar T2 Pexp G → 
                            T1.start = T2.start → T1 = T2 := by
    intro (.mk T1 valid_T1 wf_T1) (.mk T2 valid_T2 wf_T2) inp G Pexp hi1 hi2 hg1 hg2 hstart;
    cases T1 with
    | skip _ _ _ => cases wf_T1;
    | ε s1 e1 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | ε s2 e2 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        match wf_T1, wf_T2 with
        | .ε (Or.inl (.ε h1)), .ε (Or.inl (.ε h2)) => rw [←h1, hstart, h2];
      }
      | _ => cases hg1; cases hg2;
    | any s1 e1 x1 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | any s2 e2 x2 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        have hx : x1 = x2 := by
          {
            simp [hstart] at hi1;
            cases hi1; cases hi2;
            apply Eq.trans; apply Eq.symm; assumption; assumption;
          }
        simp [hx];
        match wf_T1, wf_T2 with
        | .any (Or.inl (.any h1)), .any (Or.inl (.any h2)) =>
          {
            simp [hstart] at h1;
            exact Eq.trans (Eq.symm h1) h2;
          }
        | .any (Or.inl (.any h1)), .any (Or.inr (.any h2 hb2)) =>
          {
            rw [←h2, ←hstart, Fin.IsMax] at hb2;
            contradiction;
          }
        | .any (Or.inr (.any h1 hb1)), .any (Or.inl (.any h2)) =>
          {
            rw [←h1, hstart, Fin.IsMax] at hb1;
            contradiction;
          }
        | .any (Or.inr (.any h1 hb1)), .any (Or.inr (.any h2 hb2)) =>
          {
            rw [←h1, hstart, h2];
          }
      }
      | _ => cases hg1; cases hg2;
    | terminal s1 e1 a1 x1 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | terminal s2 e2 a2 x2 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        have hx : x1 = x2 := by
          {
            simp [hstart] at hi1;
            cases hi1; cases hi2;
            apply Eq.trans; apply Eq.symm; assumption; assumption;
          }
        simp [hx];
        cases hg1; cases hg2; simp;
        match wf_T1, wf_T2 with
        | .terminal (Or.inl (.terminal h1 g1)), .terminal (Or.inl (.terminal h2 g2)) =>
          {
            simp [g1, ←g2];
            apply Fin.eq_of_val_eq;
            simp [←Fin.val_eq_of_eq h1, ←Fin.val_eq_of_eq h2, Fin.inbound_succ];
            exact Fin.val_eq_of_eq hstart;
          }
        | .terminal (Or.inl (.terminal h1 g1)), .terminal (Or.inr (.terminal_mismatch h2 g2)) =>
          {
            rw [hx] at g1;
            contradiction;
          }
        | .terminal (Or.inl (.terminal h1 g1)), .terminal (Or.inr (.terminal_empty h2 hb2)) =>
          {
            simp [←h2, ←hstart, Fin.IsMax] at hb2;
            contradiction;
          }
        | .terminal (Or.inr (.terminal_mismatch h1 g1)), .terminal (Or.inl (.terminal h2 g2)) =>
          {
            rw [hx] at g1; contradiction;
          }
        | .terminal (Or.inr (.terminal_mismatch h1 g1)), .terminal (Or.inr (.terminal_mismatch h2 g2)) =>
          {
            apply Fin.eq_of_val_eq;
            simp [←Fin.val_eq_of_eq h1, ←Fin.val_eq_of_eq h2, Fin.inbound_succ];
            exact Fin.val_eq_of_eq hstart;
          }
        | .terminal (Or.inr (.terminal_mismatch h1 g1)), .terminal (Or.inr (.terminal_empty h2 hb2)) =>
          {
            simp [←h2, ←hstart, Fin.IsMax] at hb2;
            contradiction;
          }
        | .terminal (Or.inr (.terminal_empty h1 hb1)), .terminal (Or.inl (.terminal h2 g2)) =>
          {
            simp [←h1, hstart, Fin.IsMax] at hb1;
            contradiction;
          }
        | .terminal (Or.inr (.terminal_empty h1 hb1)), .terminal (Or.inr (.terminal_mismatch h2 g2)) =>
          {
            simp [←h1, hstart, Fin.IsMax] at hb1;
            contradiction;
          }
        | .terminal (Or.inr (.terminal_empty h1 hb1)), .terminal (Or.inr (.terminal_empty h2 hb2)) =>
          {
            simp [←h1, hstart, h2];
          }
      }
      | _ => cases hg1; cases hg2;
    | nonTerminal s1 e1 A1 T1 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | nonTerminal s2 e2 A2 T2 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        match wf_T1, wf_T2, valid_T1, valid_T2 with
        | .nonTerminal hss1 hee1 hwfT1, .nonTerminal hss2 hee2 hwfT2, .nonTerminal hvT1 _ , .nonTerminal hvT2 _ =>
          {
            cases hi1; cases hi2; cases hg1; cases hg2;
            have _ : (AST.mk T1 hvT1 hwfT1).size < (AST.mk (.nonTerminal s1 e1 A1 T1) valid_T1 wf_T1).size := by
            {
              simp [AST.size, PreAST.size]; apply Nat.lt_succ_self;
            }
            have g : AST.mk T1 hvT1 hwfT1 = AST.mk T2 hvT2 hwfT2 := by
            {
              apply unique_tree;
              assumption;
              assumption;
              assumption;
              assumption;
              simp [AST.start, ←hss1, ←hss2, hstart];
            }
            cases g;
            simp [hee1, hee2];
          }
      }
      | _ => cases hg1; cases hg2;
    | seq s1 e1 T11 T21 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | seq s2 e2 T12 T22 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        match wf_T1, wf_T2 with
        | .seq_F hss11 he11s21 hee21 hs21e21 hwf11 hf11 hskip21, .seq_F hss12 he12s22 hee22 hs22e22 hwf12 hf12 hskip22 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .seq hg11 hg21, .seq hg12 hg22, .seq hv11 _ _, .seq hv12 _ _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.seq s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              cases g1; simp;
              cases hskip21; cases hskip22;
              cases hg21; cases hg22;
              simp [PreAST.start, PreAST.end] at hs21e21 hee21 hs22e22 hee22;
              simp [PreAST.start] at he11s21 he12s22;
              simp [hee21, hee22, ←he11s21, ←he12s22, ←hs21e21, ←hs22e22];
            }
          }
        | .seq_F hss11 he11s21 hee21 hs21e21 hwf11 hf11 _, .seq_S hss12 he12s22 hee22 hwf12 hs12 _ =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .seq hg11 hg21, .seq hg12 hg22, .seq hv11 _ _, .seq hv12 _ _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.seq s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              cases g1; simp;
              exact absurd hf11 (hs12.ne_failure (by assumption));
            }
          }
        | .seq_S hss11 he11s21 hee21 hwf11 hs11 _, .seq_F hss12 he12s22 hee22 hs22e22 hwf12 hf12 _ =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .seq hg11 hg21, .seq hg12 hg22, .seq hv11 _ _, .seq hv12 _ _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.seq s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              cases g1; simp;
              exact absurd hs11 (hf12.ne_success (by assumption));
            }
          }
        | .seq_S hss11 he11s21 hee21 hwf11 hs11 hwf21, .seq_S hss12 he12s22 hee22 hwf12 hs12 hwf22 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .seq hg11 hg21, .seq hg12 hg22, .seq hv11 hv21 _, .seq hv12 hv22 _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.seq s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              cases g1; simp;
              have _ : (AST.mk T21 hv21 hwf21).size < (AST.mk (.seq s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [Nat.add_comm (PreAST.size T11), ←Nat.add_zero (PreAST.size T21), Nat.add_assoc (PreAST.size T21 + 0)];
                apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g2 : AST.mk T21 hv21 hwf21 = AST.mk T22 hv22 hwf22 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←he11s21, ←he12s22];
              }
              cases g2; simp;
              simp [hee21, hee22];
            }
          }
      }
      | _ => cases hg1; cases hg2;
    | prior s1 e1 T11 T21 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | prior s2 e2 T12 T22 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        match wf_T1, wf_T2 with
        | .prior_F hss11 hss21 hee21 hwf11 hf11 hwf21, .prior_F hss12 hss22 hee22 hwf12 hf12 hwf22 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .prior hg11 hg21, .prior hg12 hg22, .prior hv11 hv21 _, .prior hv12 hv22 _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.prior s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              have _ : (AST.mk T21 hv21 hwf21).size < (AST.mk (.prior s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [Nat.add_comm (PreAST.size T11), ←Nat.add_zero (PreAST.size T21), Nat.add_assoc (PreAST.size T21 + 0)];
                apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g2 : AST.mk T21 hv21 hwf21 = AST.mk T22 hv22 hwf22 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss21, ←hss22, hstart];
              }
              cases g1; cases g2; simp;
              simp [hee21, hee22];
            }
          }
        | .prior_F hss11 hss21 hee21 hwf11 hf11 hwf21, .prior_S hss12 hss22 hse22 hee12 hwf12 hs12 hskip22 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .prior hg11 hg21, .prior hg12 hg22, .prior hv11 hv21 _, .prior hv12 hv22 _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.prior s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              cases g1; simp;
              exact absurd hf11 (hs12.ne_failure (by assumption));
            }
          }
        | .prior_S hss11 hss21 hse21 hee11 hwf11 hs11 hskip21, .prior_F hss12 hss22 hee22 hwf12 hf12 hwf22 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .prior hg11 hg21, .prior hg12 hg22, .prior hv11 hv21 _, .prior hv12 hv22 _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.prior s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              cases g1; simp;
              exact absurd hs11 (hf12.ne_success (by assumption));
            }
          }
        | .prior_S hss11 hss21 hse21 hee11 hwf11 hs11 hskip21, .prior_S hss12 hss22 hse22 hee12 hwf12 hs12 hskip22 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .prior hg11 hg21, .prior hg12 hg22, .prior hv11 hv21 _, .prior hv12 hv22 _ =>
            {
              have _ : (AST.mk T11 hv11 hwf11).size < (AST.mk (.prior s1 e1 T11 T21) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T11), Nat.add_assoc (PreAST.size T11 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T11 hv11 hwf11 = AST.mk T12 hv12 hwf12 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss11, ←hss12, hstart];
              }
              cases g1; simp;
              cases hskip21; cases hskip22;
              cases hg21; cases hg22;
              simp [PreAST.start] at hss21 hss22;
              simp [PreAST.end] at hse21 hse22;
              simp [hee11, hee12, ←hss21, ←hse21, ←hss22, ←hse22, hstart];
            }
          }
      }
      | _ => cases hg1; cases hg2;
    | star s1 e1 T01 TS1 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | star s2 e2 T02 TS2 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        match wf_T1, wf_T2 with
        | .star_F hss01 he01sS1 hsS1eS1 hse1 hwf01 hf01 hskipS1, .star_F hss02 he02sS2 hsS2eS2 hse2 hwf02 hf02 hskipS2 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .star hg01 hgS1, .star hg02 hgS2, .star hv01 hvS1 _ _, .star hv02 hvS2 _ _ =>
            {
              have _ : (AST.mk T01 hv01 hwf01).size < (AST.mk (.star s1 e1 T01 TS1) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T01), Nat.add_assoc (PreAST.size T01 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T01 hv01 hwf01 = AST.mk T02 hv02 hwf02 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss01, ←hss02, hstart];
              }
              cases g1; simp;
              cases hskipS1; cases hskipS2;
              cases hgS1; cases hgS2;
              simp [PreAST.start, PreAST.end] at hsS1eS1 hsS2eS2;
              simp [PreAST.start] at he01sS1 he02sS2;
              simp [←hse1, ←hse2, ←hsS1eS1, ←hsS2eS2, ←he01sS1, ←he02sS2, hstart];
            }
          }
        | .star_F hss01 he01sS1 hsS1eS1 hse1 hwf01 hf01 hskipS1, .star_S hss02 he02sS2 heeS2 hwf02 hs02 hwfS2 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .star hg01 hgS1, .star hg02 hgS2, .star hv01 hvS1 _ _, .star hv02 hvS2 _ _ =>
            {
              have _ : (AST.mk T01 hv01 hwf01).size < (AST.mk (.star s1 e1 T01 TS1) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T01), Nat.add_assoc (PreAST.size T01 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T01 hv01 hwf01 = AST.mk T02 hv02 hwf02 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss01, ←hss02, hstart];
              }
              cases g1; simp;
              exact absurd hf01 (hs02.ne_failure (by assumption));
            }
          }
        | .star_S hss01 he01sS1 heeS1 hwf01 hs01 hwfS1, .star_F hss02 he02sS2 hsS2eS2 hse2 hwf02 hf02 hskipS2 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .star hg01 hgS1, .star hg02 hgS2, .star hv01 hvS1 _ _, .star hv02 hvS2 _ _ =>
            {
              have _ : (AST.mk T01 hv01 hwf01).size < (AST.mk (.star s1 e1 T01 TS1) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T01), Nat.add_assoc (PreAST.size T01 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T01 hv01 hwf01 = AST.mk T02 hv02 hwf02 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss01, ←hss02, hstart];
              }
              cases g1; simp;
              exact absurd hs01 (hf02.ne_success (by assumption));
            }
          }
        | .star_S hss01 he01sS1 heeS1 hwf01 hs01 hwfS1, .star_S hss02 he02sS2 heeS2 hwf02 hs02 hwfS2 =>
          {
            cases hi1; cases hi2;
            match hg1, hg2, valid_T1, valid_T2 with
            | .star hg01 hgS1, .star hg02 hgS2, .star hv01 hvS1 _ _, .star hv02 hvS2 _ _ =>
            {
              have _ : (AST.mk T01 hv01 hwf01).size < (AST.mk (.star s1 e1 T01 TS1) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [←Nat.add_zero (PreAST.size T01), Nat.add_assoc (PreAST.size T01 + 0)]; apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g1 : AST.mk T01 hv01 hwf01 = AST.mk T02 hv02 hwf02 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←hss01, ←hss02, hstart];
              }
              cases g1; simp;
              have _ : (AST.mk TS1 hvS1 hwfS1).size < (AST.mk (.star s1 e1 T01 TS1) valid_T1 wf_T1).size := by
              {
                simp [AST.size, PreAST.size]; rw [Nat.add_comm (PreAST.size T01), ←Nat.add_zero (PreAST.size TS1), Nat.add_assoc (PreAST.size TS1 + 0)];
                apply Nat.add_lt_add_left; apply Nat.zero_lt_succ;
              }
              have g2 : AST.mk TS1 hvS1 hwfS1 = AST.mk TS2 hvS2 hwfS2 := by
              {
                apply unique_tree;
                assumption;
                assumption;
                assumption;
                assumption;
                simp [AST.start, ←he01sS1, ←he02sS2];
              }
              cases g2; simp;
              simp [heeS1, heeS2];
            }
          }
      }
      | _ => cases hg1; cases hg2;
    | notP s1 e1 T1 => cases T2 with
      | skip _ _ _ => cases wf_T2;
      | notP s2 e2 T2 =>
      {
        simp [AST.start, PreAST.start] at hstart; simp [hstart];
        match wf_T1, wf_T2, valid_T1, valid_T2 with
        | .notP hse1 hssT1 hwfT1, .notP hse2 hssT2 hwfT2, .notP hv1 _, .notP hv2 _ =>
        {
          have _ : (AST.mk T1 hv1 hwfT1).size < (AST.mk (.notP s1 e1 T1) valid_T1 wf_T1).size := by
          {
            simp [AST.size, PreAST.size]; apply Nat.lt_succ_self;
          }
          have g : AST.mk T1 hv1 hwfT1 = AST.mk T2 hv2 hwfT2 := by
          {
            cases hi1; cases hi2; cases hg1; cases hg2;
            apply unique_tree;
            assumption;
            assumption;
            assumption;
            assumption;
            simp [AST.start, ←hssT1, ←hssT2, hstart];
          }
          cases g; simp;
          simp [←hse1, ←hse2, hstart];
        }
      }
      | _ => cases hg1; cases hg2;
  termination_by AST.unique_tree _ _ T1 => T1.size
  decreasing_by sorry



end Parsing