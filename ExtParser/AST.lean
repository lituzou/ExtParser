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

  inductive PreAST'.IsValid : PreAST' n b → Prop where
    | skip : IsValid (.skip s e G)
    | ε : IsValid (.ε s e)
    | any : IsValid (.any s e x)
    | terminal : IsValid (.terminal s e a x)
    | nonTerminal : IsValid T → ¬SkipPreAST' T → IsValid (.nonTerminal s e A T)
    | seq : IsValid T1 → IsValid T2 → ¬SkipPreAST' T1 → IsValid (.seq s e T1 T2)
    | prior : IsValid T1 → IsValid T2 → ¬SkipPreAST' T1 → IsValid (.prior s e T1 T2)
    | star : IsValid T0 → IsValid TS → ¬SkipPreAST' T0 → (SkipPreAST' TS ∨ StarPreAST' TS) → IsValid (.star s e T0 TS)
    | notP : IsValid T → ¬SkipPreAST' T → IsValid (.notP s e T)

  def PreAST'.size (T : PreAST' n b) : Nat :=
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
  

  structure PreAST (n : Nat) (b : Nat) where
    T : PreAST' n b
    valid_T : PreAST'.IsValid T

  mutual

  inductive SuccessAST : PreAST n b → Prop where
    | ε : s = e → SuccessAST { T := .ε s e, valid_T := .ε }
    | any : s.inbound_succ h = e → SuccessAST { T := .any s e x, valid_T := .any }
    | terminal : s.inbound_succ h = e → a = x → SuccessAST { T := .terminal s e a x, valid_T := .terminal }
    | nonTerminal : SuccessAST T → SuccessAST { T := .nonTerminal s e A T.T, valid_T := .nonTerminal T.valid_T h}
    | seq : SuccessAST T1 → SuccessAST T2 → SuccessAST { T := .seq s e T1.T T2.T, valid_T := .seq T1.valid_T T2.valid_T h }
    | prior_S : ∀ {T2 : PreAST n b}, SuccessAST T1 → SuccessAST { T := .prior s e T1.T T2.T, valid_T := .prior T1.valid_T T2.valid_T h }
    | prior_FS : FailureAST T1 → SuccessAST T2 → SuccessAST { T := .prior s e T1.T T2.T, valid_T := .prior T1.valid_T T2.valid_T h }
    | star_F : ∀ {TS : PreAST n b} {h2 : SkipPreAST' TS.T ∨ StarPreAST' TS.T}, FailureAST T0 → SuccessAST { T := .star s e T0.T TS.T, valid_T := .star T0.valid_T TS.valid_T h1 h2 }
    | star_SS : SuccessAST T0 → SuccessAST TS → SuccessAST { T := .star s e T0.T TS.T, valid_T := .star T0.valid_T TS.valid_T h1 h2 }
    | notP : FailureAST T → SuccessAST { T := .notP s e T.T, valid_T := .notP T.valid_T h }

  inductive FailureAST : PreAST n b → Prop where
    | any : s = e → FailureAST { T := .any s e x, valid_T := .any }
    | terminal_mismatch : s.inbound_succ h = e → a ≠ x → FailureAST { T := .terminal s e a x, valid_T := .terminal }
    | terminal_empty : s = e → FailureAST { T := .terminal s e a x, valid_T := .terminal }
    | nonTerminal : FailureAST T → FailureAST { T := .nonTerminal s e A T.T, valid_T := .nonTerminal T.valid_T h}
    | seq_F : ∀ {T2 : PreAST n b}, FailureAST T1 → FailureAST { T := .seq s e T1.T T2.T, valid_T := .seq T1.valid_T T2.valid_T h }
    | seq_SF : SuccessAST T1 → FailureAST T2 → FailureAST { T := .seq s e T1.T T2.T, valid_T := .seq T1.valid_T T2.valid_T h }
    | prior : FailureAST T1 → FailureAST T2 → FailureAST { T := .prior s e T1.T T2.T, valid_T := .prior T1.valid_T T2.valid_T h }
    | notP : SuccessAST T → FailureAST { T := .notP s e T.T, valid_T := .notP T.valid_T h }

  end

  theorem SuccessAST.ne_failure : ∀ {T : PreAST n b}, SuccessAST T → ¬FailureAST T := by
    intro T hs hf;
    match T with
    | .mk T valid_T => match T with
      | .skip _ _ _ => cases hs;
      | .ε _ _ => cases hf;
      | .any _ _ _ => cases hs; cases hf; apply absurd (by assumption); apply Fin.ne_of_val_ne; apply Nat.ne_of_lt; apply Fin.lt_from_inbound_succ; assumption;
      | .terminal s e a x => cases hs; cases hf; contradiction; apply absurd (by assumption); apply Fin.ne_of_val_ne; apply Nat.ne_of_lt; apply Fin.lt_from_inbound_succ; assumption;
      | .nonTerminal s e A _ => match hs with
        | .nonTerminal (T := Ts) st =>
          {
            match Ts with
            | .mk Ts' _ => simp at hf; match hf with
              | .nonTerminal (T := Ts) ft => 
                {
                  have _ : PreAST'.size Ts.T < PreAST'.size (PreAST'.nonTerminal s e A Ts.T) := by
                  {
                    rw [PreAST'.size]; apply Nat.lt_succ_self;
                  }
                  apply absurd ft; apply ne_failure; exact st;
                }
          }
      | .seq s e _ _ => match hs with
        | .seq (T1 := T1) (T2 := T2) st1 st2 =>
          {
            match T1, T2 with
            | .mk T1' _, .mk T2' _ => simp at hf; match hf with
              | .seq_F (T1 := T1) (T2 := T2) ft1 =>
                {
                  have _ : PreAST'.size T1.T < PreAST'.size (PreAST'.seq s e T1.T T2.T) := by
                  {
                    rw [PreAST'.size];
                    apply Nat.lt_succ_of_le; simp;
                    apply Nat.le_add_right;
                  }
                  apply absurd ft1; apply ne_failure; exact st1;
                }
              | .seq_SF (T1 := T1) (T2 := T2) _ ft2 =>
                {
                  have _ : PreAST'.size T2.T < PreAST'.size (PreAST'.seq s e T1.T T2.T) := by
                  {
                    rw [PreAST'.size];
                    apply Nat.lt_succ_of_le; simp;
                    apply Nat.le_add_left;
                  }
                  apply absurd ft2; apply ne_failure; exact st2;
                }
          }
      | .prior s e _ _ => match hf with
        | .prior (T1 := T1) (T2 := T2) ft1 ft2 =>
          {
            match T1, T2 with
            | .mk T1' _, .mk T2' _ => simp at hs; match hs with
              | .prior_S (T1 := T1) (T2 := T2) st1 =>
                {
                  have _ : PreAST'.size T1.T < PreAST'.size (PreAST'.prior s e T1.T T2.T) := by
                  {
                    rw [PreAST'.size];
                    apply Nat.lt_succ_of_le; simp;
                    apply Nat.le_add_right;
                  }
                  apply absurd ft1; apply ne_failure; exact st1;
                }
              | .prior_FS (T1 := T1) (T2 := T2) _ st2 =>
                {
                  have _ : PreAST'.size T2.T < PreAST'.size (PreAST'.prior s e T1.T T2.T) := by
                  {
                    rw [PreAST'.size];
                    apply Nat.lt_succ_of_le; simp;
                    apply Nat.le_add_left;
                  }
                  apply absurd ft2; apply ne_failure; exact st2;
                }
          }
      | .star s e _ _ => cases hf;
      | .notP s e _ => match hs with
        | .notP (T := T) ft =>
          {
            match T with
            | .mk T' _ => simp at hf; match hf with
              | .notP (T := T) st =>
                {
                  have _ : PreAST'.size T.T < PreAST'.size (PreAST'.notP s e T.T) := by
                  {
                    rw [PreAST'.size];
                    apply Nat.lt_succ_of_le; simp;
                  }
                  apply absurd ft; apply ne_failure; exact st;
                }
          }
  termination_by SuccessAST.ne_failure T _ _ => T.T.size

  theorem FailureAST.ne_success : ∀ {T : PreAST n b}, FailureAST T → ¬SuccessAST T := by
    intro T hf hs;
    exact SuccessAST.ne_failure hs hf;

  inductive TypeAST : PreAST n b → Prop
    | success : SuccessAST T → TypeAST T
    | failure : FailureAST T → TypeAST T
    | undefined : ¬SuccessAST T → ¬FailureAST T → TypeAST T
  
  def PreAST.check_type (T : PreAST n b) : TypeAST T :=
    match T with
    | .mk T valid_T => match T with
      | .skip s e G => .undefined (by intro h; cases h;) (by intro h; cases h;)
      | .ε s e => match decEq s e with
        | isTrue heq => .success (.ε heq)
        | isFalse hne => .undefined (by intro h; cases h; contradiction) (by intro h; cases h;)
      | .any s e x => match decEq s e, decEq s.val.succ b with
        | isTrue heq_e, _ => .failure (.any heq_e)
        | isFalse hne_e, isTrue heq_b => .undefined (by intro h; cases h; contradiction;) (by intro h; cases h; contradiction)
        | isFalse hne_e, isFalse hne_b => match decEq (s.inbound_succ hne_b) e with
          | isTrue g => .success (.any g)
          | isFalse g => .undefined (by intro h; cases h; apply absurd _ g; simp [Fin.inbound_succ] at *; apply Fin.eq_of_val_eq; apply Fin.val_eq_of_eq; assumption) (by intro h; cases h; contradiction;)
      | .terminal s e a x => match decEq s e, decEq s.val.succ b, decEq a x with
        | isTrue heq_e, _, _ => .failure (.terminal_empty heq_e)
        | isFalse hne_e, isTrue heq_b, _ => .undefined (by intro h; cases h; contradiction;) (by intro h; cases h; contradiction; contradiction;)
        | isFalse hne_e, isFalse hne_b, isTrue heq_ax => match decEq (s.inbound_succ hne_b) e with
          | isTrue g => .success (.terminal g heq_ax)
          | isFalse g => .undefined (by intro h; cases h; apply absurd _ g; simp [Fin.inbound_succ] at *; apply Fin.eq_of_val_eq; apply Fin.val_eq_of_eq; assumption) (by intro h; cases h; contradiction; contradiction;)
        | isFalse hne_e, isFalse hne_b, isFalse hne_ax => match decEq (s.inbound_succ hne_b) e with
          | isTrue g => .failure (.terminal_mismatch g hne_ax)
          | isFalse g => .undefined (by intro h; cases h; contradiction;) (by intro h; cases h; apply absurd _ g; simp [Fin.inbound_succ] at *; apply Fin.eq_of_val_eq; apply Fin.val_eq_of_eq; assumption; contradiction;)
      | .nonTerminal s e A sub_T => match valid_T with
        | .nonTerminal wf ns =>
          let T_ast : PreAST n b := (PreAST.mk sub_T wf);
          have g : (¬SkipPreAST' T_ast.T) := by simp; exact ns;
          match check_type T_ast with
          | .success h => .success (.nonTerminal (h := g) h)
          | .failure h => .failure (.nonTerminal (h := g) h)
          | .undefined hs hf => .undefined (by intro h; cases h; contradiction;) (by intro h; cases h; contradiction;)
      | .seq s e T1 T2 => match valid_T with
        | .seq wf1 wf2 ns =>
          let T1_ast : PreAST n b := (PreAST.mk T1 wf1);
          let T2_ast : PreAST n b := (PreAST.mk T2 wf2);
          have g : (¬SkipPreAST' T1_ast.T) := by simp; exact ns;
          match check_type T1_ast, check_type T2_ast with
          | .undefined h1s h1f, _ => .undefined (by intro h; cases h; contradiction;) (by intro h; cases h; contradiction; contradiction;)
          | .success h1, .success h2 => .success (.seq (h := g) h1 h2)
          | .success h1, .failure h2 => .failure (.seq_SF (h := g) h1 h2)
          | .success h1, .undefined h2s h2f => .undefined (by intro h; cases h; contradiction;) (by intro h; cases h; {apply absurd _ (h1.ne_failure); assumption}; {apply absurd _ h2f; assumption})
          | .failure h1, _ => .failure (.seq_F (T2 := T2_ast) (h := g) h1)
      | .prior s e T1 T2 => match valid_T with
        | .prior wf1 wf2 ns =>
          let T1_ast : PreAST n b := (PreAST.mk T1 wf1);
          let T2_ast : PreAST n b := (PreAST.mk T2 wf2);
          have g : (¬SkipPreAST' T1_ast.T) := by simp; exact ns;
          match check_type T1_ast, check_type T2_ast with
          | .undefined h1s h1f, _ => .undefined (by intro h; cases h; contradiction; contradiction;) (by intro h; cases h; contradiction;)
          | .success h1, _ => .success (.prior_S (T2 := T2_ast) (h := g) h1)
          | .failure h1, .success h2 => .success (.prior_FS (h := g) h1 h2)
          | .failure h1, .failure h2 => .failure (.prior (h := g) h1 h2)
          | .failure h1, .undefined h2s h2f => .undefined (by intro h; cases h; apply absurd _ (h1.ne_success); assumption; apply absurd _ h2s; assumption) (by intro h; cases h; apply absurd _ h2f; assumption)
      | .star s e T0 TS => match valid_T with
        | .star wf0 wfS n0 nS =>
          let T0_ast : PreAST n b := (PreAST.mk T0 wf0);
          let TS_ast : PreAST n b := (PreAST.mk TS wfS);
          have g1 : (¬SkipPreAST' T0_ast.T) := by simp; exact n0;
          have g2 : SkipPreAST' TS_ast.T ∨ StarPreAST' TS_ast.T := by 
          {
            cases nS; simp; apply Or.inl; assumption; simp; apply Or.inr; assumption;
          }
          match check_type T0_ast, check_type TS_ast with
          | .undefined h1s h1f, _ => .undefined (by intro h; cases h; apply absurd _ h1f; assumption; apply absurd _ h1s; assumption) (by intro h; cases h;)
          | .failure h0, _ => .success (.star_F (TS := TS_ast) (h1 := g1) (h2 := g2) h0)
          | .success h0, .success hs => .success (.star_SS (TS := TS_ast) (h1 := g1) (h2 := g2) h0 hs)
          | .success h0, .failure hs => .undefined (by intro h; cases h; apply absurd _ h0.ne_failure; assumption; apply absurd _ hs.ne_success; assumption) (by intro h; cases h;)
          | .success h0, .undefined h2s h2f => .undefined (by intro h; cases h; apply absurd _ h0.ne_failure; assumption; contradiction) (by intro h; cases h;)
      | .notP s e sub_T => match valid_T with
        | .notP wf ns =>
          let T_ast : PreAST n b := (PreAST.mk sub_T wf);
          have g : (¬SkipPreAST' T_ast.T) := by simp; exact ns;
          match check_type T_ast with
          | .success h => .failure (.notP (h := g) h)
          | .failure h => .success (.notP (h := g) h)
          | .undefined hs hf => .undefined (by intro h; cases h; contradiction) (by intro h; cases h; contradiction)


end AST