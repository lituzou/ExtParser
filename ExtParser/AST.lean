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
    | nonTerminal : IsValid sub_T → ¬SkipPreAST' sub_T → IsValid (.nonTerminal s e A sub_T)
    | seq : IsValid T1 → IsValid T2 → ¬SkipPreAST' T1 → IsValid (.seq s e T1 T2)
    | prior : IsValid T1 → IsValid T2 → ¬SkipPreAST' T1 → IsValid (.prior s e T1 T2)
    | star : IsValid T0 → IsValid TS → ¬SkipPreAST' T0 → (SkipPreAST' TS ∨ StarPreAST' TS) → IsValid (.star s e T0 TS)
    | notP : IsValid sub_T → ¬SkipPreAST' sub_T → IsValid (.notP s e sub_T)

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
  
  def PreAST'.start (T : PreAST' n b) : Fin b :=
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

  def PreAST'.end (T : PreAST' n b) : Fin b :=
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

  structure PreAST (n : Nat) (b : Nat) where
    T : PreAST' n b
    valid_T : PreAST'.IsValid T
  
  def PreAST.start (T : PreAST n b) : Fin b := T.T.start
  def PreAST.end (T : PreAST n b) : Fin b := T.T.end

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

  theorem PreAST.star_cannot_fail : ∀ {T : PreAST n b}, StarPreAST' T.T → ¬FailureAST T := by
    intro T h_star h_fail;
    match T with
    | .mk T valid_T => simp_all; cases h_star; cases h_fail
  
  def PreAST.IsMeaningful (T : PreAST n b) : Prop := SuccessAST T ∨ FailureAST T

  inductive PreAST.IsWellformed : PreAST n b → Prop where
    | ε :           IsMeaningful (mk (.ε s e) h) 
                    → IsWellformed (mk (.ε s e) h)
    | any :         IsMeaningful (mk (.any s e x) h) 
                    → IsWellformed (mk (.any s e x) h)
    | terminal :    IsMeaningful (mk (.terminal s e a x) h) 
                    → IsWellformed (mk (.terminal s e a x) h)
    | nonTerminal : ∀ {sub_T : PreAST n b} {h : PreAST'.IsValid (PreAST'.nonTerminal s e A sub_T.T)},
                    s = sub_T.start → e = sub_T.end 
                    → IsWellformed sub_T 
                    → IsWellformed (mk (.nonTerminal s e A sub_T.T) h)
    | seq_F :       ∀ {T1 T2 : PreAST n b} {h : PreAST'.IsValid (PreAST'.seq s e T1.T T2.T)},
                    s = T1.start → T1.end = T2.start → e = T2.end → T2.start = T2.end
                    → IsWellformed T1 → FailureAST T1 → SkipPreAST' T2.T
                    → IsWellformed (mk (.seq s e T1.T T2.T) h)
    | seq_S :       ∀ {T1 T2 : PreAST n b} {h : PreAST'.IsValid (PreAST'.seq s e T1.T T2.T)},
                    s = T1.start → T1.end = T2.start → e = T2.end 
                    → IsWellformed T1 → SuccessAST T1 → IsWellformed T2
                    → IsWellformed (mk (.seq s e T1.T T2.T) h)
    | prior_S :     ∀ {T1 T2 : PreAST n b} {h : PreAST'.IsValid (PreAST'.prior s e T1.T T2.T)},
                    s = T1.start → s = T2.start → s = T2.end → e = T1.end 
                    → IsWellformed T1 → SuccessAST T1 → SkipPreAST' T2.T
                    → IsWellformed (mk (.prior s e T1.T T2.T) h)
    | prior_F :     ∀ {T1 T2 : PreAST n b} {h : PreAST'.IsValid (PreAST'.prior s e T1.T T2.T)},
                    s = T1.start → s = T2.start → e = T2.end 
                    → IsWellformed T1 → FailureAST T1 → IsWellformed T2
                    → IsWellformed (mk (.prior s e T1.T T2.T) h)
    | star_S :      ∀ {T0 TS : PreAST n b} {h : PreAST'.IsValid (PreAST'.star s e T0.T TS.T)},
                    s = T0.start → T0.end = TS.start → e = TS.end
                    → IsWellformed T0 → SuccessAST T0 → IsWellformed TS
                    → IsWellformed (mk (.star s e T0.T TS.T) h)
    | star_F :      ∀ {T0 TS : PreAST n b} {h : PreAST'.IsValid (PreAST'.star s e T0.T TS.T)},
                    s = T0.start → T0.end = TS.start → TS.start = TS.end → s = e
                    → IsWellformed T0 → FailureAST T0 → SkipPreAST' TS.T  
                    → IsWellformed (mk (.star s e T0.T TS.T) h)
    | notP :        ∀ {sub_T : PreAST n b} {h : PreAST'.IsValid (PreAST'.notP s e sub_T.T)},
                    s = e → s = sub_T.start
                    → IsWellformed sub_T 
                    → IsWellformed (mk (.notP s e sub_T.T) h)

  theorem PreAST.skip_is_not_wellformed : ∀ {T : PreAST n b}, SkipPreAST' T.T → ¬IsWellformed T := by
    intro T h_skip hwf;
    cases T; simp_all; cases h_skip; cases hwf;

  theorem PreAST.wellformed_implies_meaningful : ∀ {T : PreAST n b}, IsWellformed T → IsMeaningful T := by
    intro T hwf;
    match hwf with
    | .ε _ => assumption
    | .any _ => assumption
    | .terminal _ => assumption
    | .nonTerminal (h := h_valid) _ _ hwfT =>
      {
        cases h_valid; cases wellformed_implies_meaningful hwfT;
        apply Or.inl; constructor <;> assumption;
        apply Or.inr; constructor <;> assumption;
      }
    | .seq_F (h := h_valid) _ _ _ _ _ hf1 hskip2 =>
      {
        cases h_valid; apply Or.inr;
        apply FailureAST.seq_F <;> assumption;
      }
    | .seq_S (h := h_valid) _ _ _ _ hs1 hwf2 =>
      {
        cases h_valid; cases wellformed_implies_meaningful hwf2;
        apply Or.inl; constructor <;> assumption;
        apply Or.inr; apply FailureAST.seq_SF <;> assumption;
      }
    | .prior_S (h := h_valid) _ _ _ _ _ hs1 hskip2 =>
      {
        cases h_valid; apply Or.inl;
        apply SuccessAST.prior_S <;> assumption;
      }
    | .prior_F (h := h_valid) _ _ _ _ hf1 hwf2 =>
      {
        cases h_valid; cases wellformed_implies_meaningful hwf2;
        apply Or.inl; apply SuccessAST.prior_FS <;> assumption;
        apply Or.inr; constructor <;> assumption;
      }
    | .star_S (TS := TS) (h := h_valid) _ _ _ _ hs0 hwfS =>
      {
        match h_valid with
        | PreAST'.IsValid.star _ _ _ svs => 
          match svs with
          | Or.inl hskip =>
            {
              apply absurd hwfS;
              apply skip_is_not_wellformed; assumption;
            }
          | Or.inr hstar =>
            {
              apply Or.inl; apply SuccessAST.star_SS;
              assumption; apply Or.inr; assumption; assumption;
              match wellformed_implies_meaningful hwfS with
              | Or.inl _ => assumption
              | Or.inr hf => cases TS; cases hstar; cases hf;
            }
        
      }
    | .star_F (h := h_valid) _ _ _ _ _ hf0 hskipS =>
      {
        cases h_valid; apply Or.inl;
        apply SuccessAST.star_F <;> assumption;
      }
    | .notP (h := h_valid) _ _ hwfT =>
      {
        cases h_valid; cases wellformed_implies_meaningful hwfT;
        apply Or.inr; constructor <;> assumption;
        apply Or.inl; constructor <;> assumption;
      }
  
  theorem PreAST.start_le_end : ∀ {T : PreAST n b}, IsWellformed T → T.start ≤ T.end := by
    intro T hwf;
    match hwf with
    | .ε hm =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        match hm with
        | Or.inl hs => cases hs; apply Nat.le_of_eq; apply Fin.val_eq_of_eq; assumption;
      }
    | .any hm =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        match hm with
        | Or.inl hs => cases hs; apply Nat.le_of_lt; apply Fin.lt_from_inbound_succ; assumption;
        | Or.inr hf => cases hf; apply Nat.le_of_eq; apply Fin.val_eq_of_eq; assumption;
      }
    | .terminal hm =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        match hm with
        | Or.inl hs => cases hs; apply Nat.le_of_lt; apply Fin.lt_from_inbound_succ; assumption;
        | Or.inr hf => cases hf; apply Nat.le_of_lt; apply Fin.lt_from_inbound_succ; assumption; apply Nat.le_of_eq; apply Fin.val_eq_of_eq; assumption;
      }
    | .nonTerminal (h := h_valid) hssT heeT hwfT =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hssT, heeT];
        apply start_le_end;
        assumption;
      }
    | .seq_F (h := h_valid) hss1 he1s2 hee2 hs2e2 hwf1 _ hskip2 =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hss1, hee2, ←hs2e2, ←he1s2]
        apply start_le_end hwf1;
      }
    | .seq_S (h := h_valid) hss1 he1s2 hee2 hwf1 _ hwf2 =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hss1, hee2];
        apply Nat.le_trans;
        apply start_le_end hwf1;
        rw [he1s2];
        apply start_le_end hwf2;
      }
    | .prior_S (h := h_valid) hss1 _ _ hee1 hwf1 _ hskip2 =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hss1, hee1];
        apply start_le_end hwf1;
      }
    | .prior_F (h := h_valid) _ hss2 hee2 _ _ hwf2 =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hss2, hee2];
        apply start_le_end hwf2;
      }
    | .star_S (TS := TS) (h := h_valid) hss0 he0sS heeS hwf0 _ hwfS =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hss0, heeS];
        apply Nat.le_trans;
        apply start_le_end hwf0;
        rw [he0sS];
        apply start_le_end hwfS;
      }
    | .star_F (h := h_valid) _ _ _ hse _ _ hskipS =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hse];
        apply Nat.le_refl;
      }
    | .notP (h := h_valid) hse _ hwfT =>
      {
        cases T; simp [PreAST.start, PreAST.end, PreAST'.start, PreAST'.end];
        rw [hse];
        apply Nat.le_refl;
      }

  structure AST (n : Nat) (b : Nat) where
    T : PreAST n b
    wf_T : PreAST.IsWellformed T
end AST