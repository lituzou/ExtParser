import ExtParser.Parsing
import Mathlib.Data.List.Defs

namespace ParserGen
  open Grammar
  open AST
  open Parsing
  open Function

  structure ParserOutput (WFPexp : Wellformed_GProd n) (A : Fin n) (G : PEG n) (inp : Input b) (s : Fin b) (sA : Fin b) where
    is_subterm : G ≤ WFPexp.get A
    sA_le_s : sA ≤ s
    lt_or_pattern_wf : sA < s ∨ PatternWF WFPexp.Pexp WFPexp.σ A G
    T : AST n b
    s_eq_sT : s = T.start
    true_to_grammar : AST.TrueToGrammar T WFPexp.Pexp G
    true_to_input : AST.TrueToInput T inp
    tree_consistent_success_prop0 : PreAST.SuccessAST T.T → s = T.end → IsKnown (getProp0 WFPexp.Pexp G)
    tree_consistent_success_propS : PreAST.SuccessAST T.T → s < T.end → IsKnown (getPropS WFPexp.Pexp G)
    tree_consistent_failure_propF : PreAST.FailureAST T.T → IsKnown (getPropF WFPexp.Pexp G)
  
  def parse_ε (WFPexp : Wellformed_GProd n) (A : Fin n)
            (is_subterm : .ε ≤ WFPexp.get A) (inp : Input b) (s : Fin b) (sA : Fin b) (sA_le_s : sA ≤ s) 
            (lt_or_pattern_wf : sA < s ∨ PatternWF WFPexp.Pexp WFPexp.σ A .ε)
            : ParserOutput WFPexp A .ε inp s sA :=
    ParserOutput.mk is_subterm sA_le_s lt_or_pattern_wf 
    (AST.mk (.ε s s) .ε (.ε (Or.inl (PreAST.SuccessAST.ε rfl)))) 
    (by simp [AST.start, PreAST.start]) 
    (PreAST.TrueToGrammar.ε)
    (PreAST.TrueToInput.ε)
    (fun hs heq => by simp [getProp0, g_props]; constructor; rfl)
    (fun hs hlt => by simp [AST.end, PreAST.end] at hlt; exact absurd hlt (Nat.lt_irrefl s))
    (fun hf => by apply absurd hf; apply PreAST.SuccessAST.ne_failure; constructor; apply PreAST.SuccessAST.ε rfl)
  
  def parse_any (WFPexp : Wellformed_GProd n) (A : Fin n)
            (is_subterm : .any ≤ WFPexp.get A) (inp : Input b) (s : Fin b) (sA : Fin b) (sA_le_s : sA ≤ s) 
            (lt_or_pattern_wf : sA < s ∨ PatternWF WFPexp.Pexp WFPexp.σ A .any)
            : ParserOutput WFPexp A .any inp s sA :=
    match decEq s.val.succ b with
      | isTrue h =>
        ParserOutput.mk is_subterm sA_le_s lt_or_pattern_wf
        (AST.mk (.any s s (inp s)) .any (.any (Or.inr (PreAST.FailureAST.any rfl h))))
        (by simp [AST.start, PreAST.start])
        (PreAST.TrueToGrammar.any)
        (PreAST.TrueToInput.any rfl)
        (fun hs _ => by apply absurd hs; apply PreAST.FailureAST.ne_success; constructor; apply PreAST.FailureAST.any rfl h)
        (fun hs _ => by apply absurd hs; apply PreAST.FailureAST.ne_success; constructor; apply PreAST.FailureAST.any rfl h)
        (fun hf => by simp [getPropF, g_props]; constructor; rfl)
      | isFalse h =>
        ParserOutput.mk is_subterm sA_le_s lt_or_pattern_wf
        (AST.mk (.any s (s.inbound_succ h) (inp s)) .any (.any (Or.inl (PreAST.SuccessAST.any rfl))))
        (by simp [AST.start, PreAST.start])
        (PreAST.TrueToGrammar.any)
        (PreAST.TrueToInput.any rfl)
        (fun hs heq => by apply absurd heq; simp [AST.end, PreAST.end, Fin.inbound_succ]; apply Fin.ne_of_val_ne; apply Nat.ne_of_lt; apply Nat.lt_succ_self)
        (fun hs hlt => by simp [getPropS, g_props]; constructor; rfl)
        (fun hf => by apply absurd hf; apply PreAST.SuccessAST.ne_failure; constructor; apply PreAST.SuccessAST.any rfl)
  
  def parse_terminal (WFPexp : Wellformed_GProd n) (A : Fin n)
            (is_subterm : (.terminal c) ≤ WFPexp.get A) (inp : Input b) (s : Fin b) (sA : Fin b) (sA_le_s : sA ≤ s) 
            (lt_or_pattern_wf : sA < s ∨ PatternWF WFPexp.Pexp WFPexp.σ A (.terminal c))
            : ParserOutput WFPexp A (.terminal c) inp s sA :=
    match decEq s.val.succ b, decEq (inp s) c with
      | isFalse h, isTrue g =>
        ParserOutput.mk is_subterm sA_le_s lt_or_pattern_wf
        (AST.mk (.terminal s (s.inbound_succ h) c (inp s)) .terminal (.terminal (Or.inl (PreAST.SuccessAST.terminal rfl (Eq.symm g)))))
        (by simp [AST.start, PreAST.start])
        (PreAST.TrueToGrammar.terminal)
        (PreAST.TrueToInput.terminal rfl)
        (fun hs heq => by apply absurd heq; simp [AST.end, PreAST.end, Fin.inbound_succ]; apply Fin.ne_of_val_ne; apply Nat.ne_of_lt; apply Nat.lt_succ_self)
        (fun hs hlt => by simp [getPropS, g_props]; constructor; rfl)
        (fun hf => by apply absurd hf; apply PreAST.SuccessAST.ne_failure; constructor; apply PreAST.SuccessAST.terminal rfl (Eq.symm g))
      | isFalse h, isFalse g => 
        ParserOutput.mk is_subterm sA_le_s lt_or_pattern_wf
        (AST.mk (.terminal s (s.inbound_succ h) c (inp s)) .terminal (.terminal (Or.inr (PreAST.FailureAST.terminal_mismatch rfl (fun h => by cases h; simp at g;)))))
        (by simp [AST.start, PreAST.start])
        (PreAST.TrueToGrammar.terminal)
        (PreAST.TrueToInput.terminal rfl)
        (fun hs _ => by apply absurd hs; apply PreAST.FailureAST.ne_success; constructor; constructor; rfl; intro h; cases h; simp at g)
        (fun hs _ => by apply absurd hs; apply PreAST.FailureAST.ne_success; constructor; constructor; rfl; intro h; cases h; simp at g)
        (fun hf => by simp [getPropF, g_props]; constructor; rfl)
      | isTrue h, _ =>
        ParserOutput.mk is_subterm sA_le_s lt_or_pattern_wf
        (AST.mk (.terminal s s c (inp s)) .terminal (.terminal (Or.inr (PreAST.FailureAST.terminal_empty rfl h))))
        (by simp [AST.start, PreAST.start])
        (PreAST.TrueToGrammar.terminal)
        (PreAST.TrueToInput.terminal rfl)
        (fun hs _ => by apply absurd hs; apply PreAST.FailureAST.ne_success; constructor; apply PreAST.FailureAST.terminal_empty; rfl; exact h)
        (fun hs _ => by apply absurd hs; apply PreAST.FailureAST.ne_success; constructor; apply PreAST.FailureAST.terminal_empty; rfl; exact h)
        (fun hf => by simp [getPropF, g_props]; constructor; rfl)
  
  def parse (WFPexp : Wellformed_GProd n) (A : Fin n) (G : PEG n) 
            (is_subterm : G ≤ WFPexp.get A) (inp : Input b) (s : Fin b) (sA : Fin b) (sA_le_s : sA ≤ s) 
            (lt_or_pattern_wf : sA < s ∨ PatternWF WFPexp.Pexp WFPexp.σ A G)
            : ParserOutput WFPexp A G inp s sA :=
    match G with
    | .ε => parse_ε WFPexp A is_subterm inp s sA sA_le_s lt_or_pattern_wf
    | .any => parse_any WFPexp A is_subterm inp s sA sA_le_s lt_or_pattern_wf
    | .terminal c => parse_terminal WFPexp A is_subterm inp s sA sA_le_s lt_or_pattern_wf
    | .nonTerminal B => sorry
    | .seq e1 e2 => sorry
    | .prior e1 e2 => sorry
    | .star p => sorry
    | .notP p => sorry
end ParserGen