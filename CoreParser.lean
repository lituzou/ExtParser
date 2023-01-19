-- CFG core grammar with fixed definitions of terminals and non-terminals
namespace CoreParser
  -- TokenKind definition
  inductive TokenKind where
    | GENERIC
    | DECLARE_SYNTAX_CAT
    | SYNTAX
    | LEFT_PAREN
    | RIGHT_PAREN
    | PEG_EPS
    | PEG_ANY
    | PEG_VT
    | PEG_VN
    | PEG_SEQ
    | PEG_PRIOR
    | PEG_STAR
    | PEG_NOTP
    deriving DecidableEq, Repr

  -- Token definition
  def Token := TokenKind × String deriving DecidableEq

  inductive CoreSyntaxCat where
    | PEG_EXPR
    | PEG_EXPR_0
    | PEG_EXPR_1
    | PEG_EXPR_2
    | PEG_EXPR_3
    | PEG_EXPR_4
  deriving DecidableEq, Repr

  -- PEG construct
  inductive PEG where
    | ε : PEG
    | any : PEG
    | terminal : TokenKind → PEG
    | nonTerminal : CoreSyntaxCat → PEG
    | seq : PEG → PEG → PEG
    | prior : PEG → PEG → PEG
    | star : PEG → PEG
    | notP : PEG → PEG
    deriving DecidableEq, Repr
  
  open TokenKind
  open CoreSyntaxCat
  open PEG


  def Pexp : CoreSyntaxCat → PEG
    | PEG_EXPR => nonTerminal PEG_EXPR_0
    | PEG_EXPR_0 => seq (nonTerminal PEG_EXPR_1) (seq (terminal PEG_SEQ) (nonTerminal PEG_EXPR_1))
    | PEG_EXPR_1 => seq (nonTerminal PEG_EXPR_2) (seq (terminal PEG_PRIOR) (nonTerminal PEG_EXPR_2))
    | PEG_EXPR_2 => seq (prior (terminal PEG_NOTP) ε) (nonTerminal PEG_EXPR_3)
    | PEG_EXPR_3 => seq (nonTerminal PEG_EXPR_4) (prior (terminal PEG_STAR) ε)
    | PEG_EXPR_4 => prior (terminal PEG_VT) 
                    (prior (terminal PEG_VN) 
                    (prior (terminal PEG_ANY) 
                    (prior (terminal PEG_EPS) 
                    (seq (terminal LEFT_PAREN) (seq (nonTerminal PEG_EXPR) (terminal RIGHT_PAREN)))))) 

  def g_props (G : PEG) (P : CoreSyntaxCat → (Bool × Bool × Bool)) : (Bool × Bool × Bool) :=
    match G with
      | ε => (false, true, false)
      | any => (true, false, true)
      | terminal vt => (true, false, true)
      | nonTerminal vn => P vn
      | seq e1 e2 => 
        have (e1_f, e1_0, e1_s) := g_props e1 P;
        have (e2_f, e2_0, e2_s) := g_props e2 P;
        (
          e1_f || ((e1_0 || e1_s) && e2_f), 
          e1_0 && e2_0, 
          (e1_s && (e2_0 || e2_s)) || (e1_0 && e2_s)
        )
      | prior e1 e2 =>
        have (e1_f, e1_0, e1_s) := g_props e1 P;
        have (e2_f, e2_0, e2_s) := g_props e2 P;
        (
          e1_f && e2_f, 
          e1_0 || (e1_f && e2_0), 
          e1_s || (e1_f && e2_s)
        )
      | star e =>
        have (e_f, e_0, e_s) := g_props e P;
        (false, e_f, e_s)
      | notP e =>
        have (e_f, e_0, e_s) := g_props e P;
        (e_s || e_0, e_f, false)

  def extendP (vn_1 : CoreSyntaxCat) (P : CoreSyntaxCat → (Bool × Bool × Bool)) (vn_2 : CoreSyntaxCat): (Bool × Bool × Bool) :=
    if vn_1 = vn_2 then 
      g_props (Pexp vn_2) P
    else 
      P vn_2

  def defaultP (_ : CoreSyntaxCat) : (Bool × Bool × Bool) := (false, false, false)

  def iterList : List CoreSyntaxCat := 
        [PEG_EXPR, PEG_EXPR_0, PEG_EXPR_1, PEG_EXPR_2, PEG_EXPR_3, PEG_EXPR_4]
    ++  [PEG_EXPR, PEG_EXPR_0, PEG_EXPR_1, PEG_EXPR_2, PEG_EXPR_3, PEG_EXPR_4]
    ++  [PEG_EXPR, PEG_EXPR_0, PEG_EXPR_1, PEG_EXPR_2, PEG_EXPR_3, PEG_EXPR_4]
  
  def newP : CoreSyntaxCat → (Bool × Bool × Bool) := List.foldr extendP defaultP iterList

end CoreParser