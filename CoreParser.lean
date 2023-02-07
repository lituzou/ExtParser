namespace CoreParser

  inductive PEG (n : Nat) where
    | ε
    | any
    | terminal (c : Char) 
    | nonTerminal (vn : Fin n)
    | seq (p1 p2 : PEG n)
    | prior (p1 p2 : PEG n)
    | star (p : PEG n)
    | notP (p : PEG n)
  deriving DecidableEq, Repr

  open PEG

  def stringPEG {n : Nat} (cs : List Char) : PEG n :=
    match cs with
      | [] => ε
      | c :: cs => seq (terminal c) (stringPEG cs)

  def g_props (G : PEG n) (P : Fin n → (Bool × Bool × Bool)) : (Bool × Bool × Bool) :=
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

  def extendP (vn_1 vn_2 : Fin n) (Pexp : Fin n → PEG n) (P : Fin n → (Bool × Bool × Bool)) : (Bool × Bool × Bool) :=
    if vn_1 = vn_2 then
      g_props (Pexp vn_2) P
    else
      P vn_2
  
  def allFalse (_ : Fin n) : (Bool × Bool × Bool) := (false, false, false)

end CoreParser