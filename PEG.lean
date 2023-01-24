namespace GeneralPEG

  inductive PEG (VT : Type) (VN_upper : Nat) where
    | ε
    | any
    | terminal : VT → PEG VT VN_upper
    | nonTerminal : (n : Nat) → n < VN_upper → PEG VT VN_upper
    | seq : PEG VT VN_upper → PEG VT VN_upper → PEG VT VN_upper
    | prior : PEG VT VN_upper → PEG VT VN_upper → PEG VT VN_upper
    | star : PEG VT VN_upper → PEG VT VN_upper
    | notP : PEG VT VN_upper → PEG VT VN_upper
  
  def PEG.size {VT : Type} {VN_upper : Nat} : PEG VT VN_upper → Nat
    | seq p1 p2 => p1.size + p2.size + 1
    | prior p1 p2 => p1.size + p2.size + 1
    | star p => p.size + 1
    | notP p => p.size + 1
    | _ => 0

  def PEG.grammarProps {VT : Type} {VN_upper : Nat} (G : PEG VT VN_upper) (P : Nat → (Bool × Bool × Bool)) : (Bool × Bool × Bool) :=
    match G with
      | ε => (false, true, false)
      | any => (true, false, true)
      | terminal _ => (true, false, true)
      | nonTerminal n _ => P n
      | seq e1 e2 => 
        have (e1_f, e1_0, e1_s) := e1.grammarProps P;
        have (e2_f, e2_0, e2_s) := e2.grammarProps P;
        (
          e1_f || ((e1_0 || e1_s) && e2_f), 
          e1_0 && e2_0, 
          (e1_s && (e2_0 || e2_s)) || (e1_0 && e2_s)
        )
      | prior e1 e2 =>
        have (e1_f, e1_0, e1_s) := e1.grammarProps P;
        have (e2_f, e2_0, e2_s) := e2.grammarProps P;
        (
          e1_f && e2_f, 
          e1_0 || (e1_f && e2_0), 
          e1_s || (e1_f && e2_s)
        )
      | star e =>
        have (e_f, _, e_s) := e.grammarProps P;
        (false, e_f, e_s)
      | notP e =>
        have (e_f, e_0, e_s) := e.grammarProps P;
        (e_s || e_0, e_f, false)
  
  def allTrue : Nat → (Bool × Bool × Bool) := fun _ => (true, true, true)
  def allFalse : Nat → (Bool × Bool × Bool) := fun _ => (false, false, false)


end GeneralPEG