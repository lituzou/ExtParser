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
  
  -- Grammar Production Rule
  abbrev GProd n := Fin n → PEG n

  -- Maybe Type for known and unknown properties
  inductive Maybe (p : α → Prop) (a : α) where
    | found : p a → Maybe p a
    | unknown

  open Maybe

  mutual
    -- Property of PEG grammar that can be failed
    inductive PropF : GProd n → PEG n → Prop where
      | any : PropF Pexp any
      | terminal : ∀ (c : Char), PropF Pexp (terminal c)
      | nonTerminal : ∀ (vn : Fin n), PropF Pexp (Pexp vn) → PropF Pexp (nonTerminal vn) 
      | seq_F : ∀ (e1 e2 : PEG n), PropF Pexp e1 → PropF Pexp (seq e1 e2)
      | seq_0F : ∀ (e1 e2 : PEG n), Prop0 Pexp e1 → PropF Pexp e2 → PropF Pexp (seq e1 e2)
      | seq_SF : ∀ (e1 e2 : PEG n), PropS Pexp e1 → PropF Pexp e2 → PropF Pexp (seq e1 e2)
      | prior : ∀ (e1 e2 : PEG n), PropF Pexp e1 → PropF Pexp e2 → PropF Pexp (prior e1 e2)
      | star : ∀ (e : PEG n), PropF Pexp (star e)
      | notP_0 : ∀ (e : PEG n), Prop0 Pexp e → PropF Pexp (notP e)
      | notP_S : ∀ (e : PEG n), PropS Pexp e → PropF Pexp (notP e)

    -- Property of PEG grammar that can succeed without consuming input
    inductive Prop0 : GProd n → PEG n → Prop where
      | ε : Prop0 Pexp ε
      | nonTerminal : ∀ (vn : Fin n), Prop0 Pexp (Pexp vn) → Prop0 Pexp (nonTerminal vn) 
      | seq : ∀ (e1 e2 : PEG n), Prop0 Pexp e1 → Prop0 Pexp e2 → Prop0 Pexp (seq e1 e2)
      | prior_0 : ∀ (e1 e2 : PEG n), Prop0 Pexp e1 → Prop0 Pexp (prior e1 e2)
      | prior_F0 : ∀ (e1 e2 : PEG n), PropF Pexp e1 → Prop0 Pexp e2 → Prop0 Pexp (prior e1 e2)
      | star : ∀ (e : PEG n), PropF Pexp e → Prop0 Pexp (star e)
      | notP : ∀ (e : PEG n), PropF Pexp e → Prop0 Pexp (notP e)

    -- Property of PEG grammar that can succeed only by consuming input
    inductive PropS : GProd n → PEG n → Prop where
      | any : PropS Pexp any
      | terminal : ∀ (c : Char), PropS Pexp (terminal c)
      | nonTerminal : ∀ (vn : Fin n), PropS Pexp (Pexp vn) → PropS Pexp (nonTerminal vn) 
      | seq_S0 : ∀ (e1 e2 : PEG n), PropS Pexp e1 → Prop0 Pexp e2 → PropS Pexp (seq e1 e2)
      | seq_0S : ∀ (e1 e2 : PEG n), Prop0 Pexp e1 → PropS Pexp e2 → PropS Pexp (seq e1 e2)
      | seq_SS : ∀ (e1 e2 : PEG n), PropS Pexp e1 → PropS Pexp e2 → PropS Pexp (seq e1 e2)
      | prior_S : ∀ (e1 e2 : PEG n), PropS Pexp e1 → PropS Pexp (prior e1 e2)
      | prior_FS : ∀ (e1 e2 : PEG n), PropF Pexp e1 → PropS Pexp e2 → PropS Pexp (prior e1 e2)
      | star : ∀ (e : PEG n), PropS Pexp e → PropS Pexp (star e)
  end

  abbrev PropsTriple (Pexp : GProd n) (G : PEG n) := Maybe (PropF Pexp) G × Maybe (Prop0 Pexp) G × Maybe (PropS Pexp) G
  abbrev PropsTriplePred (Pexp : GProd n) := ∀ (i : Fin n), PropsTriple Pexp (Pexp i) 

  def g_props (Pexp : GProd n) (P : PropsTriplePred Pexp) : (G : PEG n) → PropsTriple Pexp G
    | ε => (unknown, unknown, unknown)
    | any => (unknown, unknown, unknown)
    | terminal _ => (unknown, unknown, unknown)
    | nonTerminal vn =>
      have (e_f, e_0, e_s) := P vn
      (
        match e_f with
          | found h => found (PropF.nonTerminal vn h)
          | unknown => unknown
        ,
        match e_0 with
          | found h => found (Prop0.nonTerminal vn h)
          | unknown => unknown
        ,
        match e_s with
          | found h => found (PropS.nonTerminal vn h)
          | unknown => unknown
      )
    | seq e1 e2 =>
      have (e1_f, e1_0, e1_s) := g_props Pexp P e1;
      have (e2_f, e2_0, e2_s) := g_props Pexp P e2;
      (
        match (e1_f, e1_0, e1_s, e2_f) with
          | (found h, _, _, _) => found (PropF.seq_F e1 e2 h)
          | (_,found h0,_,found hf) => found (PropF.seq_0F e1 e2 h0 hf)
          | (_,_,found hs,found hf) => found (PropF.seq_SF e1 e2 hs hf)
          | _ => unknown
        ,
        match (e1_0, e2_0) with
          | (found h1, found h2) => found (Prop0.seq e1 e2 h1 h2)
          | _ => unknown
        ,
        match (e1_0, e1_s, e2_0, e2_s) with 
          | (_,found hs,found h0,_) => found (PropS.seq_S0 e1 e2 hs h0)
          | (found h0,_,_,found hs) => found (PropS.seq_0S e1 e2 h0 hs)
          | (_,found h1,_,found h2) => found (PropS.seq_SS e1 e2 h1 h2)
          | _ => unknown
      )
    | prior e1 e2 =>
      have (e1_f, e1_0, _) := g_props Pexp P e1;
      have (e2_f, e2_0, _) := g_props Pexp P e2;
      (
        match (e1_f, e2_f) with
          | (found h1, found h2) => found (PropF.prior e1 e2 h1 h2)
          | _ => unknown
        ,
        match (e1_f, e1_0, e2_0) with
          | (_,found h,_) => found (Prop0.prior_0 e1 e2 h)
          | (found hf,_,found h0) => found (Prop0.prior_F0 e1 e2 hf h0)
          | _ => unknown
        ,
        unknown
      )
    | star e =>
      have (e_f, _, e_s) := g_props Pexp P e;
      (
        unknown
        ,
        match e_f with
          | found h => found (Prop0.star e h)
          | unknown => unknown
        ,
        match e_s with
          | found h => found (PropS.star e h)
          | unknown => unknown
      )
    | notP e =>
      have (e_f, e_0, e_s) := g_props Pexp P e;
      (
        match (e_0, e_s) with
          | (found h,_) => found (PropF.notP_0 e h)
          | (_,found h) => found (PropF.notP_S e h)
          | _ => unknown
        ,
        match e_f with
          | found h => found (Prop0.notP e h)
          | unknown => unknown
        ,
        unknown
      )
  
  def g_extend {Pexp : GProd n} (P : PropsTriplePred Pexp) (x : Fin n) : PropsTriplePred Pexp :=
    fun y =>
      if x = y then
        g_props Pexp P (Pexp y)
      else
        P y

  def unknownProps (Pexp : GProd n) : PropsTriplePred Pexp := fun _ => (unknown, unknown, unknown)


  inductive Maybe.le : Maybe p a → Maybe p a → Prop where
    | lhs_unknown : ∀ {p : α → Prop} {a : α} {mr : Maybe p a}, Maybe.le unknown mr
    | all_found : ∀ {p : α → Prop} {a : α}, (l r : p a) → Maybe.le (found l) (found r) 

  instance : LE (Maybe p a) where
    le := Maybe.le

  theorem Maybe.le.refl : ∀ {x : Maybe p a}, x ≤ x := by
    intro x
    cases x
    apply Maybe.le.all_found
    apply Maybe.le.lhs_unknown
  
  theorem Maybe.le.trans : ∀ {x y z : Maybe p a}, x ≤ y → y ≤ z → x ≤ z := by
    intro x y z hxy hyz
    cases hxy
    apply Maybe.le.lhs_unknown
    cases hyz
    apply Maybe.le.all_found

  inductive PropsTriple.le : PropsTriple Pexp G → PropsTriple Pexp G → Prop where
    | mk : ∀ {e1_f e2_f : Maybe (PropF Pexp) G} {e1_0 e2_0 : Maybe (Prop0 Pexp) G} {e1_s e2_s : Maybe (PropS Pexp) G}, 
            e1_f ≤ e2_f → e1_0 ≤ e2_0 → e1_s ≤ e2_s → 
            PropsTriple.le (e1_f, e1_0, e1_s) (e2_f, e2_0, e2_s)
  
  instance : LE (PropsTriple Pexp G) where
    le := PropsTriple.le
  
  theorem PropsTriple.le.refl : ∀ {x : PropsTriple Pexp G}, x ≤ x := by
    intro x
    apply PropsTriple.le.mk <;> apply Maybe.le.refl

  theorem PropsTriple.le.trans : ∀ {x y z : PropsTriple Pexp G}, x ≤ y → y ≤ z → x ≤ z := by
    intro x y z hxy hyz
    cases hxy with
      | mk hxy_f hxy_0 hxy_s => cases hyz with
        | mk hyz_f hyz_0 hyz_s =>
          constructor
          apply Maybe.le.trans hxy_f hyz_f
          apply Maybe.le.trans hxy_0 hyz_0
          apply Maybe.le.trans hxy_s hyz_s
    

  inductive PropsTriplePred.le : PropsTriplePred Pexp → PropsTriplePred Pexp → Prop where
    | mk : ∀ {Pexp : GProd n} {l r : PropsTriplePred Pexp}, (∀ (i : Fin n), (l i) ≤ (r i)) → 
            PropsTriplePred.le l r 
  
  instance : LE (PropsTriplePred Pexp) where
    le := PropsTriplePred.le
  
  theorem PropsTriplePred.le.refl : ∀ {x : PropsTriplePred Pexp}, x ≤ x := by
    intro x
    constructor
    intro i
    apply PropsTriple.le.refl
  
  theorem PropsTriplePred.le.trans : ∀ {x y z : PropsTriplePred Pexp}, x ≤ y → y ≤ z → x ≤ z := by
    intro x y z hxy hyz
    cases hxy with
      | mk fxy => cases hyz with
        | mk fyz =>
          constructor
          intro i
          apply PropsTriple.le.trans (fxy i) (fyz i)

  example : ∀ {x : Fin n} {Pexp : GProd n}, (unknownProps Pexp) ≤ (g_extend (unknownProps Pexp) x) := by
    intro x Pexp
    constructor
    intro i
    constructor <;> apply Maybe.le.lhs_unknown
  
  

end CoreParser