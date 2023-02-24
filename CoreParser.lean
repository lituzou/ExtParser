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
  structure GProd (n : Nat) where
    pos_n : 0 < n
    f : Fin n → PEG n 

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
      | nonTerminal : ∀ (vn : Fin n), PropF Pexp (Pexp.f vn) → PropF Pexp (nonTerminal vn)
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
      | nonTerminal : ∀ (vn : Fin n), Prop0 Pexp (Pexp.f vn) → Prop0 Pexp (nonTerminal vn)
      | seq : ∀ (e1 e2 : PEG n), Prop0 Pexp e1 → Prop0 Pexp e2 → Prop0 Pexp (seq e1 e2)
      | prior_0 : ∀ (e1 e2 : PEG n), Prop0 Pexp e1 → Prop0 Pexp (prior e1 e2)
      | prior_F0 : ∀ (e1 e2 : PEG n), PropF Pexp e1 → Prop0 Pexp e2 → Prop0 Pexp (prior e1 e2)
      | star : ∀ (e : PEG n), PropF Pexp e → Prop0 Pexp (star e)
      | notP : ∀ (e : PEG n), PropF Pexp e → Prop0 Pexp (notP e)

    -- Property of PEG grammar that can succeed only by consuming input
    inductive PropS : GProd n → PEG n → Prop where
      | any : PropS Pexp any
      | terminal : ∀ (c : Char), PropS Pexp (terminal c)
      | nonTerminal : ∀ (vn : Fin n), PropS Pexp (Pexp.f vn) → PropS Pexp (nonTerminal vn)
      | seq_S0 : ∀ (e1 e2 : PEG n), PropS Pexp e1 → Prop0 Pexp e2 → PropS Pexp (seq e1 e2)
      | seq_0S : ∀ (e1 e2 : PEG n), Prop0 Pexp e1 → PropS Pexp e2 → PropS Pexp (seq e1 e2)
      | seq_SS : ∀ (e1 e2 : PEG n), PropS Pexp e1 → PropS Pexp e2 → PropS Pexp (seq e1 e2)
      | prior_S : ∀ (e1 e2 : PEG n), PropS Pexp e1 → PropS Pexp (prior e1 e2)
      | prior_FS : ∀ (e1 e2 : PEG n), PropF Pexp e1 → PropS Pexp e2 → PropS Pexp (prior e1 e2)
      | star : ∀ (e : PEG n), PropS Pexp e → PropS Pexp (star e)
  end

  abbrev PropsTriple (Pexp : GProd n) (G : PEG n) := Maybe (PropF Pexp) G × Maybe (Prop0 Pexp) G × Maybe (PropS Pexp) G
  abbrev PropsTriplePred (Pexp : GProd n) := ∀ (i : Fin n), PropsTriple Pexp (Pexp.f i)

  -- Compute grammar properties in one iteration
  def g_props {Pexp : GProd n} (G : PEG n) (P : PropsTriplePred Pexp) : PropsTriple Pexp G :=
    match G with
    | ε => (unknown, found (Prop0.ε), unknown)
    | any => (found (PropF.any), unknown, found (PropS.any))
    | terminal c => (found (PropF.terminal c), unknown, found (PropS.terminal c))
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
      have (e1_f, e1_0, e1_s) := g_props e1 P;
      have (e2_f, e2_0, e2_s) := g_props e2 P;
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
      have (e1_f, e1_0, _) := g_props e1 P;
      have (e2_f, e2_0, _) := g_props e2 P;
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
      have (e_f, _, e_s) := g_props e P;
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
      have (e_f, e_0, e_s) := g_props e P;
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

  inductive Maybe.le : Maybe p a → Maybe p a → Prop where
    | lhs_unknown : ∀ {p : α → Prop} {a : α} {mr : Maybe p a}, Maybe.le unknown mr
    | all_found : ∀ {p : α → Prop} {a : α}, (l r : p a) → Maybe.le (found l) (found r)

  instance : LE (Maybe p a) where
    le := Maybe.le

  theorem Maybe.le_refl : ∀ {x : Maybe p a}, x ≤ x := by
    intro x
    cases x
    apply Maybe.le.all_found
    apply Maybe.le.lhs_unknown

  theorem Maybe.le_trans : ∀ {x y z : Maybe p a}, x ≤ y → y ≤ z → x ≤ z := by
    intro x y z hxy hyz
    cases hxy
    apply Maybe.le.lhs_unknown
    cases hyz
    apply Maybe.le.all_found

  theorem Maybe.le.not_found_to_unknown : ∀ {p : α → Prop} {a : α}, (pa : p a) → ¬ (found pa ≤ unknown) := by
    intro p a pa h
    cases h

  theorem Maybe.le.equiv_to_imply : ∀ {p : α → Prop} {a : α} {x y : Maybe p a}, x ≤ y ↔ (x = unknown) ∨ (∃ x' y', x = found x' ∧ y = found y') := by
    intro p a x y
    apply Iff.intro
    {
      intro hxy;
      cases hxy with
      | lhs_unknown => apply Or.inl; rfl;
      | all_found l r => apply Or.inr; exists l; exists r;
    }
    {
      intro h;
      match h with
      | Or.inl g => simp [g]; exact Maybe.le.lhs_unknown;
      | Or.inr ⟨x',⟨y', ⟨fx, fy⟩⟩⟩ => simp [fx, fy]; exact Maybe.le.all_found x' y'
    }
  
  theorem Maybe.eq_of_le_le : ∀ {p : α → Prop} {a : α} {x y : Maybe p a}, x ≤ y → y ≤ x → x = y := by
    intro p a x y hxy hyx
    cases hxy <;> cases hyx <;> rfl

  inductive PropsTriple.le (P Q : PropsTriple Pexp G) : Prop where
    | mk : P.fst ≤ Q.fst → P.snd.fst ≤ Q.snd.fst → P.snd.snd ≤ Q.snd.snd → PropsTriple.le P Q

  instance : LE (PropsTriple Pexp G) where
    le := PropsTriple.le

  theorem PropsTriple.le_refl : ∀ {x : PropsTriple Pexp G}, x ≤ x := by
    intro x
    apply PropsTriple.le.mk <;> apply Maybe.le_refl

  theorem PropsTriple.le_trans : ∀ {x y z : PropsTriple Pexp G}, x ≤ y → y ≤ z → x ≤ z := by
    intro x y z hxy hyz
    cases hxy with
      | mk hxy_f hxy_0 hxy_s => cases hyz with
        | mk hyz_f hyz_0 hyz_s =>
          constructor
          apply Maybe.le_trans hxy_f hyz_f
          apply Maybe.le_trans hxy_0 hyz_0
          apply Maybe.le_trans hxy_s hyz_s
  
  theorem PropsTriple.eq_of_le_le : ∀ {x y : PropsTriple Pexp G}, x ≤ y → y ≤ x → x = y := by
    intro x y hxy hyx;
    match x with
    | (x1, x2, x3) => match y with
      | (y1, y2, y3) => 
        cases hxy <;> cases hyx <;> simp_all;
        apply And.intro; apply Maybe.eq_of_le_le; trivial; trivial;
        apply And.intro; apply Maybe.eq_of_le_le; trivial; trivial;
        apply Maybe.eq_of_le_le; trivial; trivial;


  inductive PropsTriplePred.le {Pexp : GProd n} (P Q : PropsTriplePred Pexp) : Prop where
    | mk : (∀ (i : Fin n), (P i) ≤ (Q i)) → PropsTriplePred.le P Q

  instance : LE (PropsTriplePred Pexp) where
    le := PropsTriplePred.le

  theorem PropsTriplePred.le_refl : ∀ {x : PropsTriplePred Pexp}, x ≤ x := by
    intro x
    constructor
    intro i
    apply PropsTriple.le_refl

  theorem PropsTriplePred.le_trans : ∀ {x y z : PropsTriplePred Pexp}, x ≤ y → y ≤ z → x ≤ z := by
    intro x y z (PropsTriplePred.le.mk fxy) (PropsTriplePred.le.mk fyz)
    constructor
    intro i
    apply PropsTriple.le_trans (fxy i) (fyz i)
  
  theorem PropsTriplePred.eq_of_le_le : ∀ {x y : PropsTriplePred Pexp}, x ≤ y → y ≤ x → x = y := by
    intro x y hxy hyx;
    apply funext;
    intro i;
    cases hxy with
    | mk fxy =>
      cases hyx with
      | mk fyx => apply PropsTriple.eq_of_le_le (fxy i) (fyx i);
  

  theorem g_props_growth_seq : ∀ {Pexp : GProd n} {P Q : PropsTriplePred Pexp} {e1 e2 : PEG n}, g_props e1 P ≤ g_props e1 Q → g_props e2 P ≤ g_props e2 Q → g_props (.seq e1 e2) P ≤ g_props (.seq e1 e2) Q := by
    intros Pexp P Q e1 e2 e1_growth e2_growth
    cases e1_growth with
    | mk le1_f le1_0 le1_s => cases e2_growth with
      | mk le2_f le2_0 le2_s =>
        {
          constructor <;> simp [g_props]
          {
            match (Maybe.le.equiv_to_imply.mp le1_f) with
            | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le2_f) with
              | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
              | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le1_0) with
                | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le1_s) with
                  | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
                  | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e1 Q).fst <;> cases (g_props e1 Q).snd.fst <;> simp <;> apply Maybe.le.all_found
                | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e1 Q).fst <;> simp <;> apply Maybe.le.all_found
            | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
          }
          {
            match (Maybe.le.equiv_to_imply.mp le1_0) with
            | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
            | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le2_0) with
              | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
              | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
          }
          {
            match (Maybe.le.equiv_to_imply.mp le1_0) with
            | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le1_s) with
              | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
              | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le2_0) with
                | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le2_s) with
                  | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
                  | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e1 Q).snd.fst <;> cases (g_props e2 Q).snd.fst <;> simp <;> apply Maybe.le.all_found
                | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
            | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le1_s) with
              | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le2_0) with
                | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le2_s) with
                  | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
                  | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e1 Q).snd.snd <;> cases (g_props e2 Q).snd.fst <;> simp <;> apply Maybe.le.all_found
                | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le2_s) with
                  | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
                  | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e1 Q).snd.snd <;> simp <;> apply Maybe.le.all_found
              | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le2_0) with
                | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le2_s) with
                  | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
                  | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e2 Q).snd.fst <;> simp <;> apply Maybe.le.all_found
                | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
          }
        }

  theorem g_props_growth_nonterminal : ∀ {Pexp : GProd n} {P Q : PropsTriplePred Pexp} {vn} , P ≤ Q → g_props (.nonTerminal vn) P ≤ g_props (.nonTerminal vn) Q := by
    intros Pexp P Q vn hpq
    have (PropsTriplePred.le.mk fpq) := hpq
    cases fpq vn with
    | mk le_f le_0 le_s =>
      {
        constructor <;> simp [g_props]
        {
          match (Maybe.le.equiv_to_imply.mp le_f) with
          | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
          | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
        }
        {
          match (Maybe.le.equiv_to_imply.mp le_0) with
          | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
          | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
        }
        {
          match (Maybe.le.equiv_to_imply.mp le_s) with
          | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
          | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
        }
      }

  theorem g_props_growth_prior : ∀ {Pexp : GProd n} {P Q : PropsTriplePred Pexp} {e1 e2 : PEG n}, g_props e1 P ≤ g_props e1 Q → g_props e2 P ≤ g_props e2 Q  → g_props (.prior e1 e2) P ≤ g_props (.prior e1 e2) Q := by
    intros Pexp P Q e1 e2 e1_growth e2_growth
    cases e1_growth with
    | mk le1_f le1_0 le1_s => cases e2_growth with
      | mk le2_f le2_0 le2_s =>
        {
          constructor <;> simp [g_props]
          {
            match (Maybe.le.equiv_to_imply.mp le1_f) with
            | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
            | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le2_f) with
              | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
              | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
          }
          {
            match (Maybe.le.equiv_to_imply.mp le1_f) with
            | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le1_0) with
              | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
              | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
            | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; match (Maybe.le.equiv_to_imply.mp le1_0) with
              | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le2_0) with
                | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
                | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e1 Q).snd.fst <;> simp <;> apply Maybe.le.all_found
              | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
          }
          {
            apply Maybe.le.lhs_unknown
          }
        }

  theorem g_props_growth_star : ∀ {Pexp : GProd n} {P Q : PropsTriplePred Pexp} {e : PEG n}, g_props e P ≤ g_props e Q → g_props (.star e) P ≤ g_props (.star e) Q := by
    intros Pexp P Q e e_growth
    cases e_growth with
    | mk le_f le_0 le_s =>
      {
        constructor <;> simp [g_props]
        {
          apply Maybe.le.lhs_unknown
        }
        {
          match (Maybe.le.equiv_to_imply.mp le_f) with
          | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
          | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
        }
        {
          match (Maybe.le.equiv_to_imply.mp le_s) with
          | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
          | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
        }
      }

  theorem g_props_growth_notP : ∀ {Pexp : GProd n} {P Q : PropsTriplePred Pexp} {e : PEG n}, g_props e P ≤ g_props e Q → g_props (.notP e) P ≤ g_props (.notP e) Q := by
    intros Pexp P Q e e_growth
    cases e_growth with
    | mk le_f le_0 le_s =>
      {
        constructor <;> simp [g_props]
        {
          match (Maybe.le.equiv_to_imply.mp le_0) with
          | Or.inl h => simp [h]; match (Maybe.le.equiv_to_imply.mp le_s) with
            | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
            | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; cases (g_props e Q).snd.fst <;> simp <;> apply Maybe.le.all_found
          | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
        }
        {
          match (Maybe.le.equiv_to_imply.mp le_f) with
          | Or.inl h => simp [h]; apply Maybe.le.lhs_unknown
          | Or.inr ⟨x',⟨y',⟨hx', hy'⟩⟩⟩ => simp [hx', hy']; apply Maybe.le.all_found
        }
        {
          apply Maybe.le.lhs_unknown
        }
      }

  theorem g_props_growth : ∀ {Pexp : GProd n} {G : PEG n} {P Q : PropsTriplePred Pexp}, P ≤ Q → g_props G P ≤ g_props G Q := by
    intro Pexp G P Q hpq
    cases G with
      | ε => apply PropsTriple.le_refl
      | any => apply PropsTriple.le_refl
      | terminal c => apply PropsTriple.le_refl
      | nonTerminal vn => exact g_props_growth_nonterminal hpq
      | seq e1 e2 =>
        {
          have e1_growth : g_props e1 P ≤ g_props e1 Q := g_props_growth hpq;
          have e2_growth : g_props e2 P ≤ g_props e2 Q := g_props_growth hpq;
          exact g_props_growth_seq e1_growth e2_growth
        }
      | prior e1 e2 =>
        {
          have e1_growth : g_props e1 P ≤ g_props e1 Q := g_props_growth hpq;
          have e2_growth : g_props e2 P ≤ g_props e2 Q := g_props_growth hpq;
          exact g_props_growth_prior e1_growth e2_growth
        }
      | star e =>
        {
          have e_growth : g_props e P ≤ g_props e Q := g_props_growth hpq;
          exact g_props_growth_star e_growth
        }
      | notP e =>
        {
          have e_growth : g_props e P ≤ g_props e Q := g_props_growth hpq;
          exact g_props_growth_notP e_growth
        }

  structure CoherentPred (Pexp : GProd n) where
    pred : PropsTriplePred Pexp
    coherent : ∀ (i : Fin n), pred i ≤ g_props (Pexp.f i) pred

  instance : LE (CoherentPred Pexp) where
    le := fun P Q => P.pred ≤ Q.pred
  
  theorem CoherentPred.eq_of_le_le : ∀ {x y : CoherentPred Pexp}, x ≤ y → y ≤ x → x = y := by
    intro x y hxy hyx
    cases x with
    | mk xp xc => cases y with
      | mk yp yc =>
        cases hxy; cases hyx; simp_all; apply PropsTriplePred.eq_of_le_le <;> constructor <;> trivial;

  def unknownPred (Pexp : GProd n) : CoherentPred Pexp :=
    {
      pred := fun _ => (unknown, unknown, unknown)
      coherent := by
        intro i
        constructor <;> apply Maybe.le.lhs_unknown
    }

  instance Fin.decEq {n} (a b : Fin n) : Decidable (Eq a b) :=
    match Nat.decEq a.val b.val with
    | isFalse h => isFalse (Fin.ne_of_val_ne h)
    | isTrue h => isTrue (Fin.eq_of_val_eq h)
  
  def g_extend {Pexp : GProd n} (a : Fin n) (P : CoherentPred Pexp) : CoherentPred Pexp :=
    {
      pred := fun b =>  match Fin.decEq a b with
                        | isFalse h => P.pred b
                        | isTrue rfl => g_props (Pexp.f a) P.pred
      coherent := by
        intro i; simp
        cases Fin.decEq a i with
        | isFalse _ =>
          simp; apply PropsTriple.le_trans (P.coherent i);
          apply g_props_growth;
          constructor; intro b;
          cases Fin.decEq a b with
          | isFalse _ => simp; apply PropsTriple.le_refl
          | isTrue g => cases g; simp; apply P.coherent
        | isTrue h =>
          cases h; simp; apply g_props_growth;
          constructor; intro b;
          cases Fin.decEq a b with
          | isFalse _ => simp; apply PropsTriple.le_refl
          | isTrue g => cases g; simp; apply P.coherent
    }
  
  theorem g_extend_growth1 : ∀ {Pexp : GProd n} (a : Fin n) (P : CoherentPred Pexp), P ≤ g_extend a P := by
    intro Pexp a P
    simp [g_extend]; constructor; simp;
    intro b; 
    cases Fin.decEq a b with
    | isFalse _ => simp; apply PropsTriple.le_refl
    | isTrue h => cases h; simp; apply P.coherent
  
  theorem g_extend_growth2 : ∀ {Pexp : GProd n} (a : Fin n) (P Q : CoherentPred Pexp), P ≤ Q → g_extend a P ≤ g_extend a Q := by
    intro Pexp a P Q
    intro hpq; constructor; simp [g_extend, *]
    intro b;
    cases Fin.decEq a b with
    | isFalse _ => simp; cases hpq with
      | mk fpq => exact fpq b
    | isTrue h => cases h; simp; apply g_props_growth hpq

  def inbound_succ (a : Fin n) (hne : a.val.succ ≠ n) : Fin n :=
    {val := a.val.succ, isLt := Nat.lt_of_le_of_ne (Nat.lt_of_succ_le a.isLt) hne}
  
  def inbound_pred (a : Fin n) (hne : a.val ≠ 0) : Fin n :=
    {val := a.val.pred, isLt := Nat.lt_trans (Nat.pred_lt hne) (a.isLt)}
  
  def inbound_pred_succ (a : Fin n) (hne : a.val.succ ≠ n) : Fin n :=
    have h : (inbound_succ a hne).val ≠ 0 := by rw [inbound_succ]; simp;
    inbound_pred (inbound_succ a hne) h
  
  def inbound_succ_pred (a : Fin n) (hne : a.val ≠ 0) : Fin n :=
    have h : (inbound_pred a hne).val.succ ≠ n := by rw [inbound_pred]; simp; rw [Nat.succ_pred hne]; apply Nat.ne_of_lt; apply a.isLt;
    inbound_succ (inbound_pred a hne) h
  
  theorem inbound_pred_succ_eq : ∀ (a : Fin n) (hne : a.val.succ ≠ n), a = inbound_pred_succ a hne := by
    intro a hne;
    apply Fin.eq_of_val_eq;
    rw [inbound_pred_succ]; simp;
    rw [inbound_pred]; simp;
    rw [inbound_succ]; simp;

  theorem inbound_succ_pred_eq : ∀ (a : Fin n) (hne : a.val ≠ 0), a = inbound_succ_pred a hne := by
    intro a hne;
    apply Fin.eq_of_val_eq;
    rw [inbound_succ_pred]; simp;
    rw [inbound_succ]; simp;
    rw [inbound_pred]; simp;
    rw [Nat.succ_pred hne];
  
  def recompute_props {Pexp : GProd n} (a : Fin n) (P : CoherentPred Pexp) : CoherentPred Pexp :=
    match Nat.decEq a.val.succ n with
    | isTrue _ => g_extend a P
    | isFalse hne =>
      have _ : n - a.val.succ < n - a.val := Nat.sub_succ_lt_self n a.val a.isLt; -- prove termination
      recompute_props (inbound_succ a hne) (g_extend a P)
  termination_by recompute_props a P => n - a.val

  theorem recompute_lemma1 : ∀ {Pexp : GProd n} (a : Fin n) (P : CoherentPred Pexp), P ≤ recompute_props a P := by
    intro Pexp a P
    rw [recompute_props]
    cases Nat.decEq a.val.succ n
    {
      simp; 
      have _ : n - a.val.succ < n - a.val := Nat.sub_succ_lt_self n a.val a.isLt;
      apply PropsTriplePred.le_trans (g_extend_growth1 a P);
      apply recompute_lemma1
    }
    {
      simp; apply g_extend_growth1
    }
  termination_by recompute_lemma1 a P => n - a.val

  theorem recompute_lemma2 : ∀ {Pexp : GProd n} (a : Fin n) (P Q : CoherentPred Pexp), P ≤ Q → recompute_props a P ≤ recompute_props a Q := by
    intro Pexp a P Q hpq
    rw [recompute_props, recompute_props]
    cases Nat.decEq a.val.succ n
    {
      simp;
      have _ : n - a.val.succ < n - a.val := Nat.sub_succ_lt_self n a.val a.isLt;
      apply recompute_lemma2;
      apply g_extend_growth2 a P Q hpq;
    }
    {
      simp; apply g_extend_growth2 a P Q hpq
    }
  termination_by recompute_lemma2 a P Q hpq => n - a.val

  theorem recompute_lemma3 : ∀ {Pexp : GProd n} (a : Fin n) (P : CoherentPred Pexp), (hne : ¬(a.val.succ = n)) → recompute_props (inbound_succ a hne) P ≤ recompute_props a P := by
    intro Pexp a P hne
    have h : recompute_props a P = recompute_props (inbound_succ a hne) (g_extend a P) := by
      rw [recompute_props]
      cases Nat.decEq a.val.succ n
      simp
      contradiction
    rw [h]
    apply recompute_lemma2
    apply g_extend_growth1
  
  theorem recompute_le_recompute_zero : ∀ {Pexp : GProd n} (a : Fin n) (P : CoherentPred Pexp), recompute_props a P ≤ recompute_props (Fin.mk 0 Pexp.pos_n) P := by
    intro Pexp a P;
    match Nat.decEq a.val 0 with
    | isTrue h =>
      have g : a = (Fin.mk 0 Pexp.pos_n) := Fin.eq_of_val_eq h;
      rw [g];
      apply PropsTriplePred.le_refl;
    | isFalse h =>
        have g : a = inbound_succ_pred a h := by apply inbound_succ_pred_eq;
        rw [g, inbound_succ_pred]; simp;
        apply PropsTriplePred.le_trans (recompute_lemma3 _ P _);
        apply recompute_le_recompute_zero;
  termination_by recompute_le_recompute_zero a P => a.val
  
  structure Fixpoint (Pexp : GProd n) where
    coherent_pred : CoherentPred Pexp
    isFixed : recompute_props (Fin.mk 0 Pexp.pos_n) coherent_pred = coherent_pred
  
  instance : LE (Fixpoint Pexp) where
    le := fun P Q => P.coherent_pred ≤ Q.coherent_pred
  
  theorem Fixpoint.recompute_le_self : ∀ {Pexp : GProd n} (a : Fin n) (P : Fixpoint Pexp), recompute_props a P.coherent_pred ≤ P.coherent_pred := by
    intro Pexp a P;
    have helper : (recompute_props a P.coherent_pred ≤ P.coherent_pred) = (recompute_props a P.coherent_pred ≤ recompute_props (Fin.mk 0 Pexp.pos_n) P.coherent_pred) := by
      rw [P.isFixed]
    rw [helper];
    apply recompute_le_recompute_zero;

  theorem Fixpoint.no_growth : ∀ {Pexp : GProd n} (a : Fin n) (P : Fixpoint Pexp), P.coherent_pred = g_extend a P.coherent_pred := by
    intro Pexp a P;
    simp;
    apply CoherentPred.eq_of_le_le;
    {
      apply g_extend_growth1;
    }
    {
      have g_extend_le_recompute : g_extend a P.coherent_pred ≤ recompute_props a P.coherent_pred := by 
        rw [recompute_props];
        cases Nat.decEq a.val.succ n with
        | isTrue h => simp [h]; apply PropsTriplePred.le_refl
        | isFalse h => 
          simp; apply recompute_lemma1;
      apply PropsTriplePred.le_trans g_extend_le_recompute;
      apply PropsTriplePred.le_trans;
      apply recompute_le_recompute_zero a;
      rw [P.isFixed];
      apply PropsTriplePred.le_refl;
    }
  
  def Fin.extended_add (a : Fin m) (b : Fin n) : Fin (m+n-1) :=
    match m, n with
    | Nat.zero, _ => Fin.elim0 a
    | _, Nat.zero => Fin.elim0 b
    | Nat.succ m, Nat.succ n => Fin.mk (a.val + b.val) (by 
      {
        have ha := Nat.le_of_lt_succ a.isLt;
        have hb := Nat.le_of_lt_succ b.isLt;
        rw [Nat.add_succ, Nat.succ_sub_succ, Nat.sub_zero, Nat.succ_add];
        apply Nat.lt_succ_of_le;
        apply Nat.add_le_add ha hb;
      })
  
  def Fin.cast {m n : Nat} (h : m = n) (a : Fin m) : Fin n := Fin.mk a.val (by rw [←h]; apply Fin.isLt)
  
  def Fin.extended_add_lt_left : ∀ {a1 a2 : Fin m} {b : Fin n}, a1 ≤ a2 → Fin.extended_add a1 b ≤ Fin.extended_add a2 b := by
    intro a1 a2 b h
    simp [extended_add];
    match m, n with
    | Nat.zero, _ => exact a1.elim0
    | _, Nat.zero => exact b.elim0
    | Nat.succ m, Nat.succ n => simp; apply Nat.add_le_add_right h;

  def Fin.extended_add_lt_right : ∀ {a1 a2 : Fin m} {b : Fin n}, a1 ≤ a2 → Fin.extended_add b a1 ≤ Fin.extended_add b a2 := by
    intro a1 a2 b h
    simp [extended_add];
    match m, n with
    | Nat.zero, _ => exact a1.elim0
    | _, Nat.zero => exact b.elim0
    | Nat.succ m, Nat.succ n => simp; apply Nat.add_le_add_left h;
  
  def Maybe.count_found : Maybe p a → Fin 2
    | found _ => Fin.mk 1 (by trivial)
    | unknown => Fin.mk 0 (by trivial)
  
  def PropsTriple.count_found (P : PropsTriple Pexp G) : Fin 4 :=
    Fin.extended_add P.fst.count_found (Fin.extended_add P.snd.fst.count_found P.snd.snd.count_found)

  def count_found_aux {Pexp : GProd n} {p : GProd n → PEG n → Prop} (P : (i : Fin n) → Maybe (p Pexp) (Pexp.f i)) (i : Fin n) (res : Fin (n-i.val)) : Fin (n+1) :=
    have c1 : 2 + (n - i.val) - 1 = n-i.val+1 := by rw [Nat.add_comm, Nat.add_sub_assoc]; trivial;
    have new_res : Fin (n-i.val+1) := Fin.cast c1 (Fin.extended_add (P i).count_found res);
    match Nat.decEq i.val 0 with
    | isTrue h => Fin.cast (by simp [h]) new_res
    | isFalse h =>
      have c2 : n-i.val+1 = n - (inbound_pred i h).val := by
      {
        rw [inbound_pred]; simp;
        calc
          n-i.val+1 = n-Nat.succ (Nat.pred i.val) + 1 := by rw [Nat.succ_pred h]
          _ = n-(Nat.pred i.val + 1) + 1 := rfl
          _ = n-Nat.pred i.val-1+1 := rfl
          _ = n-Nat.pred i.val := by
            {
              rw [Nat.sub_add_cancel]; 
              apply Nat.le_sub_of_add_le;
              rw [Nat.add_comm, ←Nat.succ_eq_add_one]; 
              apply Nat.succ_le_of_lt;
              apply Nat.lt_of_le_of_lt;
              apply Nat.pred_le;
              exact i.isLt;
            }
      }
      have _ : (inbound_pred i h).val + 1 < i.val + 1 := by apply Nat.succ_lt_succ; rw [inbound_pred]; simp; apply Nat.pred_lt h; -- prove termination
      count_found_aux P (inbound_pred i h) (Fin.cast c2 new_res)
  termination_by count_found_aux P i res => i

  def PropsTriplePred.count_found_helper {Pexp : GProd n} (P : PropsTriplePred Pexp) (i : Fin n) (res : Fin (3*(n-i.val)-2)) : Fin (3*n+1) :=
    have new_res := (Fin.extended_add (P i).count_found res);
    match Nat.decEq i.val 0 with
    | isTrue h =>
      have c : 4 + (3 * (n - i.val) - 2) - 1 = 3 * n + 1 := by
      {
        simp_all;
        apply Nat.sub_eq_of_eq_add;
        rw [←Nat.add_sub_assoc (by rw[←Nat.mul_one 2]; apply Nat.mul_le_mul; trivial; exact Pexp.pos_n) 4, Nat.add_comm, Nat.add_sub_assoc];
        trivial;
      }
      Fin.cast c new_res
    | isFalse h =>
      have c : 4 + (3 * (n - i.val) - 2) - 1 = 3 * (n - (inbound_pred i h).val) - 2 := by
      {
        rw [inbound_pred]; simp;
        calc
          4 + (3 * (n - i.val) - 2) - 1 = 4 + (3 * (n - Nat.succ (Nat.pred i.val)) - 2) - 1 := by rw [Nat.succ_pred h]
          _ = 4 + (3 * (n - Nat.pred i.val - 1) - 2) - 1 := by rw [←Nat.add_one, ←Nat.sub_sub];
          _ = 4 + (3 * (n - Nat.pred i.val) - 3 - 2) - 1 := by rw [Nat.mul_sub_left_distrib];
          _ = 3 * (n - Nat.pred i.val) - 2 := by sorry;
      }
      have _ : (inbound_pred i h).val + 1 < i.val + 1 := by apply Nat.succ_lt_succ; rw [inbound_pred]; simp; apply Nat.pred_lt h;
      count_found_helper P (inbound_pred i h) (Fin.cast c new_res)
  termination_by count_found_helper P i res => i

  def PropsTriplePred.count_found {Pexp : GProd n} (P : PropsTriplePred Pexp) : Fin (3*n+1) :=
    have pf := fun (i : Fin n) => (P i).fst;
    have p0 := fun (i : Fin n) => (P i).snd.fst;
    have ps := fun (i : Fin n) => (P i).snd.snd;
    have max_i : Fin n := Fin.mk (n-1) (by apply Nat.sub_lt Pexp.pos_n; trivial)
    have fin_zero : Fin (n - max_i.val) := Fin.mk 0 (by apply Nat.lt_sub_of_add_lt; simp; apply max_i.isLt);
    have c : n + 1 + (n + 1 + (n + 1) - 1) - 1 = 3 * n + 1 := by
    {
      calc
        n + 1 + (n + 1 + (n + 1) - 1) - 1 = n + (n + 1 + (n + 1) - 1) + 1 - 1 := by rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]
        _ = n + (n + 1 + (n + 1) - 1) := by rw [Nat.add_sub_cancel]
        _ = n + (n + (n + 1) + 1 - 1) := by rw [Nat.add_assoc, Nat.add_comm 1, ←Nat.add_assoc]
        _ = n + (n + (n + 1)) := by rw [Nat.add_sub_cancel]
        _ = n + n + n + 1 := by rw [←Nat.add_assoc, ←Nat.add_assoc]
        _ = 3*n+1 := by rw [Nat.succ_mul, Nat.succ_mul, Nat.one_mul]
    }
    Fin.cast c (Fin.extended_add (count_found_aux pf max_i fin_zero) (Fin.extended_add (count_found_aux p0 max_i fin_zero) (count_found_aux ps max_i fin_zero)))
  
  theorem count_growth_aux_res {Pexp : GProd n} {p : GProd n → PEG n → Prop} (P : (i : Fin n) → Maybe (p Pexp) (Pexp.f i)) (i : Fin n) (res1 res2 : Fin (n-i.val)) 
                            : res1 ≤ res2 → count_found_aux P i res1 ≤ count_found_aux P i res2 := by
    intro h;
    rw [count_found_aux, count_found_aux]; simp;
    match Nat.decEq i.val 0 with
    | isTrue g => 
      {
        simp [g, Fin.cast];
        apply Fin.extended_add_lt_right;
        exact h;
      }
    | isFalse g =>
      {
        have _ : (inbound_pred i g).val + 1 < i.val + 1 := by
        {
          apply Nat.add_lt_add_right;
          rw [inbound_pred];
          apply Nat.pred_lt g;
        }
        simp [g, Fin.cast];
        apply count_growth_aux_res;
        apply Fin.extended_add_lt_right;
        exact h;
      }
  termination_by count_growth_aux_res P i res1 res2 h => i

  theorem PropsTriplePred.count_growth : ∀ {Pexp : GProd n} {P Q : PropsTriplePred Pexp}, P ≤ Q → P.count_found ≤ Q.count_found := by
    intro Pexp P Q hpq;
    simp [count_found, Fin.cast];
    sorry
  
  structure ComputeState {Pexp : GProd n} (P : CoherentPred Pexp) where
    count : Fin (3*n+1)
    count_eq : count = P.pred.count_found
  
end CoreParser
