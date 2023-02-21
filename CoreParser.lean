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

  inductive PropsTriple.le (P Q : PropsTriple Pexp G) : Prop where
    | mk : P.fst ≤ Q.fst → P.snd.fst ≤ Q.snd.fst → P.snd.snd ≤ Q.snd.snd → PropsTriple.le P Q

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


  inductive PropsTriplePred.le {Pexp : GProd n} (P Q : PropsTriplePred Pexp) : Prop where
    | mk : (∀ (i : Fin n), (P i) ≤ (Q i)) → PropsTriplePred.le P Q

  instance : LE (PropsTriplePred Pexp) where
    le := PropsTriplePred.le

  theorem PropsTriplePred.le.refl : ∀ {x : PropsTriplePred Pexp}, x ≤ x := by
    intro x
    constructor
    intro i
    apply PropsTriple.le.refl

  theorem PropsTriplePred.le.trans : ∀ {x y z : PropsTriplePred Pexp}, x ≤ y → y ≤ z → x ≤ z := by
    intro x y z (PropsTriplePred.le.mk fxy) (PropsTriplePred.le.mk fyz)
    constructor
    intro i
    apply PropsTriple.le.trans (fxy i) (fyz i)


  theorem g_props_growth : ∀ {Pexp : GProd n} {G : PEG n} {P Q : PropsTriplePred Pexp}, P ≤ Q → g_props G P ≤ g_props G Q := by
    intro Pexp G P Q hpq
    have (PropsTriplePred.le.mk fpq) := hpq
    cases G with
      | ε => apply PropsTriple.le.refl
      | any => apply PropsTriple.le.refl
      | terminal c => apply PropsTriple.le.refl
      | nonTerminal vn =>
        {
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

        }
      | seq e1 e2 =>
        {
          have e1_growth : g_props e1 P ≤ g_props e1 Q := g_props_growth hpq;
          have e2_growth : g_props e2 P ≤ g_props e2 Q := g_props_growth hpq;
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
        }
      | prior e1 e2 =>
        {
          have e1_growth : g_props e1 P ≤ g_props e1 Q := g_props_growth hpq;
          have e2_growth : g_props e2 P ≤ g_props e2 Q := g_props_growth hpq;
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
        }
      | star e =>
        {
          have e_growth : g_props e P ≤ g_props e Q := g_props_growth hpq;
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
        }
      | notP e =>
        {
          have e_growth : g_props e P ≤ g_props e Q := g_props_growth hpq;
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
        }


  structure CoherentPred (Pexp : GProd n) where
    pred : PropsTriplePred Pexp
    coherent : ∀ (i : Fin n), pred i ≤ g_props (Pexp i) pred

  instance : LE (CoherentPred Pexp) where
    le := fun P Q => P.pred ≤ Q.pred

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
  
  #check Fin

  def g_extend {Pexp : GProd n} (a : Fin n) (P : CoherentPred Pexp) : CoherentPred Pexp :=
    {
      pred := fun b =>  match Fin.decEq a b with
                        | isFalse h => P.pred b
                        | isTrue rfl => g_props (Pexp a) P.pred
      coherent := by
        intro i; simp
        cases Fin.decEq a i with
        | isFalse _ =>
          simp; apply PropsTriple.le.trans (P.coherent i);
          apply g_props_growth;
          constructor; intro b;
          cases Fin.decEq a b with
          | isFalse _ => simp; apply PropsTriple.le.refl
          | isTrue g => cases g; simp; apply P.coherent
        | isTrue h =>
          cases h; simp; apply g_props_growth;
          constructor; intro b;
          cases Fin.decEq a b with
          | isFalse _ => simp; apply PropsTriple.le.refl
          | isTrue g => cases g; simp; apply P.coherent
    }

end CoreParser