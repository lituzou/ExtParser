namespace Fin

  instance decEq {n} (a b : Fin n) : Decidable (Eq a b) :=
    match Nat.decEq a.val b.val with
    | isFalse h => isFalse (Fin.ne_of_val_ne h)
    | isTrue h => isTrue (Fin.eq_of_val_eq h)

  def extended_add (a : Fin m) (b : Fin n) : Fin (m+n-1) :=
    Fin.mk (a.val + b.val) (by {
      match m, n with
      | Nat.zero, _ => exact Fin.elim0 a
      | _, Nat.zero => exact Fin.elim0 b
      | Nat.succ m, Nat.succ n => {
        rw [Nat.add_succ, Nat.succ_sub_succ, Nat.sub_zero, Nat.succ_add];
        apply Nat.lt_succ_of_le;
        apply Nat.add_le_add;
        exact Nat.le_of_lt_succ a.isLt;
        exact Nat.le_of_lt_succ b.isLt;
      }
    })

  def cast {m n : Nat} (h : m = n) (a : Fin m) : Fin n := Fin.mk a.val (by rw [←h]; apply Fin.isLt)


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
  
  theorem lt_from_inbound_succ : inbound_succ a hne = b → a < b := by
    intro h;
    rw [inbound_succ] at h;
    apply Nat.lt_of_succ_le;
    apply Nat.le_of_eq;
    exact Fin.val_eq_of_eq h;

  theorem extended_add_eq_add_right : ∀ {a1 a2 : Fin m} {b : Fin n}, a1 = a2 ↔ Fin.extended_add a1 b = Fin.extended_add a2 b := by
    intro a1 a2 b
    apply Iff.intro;
    {
      intro h;
      simp [h];
    }
    {
      intro h;
      simp [extended_add] at h;
      match m, n with
      | Nat.zero, _ => exact a1.elim0;
      | _, Nat.zero => exact b.elim0;
      | Nat.succ m, Nat.succ n => simp at h; apply Fin.eq_of_val_eq; apply Nat.add_right_cancel h;
    }
  
  theorem extended_add_eq_add_left : ∀ {a1 a2 : Fin m} {b : Fin n}, a1 = a2 ↔ Fin.extended_add b a1 = Fin.extended_add b a2 := by
    intro a1 a2 b
    apply Iff.intro;
    {
      intro h;
      simp [h];
    }
    {
      intro h;
      simp [extended_add] at h;
      match m, n with
      | Nat.zero, _ => exact a1.elim0;
      | _, Nat.zero => exact b.elim0;
      | Nat.succ m, Nat.succ n => simp at h; apply Fin.eq_of_val_eq; apply Nat.add_left_cancel h;
    }
  
  theorem extended_add_le_add_right : ∀ {a1 a2 : Fin m} {b : Fin n}, a1 ≤ a2 → Fin.extended_add a1 b ≤ Fin.extended_add a2 b := by
    intro a1 a2 b h
    simp [extended_add];
    match m, n with
    | Nat.zero, _ => exact a1.elim0
    | _, Nat.zero => exact b.elim0
    | Nat.succ m, Nat.succ n => simp; apply Nat.add_le_add_right h;

  theorem extended_add_le_add_left : ∀ {a1 a2 : Fin m} {b : Fin n}, a1 ≤ a2 → Fin.extended_add b a1 ≤ Fin.extended_add b a2 := by
    intro a1 a2 b h
    simp [extended_add];
    match m, n with
    | Nat.zero, _ => exact a1.elim0
    | _, Nat.zero => exact b.elim0
    | Nat.succ m, Nat.succ n => simp; apply Nat.add_le_add_left h;
  
  theorem extended_add_le_add : ∀ {a1 a2 : Fin m} {b1 b2 : Fin n}, a1 ≤ a2 → b1 ≤ b2 → Fin.extended_add a1 b1 ≤ Fin.extended_add a2 b2 := by
    intro a1 a2 b1 b2 ha hb;
    simp [extended_add, extended_add];
    match m, n with
    | Nat.zero, _ => exact a1.elim0
    | _, Nat.zero => exact b1.elim0
    | Nat.succ m, Nat.succ n => simp; apply Nat.add_le_add ha hb;
  
  theorem Nat.eq_eq_of_le_le_eq : ∀ {a b c d : Nat}, a ≤ c → b ≤ d → a + b = c + d → (a = c ∧ b = d) := by
    intro a b c d le_ac le_bd h;
    cases Nat.eq_or_lt_of_le le_ac;
    {
      simp_all; exact Nat.add_left_cancel h;
    }
    {
      cases Nat.eq_or_lt_of_le le_bd;
      {
        simp_all;
        exact Nat.add_right_cancel h;
      }
      {
        have g : a + b ≠ c + d := by apply Nat.ne_of_lt; apply Nat.add_lt_add; assumption; assumption;
        contradiction;
      }
    }

  theorem extended_eq_eq_of_le_le_eq : ∀ {a c : Fin m} {b d : Fin n}, a ≤ c → b ≤ d → Fin.extended_add a b = Fin.extended_add c d → (a = c ∧ b = d) := by
    intro a c b d le_ac le_bd h;
    simp [extended_add] at h;
    match m, n with
    | Nat.zero, _ => exact a.elim0;
    | _, Nat.zero => exact b.elim0;
    | Nat.succ m, Nat.succ n =>
      {
        simp_all;
        have g := Nat.eq_eq_of_le_le_eq le_ac le_bd h;
        exact ⟨Fin.eq_of_val_eq g.left, Fin.eq_of_val_eq g.right⟩; 
      }
  
  theorem le_trans : ∀ {a b c : Fin n}, a ≤ b → b ≤ c → a ≤ c := by
    intro a b c hab hbc;
    apply Nat.le_trans hab hbc;
  
  theorem le_cast : ∀ {a b : Fin m} {h : m = n}, a ≤ b → Fin.cast h a ≤ Fin.cast h b := by
    intro a b h hab;
    rw [Fin.cast];
    exact hab;
end Fin