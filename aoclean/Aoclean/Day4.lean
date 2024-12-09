
theorem substring_drop_reduce {ss : Substring} {n : Nat} (non_empty : ¬ss.bsize = 0) (n_pos : n ≠ 0): (ss.drop n).bsize < ss.bsize := by
  have ⟨s, b, e, s_eq⟩ : ∃ s : String, ∃ b e : String.Pos, ss = ⟨s, b, e⟩ := by
    obtain ⟨s, b, e⟩ := ss
    apply Exists.intro s
    apply Exists.intro b
    apply Exists.intro e
    rfl
  rw [s_eq]
  have bsize_sub : ∀ s : String, ∀ b e : String.Pos, {str := s, startPos := b, stopPos := e : Substring}.bsize = e.byteIdx.sub b.byteIdx := by 
    intro s b e
    rfl
  have drop_eq : (⟨s, b, e⟩ : Substring).drop n = ⟨s, b + ss.nextn n 0, e⟩ := by
    rw [s_eq]
    rfl
  rw [drop_eq]
  rw [bsize_sub s, bsize_sub s]
  repeat rw [Nat.sub_eq]
  have h1 : ∀ x y : String.Pos, (x + y).byteIdx = x.byteIdx + y.byteIdx := by intro x y; rfl
  rw [h1]
  rw [← Nat.sub_sub]
  have ⟨c, c_eq⟩ : ∃ c : Nat, c = e.byteIdx - b.byteIdx := by apply Exists.intro (e.byteIdx - b.byteIdx); rfl 
  apply Nat.sub_lt
  rw [←Nat.sub_eq, ← bsize_sub s, ← s_eq]
  rw [← Nat.ne_zero_iff_zero_lt]
  intro h
  exact non_empty.elim h
  have ⟨m, hm⟩ : ∃ m : Nat, m + 1 = n := by
    cases n with
    | zero => 
      exfalso
      apply n_pos
      rfl
    | succ m =>
      apply Exists.intro m
      rfl
  rw [← hm]
  have h2 : (ss.nextn (m + 1) 0) = (ss.nextn m (ss.next 0)):= by rfl
  rw [h2]
  have h3 : 0 ≠ ss.bsize := by 
    symm
    intro h 
    exact non_empty.elim h
  have h4 : ∀ i p, p.1 ≤ (ss.nextn i p).1 := by
    intro i
    induction i with
    | zero =>
      intro p
      have h : (ss.nextn 0 p) = p := by rfl
      rw [h]
      exact Nat.le_refl p.1
    | succ i ih =>
      intro p
      have h : (ss.nextn (i + 1) p) = ss.nextn i (ss.next p) := by rfl
      rw [h]
      have h' := ih (ss.next p)
      have h41 : p.byteIdx ≤ (ss.next p).byteIdx := by
        by_cases h42 : b + p = e
        simp [Substring.next]
        rw [s_eq, h42]
        simp
        
        simp [Substring.next]

        rw [s_eq]
        simp 
        simp [h42]
        apply Nat.le_sub_of_add_le
        rw [Nat.add_comm, ← h1]
        apply Nat.le_of_lt
        apply String.lt_next'
      apply Nat.le_trans h41 h'
  have h5 := h4 m (ss.next 0)
  have h6 : 0 < ss.bsize := by
    rw [← Nat.ne_zero_iff_zero_lt]
    assumption
  have h7 : 0 < (ss.next 0).byteIdx := by
    apply Substring.lt_next ss ⟨0⟩
    exact h6
  apply Nat.lt_of_lt_of_le h7 h5

def count_xmas_hor (s: Substring): Nat := 
  if h1 : s.bsize = 0 then
    0
  else
    let val? : Option Substring := s.dropPrefix? "XMAS".toSubstring <|> s.dropPrefix? "SAMX".toSubstring
    if h2 : val?.isSome then
      let t := s.drop 3
      have three_neq_zero : 3 ≠ 0 := by simp
      have h3 : (s.drop 3).bsize < s.bsize := substring_drop_reduce h1 three_neq_zero
      1 + count_xmas_hor t
    else
      let t := s.drop 1
      have h4 : (s.drop 1).bsize < s.bsize := substring_drop_reduce h1 Nat.one_ne_zero
      count_xmas_hor t
termination_by s.bsize

def is_xmas_ver (c1 c2 c3 c4 : Char): Bool := 
  (c1 == 'X' ∧ c2 == 'M' ∧ c3 == 'A' ∧ c4 == 'S') ∨ (c4 == 'X' ∧ c3 == 'M' ∧ c2 == 'A' ∧ c1 == 'S')

def count_xmas_ver (s1 s2 s3 s4 : String): Nat := 
  let l1 := s1.toList
  let l2 := s2.toList
  let l3 := s3.toList
  let l4 := s4.toList
  let contains_ver := (((l1.zip l2).zip l3).zip l4).map (λ ⟨⟨⟨a, b⟩, c⟩, d⟩ ↦ is_xmas_ver a b c d)
  contains_ver.count true

def count_xmas_diag (s1 s2 s3 s4 : String): Nat :=
  count_xmas_ver s1 (s2.drop 1) (s3.drop 2) (s4.drop 3)
  + count_xmas_ver (s1.drop 3) (s2.drop 2) (s3.drop 1) s4

def count_xmas (lines: List String): Nat :=
  match lines with 
    | List.nil => 0
    | l1 :: l2 :: l3 :: l4 :: xs => count_xmas_hor l1.toSubstring + count_xmas_ver l1 l2 l3 l4 + count_xmas_diag l1 l2 l3 l4 + count_xmas (l2 :: l3 :: l4 :: xs)
    | l :: xs => count_xmas_hor l.toSubstring + count_xmas xs

def count_x_mas (l1 l2 l3 : List Char): Nat := 
  if l1_len : l1.length ≥  3 then
    if l2_len : l2.length ≥ 2 then
      if l3_len : l3.length ≥ 3 then
        let c1 := l1[0]
        let c2 := l1[2]
        let c3 := l2[1]
        let c4 := l3[0] 
        let c5 := l3[2]
        let x1 := (c1 == 'M' ∧ c3 == 'A' ∧ c5 == 'S') ∨ (c1 == 'S' ∧ c3 == 'A' ∧ c5 == 'M')
        let x2 := (c2 == 'M' ∧ c3 == 'A' ∧ c4 == 'S') ∨ (c2 == 'S' ∧ c3 == 'A' ∧ c4 == 'M')
        (if x1 ∧ x2 then 1 else 0) + count_x_mas (l1.tail) (l2.tail) (l3.tail)
      else
        0
    else
      0
  else
    0


def count_x_mas_lines (lines : List String): Nat :=
  match lines with
    | l1 :: l2 :: l3 :: xs => count_x_mas (l1.toList) (l2.toList) (l3.toList) + count_x_mas_lines (l2 :: l3 :: xs)
    | _ => 0

def parse: IO (List String) := do 
  let lines ← IO.FS.lines "../data/day4-1.txt"
  pure lines.toList

def day1: IO (Nat) := do
  let lines ← parse
  pure $ count_xmas lines

def day2: IO (Nat) := do
  let lines ← parse
  pure $ count_x_mas_lines lines

#eval day1
#eval day2

def a := "abcdefg".toSubstring.drop 100
def n' := 24
#eval a
#print Substring.next
#eval (a.startPos + ⟨n'⟩, (a.next (a.startPos + ⟨n'⟩)))
