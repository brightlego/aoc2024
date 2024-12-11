theorem substring_le_next {ss : Substring} {p : String.Pos}: p.byteIdx ≤ (ss.next p).byteIdx := by
  by_cases h : ss.startPos + p = ss.stopPos
  . simp [Substring.next, h]
  . simp [Substring.next, h]
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm, ← String.Pos.add_byteIdx]
    apply Nat.le_of_lt
    apply String.lt_next'

theorem substring_le_nextn {ss : Substring} {i : Nat} {p : String.Pos}: p.byteIdx ≤ (ss.nextn i p).byteIdx := by 
  match i with 
  | .zero => simp [Substring.nextn]
  | .succ i =>
    simp [Substring.nextn]
    apply Nat.le_trans substring_le_next substring_le_nextn

theorem substring_drop_bsize_le {ss : Substring} {n : Nat}: (ss.drop n).bsize ≤ ss.bsize := by
  simp [Substring.drop, Substring.nextn, Substring.bsize]
  rw [← Nat.sub_sub]
  apply Nat.sub_le

theorem substring_drop_bsize_lt {ss : Substring} {n : Nat} (non_empty : ss.bsize ≠ 0) (n_pos : n ≠ 0): (ss.drop n).bsize < ss.bsize := by
  simp [Substring.drop, Substring.nextn, Substring.bsize]
  rw [← Nat.sub_sub]
  apply Nat.sub_lt
  . rw [← Nat.ne_zero_iff_zero_lt]
    assumption
  . let ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero n_pos
    simp [hm, Substring.nextn]
    apply Nat.lt_of_lt_of_le
    . apply Substring.lt_next
      rw [← Nat.ne_zero_iff_zero_lt]
      assumption
    . apply substring_le_nextn

#print substring_drop_bsize_lt

def count_xmas_hor (s: Substring): Nat := 
  if h1 : s.bsize = 0 then
    0
  else
    let val? : Option Substring := s.dropPrefix? "XMAS".toSubstring <|> s.dropPrefix? "SAMX".toSubstring
    if h2 : val?.isSome then
      let t := s.drop 3
      have three_neq_zero : 3 ≠ 0 := by simp
      have h3 : (s.drop 3).bsize < s.bsize := substring_drop_bsize_lt h1 three_neq_zero
      1 + count_xmas_hor t
    else
      let t := s.drop 1
      have h4 : (s.drop 1).bsize < s.bsize := substring_drop_bsize_lt h1 Nat.one_ne_zero
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

def count_xmas: List String → Nat 
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


def count_x_mas_lines: List String → Nat
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
