

def getMulHead: StateM (Substring × Bool) (Option ((Nat × Nat))) := do
  let (s, d) ← .get
  let val := do
    let s' ← s.dropPrefix? "mul(".toSubstring
    let d1 ← (s'.takeWhile Char.isDigit).toNat?
    let s'' ← (s'.dropWhile Char.isDigit).dropPrefix? ",".toSubstring
    let d2 ← (s''.takeWhile Char.isDigit).toNat?
    let s''' := s''.dropWhile Char.isDigit
    let remaining ← s'''.dropPrefix? ")".toSubstring
    pure ((d1, d2), remaining)
  let isDo := s.dropPrefix? "do()".toSubstring
  let isDont := s.dropPrefix? "don't()".toSubstring
  isDo.elim (
    isDont.elim (
      val.elim (do
        let s' := (s.drop 1).dropWhile (λ c ↦ c ≠ 'm' ∧ c ≠ 'd')
        StateT.set (s', d)
        pure none
      ) (λ ((d1, d2), s') ↦ do
        StateT.set (s', d)
        if d then
          (pure ∘ pure) (d1, d2)
        else
          pure none
      )
    ) (
      λ s' ↦ do
        StateT.set (s', false)
        pure none
    )
  ) (
    λ s' ↦ do
      StateT.set (s', true)
      pure none
  )

def getMul (n: Nat): StateM (Substring × Bool) (List (Nat × Nat)) := do
  let (s, _) ← .get
  if n = 0 ∨ s.isEmpty then
    pure []
  else do
    let val ← getMulHead
    let tail ← getMul (n - 1)
    pure $ (val.elim [] List.singleton) ++ tail

def day1: IO Nat := do
  let file ← IO.FS.readFile "../data/day3-1.txt"
  let muls := ((getMul (file.length)).run (file.toSubstring, true)).fst
  let val := muls.map (λ (x, y) ↦ x * y)
  pure val.sum

#eval day1
