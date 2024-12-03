

def parsePairs (s: String): Option (Nat × Nat) := do
  let parts := s.split (· == ' ')
  let first ← parts[0]?
  let second ← parts[3]?
  let a ← first.toNat?
  let b ← second.toNat?
  pure (a, b)

#eval parsePairs "12 34"

def parseInput: IO (Array Nat × Array Nat) := do
  let lines ← IO.FS.lines "../data/day1-1.txt"
  let pairs := lines.mapM parsePairs
  let unsafePairs := pairs.get!
  let arr1 := unsafePairs.map (Prod.fst)
  let arr2 := unsafePairs.map (Prod.snd)
  pure (arr1, arr2)

def diff (a: Nat) (b: Nat): Nat := (Nat.max a b).sub (Nat.min a b)

def day1: IO (Nat) := do
  let ⟨a1, a2⟩ ← parseInput
  let s1 := a1.toList.mergeSort
  let s2 := a2.toList.mergeSort
  let delta := List.zipWith diff s1 s2
  pure delta.sum

def count (val: Nat) (arr: Array Nat): Nat := arr.foldl (fun acc n ↦ if n == val then acc + 1 else acc) 0

def day2: IO (Nat) := do
  let ⟨a1, a2⟩ ← parseInput
  let b := a1.map (fun n ↦ n * (count n a2))
  pure b.toList.sum

#eval day1
#eval day2
