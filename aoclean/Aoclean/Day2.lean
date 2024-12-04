def parseLine (s: String): List Nat :=
  let parts := s.split (· == ' ')
  let nats := parts.map String.toNat?
  nats.foldl (fun acc val ↦ acc ++ val.elim [] List.singleton) []

#eval parseLine "12  34 5 6  1"

def parse: IO (List (List Nat)) := do
  let lines ← IO.FS.lines "../data/day2-1.txt"
  pure $ lines.toList.map parseLine

def isValid (data: List Nat): Bool :=
  let deltas := data.zipWith Int.subNatNat (data.tail)
  let monotonic := (deltas.all (λ x ↦ x ≥ 1)) ∨ (deltas.all (λ x ↦ x ≤ -1))
  let bounded := (deltas.map Int.natAbs).all (λ x ↦ x ≤ 3)
  monotonic ∧ bounded

def isValid2 (data: List Nat): Bool :=
  let indices := List.range data.length
  let sublistPairs := indices.map data.splitAt
  let removeds := sublistPairs.map (λ (xs, ys) ↦ xs ++ ys.tail)
  removeds.any isValid

def part1: IO Nat := do
  let lines ← parse
  pure (lines.filter isValid).length

def part2: IO Nat := do
  let lines ← parse
  pure (lines.filter isValid2).length

#eval part2
