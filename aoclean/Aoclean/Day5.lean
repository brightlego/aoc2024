import Std.Data.HashMap
import Std.Data.HashSet


universe u

def is_correctly_ordered (order : Nat → Nat → Bool) (list : List Nat): Bool :=
  match list with 
    | .nil => true
    | x :: xs => xs.all (order x) ∧ is_correctly_ordered order xs

def get_mid {α : Type u} [inst : Inhabited α] (l : List α): α :=
  let len := l.length
  let mid := (len + 1).div 2 
  l[mid - 1]!

#eval get_mid ([] : List Nat)

def construct_order (rules : List (Nat × Nat)): Nat → Nat → Bool :=
  let map := rules.foldl (λ m ⟨x, y⟩ ↦ m.insert x $ (m.getD x Std.HashSet.empty).insert y) Std.HashMap.empty
  λ x y ↦ ((λ s ↦ s.contains x) <$> (map.get? y)) != some true 

def parseRule (s : String): Option (Nat × Nat) := do 
  let parts := s.split (· = '|')
  let part1 ← parts[0]?
  let part2 ← parts[1]?
  let x ← part1.toNat?
  let y ← part2.toNat?
  pure (x, y)

def parseList (s: String): Option (List Nat) := do
  let parts := s.split (· = ',')
  parts.mapM String.toNat?

def parse: OptionT IO ((List (Nat × Nat)) × List (List Nat)) := do
  let lines ← IO.FS.lines "../data/day5-1.txt"
  let parts ← .mk $ pure $ lines.indexOf? ""
  let rules ← .mk $ pure $ (lines.take parts).toList.mapM parseRule 
  let lists ← .mk $ pure $ (lines.toList.drop (parts + 1)).mapM parseList
  pure (rules, lists)

def day1: IO (Nat) := do
  let ⟨rules, lists⟩ ← Option.get! <$> parse.run
  let order := construct_order rules
  pure 0

#eval parse.run
