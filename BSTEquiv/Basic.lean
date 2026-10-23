namespace AlternativeBST

/- a list with entries that are either empty or a tuple of a key and a value-/
abbrev AltBST (β : Type u) := List (Option (Nat × β))

/- def of empty tree-/
def AltBST.leaf : AltBST β := []

/- returns the index of where a given key is stored or where it would go-/
def AltBST.locate (t : AltBST β) (k : Nat) (i : Nat) : Nat :=
  if h : i < t.length then
    match t[i] with
    | none => i
    | some (key, _) =>
      if k < key then AltBST.locate t k (2 * i + 1)
      else if key < k then AltBST.locate t k (2 * i + 2)
      else i
    else i
  termination_by t.length - i

/- returns 'some v' if the value 'v' exists in the tree 't' with key 'k'-/
def AltBST.find? (t : AltBST β) (k : Nat) : Option β :=
  match t.getD (AltBST.locate t k 0) none with
  | none => none
  | some (key, value) => if key = k then some value else none

def AltBST.insert (t : AltBST β) (k : Nat) (v : β) : AltBST β :=
  let i := AltBST.locate t k 0
  let res :=
    if i < t.length then t
    else t ++ List.replicate (i + 1 - t.length) (none : Option (Nat × β))
  res.set i (some (k, v))

end AlternativeBST
