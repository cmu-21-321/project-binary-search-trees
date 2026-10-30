import BSTEquiv.Basic

namespace AlternativeBST

-- the empty tree is valid
theorem AltBST.leaf_valid :
    (AltBST.leaf : AltBST β).Valid := by
  simp [AltBST.Valid, AltBST.leaf]

-- searching beyond bounds of list returns current index
theorem AltBST.locate_out_of_bounds
    (t : AltBST β) (k i : Nat)
    (h : t.length ≤ i) :
    t.locate k i = i := by
  unfold AltBST.locate
  simp [Nat.not_lt.mpr h]

-- searching empty node returns its index
theorem AltBST.locate_none
    (t : AltBST β) (k i : Nat)
    (h : i < t.length)
    (hnone : t[i] = none) :
    t.locate k i = i := by
  unfold AltBST.locate
  simp [h, hnone]

-- searching for a key at its own node returns that index
theorem AltBST.locate_key
    (t : AltBST β) (k i : Nat) (v : β)
    (h : i < t.length)
    (hkey : t[i] = some (k, v)) :
    t.locate k i = i := by
  unfold AltBST.locate
  simp [h, hkey]

-- inserting a key preserves its search location
theorem AltBST.locate_insert_same
    (t : AltBST β) (k : Nat) (v : β) :
    (t.insert k v).locate k 0 = t.locate k 0 := by
  sorry

-- inserting into a valid tree produces another valid tree
theorem AltBST.insert_valid
    (t : AltBST β) (k : Nat) (v : β)
    (h : t.Valid) :
    (t.insert k v).Valid := by
  sorry

end AlternativeBST
