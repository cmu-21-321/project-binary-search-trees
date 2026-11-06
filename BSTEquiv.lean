import BSTEquiv.Basic
import Mathlib

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

theorem getElem?_set_ne
    (t : AltBST β) (i j : Nat)
    (x : Option (Nat × β))
    (h : i ≠ j) :
    (t.set i x)[j]? = t[j]? := by
  simp [h]

theorem getElem?_append_replicate
    (t : AltBST β) (n j : Nat)
    (h : j < t.length) :
    (t ++ List.replicate n (none : Option (Nat × β)))[j]? =
      t[j]? := by
  simp [List.getElem?_append, h]

theorem getElem?_append_replicate_none
    (t : AltBST β) (n j : Nat)
    (h1 : t.length ≤ j)
    (h2 : j < t.length + n) :
    (t ++ List.replicate n (none : Option (Nat × β)))[j]? =
      some none := by
  simp [h1, h2]

private theorem locate_set_same_key_aux
    (t : AltBST β) (k start i : Nat)
    (v w : β)
    (h : t.locate k start = i)
    (hi : i < t.length)
    (hkey : t[i] = some (k, v)) :
    AltBST.locate
    (List.set t i (some (k, w))) k 0 = i := by
  sorry
termination_by t.length - start

theorem locate_set_same_key
    (t : AltBST β) (k : Nat) (i : Nat)
    (v w : β)
    (h : t.locate k 0 = i)
    (hi : i < t.length)
    (hkey : t[i] = some (k, v)) :
    AltBST.locate
    (List.set t i (some (k, w))) k 0 = i := by
  exact locate_set_same_key_aux t k 0 i v w h hi hkey
/-- every slot is out of bounds, empty, or holds a key -/
theorem slot_cases (t : AltBST β) (i : Nat) :
    t[i]? = none ∨ t[i]? = some none ∨
      ∃ key w, t[i]? = some (some (key, w)) := by
  cases h : t[i]? with
  | none => exact Or.inl rfl
  | some o =>
    cases o with
    | none => exact Or.inr (Or.inl rfl)
    | some p =>
      obtain ⟨a, b⟩ := p
      exact Or.inr (Or.inr ⟨a, b, rfl⟩)

/-- `locate` stops at an out-of-bounds or empty slot -/
theorem locate_stop (t : AltBST β) (k i : Nat)
    (h : t[i]? = none ∨ t[i]? = some none) : t.locate k i = i := by
  by_cases hi : i < t.length
  · have hn : t[i] = none := by
      rw [List.getElem?_eq_getElem hi] at h
      rcases h with h | h
      · simp at h
      · exact Option.some.inj h
    exact AltBST.locate_none t k i hi hn
  · exact AltBST.locate_out_of_bounds t k i (Nat.le_of_not_lt hi)

/-- one step of `locate` at a slot holding `key` -/
theorem locate_step (t : AltBST β) (k i key : Nat) (w : β)
    (h : t[i]? = some (some (key, w))) :
    t.locate k i =
      if k < key then t.locate k (2 * i + 1)
      else if key < k then t.locate k (2 * i + 2)
      else i := by
  have hi : i < t.length := by
    by_contra hn
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
    simp at h
  rw [List.getElem?_eq_getElem hi] at h
  have h' : t[i] = some (key, w) := Option.some.inj h
  conv_lhs => unfold AltBST.locate
  simp [hi, h']

/-- `locate` stops at an empty slot or at a slot holding `k` -/
theorem locate_stop_key (t : AltBST β) (k j : Nat)
    (h : t[j]? = some none ∨ ∃ v, t[j]? = some (some (k, v))) :
    t.locate k j = j := by
  rcases h with h | ⟨v, h⟩
  · exact locate_stop t k j (Or.inr h)
  · have hs := locate_step t k j k v h
    rw [ite_eq_right (Nat.lt_irrefl k), ite_eq_right (Nat.lt_irrefl k)] at hs
    exact hs

/-- `locate` never moves backwards -/
theorem locate_ge (t : AltBST β) (k : Nat) :
    ∀ N start, t.length - start ≤ N → start ≤ t.locate k start := by
  intro N
  induction N with
  | zero =>
    intro start hN
    exact le_of_eq (AltBST.locate_out_of_bounds t k start (by omega)).symm
  | succ N ih =>
    intro start hN
    rcases slot_cases t start with hn | hn | ⟨key, w, hw⟩
    · rw [locate_stop t k start (Or.inl hn)]
    · rw [locate_stop t k start (Or.inr hn)]
    · have hs := locate_step t k start key w hw
      by_cases hlt : k < key
      · rw [ite_eq_left hlt] at hs
        have := ih (2 * start + 1) (by omega)
        omega
      · by_cases hgt : key < k
        · rw [ite_eq_right hlt, ite_eq_left hgt] at hs
          have := ih (2 * start + 2) (by omega)
          omega
        · rw [ite_eq_right hlt, ite_eq_right hgt] at hs
          omega

/-- the slot where `locate` stops (if in bounds) is empty or holds `k` -/
theorem locate_stops (t : AltBST β) (k : Nat) :
    ∀ N start, t.length - start ≤ N → t.locate k start < t.length →
      (t[t.locate k start]? = some none ∨
       ∃ v, t[t.locate k start]? = some (some (k, v))) := by
  intro N
  induction N with
  | zero =>
    intro start hN hlt
    have := AltBST.locate_out_of_bounds t k start (by omega)
    exfalso
    omega
  | succ N ih =>
    intro start hN hlt
    rcases slot_cases t start with hn | hn | ⟨key, w, hw⟩
    · rw [locate_stop t k start (Or.inl hn)] at hlt
      have := List.getElem?_eq_getElem hlt
      rw [hn] at this
      simp at this
    · rw [locate_stop t k start (Or.inr hn)]
      exact Or.inl hn
    · have hs := locate_step t k start key w hw
      by_cases hlt1 : k < key
      · rw [ite_eq_left hlt1] at hs
        rw [hs] at hlt ⊢
        exact ih (2 * start + 1) (by omega) hlt
      · by_cases hgt : key < k
        · rw [ite_eq_right hlt1, ite_eq_left hgt] at hs
          rw [hs] at hlt ⊢
          exact ih (2 * start + 2) (by omega) hlt
        · rw [ite_eq_right hlt1, ite_eq_right hgt] at hs
          have hkk : key = k := by omega
          rw [hs]
          right
          exact ⟨w, by rw [hw, hkk]⟩

/-- slots in the padding (or beyond it) are out of bounds or empty -/
theorem pad_getElem_ge (t : AltBST β) (n m : Nat) (hge : t.length ≤ m) :
    (t ++ List.replicate n (none : Option (Nat × β)))[m]? = none ∨
    (t ++ List.replicate n (none : Option (Nat × β)))[m]? = some none := by
  by_cases hm : m < t.length + n
  · exact Or.inr (getElem?_append_replicate_none t n m hge hm)
  · left
    apply List.getElem?_eq_none
    rw [List.length_append, List.length_replicate]
    omega

/-- padding with `none`s doesn't change where `locate` stops -/
theorem locate_pad_eq (t : AltBST β) (n k : Nat) :
    ∀ N start, t.length - start ≤ N →
      AltBST.locate (t ++ List.replicate n (none : Option (Nat × β))) k start
        = t.locate k start := by
  have hge_case : ∀ start, t.length ≤ start →
      AltBST.locate (t ++ List.replicate n (none : Option (Nat × β))) k start
        = t.locate k start := by
    intro start hge
    have h1 := AltBST.locate_out_of_bounds t k start hge
    have h2 := locate_stop (t ++ List.replicate n (none : Option (Nat × β)))
      k start (pad_getElem_ge t n start hge)
    rw [h1, h2]
  intro N
  induction N with
  | zero =>
    intro start hN
    exact hge_case start (by omega)
  | succ N ih =>
    intro start hN
    by_cases hs : t.length ≤ start
    · exact hge_case start hs
    · have hlt : start < t.length := by omega
      have hget := getElem?_append_replicate t n start hlt
      rcases slot_cases t start with hn | hn | ⟨key, w, hw⟩
      · have h1 := locate_stop t k start (Or.inl hn)
        have h2 := locate_stop
          (t ++ List.replicate n (none : Option (Nat × β))) k start
          (by rw [hget]; exact Or.inl hn)
        rw [h1, h2]
      · have h1 := locate_stop t k start (Or.inr hn)
        have h2 := locate_stop
          (t ++ List.replicate n (none : Option (Nat × β))) k start
          (by rw [hget]; exact Or.inr hn)
        rw [h1, h2]
      · have hw' : (t ++ List.replicate n (none : Option (Nat × β)))[start]?
            = some (some (key, w)) := by
          rw [hget]; exact hw
        have hs1 := locate_step t k start key w hw
        have hs2 := locate_step
          (t ++ List.replicate n (none : Option (Nat × β))) k start key w hw'
        by_cases hlt1 : k < key
        · rw [if_pos hlt1] at hs1 hs2
          rw [hs2, hs1]
          exact ih (2 * start + 1) (by omega)
        · by_cases hgt : key < k
          · rw [if_neg hlt1, if_pos hgt] at hs1 hs2
            rw [hs2, hs1]
            exact ih (2 * start + 2) (by omega)
          · rw [if_neg hlt1, if_neg hgt] at hs1 hs2
            rw [hs1, hs2]

theorem locate_congr
    (t s : AltBST β)
    (k start i : Nat)
    (h : t.locate k start = i)
    (hprefix : ∀ j, j < i → t[j]? = s[j]?)
    (hstop :
      s[i]? = some none ∨
      ∃ v, s[i]? = some (some (k, v))) :
    s.locate k start = i := by
  have aux : ∀ N start, t.length - start ≤ N →
      t.locate k start = i → s.locate k start = i := by
    intro N
    induction N with
    | zero =>
      intro start hN h
      have h1 := AltBST.locate_out_of_bounds t k start (by omega)
      have hi : i = start := by omega
      rw [hi] at hstop ⊢
      exact locate_stop_key s k start hstop
    | succ N ih =>
      intro start hN h
      rcases slot_cases t start with hn | hn | ⟨key, w, hw⟩
      · have h1 := locate_stop t k start (Or.inl hn)
        have hi : i = start := by omega
        rw [hi] at hstop ⊢
        exact locate_stop_key s k start hstop
      · have h1 := locate_stop t k start (Or.inr hn)
        have hi : i = start := by omega
        rw [hi] at hstop ⊢
        exact locate_stop_key s k start hstop
      · have hs := locate_step t k start key w hw
        by_cases hlt : k < key
        · rw [if_pos hlt] at hs
          have hge := locate_ge t k t.length (2 * start + 1) (by omega)
          have hpre := hprefix start (by omega)
          have hsw : s[start]? = some (some (key, w)) := by
            rw [← hpre]; exact hw
          have hss := locate_step s k start key w hsw
          rw [if_pos hlt] at hss
          rw [hss]
          exact ih (2 * start + 1) (by omega) (by omega)
        · by_cases hgt : key < k
          · rw [if_neg hlt, if_pos hgt] at hs
            have hge := locate_ge t k t.length (2 * start + 2) (by omega)
            have hpre := hprefix start (by omega)
            have hsw : s[start]? = some (some (key, w)) := by
              rw [← hpre]; exact hw
            have hss := locate_step s k start key w hsw
            rw [if_neg hlt, if_pos hgt] at hss
            rw [hss]
            exact ih (2 * start + 2) (by omega) (by omega)
          · rw [if_neg hlt, if_neg hgt] at hs
            have hi : i = start := by omega
            rw [hi] at hstop ⊢
            exact locate_stop_key s k start hstop
  exact aux t.length start (by omega) h

theorem locate_append_none
    (t : AltBST β) (k i : Nat)
    (h : t.locate k 0 = i)
    (hi : t.length ≤ i) :
    (t ++ List.replicate (i + 1 - t.length)
      (none : Option (Nat × β))).locate k 0 = i := by
  rw [locate_pad_eq t (i + 1 - t.length) k t.length 0 (by omega)]
  exact h

theorem locate_set_new_key
    (t : AltBST β) (k i : Nat)
    (v : β)
    (h : t.locate k 0 = i)
    (hi : i < t.length)
    (hnone : t[i] = none) :
    AltBST.locate
    (List.set t i (some (k, v))) k 0 = i := by
  exact locate_congr t (List.set t i (some (k, v))) k 0 i h
    (fun j hj => (getElem?_set_ne t i j _ (by omega)).symm)
    (Or.inr ⟨v, by simp [hi]⟩)

theorem locate_result_characterization
    (t : AltBST β) (k : Nat) :
    let i := t.locate k 0
    i < t.length →
      (t[i]? = some none ∨
       ∃ v, t[i]? = some (some (k, v))) := by
  intro i
  exact locate_stops t k t.length 0 (by omega)

-- inserting a key preserves its search location
theorem AltBST.locate_insert_same
    (t : AltBST β) (k : Nat) (v : β) :
    (t.insert k v).locate k 0 = t.locate k 0 := by
  simp only [AltBST.insert]
  generalize hi : AltBST.locate t k 0 = i
  by_cases hlt : i < t.length
  · -- the key's slot is already inside the list
    rw [ite_eq_left hlt]
    have hchar : i < t.length →
        (t[i]? = some none ∨ ∃ w, t[i]? = some (some (k, w))) := by
      subst hi
      exact locate_result_characterization t k
    rcases hchar hlt with h | ⟨w, h⟩
    · -- empty slot: inserting a new key
      rw [List.getElem?_eq_getElem hlt] at h
      have hnone : t[i] = none := Option.some.inj h
      exact locate_set_new_key t k i v hi hlt hnone
    · -- slot already holds key k: overwriting its value
      rw [List.getElem?_eq_getElem hlt] at h
      have hkey : t[i] = some (k, w) := Option.some.inj h
      exact locate_set_same_key t k i w v hi hlt hkey
  · -- the slot is past the end: pad with `none`s, then set
    rw [ite_eq_right hlt]
    have hge : t.length ≤ i := Nat.not_lt.mp hlt
    have hloc := locate_append_none t k i hi hge
    have hlen : i < (t ++ List.replicate (i + 1 - t.length)
        (none : Option (Nat × β))).length := by
      simp only [List.length_append, List.length_replicate]
      omega
    have h2 := getElem?_append_replicate_none t (i + 1 - t.length) i hge
      (by omega)
    rw [List.getElem?_eq_getElem hlen] at h2
    have hnone : (t ++ List.replicate (i + 1 - t.length)
        (none : Option (Nat × β)))[i] = none := Option.some.inj h2
    exact locate_set_new_key _ k i v hloc hlen hnone

def keyAt (t : AltBST β) (m : Nat) : Option Nat :=
  ((t[m]?).bind id).map Prod.fst

theorem keyAt_of_none (l : AltBST β) (m : Nat) (h : l[m]? = none) :
    keyAt l m = none := by
  simp [keyAt, h]

theorem keyAt_of_some_none (l : AltBST β) (m : Nat) (h : l[m]? = some none) :
    keyAt l m = none := by
  simp [keyAt, h]

theorem keyAt_of_some_some (l : AltBST β) (m key : Nat) (w : β)
    (h : l[m]? = some (some (key, w))) :
    keyAt l m = some key := by
  simp [keyAt, h]

theorem keyAt_eq_some {t : AltBST β} {i key : Nat}
    (h : keyAt t i = some key) :
    ∃ w, t[i]? = some (some (key, w)) := by
  cases hx : t[i]? with
  | none => simp [keyAt, hx] at h
  | some o =>
    cases o with
    | none => simp [keyAt, hx] at h
    | some p =>
      obtain ⟨key', w⟩ := p
      simp [keyAt, hx] at h
      exact ⟨w, by rw [← h]⟩

theorem keyAt_set_ne (t : AltBST β) (i m : Nat)
    (x : Option (Nat × β)) (h : i ≠ m) :
    keyAt (t.set i x) m = keyAt t m := by
  unfold keyAt
  rw [getElem?_set_ne t i m x h]

theorem keyAt_pad (t : AltBST β) (n m : Nat) :
    keyAt (t ++ List.replicate n (none : Option (Nat × β))) m = keyAt t m := by
  by_cases hm : m < t.length
  · unfold keyAt
    rw [getElem?_append_replicate t n m hm]
  · have hge : t.length ≤ m := Nat.le_of_not_lt hm
    rw [keyAt_of_none t m (List.getElem?_eq_none hge)]
    by_cases hm2 : m < t.length + n
    · exact keyAt_of_some_none _ m
        (getElem?_append_replicate_none t n m hge hm2)
    · have h2 : (t ++ List.replicate n (none : Option (Nat × β)))[m]? = none := by
        apply List.getElem?_eq_none
        rw [List.length_append, List.length_replicate]
        omega
      exact keyAt_of_none _ m h2

theorem getElem?_pad_some (t : AltBST β) (n m : Nat) (x : Nat × β)
    (h : (t ++ List.replicate n (none : Option (Nat × β)))[m]? = some (some x)) :
    t[m]? = some (some x) := by
  by_cases hm : m < t.length
  · rwa [getElem?_append_replicate t n m hm] at h
  · exfalso
    have hge : t.length ≤ m := Nat.le_of_not_lt hm
    by_cases hm2 : m < t.length + n
    · rw [getElem?_append_replicate_none t n m hge hm2] at h
      simp at h
    · have h2 : (t ++ List.replicate n (none : Option (Nat × β)))[m]? = none := by
        apply List.getElem?_eq_none
        rw [List.length_append, List.length_replicate]
        omega
      rw [h2] at h
      simp at h

/-- one step of `locate` at a slot holding key `key` -/
theorem locate_step_some (t : AltBST β) (k i key : Nat) (w : β)
    (h : t[i]? = some (some (key, w))) :
    t.locate k i =
      if k < key then t.locate k (2 * i + 1)
      else if key < k then t.locate k (2 * i + 2)
      else i := by
  have hi : i < t.length := by
    by_contra hn
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
    simp at h
  rw [List.getElem?_eq_getElem hi] at h
  have h' : t[i] = some (key, w) := Option.some.inj h
  conv_lhs => unfold AltBST.locate
  rw [dite_eq_left hi]
  simp [h']

theorem locate_of_keyAt_none (t : AltBST β) (k i : Nat)
    (h : keyAt t i = none) : t.locate k i = i := by
  by_cases hi : i < t.length
  · unfold AltBST.locate
    rw [dite_eq_left hi]
    rcases hx : t[i] with _ | ⟨key', w⟩
    · simp
    · exfalso
      unfold keyAt at h
      rw [List.getElem?_eq_getElem hi, hx] at h
      simp at h
  · exact AltBST.locate_out_of_bounds t k i (Nat.le_of_not_lt hi)

/-- `locate` always stops at an empty slot or at a slot holding `k` -/
theorem keyAt_locate (t : AltBST β) (k : Nat) :
    ∀ (N start : Nat), t.length - start ≤ N →
      keyAt t (t.locate k start) = none ∨
      keyAt t (t.locate k start) = some k := by
  intro N
  induction N with
  | zero =>
    intro start hN
    have h0 : t.length ≤ start := by omega
    rw [AltBST.locate_out_of_bounds t k start h0]
    exact Or.inl (keyAt_of_none t start (List.getElem?_eq_none h0))
  | succ N ih =>
    intro start hN
    rcases hka : keyAt t start with _ | key
    · rw [locate_of_keyAt_none t k start hka]
      exact Or.inl hka
    · obtain ⟨w, hw⟩ := keyAt_eq_some hka
      have hts : start < t.length := by
        by_contra hn
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hw
        simp at hw
      by_cases hlt : k < key
      · rw [locate_step_some t k start key w hw, ite_eq_left hlt]
        exact ih (2 * start + 1) (by omega)
      · by_cases hgt : key < k
        · rw [locate_step_some t k start key w hw, ite_eq_right hlt, ite_eq_left hgt]
          exact ih (2 * start + 2) (by omega)
        · rw [locate_step_some t k start key w hw, ite_eq_right hlt, ite_eq_right hgt]
          have hkk : key = k := by omega
          right
          rw [hka, hkk]

/-- If `s` differs from `t` only at slot `p`, and at `p` either `t` is empty
or the key is unchanged, then a search that ends at `j ≠ p` in `t`
ends at `j` in `s` too. -/
theorem locate_cong_off (t s : AltBST β) (k p : Nat)
    (hag : ∀ m, m ≠ p → keyAt s m = keyAt t m)
    (hp : keyAt t p = none ∨ keyAt s p = keyAt t p) :
    ∀ (N start j : Nat), t.length - start ≤ N → s.length - start ≤ N →
      t.locate k start = j →
      (keyAt s p = keyAt t p ∨ j ≠ p) →
      s.locate k start = j := by
  intro N
  induction N with
  | zero =>
    intro start j ht hs hloc _
    have ht' : t.length ≤ start := by omega
    have hs' : s.length ≤ start := by omega
    rw [AltBST.locate_out_of_bounds t k start ht'] at hloc
    rw [AltBST.locate_out_of_bounds s k start hs']
    exact hloc
  | succ N ih =>
    intro start j ht hs hloc hj
    have hsame : keyAt s start = keyAt t start := by
      by_cases hsp : start = p
      · by_cases heq : keyAt s p = keyAt t p
        · rw [hsp]; exact heq
        · exfalso
          have hnone : keyAt t p = none := hp.resolve_right heq
          have hj' : j ≠ p := hj.resolve_left heq
          apply hj'
          rw [← hloc, hsp]
          exact locate_of_keyAt_none t k p hnone
      · exact hag start hsp
    rcases hka : keyAt t start with _ | key
    · rw [hka] at hsame
      rw [← hloc, locate_of_keyAt_none t k start hka,
        locate_of_keyAt_none s k start hsame]
    · rw [hka] at hsame
      obtain ⟨w, hw⟩ := keyAt_eq_some hka
      obtain ⟨w', hw'⟩ := keyAt_eq_some hsame
      have hts : start < t.length := by
        by_contra hn
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hw
        simp at hw
      have hss : start < s.length := by
        by_contra hn
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hw'
        simp at hw'
      by_cases hlt : k < key
      · rw [locate_step_some t k start key w hw, ite_eq_left hlt] at hloc
        rw [locate_step_some s k start key w' hw', ite_eq_left hlt]
        exact ih (2 * start + 1) j (by omega) (by omega) hloc hj
      · by_cases hgt : key < k
        · rw [locate_step_some t k start key w hw, ite_eq_right hlt, ite_eq_left hgt] at hloc
          rw [locate_step_some s k start key w' hw', ite_eq_right hlt, ite_eq_left hgt]
          exact ih (2 * start + 2) j (by omega) (by omega) hloc hj
        · rw [locate_step_some t k start key w hw, ite_eq_right hlt, ite_eq_right hgt] at hloc
          rw [locate_step_some s k start key w' hw', ite_eq_right hlt, ite_eq_right hgt]
          exact hloc

theorem AltBST.insert_valid
    (t : AltBST β) (k : Nat) (v : β)
    (h : t.Valid) :
    (t.insert k v).Valid := by
  intro j k' w hj
  have hsame := AltBST.locate_insert_same t k v
  -- name the (possibly padded) list that `insert` writes into
  obtain ⟨res, hres_len, hres_key, hres_get, hins⟩ :
      ∃ res : AltBST β, t.locate k 0 < res.length ∧
        (∀ m, keyAt res m = keyAt t m) ∧
        (∀ m x, res[m]? = some (some x) → t[m]? = some (some x)) ∧
        t.insert k v = res.set (t.locate k 0) (some (k, v)) := by
    by_cases hlt : t.locate k 0 < t.length
    · exact ⟨t, hlt, fun m => rfl, fun m x hx => hx,
        by simp [AltBST.insert, hlt]⟩
    · refine ⟨t ++ List.replicate (t.locate k 0 + 1 - t.length)
          (none : Option (Nat × β)), ?_, fun m => keyAt_pad _ _ m,
        fun m x hx => getElem?_pad_some _ _ m x hx, ?_⟩
      · rw [List.length_append, List.length_replicate]
        omega
      · simp [AltBST.insert, hlt]
  rw [hins] at hj hsame ⊢
  set i := t.locate k 0 with hi
  have hget : (res.set i (some (k, v)))[i]? = some (some (k, v)) := by
    simp [hres_len]
  by_cases hji : j = i
  · -- the freshly written slot: its key is `k`
    rw [hji] at hj ⊢
    rw [hget] at hj
    have hk : k = k' := by
      have h2 := hj
      simp at h2
      exact h2.1
    rw [← hk]
    exact hsame
  · -- any other slot already held `(k', w)` in `t`
    have hne : i ≠ j := fun h' => hji h'.symm
    rw [getElem?_set_ne res i j _ hne] at hj
    have hjt : t[j]? = some (some (k', w)) := hres_get j (k', w) hj
    have hvalid : t.locate k' 0 = j := h j k' w hjt
    have hag : ∀ m, m ≠ i →
        keyAt (res.set i (some (k, v))) m = keyAt t m := by
      intro m hm
      rw [keyAt_set_ne res i m _ (fun h' => hm h'.symm), hres_key m]
    have hp : keyAt t i = none ∨
        keyAt (res.set i (some (k, v))) i = keyAt t i := by
      have hloc := keyAt_locate t k t.length 0 (by omega)
      rw [← hi] at hloc
      rcases hloc with h0 | h1
      · exact Or.inl h0
      · right
        rw [keyAt_of_some_some _ i k v hget, h1]
    exact locate_cong_off t (res.set i (some (k, v))) k' i hag hp
      (t.length + (res.set i (some (k, v))).length) 0 j
      (by omega) (by omega) hvalid (Or.inr hji)
end AlternativeBST
