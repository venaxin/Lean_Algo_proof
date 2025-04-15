import Std

def insert (a : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [a]
  | x :: xs => if a <= x then a :: x :: xs else x :: insert a xs

def insertionSort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs => insert x (insertionSort xs)

-- Test the algorithm
#eval insertionSort [5, 3, 1, 4, 2]  -- Should output [1, 2, 3, 4, 5]

-- Define what it means for a list to be sorted
def isSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: y :: xs => x <= y ∧ isSorted (y :: xs)

-- Helper lemma for empty list
theorem insert_nil_sorted (a : Nat) : isSorted (insert a []) := by
  unfold insert
  unfold isSorted
  trivial

-- Helper lemma for singleton list
theorem insert_singleton_sorted (a b : Nat) :
  isSorted [b] → isSorted (insert a [b]) := by
  intro h
  unfold insert
  by_cases h_comp : a <= b
  . -- Case: a <= b
    simp [h_comp]
    unfold isSorted
    exact ⟨h_comp, trivial⟩
  . -- Case: a > b
    simp [h_comp]
    unfold insert
    unfold isSorted
    trivial

-- We need to prove that inserting an element into a sorted list produces a sorted list
theorem insert_preserves_sorted (a : Nat) (l : List Nat) :
  isSorted l → isSorted (insert a l) := by
  induction l with
  | nil => exact insert_nil_sorted a
  | cons x xs ih =>
    intro h_sorted
    unfold insert
    by_cases h_comp : a <= x
    . -- Case: a <= x
      simp [h_comp]
      unfold isSorted
      cases xs with
      | nil =>
        unfold isSorted at h_sorted
        exact ⟨h_comp, h_sorted⟩
      | cons y ys =>
        unfold isSorted at h_sorted
        cases h_sorted with
        | intro h1 h2 =>
          exact ⟨h_comp, h_sorted⟩
    . -- Case: a > x
      simp [h_comp]
      unfold isSorted
      cases xs with
      | nil =>
        -- When xs is empty, we get x::[a]
        unfold insert
        unfold isSorted
        -- Need to show x <= a
        simp [not_le] at h_comp
        have h_x_lt_a : x < a := h_comp
        have h_x_le_a : x <= a := Nat.le_of_lt h_x_lt_a
        exact ⟨h_x_le_a, trivial⟩
      | cons y ys =>
        -- When xs is y::ys
        unfold isSorted at h_sorted
        cases h_sorted with
        | intro h_x_le_y h_ys_sorted =>
          -- We know x <= y from h_sorted
          -- Need to show x <= first element of (insert a (y::ys))
          -- And show that (insert a (y::ys)) is sorted
          have h_insert_sorted := ih (y::ys) h_ys_sorted
          exact ⟨h_x_le_y, h_insert_sorted⟩

-- Now we can prove that insertion sort produces a sorted list
theorem insertionSort_sorts (l : List Nat) :
  isSorted (insertionSort l) := by
  induction l with
  | nil =>
    unfold insertionSort
    unfold isSorted
    trivial
  | cons x xs ih =>
    unfold insertionSort
    apply insert_preserves_sorted
    exact ih
