import Mathlib.Data.List.Sort

namespace InsertionSort

-- Define the insertion function
def insert (a : ℕ) (l : List ℕ) : List ℕ :=
  match l with
  | [] => [a]
  | x :: xs => if a ≤ x then a :: x :: xs else x :: insert a xs

-- Define insertion sort
def insertionSort : List ℕ → List ℕ
  | [] => []
  | x :: xs => insert x (insertionSort xs)

-- Prove that insertion preserves sortedness
theorem insert_sorted (a : ℕ) (l : List ℕ) (h : List.Sorted (· ≤ ·) l) :
    List.Sorted (· ≤ ·) (insert a l) := by
  induction l with
  | nil => simp [insert]  -- Inserting into empty list is trivially sorted
  | cons x xs ih =>
    cases xs with
    | nil =>
      -- Single-element list case
      simp [insert, List.Sorted]
      split <;> simp_all [List.Sorted]
    | cons y ys =>
      -- Multi-element list case
      simp [insert, List.Sorted] at h ⊢
      split <;> simp_all [List.Sorted]
      <;> cases h <;> simp_all [List.Sorted]
      <;> nlinarith

-- Prove insertion sort produces sorted lists
theorem insertion_sort_sorts (l : List ℕ) : List.Sorted (· ≤ ·) (insertionSort l) := by
  induction l with
  | nil => simp [insertionSort]  -- Empty list is sorted
  | cons x xs ih =>
    simp [insertionSort]
    exact insert_sorted x _ ih

-- Example usage
#eval insertionSort [5, 3, 1, 4, 2]  -- Output: [1, 2, 3, 4, 5]
