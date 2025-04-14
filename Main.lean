import Std

def insert (a : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [a]
  | x :: xs => if a <= x then a :: x :: xs else x :: insert a xs

def insertionSort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs => insert x (insertionSort xs)

#eval insertionSort [5, 3, 1, 4, 2]

def isSorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: y :: xs => x <= y ∧ isSorted (y :: xs)

theorem insertionSort_sorts (l : List Nat) :
  isSorted (insertionSort l) := by
  sorry  
