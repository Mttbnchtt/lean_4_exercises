
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero}

#eval Nat.zero = 0
#eval natOrigin

def replaceX (α : Type) (p : PPoint α) (newX : α) : PPoint α :=
  { p with x := newX}
#check (replaceX)
#check replaceX
#check (replaceX Nat)
#check replaceX Nat
#check (replaceX Nat natOrigin)
#check replaceX Nat natOrigin
#check (replaceX Nat natOrigin 1)
#check replaceX Nat natOrigin 1
#eval replaceX Nat natOrigin 1

inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int | Sign.zero => Nat :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
  | Sign.zero => (0 : Nat)

#eval posOrNegThree Sign.pos
#eval posOrNegThree Sign.neg
#eval posOrNegThree Sign.zero

def divisors ( n : Nat) : List Nat :=
  List.filter (fun x => (n % x = 0)) (List.range' 1 (n-1))

def is_perfect (n : Nat) : Bool :=
  match n with
  | 0 | 1 => false
  | _ => (divisors n).sum = n

def perfect_numbers (n : Nat) : List Nat :=
  (List.range n).filter (fun x => (is_perfect x))

#eval is_perfect 0
#eval is_perfect 1
#eval is_perfect 2
#eval is_perfect 6
#eval divisors 6

#eval perfect_numbers 1000


#eval divisors 10
#eval [2, 3, 5, 7].length
#eval [2, 3, 5, 7].map (fun x => x + 1)
#eval ([2, 3, 5, 7].map (fun x => x + 1)).length
#eval [2, 3, 5, 7].map (fun x => x + 1)
def primesUnder10 : List Nat := [2, 3, 5, 7]
#eval primesUnder10.length
#eval primesUnder10.head?
#eval primesUnder10.head!
#eval List.nil.head? (α := Nat)
#eval [].head? (α := Nat)
#eval ([] : List Nat).head?

#eval List.sum [2, 3]
#eval [2, 3].sum

#eval is_perfect 100
#eval perfect_numbers 0

-- exercises
-- exercise 1
def list_last_element {α : Type} (xs : List α) : Option α :=
  xs.reverse.head?
#eval list_last_element [1, 2, 3]
#eval list_last_element [1, 2, 3, 4, 5]

-- exercise 2
def List.findFirst? {α : Type} (xs : List α) (predicate : α -> Bool) : Option α :=
  match xs with
  | [] => none
  | x :: xs' => if predicate x then some x else findFirst? xs' predicate

#eval List.findFirst? [1, 2, 3] (fun x => x > 1)  -- some 2
#eval List.findFirst? [5, 3, 4] (fun x => x % 2 == 0)  -- some 4
#eval List.findFirst? [1, 3, 5] (fun x => x % 2 == 0)  -- none
#eval List.findFirst? [] (fun x => x > 1)  -- none
-- #eval List.findFirst? [] (fun x => x == x)
#eval List.findFirst? ([] : List Nat) (fun x => x == x)
#eval List.findFirst? ([] : List Nat) (fun x => x = x)


#print List

-- exercise 3

def Prod.swap {α β : Type} (pair : α × β) : β × α :=
  match pair with
  | (a, b) => (b, a)

#eval Prod.swap (1, 2)

-- def insert_everywhere  {α : Type} (x : α) (xs : List α) : List (List α) :=
--   match xs with
--   | [] => [[x]]
--   | y :: ys =>
--     let r := insert_everywhere x ys
--     [x :: xs] ++ (r.map (fun zs => y :: zs))

def insert_everywhere {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insert_everywhere x ys).map (fun zs => y :: zs)

#eval insert_everywhere 3 [1, 2]


def list_permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | y :: ys => ((list_permutations ys).map (fun zs => insert_everywhere y zs)).flatten

#eval list_permutations [1, 2, 3]


-- def f {α : Type} (xs: List α) : List (List α) :=
--   match xs with
--   | [] => [[]]
--   | y :: ys =>
--   let r := f ys
--   (r.map (fun zs => insert_everywhere y zs)).flatten
  -- insert_everywhere y (f ys)

#eval list_permutations [1, 2, 3]

-- exercise 4



def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | (n+1) => (n+1) * factorial n

#eval factorial 0
#eval factorial 1
#eval factorial 2
#eval factorial 3

theorem t : factorial 3 = 6 := by
  simp [factorial]

theorem t {α : Type} (xs : List α) :
  (list_permutations xs).length = factorial xs.length := by
  induction xs with
  | nil =>
    simp [list_permutations, factorial]
  | cons y ys ih =>
    simp [list_permutations, factorial, ih]
    linarith



theorem length_list_of_sublists {α : Type} (xs : List α) :
  (find_sublists xs).length = 2^(xs.length) := by
  induction xs with
  | nil =>
    simp [find_sublists]
  | cons y ys ih =>
    simp [find_sublists, List.length_append, List.length_map, Nat.pow_succ, ih]
    linarith





-------------------------------------

/--
function that, for every list L,
returns the list of exactly all the sublists of L
-/
def find_sublists {α : Type} (xs : List α) : List (List α) :=
  match xs with
  -- the empty list has one sublist, the empty list
  | [] => [[]]
  -- if the list is not empty,
  -- find the sublists of the tail of the list
  -- then concatenate the result with the result of mapping the sublists of the tail
  -- by adding the head to each sublist
  | y :: ys => (find_sublists ys) ++ (find_sublists ys).map (fun x => y :: x)

#eval find_sublists [1, 2, 3]

-- theorem length_list_of_subslists {α: Type} (xs : List α) :
--   (find_sublists xs).length = 2^(xs.length) :=
-- by
--   induction xs with
--   | nil =>
--     simp [find_sublists]
--   | cons y ys ih =>
--     simp [find_sublists, List.length_append, List.length_map, Nat.pow_succ, ih]
--     <;> linarith

-- theorem length_list_of_sublists {α : Type} (xs : List α) :
--   (find_sublists xs).length = 2^(xs.length) := by
--   induction xs with
--   | nil =>
--     -- Base case: xs = []
--     simp [find_sublists]  -- Simplifies to 1 = 2^0
--   | cons y ys ih =>
--     -- Inductive case: xs = y :: ys
--     simp [find_sublists, List.length_append, List.length_map, Nat.pow_succ, ih]
--     -- Combine lengths and use induction hypothesis
--     linarith  -- Confirm arithmetic holds (2 * 2^ys.length = 2^(ys.length + 1))


-- theorem length_list_of_sublists {α : Type} (xs : List α) :
--   (find_sublists xs).length = 2^(xs.length) := by
--   induction xs with
--   | nil =>
--     simp [find_sublists]
--   | cons y ys ih =>
--     simp [find_sublists, List.length_append, List.length_map, Nat.pow_succ, ih]
--     -- linarith


-- #check List.length_append
-- #check List.length_map
-- #check Nat.pow_succ
-- #check linarith
