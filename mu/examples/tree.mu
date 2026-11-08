inductive Tree (A : Type) : Type
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A
def Tree.size {A : Type} (t : Tree A) : Nat :=
  Tree.rec (fun (_ : Tree A) => Nat) 0 (fun (l : Tree A) (x : A) (r : Tree A) (ihl : Nat) (ihr : Nat) => Nat.succ (ihl + ihr)) t
eval Tree.size (Tree.node (Tree.node Tree.leaf 1 Tree.leaf) 2 Tree.leaf)
