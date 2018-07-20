
Require Setoid.
Require Import List.
Require Import Sorting.Heap.

Module ConcState.
Variable conc_state : Set.


(* conc_ex(A) returns ConcState that results from 
the concrete execution of ConcState A  *)

Definition conc_ex (A:conc_state) : conc_state:=
match A with 
| conc_state => conc_state
end.

Inductive conc_state_subset : Set :=
| IsConc (a : conc_state).


End ConcState.

Import ConcState.

Module SymState.
(* Symbolic state contains abstract state 
and path constraint. *)


Variable Phi PC : Set.

Inductive sym_state : Set :=
|ConstructState (a : Phi) (p : PC).


(* get_phi returns abstract state *)
Definition get_phi (x : sym_state) : Phi :=
match x with
|ConstructState phi pc => phi
end.

(* get_pc returns the path constraint *)
Definition get_pc (x : sym_state) : PC :=
match x with
|ConstructState phi pc => pc
end.





(* sym_ex(A) returns an object
 in the equivalence class of SymState
 that results from 
the symbolic execution of an object
in the equivalence class of SymState A  *)
Definition sym_ex (A:sym_state) : sym_state:=
match A with 
| sym_state => sym_state
end.


(* unif(A) returns the set of concrete states
 represented by symbolic state A. *)
(* Not convinced that this is saying what I want it to. 
I think it's returning the entire set of conc states, not just a subset.*)
Definition unif (A:sym_state) : Set :=
match A with 
| sym_state => ConcState.conc_state_subset
end.


End SymState.

Import SymState. 

Module SETree.
(* is_leaf(T, n) returns true if
 n is a leaf in tree T. *)
(* is_root(T, n) returns true if
 n is a root in tree T. *)
(* get_root(T) returns the root of tree T. *)
(*Modified version of FSet RBT https://github.com/coq-contribs/fsets/blob/master/FSetRBT.v *)
Inductive SE_tree : Set :=
| leaf : SE_tree
| node : SE_tree -> SymState.sym_state -> SE_tree -> SE_tree.

Definition elt := SymState.sym_state.

(* Need concept of equivalence. *)

(*Inductive In_tree (x : elt) : SE_tree -> Prop :=
| IsRoot : 
  forall (l r : SE_tree)  (y : elt),
  X.eq x y -> In_tree x (node l y r)
| InLeft :
  forall (l r : tree) (y : elt),
  In_tree x l -> In_tree x (node l y r)
| InRight :
        forall (l r : SE_tree) (y : elt),
        In_tree x r -> In_tree x (node l y r).*)

End SETree.


 Import SETree. 

Module System.
(* System initializes with a defined set of
 initial configuration states, InitStates *)
Inductive init_conc_states : Set :=
| IsConc (a : ConcState.conc_state).

End System.

Import System. 



