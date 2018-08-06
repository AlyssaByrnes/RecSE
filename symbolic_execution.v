
Require Setoid.
Require Import List.
Require Import Sorting.Heap.
Require Import Ensembles.


Module SymState.
(* Symbolic state contains abstract state 
and path constraint. *)


Variable Phi PC : Type.

Inductive sym_state : Type :=
|ConstructState (a : Phi) (p : PC)
|SymEx (x : sym_state).


(* get_phi returns abstract state *)
Fixpoint get_phi (x : sym_state) : Phi :=
match x with
|ConstructState phi pc => phi
|SymEx a => get_phi a
end.

(* get_pc returns the path constraint *)
Fixpoint get_pc (x : sym_state) : PC :=
match x with
|ConstructState phi pc => pc
|SymEx a => get_pc a
end.





(* sym_ex(A) returns an object
 in the equivalence class of SymState
 that results from 
the symbolic execution of an object
in the equivalence class of SymState A  *)
Fixpoint sym_ex (A:sym_state) : sym_state:=
match A with 
| ConstructState phi pc => SymEx A
| SymEx a => sym_ex a
end.


Fixpoint sym_ex_n (x:sym_state) (n:nat) : sym_state :=
match n with
|0 => x
|S n' => sym_ex (sym_ex_n x (n'))
end.


(* unif(A) returns the set of concrete states
 represented by symbolic state A. *)
(* Not convinced that this is saying what I want it to. 
I think it's returning the entire set of conc states, not just a subset.*)
(*Definition unif (A:sym_state) : ConcState.conc_state_set :=
match A with 
| sym_state => ConcState.conc_state_set
end.*)


End SymState.

Import SymState. 

Module ConcState.
(*Variable conc_state : Type.*)

Inductive conc_state : Type :=
|concstate
|NextState (x: conc_state).

Inductive conc_state_set : Set :=
|Empty 
|Cons (x : conc_state) (s: conc_state_set).

Variable fillerset : conc_state_set. 

Definition unif (x : SymState.sym_state) : conc_state_set := fillerset. 


(*Definition conc_state_set := conc_state -> Prop.*)

Fixpoint In (A:conc_state_set) (x:conc_state) : Prop := 
match A with 
|Empty => False
|Cons y s => (y=x) \/ In s x
end.

(*Definition Included (B C:conc_state_set) : Prop := forall x:conc_state, In B x -> In C x.

Inductive Empty_set : conc_state_set :=.*)


(* conc_ex(A) returns ConcState that results from 
the concrete execution of ConcState A  *)










End ConcState.

Import ConcState.



Module System.
(* System initializes with a defined set of
 initial configuration states, InitStates *)
(*Inductive init_conc_states : Set :=
| IsConc (a : ConcState.conc_state).*)


Definition conc_ex (A: ConcState.conc_state) : ConcState.conc_state := 
match A with
|concstate => NextState A
|NextState x => NextState (NextState x)
end.

Fixpoint conc_ex_n (x: ConcState.conc_state) (n:nat) : ConcState.conc_state :=
match n with
|0 => x
|S n' => conc_ex (conc_ex_n x (n'))
end.

End System.

Import System. 

Module SETree.
(* is_leaf(T, n) returns true if
 n is a leaf in tree T. *)
(* is_root(T, n) returns true if
 n is a root in tree T. *)
(* get_root(T) returns the root of tree T. *)
(*Modified version of FSet RBT https://github.com/coq-contribs/fsets/blob/master/FSetRBT.v *)


Inductive SE_tree : Type :=
|root.



Inductive SE_tree_list : Set :=
|EmptyList
|ConsList (x : SE_tree) (s: SE_tree_list).

Fixpoint in_tree_list  (tlist : SE_tree_list) (t : SETree.SE_tree) : Prop :=
match tlist with 
|EmptyList => False
|ConsList x s => (x = t) \/ (in_tree_list s x)
end.




Definition is_leaf (T: SE_tree) (n : SymState.sym_state) : Prop := True.

Definition is_root (T: SE_tree) (n : SymState.sym_state) : Prop := True.

Definition get_root (T: SE_tree) : SymState.sym_state. Abort.


(* SE Properties Go Here *)
Axiom lem_1 : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymState.sym_state),
(conc_ex conc1 = conc2) /\ (In (unif sym1) conc1)  ->
exists sym2, 
(In (unif sym2) conc2) /\ sym_ex sym1 = sym2. 

Axiom lem_1_n : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymState.sym_state) (n : nat),
(conc_ex_n conc1 n = conc2) /\ (In (unif sym1) conc1)  ->
exists sym2, 
(In (unif sym2) conc2) /\ sym_ex_n sym1 n = sym2.

Axiom lem_2 : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymState.sym_state),
(sym_ex sym1 = sym2) /\ (In (unif sym2) conc2)  ->
exists conc1, 
(In (unif sym1) conc1) /\ 
(conc_ex conc1 = conc2).

Axiom lem_2_n : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymState.sym_state) (n:nat),
(sym_ex_n sym1 n = sym2) /\ (In (unif sym2) conc2)  ->
exists conc1, 
(In (unif sym1) conc1) /\ 
(conc_ex_n conc1 n = conc2).








End SETree.


Import SETree. 


Module SETreeList. 



End SETreeList.

Import SETreeList.

Module SERecurs.


Definition circle_op_1 (sym : SymState.sym_state) : ConcState.conc_state_set :=
unif sym.

Definition circle_op_2 (sym : SymState.sym_state) : ConcState.conc_state_set :=
unif (sym_ex sym).

Fixpoint set_in_set (set1 set2 : ConcState.conc_state_set) : Prop :=
match set1 with 
|Empty => (set2 = Empty) \/ False
|Cons y s => (set1 = set2) \/ (set_in_set s set2)
end.

Variable init_conc_states: ConcState.conc_state_set.

(* 3 properties and sufficiency go here *)
Variable ErrorStates: ConcState.conc_state_set.

Variable tree_list : SETree.SE_tree_list.
(* NEED TREE LIST GENERATION *)


Definition is_connected (tlist : SETree.SE_tree_list) : Prop := True.


Axiom properties : forall (e : SETree.SE_tree), 
in_tree_list tree_list e -> 
exists n,
(SETree.is_leaf e n)
/\(set_in_set init_conc_states  (circle_op_1 n))
/\ (set_in_set  ErrorStates (circle_op_2 n))
/\ (is_connected tree_list). 

End SERecurs.


