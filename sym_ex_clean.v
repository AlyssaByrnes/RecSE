Module ConcState.

Inductive conc_state : Type :=
|concstate.


Inductive conc_state_set : Type :=
|Empty 
|Cons (x : conc_state) (s: conc_state_set).

(* conc_ex(A) returns ConcState that results from 
the concrete execution of ConcState A  *)
Definition concrete_execution := conc_state_set -> conc_state_set.

Axiom conc_ex : concrete_execution.


Fixpoint In (A:conc_state_set) (x:conc_state) : Prop := 
match A with 
|Empty => False
|Cons y s => (y=x) \/ In s x
end.


End ConcState.

Import ConcState.








Module System.
(* System initializes with a defined set of
 initial configuration states, InitStates *)

Definition conc_ex (A: ConcState.conc_state_set) : ConcState.conc_state_set := 
conc_ex A.

Fixpoint conc_ex_n (x: ConcState.conc_state) (n:nat) : ConcState.conc_state_set :=
match n with
|0 => Cons x Empty
|S n' => conc_ex (conc_ex_n x (n'))
end.

End System.

Import System. 

Module SymbolicExec.


(* Symbolic state contains abstract state 
and path constraint. *)


Variable Phi PC : Type.

Inductive sym_state: Type :=
|ConstructState (a : Phi) (p : PC)
|nilstate.



Definition up_pc := PC -> PC.
Axiom update_pc : up_pc.

Definition up_phi := Phi -> Phi.
Axiom update_phi: up_phi.

(* get_phi returns abstract state *)
Definition get_sym_state  :=  sym_state -> Phi.
Axiom get_phi : get_sym_state.

(* get_pc returns the path constraint *)
Definition get_path_constraint := sym_state -> PC.
Axiom get_pc : get_path_constraint.

Definition sym_execution := sym_state -> sym_state.
Axiom sym_ex : sym_execution.

Fixpoint sym_ex_n (x:sym_state) (n:nat) : sym_state :=
match n with
|0 => x
|S n' => sym_ex (sym_ex_n x (n'))
end.


Definition uni := sym_state -> ConcState.conc_state_set.
Axiom unif : uni.

(* is_leaf(T, n) returns true if
 n is a leaf in tree T. *)
(* is_root(T, n) returns true if
 n is a root in tree T. *)
(* get_root(T) returns the root of tree T. *)
(*Modified version of FSet RBT https://github.com/coq-contribs/fsets/blob/master/FSetRBT.v *)
Definition state := sym_state.

Inductive SE_tree : Type :=
| leaf: SE_tree
| ConsNode: SE_tree -> state -> SE_tree -> SE_tree.

Definition root (t : SE_tree) : sym_state :=
match t with 
|leaf => nilstate
|ConsNode l n r => n
end.

Fixpoint tree_height (t : SE_tree) : nat :=
match t with
|leaf => O
|ConsNode l n r  => S (max (tree_height l) (tree_height r))
end.


Fixpoint is_leaf_state (tree : SE_tree) (state : sym_state) : Prop :=
match tree with 
|leaf => False
|ConsNode l n r => 
  ((n = state) /\ (l = leaf))
  \/ (is_leaf_state l state)
  \/ (is_leaf_state r state)
end.


Definition sym_ex_with_branching (state : sym_state) : SE_tree :=
match state with 
|ConstructState phi pc => 
ConsNode 
(ConsNode leaf (ConstructState (update_phi phi ) (update_pc pc)) leaf)
 state
(ConsNode leaf (ConstructState (update_phi phi ) (update_pc pc)) leaf)
|nilstate => leaf
end.



Inductive SE_tree_list : Type :=
|nil: SE_tree_list
|cons: SE_tree -> SE_tree_list -> SE_tree_list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:SE_tree_list) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.




Fixpoint in_tree_list  (tlist : SE_tree_list) (x : SE_tree) : Prop :=
match tlist with 
|nil => False
|h :: t => (x = h) \/ (in_tree_list t x)
end.

Definition head (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => h
end.

Fixpoint tail (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => 
  match t with
  |nil => h
  |tailh :: tailt => tail t
  end
end.

(*is_consecutive_in_order checks if A and B are consecutive in the tree list
and if A comes before B *)
Fixpoint is_consecutive_in_order (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  ((A = h) /\  (B = (head t))) 
  \/ (is_consecutive_in_order A B t)
end.



Definition is_connected  (tlist : SE_tree_list) : Prop :=
 forall (A B : SE_tree), 
 (is_consecutive_in_order A B tlist) ->
  is_leaf_state A (root B). 




Definition is_leaf (T: SE_tree) (n : SymbolicExec.sym_state) : Prop := True.



(* SE Properties Go Here *)
Axiom lem_1 : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state),
(conc_ex (Cons conc1 Empty) = (Cons conc2 Empty)) /\ (In (unif sym1) conc1)  ->
exists sym2, 
(In (unif sym2) conc2) /\ sym_ex sym1 = sym2. 

Axiom lem_1_n : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state) (n : nat),
(conc_ex_n conc1 n = (Cons conc2 Empty)) /\ (In (unif sym1) conc1)  ->
exists sym2, 
(In (unif sym2) conc2) /\ sym_ex_n sym1 n = sym2.

Axiom lem_2 : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state),
(sym_ex sym1 = sym2) /\ (In (unif sym2) conc2)  ->
exists conc1, 
(In (unif sym1) conc1) /\ 
((conc_ex (Cons conc1 Empty)) = (Cons conc2 Empty)).

Axiom lem_2_n : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state) (n:nat),
(sym_ex_n sym1 n = sym2) /\ (In (unif sym2) conc2)  ->
exists conc1, 
(In (unif sym1) conc1) /\ 
(conc_ex_n conc1 n = (Cons conc2 Empty)).








End SymbolicExec.


Import SymbolicExec. 


Module SymbolicExecList. 



End SymbolicExecList.

Import SymbolicExecList.

Module SERecurs.


Definition circle_op_1 (sym : SymbolicExec.sym_state) : ConcState.conc_state_set :=
unif sym.

Definition circle_op_2 (sym : SymbolicExec.sym_state) : ConcState.conc_state_set :=
unif (sym_ex sym).

Fixpoint set_in_set (set1 set2 : ConcState.conc_state_set) : Prop :=
match set1 with 
|Empty => (set2 = Empty) \/ False
|Cons y s => (set1 = set2) \/ (set_in_set s set2)
end.

Variable init_conc_states: ConcState.conc_state_set.

(* 3 properties and sufficiency go here *)
Variable ErrorStates: ConcState.conc_state_set.

Variable tree_list : SymbolicExec.SE_tree_list.
(* NEED TREE LIST GENERATION *)


Definition is_connected (tlist : SymbolicExec.SE_tree_list) : Prop := True.


Axiom properties : 
(set_in_set init_conc_states  (circle_op_1 (root(head tree_list))))
/\ (set_in_set  ErrorStates (circle_op_2 (root(tail tree_list))))
/\ (is_connected tree_list). 

End SERecurs.


