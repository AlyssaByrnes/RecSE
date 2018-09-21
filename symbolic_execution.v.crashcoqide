Require Import Ensembles. 

Module ConcState.

Variable input : Type.


Inductive input_list : Type :=
|EmptyList
|ConsList (i : input) (s : input_list).

Fixpoint in_input_list (l : input_list) (i : input) : Prop :=
match l with
|EmptyList => False
|ConsList item i_list => (item = i) \/ (in_input_list i_list i)
end . 




Variable conc_state : Type.


(* conc_ex(A, input) returns ConcState that results from 
the concrete execution of ConcState A with an input  *)
Definition concrete_execution := Ensemble conc_state -> input -> Ensemble conc_state.

Axiom conc_ex : concrete_execution.


Definition singleton (l : conc_state) : Ensemble conc_state :=
  Add conc_state (Empty_set conc_state) l.





End ConcState.

Import ConcState.





Module SymbolicExec.


(* Symbolic state contains abstract state 
and path constraint. *)


Variable Phi PC : Type.

Inductive sym_state: Type :=
|ConstructState (a : Phi) (p : PC)
|nilstate.



Definition up_pc_l := PC -> PC.
Axiom update_pc_left : up_pc_l.

Definition up_pc_r := PC -> PC.
Axiom update_pc_right : up_pc_r.

Definition up_phi_l := Phi -> Phi.
Axiom update_phi_left: up_phi_l.

Definition up_phi_r := Phi -> Phi.
Axiom update_phi_right: up_phi_r.

(* get_phi returns abstract state *)
Definition get_sym_state  :=  sym_state -> Phi.
Axiom get_phi : get_sym_state.

(* get_pc returns the path constraint *)
Definition get_path_constraint := sym_state -> PC.
Axiom get_pc : get_path_constraint.


Definition uni := Phi -> PC -> Ensemble ConcState.conc_state.

Axiom unif : uni.

Definition get_inp := PC -> ConcState.input.
Axiom get_input : get_inp.


Inductive SE_tree : Type :=
| leaf: SE_tree
| ConsNode: SE_tree -> sym_state -> SE_tree -> SE_tree.

Definition root (t : SE_tree) : sym_state :=
match t with 
|leaf => nilstate
|ConsNode l n r => n
end.


Fixpoint is_leaf_state (tree : SE_tree) (state : sym_state) : Prop :=
match tree with 
|leaf => False
|ConsNode l n r => 
  ((n = state) /\ (l = leaf))
  \/ (is_leaf_state l state)
  \/ (is_leaf_state r state)
end.

Definition left_child (tree : SE_tree) : sym_state :=
match tree with 
|leaf => nilstate
|ConsNode l n r => root l
end.

Definition right_child (tree : SE_tree) : sym_state :=
match tree with 
|leaf => nilstate
|ConsNode l n r => root r
end.


Definition sym_ex_with_branching (state : sym_state) : SE_tree :=
match state with 
|ConstructState phi pc => 
ConsNode 
(ConsNode leaf (ConstructState (update_phi_left phi ) (update_pc_left pc)) leaf)
 state
(ConsNode leaf (ConstructState (update_phi_right phi ) (update_pc_right pc)) leaf)
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

Definition second_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with
|nil => leaf
|h :: t => (head t)
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

Inductive Sym_state_list : Type :=
|nil_list: Sym_state_list
|sscons: sym_state -> Sym_state_list -> Sym_state_list.





(*
(* SE Properties Go Here *)
Axiom lem_1 : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state),
(conc_ex (singleton conc1) = (singleton conc2)) /\ (In (unif (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In (unif (get_phi sym2) (get_pc sym2)) conc2) /\ sym_ex sym1 = sym2. 

Axiom lem_1_n : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state) (n : nat),
(conc_ex_n conc1 n = (Cons conc2 Empty)) /\ (In (unif (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In (unif (get_phi sym2) (get_pc sym2)) conc2) /\ sym_ex_n sym1 n = sym2.

Axiom lem_2 : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state),
(sym_ex sym1 = sym2) /\ (In (unif (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, 
(In (unif (get_phi sym1) (get_pc sym1)) conc1) /\ 
((conc_ex (Cons conc1 Empty)) = (Cons conc2 Empty)).

Axiom lem_2_n : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state) (n:nat),
(sym_ex_n sym1 n = sym2) /\ (In (unif (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, 
(In (unif (get_phi sym1) (get_pc sym1)) conc1) /\ 
(conc_ex_n conc1 n = (Cons conc2 Empty)).

*)






End SymbolicExec.


Import SymbolicExec. 



Module SERecurs.

(* Takes as input symbolic state of root and pc of its leaf 
and returns all and only the concrete states that will take us down 
the path that leads to the leaf. *)
Definition circle_op_1 (sym sym_leaf : SymbolicExec.sym_state) : Ensemble ConcState.conc_state :=
unif (get_phi sym) (get_pc sym_leaf).

(*Takes as input symbolic state of leaf state and pc of leaf state 
and returns concrete states that correspond *)
Definition circle_op_2 (sym : SymbolicExec.sym_state) : Ensemble ConcState.conc_state :=
unif (get_phi sym) (get_pc sym).




Variable init_conc_states: Ensemble ConcState.conc_state.

Fixpoint execute_tree_list (tlist : SE_tree_list)  (cs : Ensemble ConcState.conc_state)  : Ensemble ConcState.conc_state :=
match tlist with 
|nil => Empty_set ConcState.conc_state
|h :: t => 
  match t with
  |nil => conc_ex cs (get_input (get_pc (left_child h)))
  |thead :: ttail => 
    execute_tree_list 
    t 
    (conc_ex cs (get_input (get_pc (root (second_elem tlist)))))
  end
end.







Variable ErrorStates: Ensemble ConcState.conc_state.

Variable tree_list : SymbolicExec.SE_tree_list.


Axiom properties : 
(Included ConcState.conc_state 
init_conc_states
(circle_op_1 (root(head tree_list)) (root (second_elem tree_list))))
/\ (((Intersection ConcState.conc_state  ErrorStates (circle_op_2 (right_child (tail tree_list))) 
<> Empty_set ConcState.conc_state))
\/((Intersection ConcState.conc_state  ErrorStates (circle_op_2 (left_child (tail tree_list))) 
<> Empty_set ConcState.conc_state)))
/\ (is_connected tree_list). 



Theorem sufficiency : 
Included ConcState.conc_state
(execute_tree_list tree_list init_conc_states)  ErrorStates.
Proof. Abort.

End SERecurs.


