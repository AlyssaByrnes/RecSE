Require Import Ensembles. 
Require Import Arith PeanoNat.



Module ConcState.

Variable input : Type.
Variable state: Type.





Inductive input_list : Type :=
|EmptyList
|ConsList (i : input) (s : input_list).

Fixpoint in_input_list (l : input_list) (i : input) : Prop :=
match l with
|EmptyList => False
|ConsList item i_list => (item = i) \/ (in_input_list i_list i)
end . 




(*Variable conc_state : Type.*)

Inductive conc_state : Type :=
|EmptyState
|ConsState (i: input) (s: state).


(* conc_ex(A, input) returns ConcState that results from 
the concrete execution of ConcState A with an input  *)
Definition concrete_execution := Ensemble conc_state -> input -> Ensemble conc_state.

Axiom conc_ex : concrete_execution.



Definition singleton (l : conc_state) : Ensemble conc_state :=
  Add conc_state (Empty_set conc_state) l.


Fixpoint conc_ex_input_list (states : Ensemble conc_state) (ilist : input_list) : Ensemble conc_state:=
match ilist with
|EmptyList => states
|ConsList inp list_last_elem => conc_ex_input_list (conc_ex states inp) list_last_elem
end.




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

Axiom concretize : uni.

Definition get_inp := PC -> ConcState.input.
Axiom get_input : get_inp.


Definition get_st := Phi -> ConcState.state.
Axiom get_state : get_st.

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

Fixpoint in_tree (tree: SE_tree) (state : sym_state) : Prop :=
match tree with
|leaf => False
|ConsNode l n r => 
(in_tree l state)\/
(n = state) \/
(in_tree r state)
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


Fixpoint sym_ex_n_with_branching (state : sym_state) (n:nat) : SE_tree :=
match n with
|0 => sym_ex_with_branching state
|S n' => ConsNode 
(sym_ex_n_with_branching (left_child (sym_ex_with_branching state)) n')
state
(sym_ex_n_with_branching (right_child (sym_ex_with_branching state)) n')
end.


Inductive SE_tree_list : Type :=
|nil: SE_tree_list
|cons:  SE_tree_list -> SE_tree -> SE_tree_list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).



Fixpoint head (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|nil :: h => h
|h :: t => head h
end.

Definition headlist (tlist : SE_tree_list) : SE_tree_list :=
match tlist with 
|nil => nil
|h :: t => h
end.

Fixpoint second_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => 
  match h with
|nil => leaf
|nil :: se => t
|tail :: se => second_elem tail
end
end.

Definition last_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => t
end.

Definition second_last_elem (tlist: SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|nil :: t => leaf
|h :: t => last_elem h
end.

(*Definition tail (tlist : SE_tree_list) : SE_tree_list :=
match tlist with
|nil => nil
|h::nil => nil
|h::t => t
end.*)

(*is_consecutive_in_order checks if A and B are consecutive in the tree list
and if A comes before B *)
Fixpoint is_consecutive_in_order (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  ((A = last_elem h) /\  (B = t)) 
  \/ (is_consecutive_in_order A B h)
end.


Fixpoint is_consecutive_in_order_2 (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  match h with
  |nil => False
  |newh :: newt => ((A = newt) /\  (B = t)) 
  \/ (is_consecutive_in_order A B h)
  end
end.


Fixpoint size (tlist : SE_tree_list) : nat :=
match tlist with
|nil => 0
|h :: t => S (size h)
end.
 

Definition is_connected  (tlist : SE_tree_list) : Prop :=
 forall (A B : SE_tree),
 (size tlist) >= 2 ->
 (is_consecutive_in_order A B tlist) ->
  is_leaf_state A (root B). 




Axiom is_connected_app: 
forall (tlist : SE_tree_list),
is_connected tlist ->
is_leaf_state (second_last_elem tlist) (root (last_elem tlist)).









End SymbolicExec.


Import SymbolicExec. 



Module SERecurs.

(* Takes as input symbolic state of root and pc of its leaf 
and returns all and only the concrete states that will take us down 
the path that leads to the leaf. *)
Definition circle_op_1 (sym sym_leaf : SymbolicExec.sym_state) : Ensemble ConcState.conc_state :=
concretize (get_phi sym) (get_pc sym_leaf).

(*Takes as input symbolic state of leaf state and pc of leaf state 
and returns concrete states that correspond *)
Definition circle_op_2 (sym : SymbolicExec.sym_state) : Ensemble ConcState.conc_state :=
concretize (get_phi sym) (get_pc sym).


Axiom circle_op_switch : forall (s0 s1: sym_state), 
conc_ex (circle_op_1 s1 s0) (get_input (get_pc s0))
= conc_ex (circle_op_2 s1) (get_input (get_pc s0)).



Variable init_conc_states: Ensemble ConcState.conc_state.





Theorem tlist_size: 
forall (tlist: SE_tree_list) (s: SE_tree),
size (tlist :: s) = S (size tlist).
Proof. intros. induction tlist.
-simpl;auto.
-simpl; auto. Qed.

Theorem tlist_size_geq_0: 
forall (tlist: SE_tree_list) (s: SE_tree),
size (tlist :: s) >= 0.
Proof. intros. induction tlist.
-simpl;auto.
-rewrite tlist_size in IHtlist. simpl; auto.
Qed. 

Theorem tlist_size_0:
forall (tlist: SE_tree_list) (s: SE_tree),
tlist = [] ->
size (tlist) = 0.
Proof. intros. induction tlist.
-simpl;auto.
-simpl; auto. inversion H. Qed.

Theorem tlist_size_1:
forall (tlist: SE_tree_list) (s: SE_tree),
size (tlist::s) = 1 ->
tlist = [].
Proof. intros.
induction tlist.
-auto.
-simpl in H. inversion H. Qed.


Fixpoint execute_tree_list (tlist : SE_tree_list)  : Ensemble ConcState.conc_state :=
match tlist with 
|nil => Singleton ConcState.conc_state EmptyState
|h :: t =>
  match h with
  |nil => Singleton ConcState.conc_state EmptyState
  |nil :: htop => conc_ex (conc_ex init_conc_states (get_input (get_pc (root htop)))) (get_input (get_pc  (root t)))
  |newhead :: htop => conc_ex (execute_tree_list h) (get_input (get_pc  (root t)))
  end
end.




Theorem etl_empty: 
forall tlist : SE_tree_list,
(size tlist) = 0 ->
execute_tree_list tlist = Singleton ConcState.conc_state EmptyState.
Proof. intros. induction tlist.
-simpl; auto.
-pose H as H1. rewrite tlist_size in H1. simpl in H1. 
pose tlist_size_geq_0 as z. simpl in H. pose gt_Sn_O. inversion H.
Qed.

Theorem etl_size_1: 
forall tlist : SE_tree_list,
(size tlist) = 1 ->
execute_tree_list tlist = Singleton ConcState.conc_state EmptyState.
Proof. intros. induction tlist.
-simpl; auto.
-apply tlist_size_1 in H. rewrite H. simpl;auto.
Qed.




Theorem etl_size2_modified:
forall (tlist : SE_tree_list) (s t : SE_tree),
(size tlist) = 0 ->
execute_tree_list ((tlist :: s) :: t) =
conc_ex (conc_ex init_conc_states (get_input (get_pc (root s)))) (get_input (get_pc  (root t))).
Proof. intros.
destruct tlist.
-simpl. auto.
-inversion H. Qed.


Theorem tlist_size_1_mod:
forall (s: SE_tree),
size ([ ] :: s) = 1.
Proof. intros. simpl;auto. Qed.



Theorem etl_size_gt1:
forall (tlist : SE_tree_list) (s t : SE_tree),
(size tlist) > 1 ->
execute_tree_list (tlist :: t) =
conc_ex 
(execute_tree_list tlist)
(get_input (get_pc  (root t))).
Proof. intros.
destruct tlist.
-inversion H.
-destruct tlist.
*pose tlist_size_1_mod. inversion H. inversion H1.
*simpl;auto. Qed.






Variable ErrorStates: Ensemble ConcState.conc_state.

(*Necessary?*)
Axiom error_include_empty: In conc_state ErrorStates EmptyState.



Variable tree_list : SymbolicExec.SE_tree_list.


Axiom tl_size: (size tree_list) >= 2.



(*Expand circle ops*)
Axiom property1 : 
Included ConcState.conc_state 
init_conc_states
(circle_op_1 (root(head tree_list)) (root (second_elem tree_list))).


(* Equivalent to, but different than property 2 in paper. *)
Axiom property2: (Intersection ConcState.conc_state (circle_op_2 (root (last_elem tree_list))) ErrorStates) 
<> Empty_set ConcState.conc_state.

Axiom property3: is_connected tree_list.



Axiom empt : [ ] = [ ] :: leaf. 


Theorem tlist_structure : forall t : SE_tree_list,
t = (headlist t)::(last_elem t).
Proof.
induction t.
-simpl. apply empt.
-simpl. auto. Qed.



Theorem tree_list_struct : 
tree_list = headlist tree_list :: last_elem tree_list.
Proof. apply tlist_structure. Qed.


(*Axiom cio : forall (tl tl2 : SE_tree_list) (a b : SE_tree),
tl2 = ((tl :: a ) :: b) ->
is_consecutive_in_order a b tl2.*)

Axiom base_case: 
forall s0 s : SE_tree,
is_connected (([ ] :: s0) :: s) ->
conc_ex
  (conc_ex init_conc_states
     (get_input (get_pc (root s0))))
  (get_input (get_pc (root s))) =
circle_op_2 (root s).


Axiom base_case_2 : forall (s s0 s1 : SE_tree),
is_connected ((([] :: s1) :: s0) :: s) ->
conc_ex (execute_tree_list (([] :: s1) :: s0))
  (get_input (get_pc (root s))) =
circle_op_2
  (root (last_elem ((([] :: s1) :: s0) :: s))).


Axiom co_2_def:
forall (s0 : SE_tree) (s: sym_state),
is_leaf_state s0 s ->
conc_ex (circle_op_2 (root s0))
  (get_input (get_pc s)) =
(circle_op_2  s).

Theorem etl_size_gt2:
forall (x : SE_tree_list) (y z : SE_tree),
(size ((x :: y) :: z)) > 2 ->
execute_tree_list ((x :: y) :: z) = 
conc_ex (execute_tree_list (x::y)) (get_input (get_pc  (root z))).
Proof. intros. induction x.
-simpl in H. inversion H. inversion H1. inversion H3.
-simpl;auto. Qed.


Theorem size_const_helper: forall (t : SE_tree_list) (s0 s1 s2 : SE_tree),
size (((t :: s2) :: s1) :: s0) >= 2.
Proof. intros.
induction t.
-simpl;auto.
-simpl; auto. Qed.

Theorem size_const_2_helper: forall (t : SE_tree_list) (s s0 s1 s2 : SE_tree),
size ((((t :: s2) :: s1) :: s0) :: s) > 2.
Proof. intros.
induction t.
-simpl;auto.
-simpl; auto. Qed.

Theorem size_const_3_helper: forall (t : SE_tree_list) (s0 s1 s2 s3 : SE_tree),
size ((((t :: s3) :: s2) :: s1) :: s0)  >= 2.
Proof. intros.
induction t.
-simpl;auto.
-simpl; auto. Qed.


Theorem cio_fundamental : 
forall (x : SE_tree_list) (y z : SE_tree),
  is_consecutive_in_order y z ((x::y)::z).
Proof. intros. simpl; auto. Qed.


Theorem connection:
forall (t : SE_tree_list) (s s0 s1 s2 : SE_tree),
is_connected ((((t :: s2) :: s1) :: s0) :: s) ->
conc_ex
  (circle_op_2
     (root (last_elem (((t :: s2) :: s1) :: s0))))
  (get_input (get_pc (root s))) =
circle_op_2
  (root
     (last_elem ((((t :: s2) :: s1) :: s0) :: s))).
Proof. intros. unfold last_elem. apply co_2_def. 
unfold is_connected in H. apply H.
-apply size_const_3_helper.
- apply cio_fundamental. Qed.



Axiom connected_elim: 
forall (t : SE_tree_list) (s0 s : SE_tree),
is_connected ((t :: s0) :: s)->
is_connected (t :: s0).




Theorem etl_con : 
forall t: SE_tree_list,
is_connected t /\ (size t) >= 2 -> 
execute_tree_list t = 
(circle_op_2 (root (last_elem t))).
Proof. intros. destruct H.
induction t. 
-inversion H0.
-destruct t.
*inversion H0. inversion H2.
*destruct t.
+rewrite etl_size2_modified. unfold last_elem.
++apply base_case. apply H.
++auto.
+destruct t.
++rewrite etl_size_gt2. 
+++apply base_case_2. assumption.
+++simpl;auto.
++rewrite etl_size_gt2.
+++ rewrite IHt. apply connection.
assumption.
++++ apply connected_elim in H. assumption.
++++apply size_const_helper.
+++apply size_const_2_helper.
Qed.






Theorem etl : execute_tree_list tree_list = (circle_op_2 (root (last_elem tree_list))).
Proof. apply etl_con. split.
-apply property3.
-apply tl_size.  Qed.



Theorem sufficiency : 
(Intersection ConcState.conc_state
(execute_tree_list tree_list)  ErrorStates)
<> Empty_set ConcState.conc_state.
Proof. 
rewrite etl. apply property2. Qed.


End SERecurs.


