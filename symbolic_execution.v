Require Import Ensembles. 
Require Import Arith PeanoNat.



Module ConcState.

Variable input : Type.
Variable state: Type.

Inductive input_list : Type :=
|EmptyList
|ConsList (i : input) (s : input_list).

Fixpoint list_size (l : input_list) : nat :=
match l with
|EmptyList => 0
|ConsList i s => S (list_size s)
end.

Inductive conc_state : Type :=
|EmptyState
|ConsState (i: input) (s: state).


(* conc_ex(A, input) returns ConcState that results from 
the concrete execution of ConcState A with an input  *)
Definition concrete_execution := Ensemble conc_state -> input -> Ensemble conc_state.

Axiom conc_ex : concrete_execution.

(*Definition concrete_execution_n := Ensemble conc_state -> input -> Ensemble conc_state.

Axiom conc_ex_n : concrete_execution_n.*)

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


(* get_phi returns abstract state *)
Definition get_sym_state  :=  sym_state -> Phi.
Axiom get_phi : get_sym_state.

(* get_pc returns the path constraint *)
Definition get_path_constraint := sym_state -> PC.
Axiom get_pc : get_path_constraint.

Definition s_e := sym_state -> sym_state.
Axiom sym_ex : s_e.



Definition uni := Phi -> PC -> Ensemble ConcState.conc_state.
Axiom concretize : uni.

Definition get_inp := PC -> ConcState.input.
Axiom get_input : get_inp.

Inductive SE_tree : Type :=
| leaf: SE_tree
| ConsNode: SE_tree -> sym_state -> SE_tree -> SE_tree.

Definition s_e_n := sym_state -> nat -> SE_tree.
Axiom sym_ex_n : s_e_n.


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



(*is_consecutive_in_order checks if A and B are consecutive in the tree list
and if A comes before B *)
Fixpoint is_consecutive_in_order (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  ((A = last_elem h) /\  (B = t)) 
  \/ (is_consecutive_in_order A B h)
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




Definition singleton (x : ConcState.conc_state) : Ensemble ConcState.conc_state :=
Singleton ConcState.conc_state x.

(*Axiom lem_1 : forall (conc1 conc2 : ConcState.conc_state) (inp1 : ConcState.input)
 (sym1: SymbolicExec.sym_state),
(conc_ex (singleton conc1) inp1 = (singleton conc2)) /\ (In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2) /\ 
(is_leaf_state (sym_ex_n sym1) sym2). *)

Axiom lem_1_n : forall (conc1 conc2 : ConcState.conc_state) (inp1 : ConcState.input_list)
 (sym1: SymbolicExec.sym_state) (n : nat),
(list_size inp1 = n)/\(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)) /\ (In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In  ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2) /\ (is_leaf_state (sym_ex_n sym1 n) sym2).



(*
Axiom lem_2 : forall (conc2 : ConcState.conc_state) (inp1 : ConcState.input)
 (sym1 sym2: SymbolicExec.sym_state),
(in_tree (sym_ex_with_branching sym1) sym2) /\ (In ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, 
(In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1) /\ 
((conc_ex (singleton conc1) inp1) = (singleton conc2)).*)

Axiom lem_2_n : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state) (n:nat),
(is_leaf_state (sym_ex_n sym1 n) sym2) /\ (In ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, exists inp1,
(list_size inp1 = n) /\
(In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1) /\ 
(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)).




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


Definition trees_connect (A B : SE_tree) : Prop :=
forall (x y : sym_state),
(is_leaf_state A x) /\ (is_leaf_state B y) ->
Included ConcState.conc_state 
(circle_op_2 x)
(circle_op_1 (root B) y).


Definition is_connected2 (tlist : SE_tree_list) : Prop :=
forall (A B : SE_tree),
 (size tlist) >= 2 ->
 (is_consecutive_in_order A B tlist) ->
  trees_connect A B. 

Theorem lem_1_n_circle_op_2 : forall (conc1 conc2 : ConcState.conc_state) (inp1 : ConcState.input_list)
 (sym1: SymbolicExec.sym_state) (n : nat),
(list_size inp1 = n)/\(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)) 
/\ (In ConcState.conc_state (circle_op_2 sym1) conc1)  ->
exists sym2, 
(In  ConcState.conc_state (circle_op_2 sym2) conc2) /\ (is_leaf_state (sym_ex_n sym1 n) sym2).
Proof. unfold circle_op_2. apply lem_1_n. Qed.


Theorem lem_2_n_circle_op_2 : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state) (n:nat),
(is_leaf_state (sym_ex_n sym1 n) sym2) /\ (In ConcState.conc_state (circle_op_2 sym2) conc2)  ->
exists conc1, exists inp1,
(list_size inp1 = n) /\
(In ConcState.conc_state (circle_op_2 sym1) conc1) /\ 
(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)).
Proof. unfold circle_op_2. apply lem_2_n. Qed.

Variable init_conc_states: Ensemble ConcState.conc_state.


Axiom base_case: 
forall s0 s : SE_tree,
is_connected (([ ] :: s0) :: s) ->
conc_ex
  (conc_ex init_conc_states
     (get_input (get_pc (root s0))))
  (get_input (get_pc (root s))) =
circle_op_2 (root s).

Axiom bc2: 
forall s0 s : SE_tree,
is_connected2 (([ ] :: s0) :: s) ->
forall c : sym_state,
is_leaf_state s0 c ->
conc_ex
  (conc_ex init_conc_states
     (get_input (get_pc (root s0))))
  (get_input (get_pc (c))) =
circle_op_2 (root s).

Axiom co_2_def:
forall (s0 : SE_tree) (s: sym_state),
is_leaf_state s0 s ->
conc_ex (circle_op_2 (root s0))
  (get_input (get_pc s)) =
(circle_op_2  s).

Axiom co_2_def2:
forall (A B : SE_tree),
trees_connect A B ->
forall c : sym_state,
  is_leaf_state A c ->
  conc_ex (circle_op_2 (root A)) (get_input (get_pc c)) =
  circle_op_2 (root B).


Theorem tlist_size: 
forall (tlist: SE_tree_list) (s: SE_tree),
size (tlist :: s) = S (size tlist).
Proof. intros. induction tlist.
-simpl;auto.
-simpl; auto. Qed.

Definition check_eq_prop (B : SE_tree) (c d : sym_state) : Prop :=
Included ConcState.conc_state (circle_op_2 c) (circle_op_1 (root B) d). 

(*Find leaf c of A such that circle_op_2(c) is subset of circle_op_1(B, d),
 where d is a leaf of B.*)

Definition fl := SE_tree -> sym_state.
Axiom find_leaf : fl.

Axiom Prop_3_req: forall (A B : SE_tree) (c : sym_state), 
(check_eq_prop B (find_leaf A) c ) = True.






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




Theorem etl_size2_modified:
forall (tlist : SE_tree_list) (s t : SE_tree),
(size tlist) = 0 ->
execute_tree_list ((tlist :: s) :: t) =
conc_ex (conc_ex init_conc_states (get_input (get_pc (root s)))) (get_input (get_pc  (root t))).
Proof. intros.
destruct tlist.
-simpl. auto.
-inversion H. Qed.




Variable ErrorStates: Ensemble ConcState.conc_state.



Variable tree_list : SymbolicExec.SE_tree_list.


Axiom tl_size: (size tree_list) >= 2.


Axiom property1 : 
Included ConcState.conc_state 
init_conc_states
(circle_op_1 (root(head tree_list)) (root (second_elem tree_list))).


(* Equivalent to, but different than property 2 in paper. *)
Axiom property2: (Intersection ConcState.conc_state (circle_op_2 (root (last_elem tree_list))) ErrorStates) 
<> Empty_set ConcState.conc_state.

Axiom property3: is_connected tree_list.

Axiom p3: is_connected2 tree_list.

Theorem cio_helper: 
forall (t : SE_tree_list) (A B s : SE_tree),
(is_consecutive_in_order A B t)
-> (is_consecutive_in_order A B (t::s)).
Proof. intros. 
destruct t.
-simpl;auto.
-simpl. simpl in H. right. assumption. Qed.

Axiom connected_elim2: 
forall (t : SE_tree_list) (s0 s : SE_tree),
is_connected2 ((t :: s0) :: s)->
is_connected2 (t :: s0).


Theorem connected_elim: 
forall (t : SE_tree_list) (s0 s : SE_tree),
is_connected ((t :: s0) :: s)->
is_connected (t :: s0).
Proof. intros.  
unfold is_connected in H.
destruct t.
-unfold is_connected. intros. inversion H0.
apply H.  
*simpl;auto.
*apply cio_helper. apply H1.
-unfold is_connected. intros. apply H.
*simpl;auto.
*apply cio_helper. apply H1. Qed.



Theorem connected_ends: 
forall s1 s0 s : SE_tree,
is_connected ((([] :: s1) :: s0) :: s) -> is_leaf_state s0 (root s).
Proof. intros. unfold is_connected in H. apply H. 
-simpl;auto.
-simpl;auto. Qed.

Axiom bc_helper2: 
forall s0 s : SE_tree,
is_connected2 (([ ] :: s0) :: s) ->
execute_tree_list  (([ ] :: s0) :: s) = 
conc_ex
  (conc_ex init_conc_states
     (get_input (get_pc (root s0))))
  (get_input (get_pc (root s))).

Theorem bc_helper: 
forall s0 s : SE_tree,
is_connected (([ ] :: s0) :: s) ->
execute_tree_list  (([ ] :: s0) :: s) = 
conc_ex
  (conc_ex init_conc_states
     (get_input (get_pc (root s0))))
  (get_input (get_pc (root s))).
Proof. intros. simpl; auto. Qed.

Theorem base_case_2 : forall (s s0 s1 : SE_tree),
is_connected ((([] :: s1) :: s0) :: s) ->
conc_ex (execute_tree_list (([] :: s1) :: s0))
  (get_input (get_pc (root s))) =
circle_op_2
  (root (last_elem ((([] :: s1) :: s0) :: s))).
Proof. intros. pose H as H1. apply connected_elim in H1.
rewrite bc_helper.
-rewrite base_case. simpl. rewrite co_2_def.
*auto.
*apply connected_ends in H. apply H.
*auto.
-auto. Qed.

(*Axiom bcbc : 
forall (s1 s0 : SE_tree) (c : sym_state),
is_leaf_state s1 c ->
execute_tree_list (([ ] :: s1) :: s0)
= conc_ex (conc_ex init_conc_states (get_input (get_pc (root htop)))) (get_input (get_pc  (root t)))*)
(*
Theorem bc22 : forall (s s0 s1 : SE_tree),
is_connected2 ((([] :: s1) :: s0) :: s) ->
forall (c : sym_state),
(is_leaf_state s0 c) ->
(conc_ex (execute_tree_list (([] :: s1) :: s0))
  (get_input (get_pc (c))) =
circle_op_2
  (root (last_elem ((([] :: s1) :: s0) :: s)))).*)
(*Proof. intros. pose H as H1. apply connected_elim2 in H1.
*)

pose bc2 as bc. rewrite bc_helper2.
*simpl. apply bc. Search "bc".

simpl. apply bc2.
rewrite bc_helper2.
- apply bc2.
*simpl. rewrite co_2_def2.
rewrite <- exists_elim. rewrite co_2_def2. split. auto.
*



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


Axiom connection2:
forall (t : SE_tree_list) (s s0 s1 s2 : SE_tree),
is_connected2 ((((t :: s2) :: s1) :: s0) :: s) ->
conc_ex
  (circle_op_2
     (root (last_elem (((t :: s2) :: s1) :: s0))))
  (get_input (get_pc (root s))) =
circle_op_2
  (root
     (last_elem ((((t :: s2) :: s1) :: s0) :: s))).


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

Theorem etl_con2 : 
forall t: SE_tree_list,
is_connected2 t /\ (size t) >= 2 -> 
execute_tree_list t = 
(circle_op_2 (root (last_elem t))).
Proof. intros. destruct H.
induction t. 
-inversion H0.
-destruct t.
*inversion H0. inversion H2.
*destruct t.
+rewrite etl_size2_modified. unfold last_elem.
++apply bc2. apply H.
++auto.
+destruct t.
++rewrite etl_size_gt2. 
+++apply bc22. assumption.
+++simpl;auto.
++rewrite etl_size_gt2.
+++ rewrite IHt. apply connection2.
assumption.
++++ apply connected_elim2 in H. assumption.
++++apply size_const_helper.
+++apply size_const_2_helper.
Qed.






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


Theorem etl2 : execute_tree_list tree_list = (circle_op_2 (root (last_elem tree_list))).
Proof. apply etl_con2. split.
-apply p3.
-apply tl_size. Qed.


Theorem sufficiency : 
(Intersection ConcState.conc_state
(execute_tree_list tree_list)  ErrorStates)
<> Empty_set ConcState.conc_state.
Proof. 
rewrite etl. apply property2. Qed.


End SERecurs.


