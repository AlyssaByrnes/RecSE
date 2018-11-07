Require Import Ensembles. 
Require Import Arith.

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
(*Notation "[ x ; .. ; y ]" := (cons y .. (cons x nil) ..).*)



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

Fixpoint last_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: leaf => last_elem h
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
|h :: leaf => size h
|h :: t => S (size h)
end.


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
(list_size inp1 = n)/\(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)) 
/\ (In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In  ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2) 
/\ (is_leaf_state (sym_ex_n sym1 n) sym2).



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


Axiom sym_ex_c_o_2 : 
forall (t : SE_tree) (s : sym_state),
is_leaf_state t s ->
conc_ex (circle_op_2 (root t)) (get_input(get_pc s)) 
= circle_op_2 s.


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

Variable init_conc_state: ConcState.conc_state.
Variable Error_States : Ensemble ConcState.conc_state.


Definition check_eq_prop (B : SE_tree) (c d : sym_state) : Prop :=
Included ConcState.conc_state (circle_op_2 c) (circle_op_1 (root B) d). 

(*Find leaf c of A such that circle_op_2(c) is subset of circle_op_1(B, d),
 where d is a leaf of B.*)





Axiom Prop_3 : forall (A B : SE_tree) (tlist  : SE_tree_list),
is_consecutive_in_order A B tlist ->
forall (x y : sym_state),
(is_leaf_state A x) /\ (is_leaf_state B y) ->
Included ConcState.conc_state 
(circle_op_2 x)
(circle_op_1 (root B) y).

Theorem Prop_3_short: 
forall (A B : SE_tree) (tlist  : SE_tree_list),
is_consecutive_in_order A B tlist ->
(trees_connect A B).
Proof. unfold trees_connect. apply Prop_3. Qed.

Definition fl := SE_tree -> sym_state.
Axiom find_leaf : fl.

Axiom find_leaf_returns_leaf :
forall t : SE_tree,
is_leaf_state t (find_leaf t).

Axiom Prop_3_req: 
(*This axiom defines the find_leaf method*)
forall (A B : SE_tree) (c : sym_state), 
trees_connect A B ->
((check_eq_prop B (find_leaf A) c ) = True).


Definition s_1_etl_leaf := SE_tree -> sym_state.
Axiom size_1_etl_leaf : s_1_etl_leaf.



Axiom Prop_1: 
(*size_1_etl_leaf is defined within property 1*)
forall (t : SE_tree_list),
(size t) = 1 ->
In ConcState.conc_state
(circle_op_1 (root (last_elem t)) (size_1_etl_leaf (last_elem t))) 
init_conc_state.



(*Definition l_e_etl_leaf := SE_tree -> sym_state.
Axiom last_elem_etl_leaf : l_e_etl_leaf.*)


Axiom Prop_2: 
(*last_elem_etl_leaf is defined within property 2*)
forall (t : SE_tree_list),
Intersection ConcState.conc_state
(circle_op_2 (find_leaf (last_elem t)))
Error_States
<> Empty_set ConcState.conc_state.

(*Fixpoint execute_tree_list_rec (tlist : SE_tree_list)  : Ensemble ConcState.conc_state  :=
match tlist with
|nil => singleton EmptyState
|nil :: t => conc_ex (singleton init_conc_state) (get_input (get_pc (size_1_etl_leaf t)))
|h :: t => conc_ex (execute_tree_list_rec h) (get_input (get_pc (find_leaf t)))
end.*)

Fixpoint execute_tree_list (tlist : SE_tree_list) : Ensemble ConcState.conc_state :=
match tlist with
|nil => singleton EmptyState
|nil :: leaf => singleton EmptyState
|nil :: t => conc_ex (singleton init_conc_state) (get_input (get_pc (size_1_etl_leaf t)))
|h::leaf => execute_tree_list h
|h::t => conc_ex (execute_tree_list h) (get_input(get_pc(find_leaf t)))
end.


Axiom etl_1_step:
forall (t : SE_tree_list) (A B : SE_tree),
trees_connect A B ->
execute_tree_list ((t::A)::B)
= conc_ex (execute_tree_list (t::A)) (get_input(get_pc(find_leaf B))).


(*Variable tree_list : SE_tree_list.*)

(*Theorem etl : 
forall tlist : SE_tree_list,
(size tlist) > 1 ->
execute_tree_list tlist = circle_op_2 (last_elem_etl_leaf (last_elem tlist)).
Proof. intros.*)

Axiom etl_base: 
forall s : SE_tree,
conc_ex (singleton init_conc_state)
  (get_input (get_pc (size_1_etl_leaf s))) =
circle_op_1 (root s) (size_1_etl_leaf s).

Axiom circle_op_1_nil: 
singleton EmptyState =
circle_op_1 nilstate (size_1_etl_leaf leaf).

Axiom circle_op_2_nil: 
singleton EmptyState =
circle_op_2 (find_leaf leaf).


Theorem last_elem_property:
forall (x: SE_tree_list) (s: SE_tree),
x <> nil /\ s <> leaf ->
(last_elem (x::s)) = s.
Proof. intros. destruct s. 
-inversion H. contradiction.
-simpl;auto. Qed.

Theorem last_elem_property_leaf:
forall (x: SE_tree_list),
x <> nil  ->
(last_elem (x::leaf)) = (last_elem x).
Proof. intros. simpl;auto. Qed.


Axiom size_property_leaf:
forall (x: SE_tree_list),
(size (x::leaf)) = (size x).

Axiom non_empty: 
forall (x: SE_tree_list) (s0 : SE_tree),
x :: s0 <> [ ].

Axiom non_empty_2:
forall (x: SE_tree_list),
(size x) = 1 -> x <> [ ].


Theorem etl_property_leaf:
forall (x: SE_tree_list),
x <> nil  ->
(execute_tree_list (x::leaf)) = (execute_tree_list x).
Proof. intros. 
destruct x.
-contradiction.
- simpl;auto. Qed.

Theorem succ_basic: 
forall x : nat,
S (x + 1) = (S x) + 1.
Proof. auto. Qed.

Theorem S_x:
forall x : nat,
x + 1 = S x.
Proof. intros. induction x.
simpl;auto. rewrite <- succ_basic. rewrite IHx. auto. Qed.

Theorem size_elim : 
forall (s : SE_tree_list) (s0: SE_tree),
s0 <> leaf ->
size (s :: s0) = (size (s)) + 1.
Proof. intros. 
destruct s0.
-contradiction.
-simpl. rewrite S_x. auto. Qed.

Axiom c_o_1_base_case: 
forall x: SE_tree,
 conc_ex (singleton init_conc_state)
  (get_input
     (get_pc
        (size_1_etl_leaf
           x))) =
circle_op_1 (root x)
  (size_1_etl_leaf x).

(*Theorem size_elim_2 : 
forall (s : SE_tree_list) (s0 s1: SE_tree),
s1 <> leaf ->
(size ((s :: s0) :: s1)) = (size (s::s0)) + 1.
Proof. intros. 
destruct s1.
-contradiction.
-simpl. rewrite S_x. auto. Qed.*)

Axiom nat_plus_1:
forall x : nat,
x + 1 = 1 ->
x = 0.

Axiom size_0:
forall tlist : SE_tree_list,
(size tlist) = 0 ->
tlist = [].



Axiom size_1:
forall (tlist : SE_tree_list) (s : SE_tree),
size (tlist :: s) = 1 ->
tlist = [].




Theorem etl_size_1 :
forall tlist : SE_tree_list,
(size tlist) = 1 ->
execute_tree_list tlist = (circle_op_1 (root (last_elem tlist)) (size_1_etl_leaf (last_elem tlist))).
Proof. intros. 
induction tlist.
-inversion H.
-pose H as H1. apply size_1 in H1. rewrite H1.  destruct s.
*simpl in H. apply non_empty_2 in H. contradiction.
*simpl. apply c_o_1_base_case. Qed.

(*Theorem etl_size_n :
forall tlist : SE_tree_list,
(size tlist) > 0 ->
execute_tree_list tlist = (circle_op_1 (root (last_elem tlist)) (size_1_etl_leaf (last_elem tlist))).
*)



(*
Axiom size_base_case:
forall (s0 : SE_tree),
size ([]::s0) = 1.

Axiom size_base_case_0:
forall (s : SE_tree_list),
size s >= 0.*)

Theorem succ: 
forall x:nat,
x > 0 -> S x > 0.
Proof. auto. Qed.

Theorem successor:
forall x:nat,
S x > 0 -> S( S x) > 0.
Proof. auto. Qed.

(*Theorem size_base_case:
forall (s : SE_tree_list) (s0 : SE_tree),
size (s  :: s0) > 0.
Proof. intros.
induction s.
-destruct s0.
*simpl;auto.
-simpl. simpl in IHs. apply successor. apply IHs. Qed.*)





(*Axiom succ_minus : 
forall x : nat,
x = (S x) - 1.*)

Theorem sub_1_gt :
forall x : nat, 
x > 0 ->
x + 1 > 1.
Proof. intros. rewrite S_x. apply le_lt_n_Sm. 
apply lt_le_S in H. auto. Qed.

 



Axiom etl_size_1_mod: forall tlist : SE_tree_list,
   size tlist = 1 ->
   execute_tree_list tlist =
   circle_op_2 (find_leaf (last_elem tlist)).

(*Theorem size_base_case2:
forall (s : SE_tree_list) (s0 s1 : SE_tree),
size ((s :: s1) :: s0) > 1.
Proof. intros. pose size_base_case as H. 
rewrite size_elim.  apply sub_1_gt.  apply H.
Qed. *)

Axiom not_leaf: forall (s1 s3 : SE_tree) (s2 : sym_state),
(ConsNode s1 s2 s3) <> leaf.

Theorem etl:
forall tree_list : SE_tree_list,
size tree_list >= 1 ->
execute_tree_list tree_list =
(circle_op_2 (find_leaf (last_elem tree_list))).
Proof. intros. induction tree_list.
-simpl. apply circle_op_2_nil.
-induction tree_list.
*destruct s.
** simpl in H. inversion H.
**apply etl_size_1_mod. rewrite size_elim. simpl;auto. apply not_leaf.
*rewrite etl_1_step. rewrite IHtree_list. rewrite last_elem_property. rewrite last_elem_property. 
pose sym_ex_c_o_2. simpl.
**rewrite etl_1_step. apply IHtree_list0.

pose etl_1_step.

Theorem Sufficiency: 
forall (tree_list : SE_tree_list),
(size tree_list >= 1) ->
(Intersection ConcState.conc_state
(execute_tree_list tree_list)  Error_States)
<> Empty_set ConcState.conc_state.
Proof. intros. rewrite etl. apply Prop_2. auto. Qed.
