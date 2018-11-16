Require Import Ensembles. 
Require Import Setoid.

Module ConcState.

Variable input : Type.
Variable state: Type.

Inductive conc_state : Type :=
|EmptyState
|ConsState (i: input) (s: state).

Definition concrete_execution := conc_state -> input -> conc_state.
Axiom conc_ex : concrete_execution.

End ConcState.
Import ConcState.

Module SymbolicExec.

Variable Phi PC : Type.

Inductive sym_state: Type :=
|ConstructState (a : Phi) (p : PC)
|nilstate.


(*** SYM STATE STRUCTURE ***)

(* get_phi returns abstract state *)
Definition get_sym_state  :=  sym_state -> Phi.
Axiom get_phi : get_sym_state.

(* get_pc returns the path constraint *)
Definition get_path_constraint := sym_state -> PC.
Axiom get_pc : get_path_constraint.

Definition conc := Phi -> PC -> Ensemble ConcState.conc_state.
Axiom concretize : conc.

Definition get_inp := PC -> ConcState.input.
Axiom get_input : get_inp.


(*** SYM EX TREE STRUCTURE ***)
Inductive SE_tree : Type :=
| leaf: SE_tree
| ConsNode: SE_tree -> sym_state -> SE_tree -> SE_tree.

Axiom non_empty_tree : 
forall (b c : SE_tree) (a : sym_state),
 (ConsNode b a c) <> leaf.

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


(*** TREE LIST STRUCTURE ***)
Inductive SE_tree_list : Type :=
|nil: SE_tree_list
|cons:  SE_tree_list -> SE_tree -> SE_tree_list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.

Fixpoint in_list (t : SE_tree_list) (s : SE_tree) : Prop :=
match t with
|nil => False
|h :: tl => (tl = s) \/ (in_list h s)
end.

Axiom tree_list_requirement:
forall (t t' : SE_tree_list) (s : SE_tree),
t = t'::s -> s <> leaf.

Axiom tree_list_requirement':
forall (t : SE_tree_list) (s : SE_tree),
in_list t s -> s <> leaf.


Fixpoint first_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|nil :: h => h
|h :: t => first_elem h
end.

Fixpoint last_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: leaf => last_elem h
|h :: t => t
end.

Fixpoint second_last_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: leaf => second_last_elem h
|h :: t => last_elem h
end.

Axiom s_l_e_helper:
forall (t : SE_tree_list) (s : SE_tree),
s <> leaf ->
second_last_elem (t :: s) = last_elem t.

Axiom s_l_e_helper_2:
forall (t : SE_tree_list) (s : SE_tree),
s <> leaf ->
last_elem t = second_last_elem (t :: s).

Axiom s_l_e_helper_3:
forall (A B : SE_tree) (t: SE_tree_list),
second_last_elem ((t :: A) :: (last_elem ((t :: A) :: B)))
= last_elem (t :: A).

Fixpoint size (tlist : SE_tree_list) : nat :=
match tlist with
|nil => 0
|h :: leaf => size h
|h :: t => S (size h)
end.

(*** SET OPERATION SHORT HANDS ***)
Definition singleton (x : ConcState.conc_state) : Ensemble ConcState.conc_state :=
Singleton ConcState.conc_state x.

Definition is_subset (x y : Ensemble ConcState.conc_state) : Prop :=
Included ConcState.conc_state x y.

Definition is_element_of (y : Ensemble ConcState.conc_state) (x : ConcState.conc_state) : Prop :=
In ConcState.conc_state y x.

Definition empty_set := Empty_set ConcState.conc_state.

Definition intersection (x y : Ensemble ConcState.conc_state) : Ensemble ConcState.conc_state :=
Intersection ConcState.conc_state x y.

End SymbolicExec.
Import SymbolicExec. 

Module SERecurs.

Variable init_conc_state: ConcState.conc_state.
Variable Error_States : Ensemble ConcState.conc_state.

Definition fl := SE_tree -> sym_state.
Axiom find_leaf : fl.

(*** CIRCLE OPERATIONS ***)
(* Takes as input symbolic state of root and pc of its leaf 
and returns all and only the concrete states that will take us down 
the path that leads to the leaf. *)
Definition c_o_1 := SymbolicExec.sym_state -> SymbolicExec.sym_state -> Ensemble ConcState.conc_state.
Axiom circle_op_1 : c_o_1.

Definition c_o_2 := SymbolicExec.sym_state -> Ensemble ConcState.conc_state.
Axiom circle_op_2 : c_o_2.

Axiom circle_op_property : 
forall (t : SE_tree),
(concretize (get_phi (find_leaf t)) (get_pc (find_leaf t))) 
= circle_op_2 (find_leaf t).

Axiom circle_op_property_2: 
forall (t : SE_tree) (x : conc_state),
is_element_of 
(circle_op_1 (root t) (find_leaf t)) x 
->
is_element_of
(circle_op_2 (find_leaf t))
(conc_ex x
(get_input (get_pc (find_leaf t)))).

Axiom circle_op_property_3:
(* Used to prove Property 3' *)
forall (s : SE_tree),
s <> leaf ->
circle_op_2 (find_leaf s) <> empty_set.

(*** PROPERTIES 1-3 ***)
Definition trees_connect (A B : SE_tree) : Prop :=
Included ConcState.conc_state 
(circle_op_2 (find_leaf A))
(circle_op_1 (root B) (find_leaf B)).

Definition is_connected (tlist : SE_tree_list) : Prop :=
forall (A : SE_tree), 
last_elem tlist = A ->
trees_connect (second_last_elem tlist) A.

Definition is_connected'(t : SE_tree_list) : Prop :=
forall (A : SE_tree), 
last_elem t = A ->
(circle_op_2 (find_leaf (second_last_elem t))) <> empty_set.

Axiom Prop1 : 
forall t : SE_tree_list,
(size t = 1) ->
is_element_of 
(circle_op_1 (root (last_elem t)) 
(find_leaf (last_elem t))) init_conc_state.

Axiom Prop2 : 
forall t : SE_tree_list,
intersection 
(circle_op_2 (find_leaf (last_elem t)))
Error_States 
<> empty_set.

Axiom Prop2':
forall t : SE_tree_list,
is_subset
(circle_op_2 (find_leaf (last_elem t)))
Error_States.

Axiom Prop3 : 
forall (t : SE_tree_list),
is_connected t.

Axiom Prop3':
forall (t : SE_tree_list),
is_connected' t.





(*** SUFFICIENCY ***)
Fixpoint execute_tree_list (tlist : SE_tree_list) : ConcState.conc_state :=
match tlist with
|nil => EmptyState
|nil :: leaf => EmptyState
|nil :: t => conc_ex (init_conc_state) (get_input (get_pc (find_leaf t)))
|h::leaf => execute_tree_list h
|h::t => conc_ex (execute_tree_list h) (get_input(get_pc(find_leaf t)))
end.

Theorem etl_1_step:
forall (t : SE_tree_list) (s : SE_tree),
(s<>leaf)/\ (size t > 0)->
execute_tree_list (t :: s) = conc_ex (execute_tree_list t) (get_input(get_pc(find_leaf s))).
Proof. intros.
induction s.
-destruct H. contradiction H. auto.
-induction t.
*destruct H. simpl in H0. inversion H0.
*simpl. auto.
Qed.

Axiom etl_size_1:
forall t : SE_tree_list,
size t = 1 
-> execute_tree_list t = conc_ex (init_conc_state) (get_input (get_pc (find_leaf (last_elem t)))). 


Axiom set_property_1:
forall (A : ConcState.conc_state) (B C : Ensemble ConcState.conc_state),
(is_element_of B A)
/\ (is_subset B C)
/\ (intersection B C <> empty_set)
-> (is_element_of C A).

Axiom set_property_2:
forall (A : ConcState.conc_state) (B C : Ensemble ConcState.conc_state) (i : ConcState.input),
((is_element_of B A)
/\
(forall (x : ConcState.conc_state),
is_element_of B x
-> is_element_of C (conc_ex x i))
/\
(C <> empty_set))
-> is_element_of C (conc_ex A i).

Axiom set_property_3:
forall (A B : Ensemble ConcState.conc_state) (C : ConcState.conc_state),
is_subset A B /\ is_element_of A C
-> is_element_of B C.

Theorem P1_and_circle_op_prop:
forall (t : SE_tree_list) (i: ConcState.input),
((is_element_of 
  (circle_op_1 (root (last_elem t)) (find_leaf (last_elem t))) 
  init_conc_state)
/\
(forall (x : ConcState.conc_state),
is_element_of 
  (circle_op_1 (root (last_elem t)) (find_leaf (last_elem t))) x
-> is_element_of (circle_op_2(find_leaf (last_elem t))) (conc_ex x i))
/\
((circle_op_2(find_leaf (last_elem t))) <> empty_set))
-> is_element_of (circle_op_2(find_leaf (last_elem t))) (conc_ex init_conc_state i).
Proof. intros. apply set_property_2 in H. apply H. Qed.

Theorem P1_and_circle_op_prop_ind_step:
forall (t : SE_tree_list) (i: ConcState.input) (s : SE_tree),
((is_element_of 
  (circle_op_1 (root (last_elem (t::s))) (find_leaf (last_elem (t::s)))) 
  (execute_tree_list t))
/\
(forall (x : ConcState.conc_state),
is_element_of 
  (circle_op_1 (root (last_elem (t::s))) (find_leaf (last_elem (t::s)))) x
-> is_element_of (circle_op_2(find_leaf (last_elem (t::s)))) (conc_ex x i))
/\
((circle_op_2(find_leaf (last_elem (t::s)))) <> empty_set))
-> is_element_of (circle_op_2(find_leaf (last_elem (t::s)))) 
(conc_ex (execute_tree_list t) i).
Proof. intros. apply set_property_2 in H. apply H. Qed.

Theorem P3_and_IH:
forall (t: SE_tree_list) (A : SE_tree),
is_subset
(circle_op_2 (find_leaf (second_last_elem (t::A))))
(circle_op_1 (root A) (find_leaf A))
/\
is_element_of
        (circle_op_2
           (find_leaf (second_last_elem (t::A))))
        (execute_tree_list t)
->
is_element_of
(circle_op_1 (root A) (find_leaf A))
(execute_tree_list t).
Proof. intros. apply set_property_3 in H. apply H. Qed.

Theorem P2_and_etl_imp:
forall (t : SE_tree_list),
(is_element_of 
(circle_op_2 (find_leaf (last_elem t)))
(execute_tree_list t))
/\
(is_subset 
(circle_op_2 (find_leaf (last_elem t)))
Error_States)
/\
((intersection
(circle_op_2 (find_leaf (last_elem t)))
Error_States)
<> empty_set
)
->
is_element_of 
Error_States
(execute_tree_list t).
Proof. intros. apply set_property_1 in H. apply H. Qed.

Theorem P2_and_etl_imp_ind_step:
forall (t : SE_tree_list),
(is_element_of 
(circle_op_2 (find_leaf (last_elem t)))
(execute_tree_list t))
/\
(is_subset 
(circle_op_2 (find_leaf (last_elem t)))
 (circle_op_1 (root(second_last_elem t)) (find_leaf (second_last_elem t))))
/\
((intersection
(circle_op_2 (find_leaf (last_elem t)))
 (circle_op_1 (root(second_last_elem t)) (find_leaf (second_last_elem t))))
<> empty_set
)
->
is_element_of
 (circle_op_1  (root(second_last_elem t)) (find_leaf (second_last_elem t)))
(execute_tree_list t).
Proof. intros. apply set_property_1 in H. apply H. Qed.



Axiom etl:
forall t : SE_tree_list,
size t > 0 /\ is_connected t /\ is_connected' t ->
is_element_of 
  (circle_op_2(find_leaf (last_elem t))) 
  (execute_tree_list t).

Theorem sufficiency: 
forall t : SE_tree_list,
size t > 0 ->
is_element_of Error_States (execute_tree_list t).
Proof. intros. 
apply P2_and_etl_imp.
split.
-apply etl. split. apply H. 
split. apply Prop3. apply Prop3'.
-split. apply Prop2'.
apply Prop2. Qed.

End SERecurs.
