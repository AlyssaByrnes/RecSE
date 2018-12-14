Require Import Ensembles. 
(*Require Import Setoid.*)
(*Require Import Datatypes.*)
Require Import Logic.

Module ConcState.


Variable input : Type.
Variable state: Type.
Variable conc_state : Type.

(*Inductive conc_state : Type :=
|EmptyState
|ConsState (i: input) (s: state).*)

Definition concrete_execution := list conc_state -> list input -> list conc_state.
Axiom conc_ex : concrete_execution.

(*Definition concrete_execution_many := list conc_state -> list input -> list conc_state.
Axiom conc_ex_many : concrete_execution_many.*)

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


(*** SYM EX TREE STRUCTURE ***)
Inductive SE_tree : Type :=
| nilleaf: SE_tree
| ConsNode: SE_tree -> sym_state -> SE_tree -> SE_tree.


Definition root (t : SE_tree) : sym_state :=
match t with 
|nilleaf => nilstate
|ConsNode l n r => n
end.


Fixpoint is_leaf (s' : sym_state) (s : SE_tree) : Prop :=
match s with
|ConsNode nilleaf n nilleaf => s' = n
|ConsNode l n r => (is_leaf s' l) \/ (is_leaf s' r)
|nilleaf => False
end.

(*** SYMBOLIC EXECUTION ***)
Definition s_e := sym_state -> SE_tree.
Axiom sym_ex : s_e.


(*Definition r_inst_s :=  sym_state -> list ConcState.conc_state.
Axiom randomly_instantiate_conc_state : r_inst_s.

Definition r_inst_i := sym_state -> list ConcState.input.
Axiom randomly_instantiate_input : r_inst_i.*)

Definition pc_e := PC -> list ConcState.conc_state -> list ConcState.input -> Prop.
Axiom pc_eval : pc_e.

Definition inst := Phi -> list ConcState.conc_state -> list ConcState.input -> list ConcState.conc_state.
Axiom instantiate : inst.

(*Axiom commutativity : 
forall (li : list ConcState.input) (cs : list ConcState.conc_state) (s s' : sym_state),
(*li = (randomly_instantiate_input s) /\
cs = (randomly_instantiate_conc_state s) /\*)
is_leaf s' (sym_ex s) /\
(pc_eval (get_pc s') cs li) 
->
conc_ex cs li = instantiate (get_phi s') cs li.*)


Axiom commutativity':
forall (li : list ConcState.input) 
(lcs : list ConcState.conc_state) (x : sym_state),
(exists t : SE_tree,
is_leaf x t /\
pc_eval (get_pc x) lcs li
)
-> conc_ex lcs li = instantiate (get_phi x) lcs li.




(*** TREE LIST STRUCTURE ***)


Notation "x :: l" := (cons x l) (at level 60, right associativity).

Fixpoint first_elem ( l : list SE_tree) : SE_tree :=
match l with
|nil => nilleaf
|x :: nil => x
|x :: y => first_elem y
end.

Definition front (l : list SE_tree) : list SE_tree :=
match l with
|nil => nil
|x :: y => y
end.

Definition last_elem (l : list SE_tree) : SE_tree :=
match l with
|nil => nilleaf
|x :: y => x
end.

Definition second_last_elem (l : list SE_tree) : SE_tree :=
match l with
|nil => nilleaf
|x :: y => last_elem y
end.

Fixpoint list_size (l : list SE_tree) : nat :=
match l with
|nil => 0
|x :: nil => 1
|x :: y => S (list_size y)
end.

Fixpoint in_list (l : list SE_tree) (t : SE_tree) : Prop :=
match l with
|nil => False
|x :: y => (x = t) \/ (in_list y t)
end.

Fixpoint consecutive_in_order (a b : SE_tree) (l : list SE_tree) : Prop :=
match l with
| h :: t => (a = h /\ b = (last_elem t)) \/ consecutive_in_order a b t
| nil => False
end.

(* Checks if l2 is a prefix of l1*)
Fixpoint is_prefix (l1 l2 : list SE_tree) : Prop :=
match l1 with
|nil => False
|h :: t => (l2 <> nil) /\ ((l2 = l1) \/ (is_prefix t l2))
end.


(*** SET OPERATION SHORT HANDS ***)
Definition is_subset (x y : Ensemble (list ConcState.conc_state)) : Prop :=
Included (list ConcState.conc_state) x y.

Definition is_element_of (y : Ensemble (list ConcState.conc_state)) (x : list ConcState.conc_state) : Prop :=
In (list ConcState.conc_state) y x.

Definition empty_set : Ensemble (list ConcState.conc_state) := 
Empty_set (list ConcState.conc_state).

Definition intersection (x y : Ensemble (list ConcState.conc_state)) : Ensemble (list ConcState.conc_state) :=
Intersection (list ConcState.conc_state) x y.


End SymbolicExec.
Import SymbolicExec. 

Module SERecurs.

Variable init_conc_state: (list ConcState.conc_state).
Variable Error_States : Ensemble (list ConcState.conc_state).
Variable tree_list : list SE_tree.

Axiom no_leaf_requirement:
forall (s : SE_tree),
in_list tree_list s -> s <> nilleaf.

Axiom non_empty : 
tree_list <> nil.

Axiom size_requirement: 
list_size tree_list > 0.

Axiom nil_is_nil:
nilleaf :: nil = nil.

Axiom nil_leaf_elim:
forall l : list SE_tree,
 l <> nil -> (nilleaf :: l) <> nil.

Axiom leaf_elim:
forall (l : list SE_tree) (s : SE_tree),
 l <> nil -> (s :: l) <> nil.

Axiom non_nil_elem_in_list:
forall (l : list SE_tree) (s : SE_tree),
 s <> nilleaf -> (s :: l) <> nil.


Definition fl := SE_tree -> sym_state.
Axiom find_leaf : fl.

Definition gi := SymbolicExec.PC -> list ConcState.input.
Axiom get_input : gi.

(*Axiom get_input_def := 
Finds inputs given a pc that satisfy that pc
*)

(*** CIRCLE OPERATIONS ***)
(* Takes as input symbolic state of root and pc of its leaf 
and returns all and only the concrete states that will take us down 
the path that leads to the leaf. *)
Definition c_o_1 := SE_tree -> Ensemble (list ConcState.conc_state).
Axiom circle_op_1 : c_o_1.

Definition c_o_2 := SE_tree -> Ensemble (list ConcState.conc_state).
Axiom circle_op_2 : c_o_2.


Axiom c_o_1_def : 
forall (t : SE_tree) (lcs: list ConcState.conc_state) ,
is_element_of (circle_op_1 t) lcs <->
forall (s' : sym_state) (li: list ConcState.input),
(is_leaf s' t) ->
pc_eval (get_pc s') lcs li.

Axiom c_o_2_def : 
forall (t : SE_tree) (lcs': list ConcState.conc_state),
is_element_of (circle_op_2 t) lcs' <->
exists (s' : sym_state) (li: list ConcState.input)
 (lcs: list ConcState.conc_state),
(is_leaf s' t) /\
pc_eval (get_pc s') lcs li /\
(lcs' = instantiate (get_phi s') lcs li).


Theorem circle_op_property':
forall (t : SE_tree) 
 (li: list ConcState.input) (lcs : list ConcState.conc_state) ,
(exists s' : sym_state,
      pc_eval (get_pc s') lcs li /\
      is_element_of (circle_op_1 t) lcs /\
      is_leaf s' t)
->is_element_of 
(circle_op_2 t)
(conc_ex lcs li).
Proof. intros. destruct H. apply c_o_2_def.
exists x. exists li. exists lcs.
destruct H. destruct H0. split. apply H1. split. apply H.
apply commutativity'. exists t. split. apply H1. apply H. Qed.




Axiom get_input_def' : 
forall (t : SE_tree) (li: list ConcState.input) (lcs : list ConcState.conc_state), 
is_element_of (circle_op_1 t) lcs /\(li = get_input (get_pc (find_leaf t))) 
-> exists
(s' : sym_state),
 (pc_eval (get_pc s') lcs li)
/\ is_element_of (circle_op_1 t) lcs
/\ is_leaf s' t.



Theorem circle_op_property_2':
forall (t : SE_tree)
 (li: list ConcState.input)  (lcs lcs': list ConcState.conc_state),
is_element_of
(circle_op_1 t) lcs
/\ (li = get_input (get_pc (find_leaf t)))
->
is_element_of 
(circle_op_2 t)
(conc_ex lcs li).
Proof. intros. apply get_input_def' in H.  
apply circle_op_property' in H. apply H. Qed.




Theorem circle_op_property_2: 
forall (t : SE_tree) (x : list ConcState.conc_state),
is_element_of 
(circle_op_1 t) x 
->
is_element_of
(circle_op_2 t)
(conc_ex x
(get_input (get_pc (find_leaf t)))).
Proof. intros. apply circle_op_property_2'.
* auto. 
* split. apply H. auto. Qed.




(*** PROPERTIES 1-3 ***)
Definition trees_connect (A B : SE_tree) : Prop :=
is_subset
(circle_op_2 A)
(circle_op_1 B).


Axiom Prop1 : 
is_element_of 
(circle_op_1 (first_elem tree_list)) init_conc_state.

(*Axiom Prop2 : 
intersection 
(circle_op_2 (last_elem tree_list))
Error_States 
<> empty_set.*)

Axiom Prop2':
is_subset
(circle_op_2 (last_elem tree_list))
Error_States.

Axiom Prop3 : 
forall (a b : SE_tree), 
consecutive_in_order a b tree_list ->
trees_connect b a.

(*Axiom Prop3':
forall (a : SE_tree), 
in_list tree_list a ->
(circle_op_2 a) <> empty_set.*)



(*** SUFFICIENCY ***)

Fixpoint execute_tree_list (tlist : list SE_tree) : list ConcState.conc_state :=
match tlist with
|nil => nil
|h :: nil => conc_ex (init_conc_state) (get_input (get_pc (find_leaf h)))
|h :: t => conc_ex (execute_tree_list t) (get_input(get_pc(find_leaf h)))
end.


Theorem etl_1_step:
forall (t : list SE_tree) (s : SE_tree),
(list_size t > 0) /\ (list_size (s :: t) > 0) /\ s <> nilleaf ->
execute_tree_list (s :: t) = conc_ex (execute_tree_list t) (get_input(get_pc(find_leaf s))).
Proof. intros.
induction s.
-destruct H. destruct H0. contradiction. 
-induction t.
*destruct H. simpl in H. inversion H.
*simpl; auto.
Qed.


(*** SET PROPERTIES ***)
Theorem set_property_1:
forall (A : list ConcState.conc_state) (B C : Ensemble (list ConcState.conc_state)),
(is_element_of B A)
/\ (is_subset B C)
-> (is_element_of C A).
Proof. intros. unfold is_element_of.  destruct H. 
unfold is_subset in H0. unfold Included in H0. 
apply H0.
unfold is_element_of in H. apply H. Qed.

Theorem set_property_2:
forall (A : (list ConcState.conc_state)) (B C : Ensemble (list ConcState.conc_state)) (i : list ConcState.input),
((is_element_of B A)
/\
(forall (x : (list ConcState.conc_state)),
is_element_of B x
-> is_element_of C (conc_ex x i))
)
-> is_element_of C (conc_ex A i).
Proof. intros. destruct H. 
apply H0. apply H. Qed.





(*** APPLICATION OF SET PROPERTIES ***)

Theorem P1_and_circle_op_prop:
forall (t : list SE_tree) (i: list ConcState.input),
((is_element_of 
  (circle_op_1 (last_elem t)) 
  init_conc_state)
/\
(forall (x : list ConcState.conc_state),
is_element_of 
  (circle_op_1 (last_elem t)) x
-> is_element_of (circle_op_2(last_elem t)) (conc_ex x i)))
-> is_element_of (circle_op_2(last_elem t)) (conc_ex init_conc_state i).
Proof. intros. apply set_property_2 in H. apply H. Qed.

Theorem P1_and_circle_op_prop_ind_step:
forall (t : list SE_tree) (i: list ConcState.input) ,
((is_element_of 
  (circle_op_1 (last_elem t)) 
  (execute_tree_list (front t)))
/\
(forall (x : list ConcState.conc_state),
is_element_of 
  (circle_op_1 (last_elem t)) x
-> is_element_of (circle_op_2(last_elem t)) (conc_ex x i)))
-> is_element_of (circle_op_2((last_elem (t)))) 
(conc_ex (execute_tree_list (front t)) i).
Proof. intros. apply set_property_2 in H. apply H. Qed. 

Theorem P3_and_IH:
forall (t: list SE_tree),
is_element_of
        (circle_op_2
           ((second_last_elem t)))
        (execute_tree_list (front t))
/\
is_subset
(circle_op_2 (second_last_elem t))
(circle_op_1 (last_elem t))
->
is_element_of
(circle_op_1 (last_elem t))
(execute_tree_list (front t)).
Proof. intros. apply set_property_1 in H. apply H. Qed. 

Theorem P2_and_etl_imp:
forall (t : list SE_tree),
(is_element_of 
(circle_op_2 (last_elem t))
(execute_tree_list t))
/\
(is_subset 
(circle_op_2 ( (last_elem t)))
Error_States)
->
is_element_of 
Error_States
(execute_tree_list t).
Proof. intros. apply set_property_1 in H. apply H. Qed.

(*Theorem P2_and_etl_imp_ind_step:
forall (t : list SE_tree),
(is_element_of 
(circle_op_2 ((last_elem t)))
(execute_tree_list t))
/\
(is_subset 
(circle_op_2 ((last_elem t)))
 (circle_op_1 ((second_last_elem t))))
/\
((intersection
(circle_op_2 ((last_elem t)))
 (circle_op_1 (second_last_elem t)))
<> empty_set
)
->
is_element_of
 (circle_op_1  (second_last_elem t))
(execute_tree_list t).
Proof. intros. apply set_property_1 in H. apply H. Qed.*)



(*** HELPER THEOREMS ***)

Theorem prefix_not_nil:
forall (t l : list SE_tree),
is_prefix l t -> t <> nil.
Proof. intros. destruct t. 
* destruct l. 
  simpl in H. contradiction. 
  simpl in H. destruct H. contradiction.
* induction l.
  simpl in H. contradiction.
  simpl in H. destruct H. apply H. Qed.


Theorem prefix_def_bw:
forall (t l : list SE_tree) (s : SE_tree),
t <> nil /\ (t = s :: l \/ is_prefix l t) ->
is_prefix (s::l) t.
Proof. intros. simpl. apply H. Qed.



Theorem prefix_not_nil2:
forall (t l : list SE_tree),
is_prefix l t -> l <> nil.
Proof. intros. induction l. 
simpl in H. contradiction.
destruct a. destruct l. simpl in H.
destruct H. inversion H0.
rewrite H1 in H. apply H. 
contradiction.
* simpl in H. destruct H. inversion H0.
** rewrite H1 in H. apply H.
** apply prefix_def_bw in H1. apply IHl in H1.
  apply nil_leaf_elim. apply H1.
* simpl in H. destruct H.
  inversion H0.
** rewrite H1 in H. apply H.
** apply IHl in H1. apply leaf_elim.
    apply H1. Qed.

Theorem no_prefix_of_nil:
forall l : list SE_tree,
is_prefix l nil -> False.
Proof. intros. induction l. 
simpl in H. auto. 
simpl in H. destruct H.
contradiction. Qed.



Theorem prefix_of_self_general:
forall l : list SE_tree,
l <> nil ->
is_prefix l l.
Proof. intros. induction l.
* contradiction.
* simpl;auto. Qed.

Theorem prefix_of_self:
tree_list <> nil ->
is_prefix tree_list tree_list.
Proof. intros. induction tree_list.
* simpl;auto.
* simpl; auto.  Qed.

Theorem first_elem_last_elem:
forall s : SE_tree,
last_elem (s :: nil) = first_elem (s :: nil).
Proof. intros. simpl. auto. Qed. 

(*Axiom prefix_def:
forall (s l : list SE_tree) ( t : SE_tree),
(t :: s) = l /\ s <> nil
-> is_prefix l s.

Axiom prefix_elim:
forall (s l : list SE_tree) ( t : SE_tree),
is_prefix l (t :: s) /\ s <> nil ->
is_prefix l s.
(*Proof. intros. induction l.
* simpl in H. contradiction.
* simpl in H. destruct H. inversion H0.
**  apply prefix_def. *) *)

Theorem first_elem_elim:
forall (s : list SE_tree) ( t : SE_tree),
s <> nil ->
first_elem s = first_elem (t :: s).
Proof. intros. destruct s.
* contradiction.
* simpl; auto. Qed.



Theorem prefix_first_elem :
forall s : list SE_tree,
is_prefix tree_list s 
-> first_elem s = first_elem tree_list.
Proof. intros. destruct s.
apply no_prefix_of_nil in H. contradiction.
destruct s.
* induction tree_list. simpl in H. contradiction. 
  pose H as H1. simpl in H1. destruct H1. inversion H1.
** rewrite H2. auto.
** pose H2 as H3. apply IHl in H3. 
  assert (first_elem l = first_elem (a :: l)).
  apply first_elem_elim. apply prefix_not_nil2 in H2. 
  apply H2. rewrite <- H4. apply H3. 
* induction tree_list.
** simpl in H. contradiction.
** simpl in H. destruct H. inversion H0.
*** rewrite H1. auto.
*** pose H1 as H2. apply prefix_not_nil2 in H2.
    apply IHl in H1. assert (first_elem l = first_elem (a :: l)).
    apply first_elem_elim. apply H2.
    rewrite <- H3. apply H1. Qed.


Theorem basecase:
forall s : SE_tree,
(is_prefix tree_list (s :: nil)) ->
is_element_of (circle_op_2 ((last_elem (s :: nil))))
  (execute_tree_list (s :: nil)).
Proof. intros. apply P1_and_circle_op_prop. split.
*  rewrite first_elem_last_elem. 
apply prefix_first_elem in H. rewrite H.
  apply Prop1.
* apply circle_op_property_2. Qed.

Theorem s_l_e_rewrite :
forall (s s0 : SE_tree) (t : list SE_tree),
second_last_elem (s :: s0 :: t)  = last_elem (s0 :: t).
Proof. intros. simpl; auto. Qed.

Theorem front_rewrite : 
forall (s s0 : SE_tree) (t : list SE_tree), 
front (s :: s0 :: t) = (s0 :: t).
Proof. intros. simpl; auto. Qed.

Theorem sl_nil : 
(is_prefix tree_list nil -> False).
Proof. intros. apply no_prefix_of_nil in H.
 apply H. Qed.

Theorem sl_elim:
forall (s s0 : SE_tree) (t : list SE_tree), 
is_prefix  tree_list (s0 :: s :: t) /\ (s :: t) <> nil
->
is_prefix  tree_list (s :: t).
Proof. intros.  destruct H. induction tree_list.
* simpl in H. contradiction.
* simpl in H. destruct H. inversion H1.
** rewrite <- H2. simpl. split. apply H0.
right. split. apply H0. left. auto.
** apply IHl in H2. simpl. split. apply H0.
right. apply H2. Qed.




Theorem in_list_elim2:
forall (s a : SE_tree) (l : list SE_tree), 
 in_list l s -> in_list (a::l) s.
Proof. intros. induction l.
simpl in H. contradiction.
simpl in H. inversion H.
** simpl. right. left. apply H0.
** simpl. right. right. apply H0. Qed.

Theorem middle_in_list: 
forall (s a : SE_tree) (t : list SE_tree),
is_prefix tree_list (a :: s :: t) ->
in_list tree_list s.
Proof. intros. induction tree_list.
* simpl in H. contradiction.
* simpl in H. destruct H. inversion H0.
** rewrite <- H1. simpl;auto.
**  apply IHl in H1. apply in_list_elim2. apply H1. Qed.

Theorem in_list_elim:
forall (s s0 : SE_tree) (t : list SE_tree), 
is_prefix tree_list (s0 :: s :: t)
->
in_list tree_list s0.
Proof. intros. induction tree_list.
* simpl in H. contradiction.
* simpl in H. destruct H. inversion H0.
** rewrite <- H1. simpl;auto.
** apply IHl in H1. apply in_list_elim2. apply H1. Qed.

Theorem in_list_elim3:
forall (s : SE_tree) (t : list SE_tree), 
is_prefix tree_list (s :: t)
->
in_list tree_list s.
Proof. intros. induction tree_list.
* simpl in H. contradiction.
* simpl in H. destruct H. inversion H0.
** rewrite <- H1. simpl;auto.
** apply IHl in H1. apply in_list_elim2. apply H1. Qed.

Theorem not_leaf_prefix:
forall (s : SE_tree) (t : list SE_tree), 
is_prefix tree_list (s :: t) 
->
s <> nilleaf.
Proof. intros. 
apply in_list_elim3 in H.
apply no_leaf_requirement in H. apply H. Qed.

Theorem not_nil_prefix: 
forall (s a : SE_tree) (t : list SE_tree),
is_prefix tree_list (a :: s :: t) ->
( s :: t) <> nil.
Proof. intros. pose H as H1.
apply middle_in_list in H1.
apply no_leaf_requirement in H1.
apply non_nil_elem_in_list. apply H1. Qed.

(*Theorem list_size_nil_elim:
forall (x : SE_tree) (t : list SE_tree),
list_size (x :: nilleaf :: t) = list_size ( x :: t).
Proof. intros. destruct x.
* simpl;auto. simpl;auto.

Theorem list_size_middle_elim:
forall (x y : SE_tree) (t l : list SE_tree),
list_size (x :: t) = list_size l + 1
-> 
list_size (x :: y :: t) = list_size (y :: l) + 1.
Proof. intros. destruct y.
* simpl. simpl in H. *)



(*Theorem list_size_ind: 
forall (s : SE_tree) (t : list SE_tree),
s <> nilleaf ->
list_size ( s :: t) = (list_size t) + 1.
Proof. intros. destruct s.
* contradiction.
* induction t. 
** simpl;auto.
** apply IHt. Qed.*)

Theorem not_nil_size: 
forall (s : SE_tree) (t : list SE_tree),
list_size ( s :: t) > 0.
Proof. intros. induction t.
* simpl;auto.
* simpl;auto. Qed.

Theorem list_size_prefix:
forall (s : SE_tree) (t : list SE_tree), 
is_prefix  tree_list (s :: t) 
->
list_size (s :: t) > 0.
Proof. intros. apply not_nil_size. Qed.

Theorem c_i_o_elim1 :
forall (a b c: SE_tree) (l : list SE_tree),
consecutive_in_order a b l
-> consecutive_in_order a b (c :: l).
Proof. intros. destruct l. 
* simpl in H. contradiction.
* simpl in H. inversion H.
** simpl. right. left. apply H0.
** simpl. right. right. apply H0. Qed.


Theorem c_i_o_elim :
forall (a b : SE_tree) (t l : list SE_tree),
is_prefix  l (a :: b :: t) ->
consecutive_in_order a b l.
Proof. intros. induction l.
* simpl in H. contradiction.
* simpl in H. destruct H. inversion H0.
** rewrite <- H1. simpl;auto.
** apply IHl in H1.  apply c_i_o_elim1. apply H1. Qed.



(*** MAIN PROOF***)

Theorem etl:
forall t : list SE_tree,
is_prefix tree_list t ->
is_element_of 
  (circle_op_2((last_elem t))) 
  (execute_tree_list t).
Proof. intros. induction t. 
- apply sl_nil in H. contradiction.
- destruct t. 
* apply basecase. apply H.
* rewrite etl_1_step.
** apply P1_and_circle_op_prop_ind_step. split.
*** apply P3_and_IH. split.
+ rewrite front_rewrite. rewrite s_l_e_rewrite. apply IHt.
  pose H as H1. apply not_nil_prefix in H1.
  assert (is_prefix tree_list (a :: s :: t) /\ (s :: t) <> nil).
  split. apply H. apply H1.
  apply sl_elim in H0. apply H0.
+ unfold last_elem.
  pose Prop3 as P3. unfold trees_connect in P3.
  apply P3. simpl. pose H as H1. 
  apply c_i_o_elim in H1. apply H1.
*** apply circle_op_property_2. 
** split. apply list_size_prefix.
  pose H as H1. apply not_nil_prefix in H1.
  assert (is_prefix tree_list (a :: s :: t) /\ (s :: t) <> nil).
  split. apply H. apply H1.
   apply sl_elim in H0. apply H0.
   split. apply list_size_prefix. apply H.
   apply not_leaf_prefix in H. apply H. Qed.


Theorem sufficiency: 
is_element_of Error_States (execute_tree_list tree_list).
Proof. intros. 
apply P2_and_etl_imp.
split. apply etl. auto. apply prefix_of_self. apply non_empty.
apply Prop2'. Qed.

End SERecurs.

