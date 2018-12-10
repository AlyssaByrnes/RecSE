Require Import Ensembles. 
(*Require Import Setoid.*)
(*Require Import Datatypes.*)

Module ConcState.


Variable input : Type.
Variable state: Type.

Inductive conc_state : Type :=
|EmptyState
|ConsState (i: input) (s: state).

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

(*Definition s_e_many := list sym_state -> list sym_state.
Axiom sym_ex_many : s_e_many.
*)
Definition r_inst_s :=  sym_state -> list ConcState.conc_state.
Axiom randomly_instantiate_conc_state : r_inst_s.

Definition r_inst_i := sym_state -> list ConcState.input.
Axiom randomly_instantiate_input : r_inst_i.

Definition pc_e := PC -> list ConcState.conc_state -> list ConcState.input -> Prop.
Axiom pc_eval : pc_e.

Definition inst := Phi -> list ConcState.conc_state -> list ConcState.input -> list ConcState.conc_state.
Axiom instantiate : inst.

Axiom commutativity : 
forall (li : list ConcState.input) (cs : list ConcState.conc_state) (s s' : sym_state),
(*li = (randomly_instantiate_input s) /\
cs = (randomly_instantiate_conc_state s) /\*)
is_leaf s' (sym_ex s) /\
(pc_eval (get_pc s') cs li) 
->
conc_ex cs li = instantiate (get_phi s') cs li.

Axiom commutativity2 : 
forall (li : list ConcState.input) (cs : list ConcState.conc_state) 
(t : SE_tree),
(*li = (randomly_instantiate_input s) /\
cs = (randomly_instantiate_conc_state s) /\*)
exists (s' : sym_state),
is_leaf s' t /\
(pc_eval (get_pc s') cs li) 
->
conc_ex cs li = instantiate (get_phi s') cs li.



Axiom commutativity':
forall (li : list ConcState.input) 
(lcs : list conc_state) (x : sym_state),
(exists t : SE_tree,
is_leaf x t /\
pc_eval (get_pc x) lcs li
)
-> conc_ex lcs li = instantiate (get_phi x) lcs li.

(*Axiom commutativity2 : 
forall (csl : list ConcState.conc_state) (t : SE_tree),
 exists(s' : sym_state) (li : list ConcState.input),
      is_leaf s' t /\
      pc_eval (get_pc s') csl li
<-> conc_ex csl li = instantiate (get_phi s') csl li.*)


Axiom commutativity3 :
forall (lcs : list ConcState.conc_state) (t : SE_tree),
exists
  (s' : sym_state) (li : list ConcState.input) ,
  is_leaf s' t /\
  pc_eval (get_pc s') lcs li /\
  conc_ex lcs li =
  instantiate (get_phi s') lcs li.

Axiom commutativity4:
forall (li : list ConcState.input) 
(s' : sym_state) (t : SE_tree),
exists lcs : list conc_state,
  is_leaf s' t /\
  pc_eval (get_pc s') lcs li /\
  conc_ex lcs li =
  instantiate (get_phi s') lcs li.


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

Fixpoint is_sublist (l1 l2 : list SE_tree) : Prop :=
match l1 with
|nil => False
|h :: t => (l2 = l1) \/ is_sublist t l2
end.

Axiom c_i_o_elim :
forall (a b : SE_tree) (t l : list SE_tree),
is_sublist (a :: b :: t) l ->
consecutive_in_order a b l.




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
(*Definition c_o_1 := SE_tree -> Ensemble (list ConcState.conc_state).
Axiom circle_op_1 : c_o_1.*)

Inductive circle_op_1 (t : SE_tree)  : Ensemble (list ConcState.conc_state) :=
c_o_1_intro: 
forall (lcs : list ConcState.conc_state) (s' : sym_state) 
(li: list ConcState.input),
(is_leaf s' t) /\
pc_eval (get_pc s') lcs li ->
is_element_of (circle_op_1 t) lcs.

(*Definition c_o_2 := SE_tree -> Ensemble (list ConcState.conc_state).
Axiom circle_op_2 : c_o_2.*)

(*Axiom c_o_2_def : 
forall (t : SE_tree) (l : SE_state),
is_leaf l t
-> c_o_2 l = *)

Inductive circle_op_2 (t : SE_tree)  : Ensemble (list ConcState.conc_state) :=
c_o_2_intro: 
forall (lcs lcs' : list ConcState.conc_state) (s' : sym_state) 
(li: list ConcState.input),
(is_leaf s' t) /\
pc_eval (get_pc s') lcs li /\
(lcs' = instantiate (get_phi s') lcs li) ->
is_element_of (circle_op_2 t) lcs'.

(*
Axiom c_o_1_def:
forall (lcs : list ConcState.conc_state) (s' : sym_state) 
(li: list ConcState.input) (t : SE_tree),
is_element_of (circle_op_1 t) lcs
<->
(is_leaf s' t) /\
pc_eval (get_pc s') lcs li.

Axiom c_o_2_def:
forall (lcs lcs' : list ConcState.conc_state) (s' : sym_state) 
(li: list ConcState.input) (t : SE_tree),
is_element_of (circle_op_2 t) lcs'
<->
(is_leaf s' t) /\
pc_eval (get_pc s') lcs li /\
(lcs' = instantiate (get_phi s') lcs li).*)


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

Axiom connection : True.

(*
Axiom circle_op_property:
forall (t : SE_tree) (lcs lcs': list ConcState.conc_state) (li: list ConcState.input)
(s' : sym_state),
is_element_of
(circle_op_1 t) lcs
/\ (pc_eval (get_pc s') lcs li)
->
is_element_of 
(circle_op_2 t)
(conc_ex lcs li).

*)
(*
Theorem c_o_rw_all: 
forall (t : SE_tree) 
  (lcs : list conc_state) (li: list ConcState.input) (x : sym_state) ,
pc_eval (get_pc x) lcs li /\
    is_element_of (circle_op_1 t) lcs
->
is_leaf x t /\ pc_eval (get_pc x) lcs li.
Proof. intros. destruct H. apply c_o_1_def in H0.



Theorem c_o_rw': 
forall (t : SE_tree) 
  (lcs : list conc_state) (li: list ConcState.input) (x : sym_state) ,
pc_eval (get_pc x) lcs li /\
    is_element_of (circle_op_1 t) lcs
->
exists (s' : sym_state) ,
is_leaf s' t /\
(pc_eval (get_pc s') lcs li).
Proof. intros. exists x. apply c_o_rw_all. apply H. Qed.
*)

(*Axiom c_o_rw: 
forall (t : SE_tree) 
  (lcs : list conc_state) (li: list ConcState.input) ,
(exists s' : sym_state,
      pc_eval (get_pc s') lcs li /\
      is_element_of (circle_op_1 t) lcs)
->
exists (s' : sym_state) ,
is_leaf s' t /\
(pc_eval (get_pc s') lcs li).
*)



Theorem circle_op_property':
forall (t : SE_tree) 
 (li: list ConcState.input) (lcs : list conc_state) ,
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
forall (t : SE_tree) (x : list conc_state),
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

Axiom Prop2 : 
intersection 
(circle_op_2 (last_elem tree_list))
Error_States 
<> empty_set.

Axiom Prop2':
is_subset
(circle_op_2 (last_elem tree_list))
Error_States.

Axiom Prop3 : 
forall (a b : SE_tree), 
consecutive_in_order a b tree_list ->
trees_connect b a.

Axiom Prop3':
forall (a : SE_tree), 
in_list tree_list a ->
(circle_op_2 a) <> empty_set.



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
Axiom set_property_1:
forall (A : list ConcState.conc_state) (B C : Ensemble (list ConcState.conc_state)),
(is_element_of B A)
/\ (is_subset B C)
/\ (intersection B C <> empty_set)
-> (is_element_of C A).

Axiom set_property_2:
forall (A : (list ConcState.conc_state)) (B C : Ensemble (list ConcState.conc_state)) (i : list ConcState.input),
((is_element_of B A)
/\
(forall (x : (list ConcState.conc_state)),
is_element_of B x
-> is_element_of C (conc_ex x i))
/\
(C <> empty_set))
-> is_element_of C (conc_ex A i).

Axiom set_property_3:
forall (A B : Ensemble (list ConcState.conc_state)) (C : (list ConcState.conc_state)),
is_subset A B /\ is_element_of A C
-> is_element_of B C.

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
-> is_element_of (circle_op_2(last_elem t)) (conc_ex x i))
/\
((circle_op_2(last_elem t)) <> empty_set))
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
-> is_element_of (circle_op_2(last_elem t)) (conc_ex x i))
/\
((circle_op_2 (last_elem t)) <> empty_set))
-> is_element_of (circle_op_2((last_elem (t)))) 
(conc_ex (execute_tree_list (front t)) i).
Proof. intros. apply set_property_2 in H. apply H. Qed. 

Theorem P3_and_IH:
forall (t: list SE_tree),
is_subset
(circle_op_2 (second_last_elem t))
(circle_op_1 (last_elem t))
/\
is_element_of
        (circle_op_2
           ((second_last_elem t)))
        (execute_tree_list (front t))
->
is_element_of
(circle_op_1 (last_elem t))
(execute_tree_list (front t)).
Proof. intros. apply set_property_3 in H. apply H. Qed. 

Theorem P2_and_etl_imp:
forall (t : list SE_tree),
(is_element_of 
(circle_op_2 (last_elem t))
(execute_tree_list t))
/\
(is_subset 
(circle_op_2 ( (last_elem t)))
Error_States)
/\
((intersection
(circle_op_2 ((last_elem t)))
Error_States)
<> empty_set
)
->
is_element_of 
Error_States
(execute_tree_list t).
Proof. intros. apply set_property_1 in H. apply H. Qed.

Theorem P2_and_etl_imp_ind_step:
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
Proof. intros. apply set_property_1 in H. apply H. Qed.

Axiom basecase:
forall s : SE_tree,
is_element_of (circle_op_2 ((last_elem (s :: nil))))
  (execute_tree_list (s :: nil)).

Axiom s_l_e_rewrite :
forall (s s0 : SE_tree) (t : list SE_tree),
second_last_elem (s :: s0 :: t)  = last_elem (s0 :: t).

Axiom front_rewrite : 
forall (s s0 : SE_tree) (t : list SE_tree), 
front (s :: s0 :: t) = (s0 :: t).

Axiom sl_nil : 
(is_sublist nil tree_list = False).

Axiom sl_elim:
forall (s s0 : SE_tree) (t : list SE_tree), 
is_sublist (s0 :: s :: t) tree_list
->
is_sublist (s :: t) tree_list.

Axiom in_list_elim:
forall (s s0 : SE_tree) (t : list SE_tree), 
is_sublist (s0 :: s :: t) tree_list
->
in_list tree_list s0.

Axiom list_size_sublist:
forall (s : SE_tree) (t : list SE_tree), 
is_sublist  (s :: t) tree_list
->
list_size (s :: t) > 0.

Axiom not_leaf_sublist:
forall (s : SE_tree) (t : list SE_tree), 
is_sublist  (s :: t) tree_list
->
s <> nilleaf.

Axiom sublist_of_self:
is_sublist tree_list tree_list.

Theorem etl:
forall t : list SE_tree,
is_sublist t tree_list ->
is_element_of 
  (circle_op_2((last_elem t))) 
  (execute_tree_list t).
Proof. intros. induction t. 
- pose sl_nil. contradiction.
- destruct t. 
* apply basecase.
* rewrite etl_1_step.
** apply P1_and_circle_op_prop_ind_step. split.
*** apply P3_and_IH. split.
+ unfold last_elem.
  pose Prop3 as P3. unfold trees_connect in P3.
  apply P3. simpl. pose H as H1. 
  apply c_i_o_elim in H1. apply H1.
+ rewrite front_rewrite. rewrite s_l_e_rewrite. apply IHt.
  apply sl_elim in H. apply H.
*** split. apply circle_op_property_2. 
    pose Prop3' as P3'. simpl. apply P3'. 
    apply in_list_elim in H. apply H.
** split. apply list_size_sublist.
   apply sl_elim in H. apply H.
   split. apply list_size_sublist. apply H.
   apply not_leaf_sublist in H. apply H. Qed.


Theorem sufficiency: 
is_element_of Error_States (execute_tree_list tree_list).
Proof. intros. 
apply P2_and_etl_imp.
split. apply etl. auto. apply sublist_of_self. 
- split. apply Prop2'.
apply Prop2. Qed.

End SERecurs.

