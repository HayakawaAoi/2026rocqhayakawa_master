Require Import ZArith Relations.
Local Open Scope Z_scope.
Require Import Autosubst.Autosubst.



(* Labels *)

Inductive level : Type :=
    | Low
    | High.

Inductive slabel : Type := 
    | label : level * level -> slabel.

Notation "{ c , e }" := (label (c, e)).

Definition conf (l : slabel) :=
    match l with
    | {c, e} => c
    end.

Definition integ (l : slabel) :=
    match l with
    | {c, e} => e
    end.



(* Types *)

Inductive utype : Type :=
    | ty_bool   : utype
    | ty_int    : utype
    | ty_arrow  : stype -> stype -> utype
    | ty_prod   : stype -> stype -> utype
with stype : Type :=
    | type : utype -> slabel -> stype.

Notation "[ u '@ty' l ]" := (type u l) (at level 0).

Notation "'Bool'" := (ty_bool).
Notation "'Int'" := (ty_int).
Notation "s1 '->s' s2" := (ty_arrow s1 s2) (at level 10).
Notation "s1 '*s' s2" := (ty_prod s1 s2) (at level 10).

Check Bool.
Check Int.
Check [Bool @ty {High, High}] ->s [Bool @ty {High, High}].
Check [Bool @ty {High, High}] *s [Bool @ty {High, High}].



(* Terms *)

Inductive tm : Type :=
    | tm_true       : slabel -> tm
    | tm_false      : slabel -> tm
    | tm_if         : tm -> tm -> tm -> tm
    | tm_int        : slabel -> Z -> tm
    | tm_op_int     : level -> (Z -> Z -> Z) -> tm -> tm -> tm
    | tm_op_bool    : level -> (Z -> Z -> bool) -> tm -> tm -> tm
    | tm_pair       : slabel -> tm -> tm -> tm
    | tm_proj1      : tm -> tm
    | tm_proj2      : tm -> tm
    | tm_abs        : slabel -> {bind tm} -> stype -> tm
    | tm_app        : tm -> tm -> tm
    | tm_var        : var -> tm
    | tm_prot       : slabel -> tm -> tm
    | tm_decl       : level -> tm -> tm.

Instance Ids_term : Ids tm. derive. Defined.
Instance Rename_term : Rename tm. derive. Defined.
Instance Subst_term : Subst tm. derive. Defined.
Instance SubstLemmas_term : SubstLemmas tm. derive. Qed.

Eval simpl in fun sigma x => (tm_var x).[sigma]. 

Eval simpl in fun sigma m1 m2 => (tm_app m1 m2).[sigma]. 

Eval simpl in fun sigma s m lb => (tm_abs s m lb).[sigma].


Inductive value : tm -> Prop :=
    | v_true : forall (l : slabel),
        value (tm_true l)
    | v_false : forall (l : slabel),
        value (tm_false l)
    | v_int : forall (l : slabel) (n : Z),
        value (tm_int l n)
    | v_pair : forall (l : slabel) (m1 m2 : tm),
        value m1 ->
        value m2 ->
        value (tm_pair l m1 m2)
    | v_abs : forall (l : slabel) (m : tm) (t : stype),
        value (tm_abs l m t).

Inductive value_context : tm -> Prop :=
    | d_true : forall (l : slabel),
        value_context (tm_true l)
    | d_false : forall (l : slabel),
        value_context (tm_false l)
    | d_int : forall (l : slabel) (n : Z),
        value_context (tm_int l n)
    | d_pair : forall (l : slabel) (m1 m2 : tm),
        value m1 ->
        value m2 ->
        value_context (tm_pair l m1 m2)
    | d_abs : forall (l : slabel) (m : tm) (t : stype),
        value_context (tm_abs l m t)
    | d_var : forall (x : var),
        value_context (tm_var x).

Lemma value_is_value_context : forall (V : tm),
    value V -> value_context V.
Proof.
    intros.
    induction H; eauto using value_context.
Qed.



(* Label relations *)

Definition clv_join (c1 c2 : level) : level :=
    match (c1, c2) with
    | (High, _) | (_, High) => High
    | _ => Low
    end.

Definition ilv_join (i1 i2 : level) : level :=
    match (i1, i2) with
    | (Low, _) | (_, Low) => Low
    | _ => High
    end.

Definition clv_meet (c1 c2 : level) : level :=
    match (c1, c2) with
    | (Low, _) | (_, Low) => Low
    | _ => High
    end.

Definition ilv_meet (i1 i2 : level) : level :=
    match (i1, i2) with
    | (High, _) | (_, High) => High
    | _ => Low
    end.

Definition join (l1 l2 : slabel) : slabel :=
    match (l1, l2) with
    | ({c1, i1}, {c2, i2}) => {(clv_join c1 c2), (ilv_join i1 i2)}
    end.

Definition meet (l1 l2 : slabel) : slabel :=
    match (l1, l2) with
    | ({c1, i1}, {c2, i2}) => {(clv_meet c1 c2), (ilv_meet i1 i2)}
    end.

Definition lv_le (lv1 lv2 : level) : Prop :=
    lv1 = Low \/ lv2 = High.

Definition label_le (l1 l2 : slabel) : Prop := 
    match (l1, l2) with
    | ({c1, i1}, {c2, i2}) => (lv_le c1 c2) /\ (lv_le i2 i1)
    end.

Definition conf_le (l1 l2 : slabel) : Prop :=
    lv_le (conf l1) (conf l2).

Definition integ_le (l1 l2 : slabel) : Prop :=
    lv_le (integ l1) (integ l2).

Notation "l1 '|_|' l2" := (join l1 l2) (at level 11).
Notation "l1 '|~|' l2" := (meet l1 l2) (at level 11).
Notation "lv1 '<=lv' lv2" := (lv_le lv1 lv2) (at level 12).
Notation "l1 '<=l' l2" := (label_le l1 l2) (at level 12).
Notation "c1 '<=c' c2" := (conf_le c1 c2) (at level 12).
Notation "i1 '<=i' i2" := (integ_le i1 i2) (at level 12).

Lemma label_deconstract : forall (a : slabel),
    a = {conf a, integ a}.
Proof.
    intros.
    destruct a.
    destruct p.
    simpl. reflexivity.
Qed.

Lemma lv_le_trans : forall (lv1 lv2 lv3 : level),
    lv1 <=lv lv2 -> lv2 <=lv lv3 -> lv1 <=lv lv3.
Proof.
    intros.
    unfold lv_le in *.
    destruct H.
    -   left.
        apply H.
    -   destruct H0.
        +   rewrite H in H0.
            discriminate H0.
        +   right.
            apply H0.
Qed.

Lemma label_le_trans : forall (l1 l2 l3 : slabel),
    l1 <=l l2 -> l2 <=l l3 -> l1 <=l l3.
Proof.
    intros.
    rewrite (label_deconstract l1) in *.
    rewrite (label_deconstract l2) in *.
    rewrite (label_deconstract l3) in *.
    unfold label_le in *.
    destruct H as [HL HR].
    destruct H0 as [H0L H0R].
    split.
    -   eapply lv_le_trans.
        apply HL. apply H0L.
    -   eapply lv_le_trans.
        apply H0R. apply HR.
Qed.

Lemma lv_le_refl : forall (lv : level),
    lv <=lv lv.
Proof.
    unfold lv_le.
    intros lv. destruct lv.
    -   left. reflexivity.
    -   right. reflexivity.
Qed.

Lemma label_le_refl : forall (l : slabel),
    l <=l l.
Proof.
    intros.
    rewrite (label_deconstract l).
    unfold label_le.
    split; apply lv_le_refl.
Qed.

Lemma integ_le_HH : forall (l : slabel),
    l <=i {High, High}.
Proof.
    intros.
    unfold integ_le. unfold lv_le.
    right. simpl. reflexivity.
Qed.

Lemma conf_le_HH : forall (l : slabel),
    l <=c {High, High}.
Proof.
    intros.
    unfold conf_le. unfold lv_le.
    right. simpl. reflexivity.
Qed.

Lemma join_comm : forall (l1 l2 : slabel),
    l1 |_| l2 = l2 |_| l1.
Proof.
    intros.
    rewrite (label_deconstract l1).
    rewrite (label_deconstract l2).
    unfold join. unfold clv_join, ilv_join.
    destruct (conf l1); destruct (integ l1); destruct (conf l2); destruct (integ l2); simpl; reflexivity.
Qed.

Lemma join_assoc : forall (l1 l2 l3 : slabel),
    (l1 |_| l2) |_| l3 = l1 |_| (l2 |_| l3).
Proof.
    intros.
    rewrite (label_deconstract l1) in *.
    rewrite (label_deconstract l2) in *.
    rewrite (label_deconstract l3) in *.
    unfold join. unfold clv_join, ilv_join.
    destruct (conf l1); destruct (integ l1); destruct (conf l2); destruct (integ l2); destruct (conf l3); destruct (integ l3); reflexivity.
Qed.

Lemma monotonicity_join : forall (l1 l2 l : slabel),
    l1 <=l l2 -> (l1 |_| l) <=l (l2 |_| l).
Proof.
    intros.
    rewrite (label_deconstract l1) in *.
    rewrite (label_deconstract l2) in *.
    rewrite (label_deconstract l) in *.
    unfold join. unfold clv_join, ilv_join.
    destruct (conf l); destruct (integ l); destruct (conf l1); destruct (integ l1); destruct (conf l2); destruct (integ l2); simpl;
    eauto using label_le_refl, label_le_trans; unfold label_le in *; unfold lv_le in *; destruct H as [[HL | HL] [HR | HR]]; destruct HL; destruct HR; auto.
Qed.

Lemma monotonicity_integ_join : forall (l1 l2 l : slabel),
    l1 <=i l2 -> (l1 |_| l) <=i l2.
Proof.
    intros.
    rewrite (label_deconstract l1) in *.
    rewrite (label_deconstract l2) in *.
    rewrite (label_deconstract l) in *.
    unfold join. unfold clv_join, ilv_join.
    destruct (conf l); destruct (integ l); destruct (conf l1); destruct (integ l1); destruct (conf l2); destruct (integ l2);
    unfold integ_le, lv_le in *; simpl in *; auto.
Qed.

Lemma monotonicity_join_weak : forall (l1 l2 : slabel),
    l1 <=l l1 |_| l2.
Proof.
    intros.
    rewrite (label_deconstract l1) in *.
    rewrite (label_deconstract l2) in *.
    unfold join. unfold ilv_join, clv_join.
    destruct (conf l1); destruct (integ l1); destruct (conf l2); destruct (integ l2);
    unfold label_le; unfold lv_le; simpl; auto.
Qed.



(* Subtyping *)

Reserved Notation "u1 '<:u' u2" (at level 10).
Reserved Notation "s1 '<:s' s2" (at level 9).

Inductive ut_subtyping : utype -> utype -> Prop :=
    | s_bool  : Bool <:u Bool
    | s_int   : Int <:u Int
    | s_pair  : forall (s1 s2 s1' s2' : stype),
        s1 <:s s1' ->
        s2 <:s s2' ->
        (s1 *s s2) <:u (s1' *s s2')
    | s_fun   : forall (s1 s2 s1' s2' : stype),
        s1' <:s s1 ->
        s2 <:s s2' ->
        (s1 ->s s2) <:u (s1' ->s s2')
with st_subtyping : stype -> stype -> Prop :=
    | s_label : forall (l1 l2 : slabel) (t1 t2 : utype),
        l1 <=l l2 ->
        t1 <:u t2 ->
        [t1 @ty l1] <:s [t2 @ty l2] 
where "s1 <:u s2" := (ut_subtyping s1 s2)
and "s1 <:s s2" := (st_subtyping s1 s2).

Scheme ut_subtyping_mut := Induction for utype Sort Prop
with st_subtyping_mut := Induction for stype Sort Prop.

Combined Scheme subtyping_mut from ut_subtyping_mut, st_subtyping_mut.

Lemma subtyping_refl : (forall (u : utype), u <:u u) /\ (forall (s : stype), s <:s s).
Proof.
    intros.
    apply subtyping_mut; 
    eauto using ut_subtyping, st_subtyping, label_le_refl.
Qed.

Corollary ut_subtyping_refl : forall (u : utype), u <:u u.
Proof.
    destruct subtyping_refl as [L _].
    apply L.
Qed.

Corollary st_subtyping_refl : forall (s : stype), s <:s s.
Proof.
    destruct subtyping_refl as [_ R].
    apply R.
Qed.



(* Typing *)

Definition op_int_type : Type := Z -> Z -> Z.
Definition op_bool_type : Type := Z -> Z -> bool.

Reserved Notation "G |- a , m ':t' s" (at level 30).

Inductive typing : (var -> option stype) -> slabel -> tm -> stype -> Prop :=
    | t_sub     : forall gamma (a : slabel) (m : tm) (s s' : stype),
        gamma |- a, m :t s ->
        s <:s s' ->
        gamma |- a, m :t s'
    | t_true    : forall gamma (a l : slabel),
        l <=i a ->
        gamma |- a, (tm_true l) :t [Bool @ty l]
    | t_false   : forall gamma (a l : slabel),
        l <=i a ->
        gamma |- a, (tm_false l) :t [Bool @ty l]
    | t_if      : forall gamma (a : slabel) (m1 m2 m3 : tm) (t : utype) (l1 l2 : slabel),
        gamma |- a, m1 :t [Bool @ty l1] ->
        gamma |- a, m2 :t [t @ty l2] ->
        gamma |- a, m3 :t [t @ty l2] ->
        gamma |- a, (tm_if m1 m2 m3) :t [t @ty (l1 |_| l2)]
    | t_int     : forall gamma (a : slabel) (n : Z) (l : slabel),
        l <=i a ->
        gamma |- a, (tm_int l n) :t [Int @ty l]
    | t_op_int  : forall gamma (a : slabel) (op_int : op_int_type) (m1 m2 : tm) (e : level) (l1 l2 : slabel),
        gamma |- a, m1 :t [Int @ty l1] ->
        gamma |- a, m2 :t [Int @ty l2] ->
        lv_le e (integ a) ->
        gamma |- a, (tm_op_int e op_int m1 m2) :t [Int @ty (l1 |_| l2 |_| {Low, e})]
    | t_op_bool : forall gamma (a : slabel) (op_bool : op_bool_type) (m1 m2 : tm) (e : level) (l1 l2 : slabel),
        gamma |- a, m1 :t [Int @ty l1] ->
        gamma |- a, m2 :t [Int @ty l2] ->
        lv_le e (integ a) ->
        gamma |- a, (tm_op_bool e op_bool m1 m2) :t [Bool @ty (l1 |_| l2 |_| {Low, e})]
    | t_pair    : forall gamma (a : slabel) (m1 m2 : tm) (s1 s2 : stype) (l : slabel),
        gamma |- a, m1 :t s1 ->
        gamma |- a, m2 :t s2 ->
        l <=i a ->
        gamma |- a, (tm_pair l m1 m2) :t [(s1 *s s2) @ty l]
    | t_proj1   : forall gamma (a : slabel) (m : tm) (u1 : utype) (s2 : stype) (l1 l : slabel),
        gamma |- a, m :t [([u1 @ty l1] *s s2) @ty l] ->
        gamma |- a, (tm_proj1 m) :t [u1 @ty (l1 |_| l)]
    | t_proj2   : forall gamma (a : slabel) (m : tm) (u2 : utype) (s1 : stype) (l2 l : slabel),
        gamma |- a, m :t [(s1 *s [u2 @ty l2]) @ty l] ->
        gamma |- a, (tm_proj2 m) :t [u2 @ty (l2 |_| l)]
    | t_fun     : forall gamma (a : slabel) (m : tm) (s1 s2 : stype) (l : slabel),
        (Some s1 .: gamma) |- a, m :t s2 ->
        l <=i a ->
        gamma |- a, (tm_abs l m s1) :t [(s1 ->s s2) @ty l]
    | t_app     : forall gamma (a : slabel) (m1 m2 : tm) (s1 : stype) (u2 : utype) (l l2: slabel),
        gamma |- a, m1 :t [(s1 ->s [u2 @ty l2]) @ty l] ->
        gamma |- a, m2 :t s1 ->
        gamma |- a, (tm_app m1 m2) :t [u2 @ty (l2 |_| l)]
    | t_var     : forall gamma (a : slabel) (x : var) (s : stype),
        gamma x = Some s ->
        gamma |- a, (tm_var x) :t s
    | t_prot    : forall gamma (a : slabel) (m : tm) (t : utype) (l l' : slabel),
        gamma |- a, m :t [t @ty l] ->
        gamma |- a, (tm_prot l' m) :t [t @ty (l |_| l')]
    | t_decl    : forall gamma (a : slabel) (m : tm) (t : utype) (c : level) (l : slabel),
        gamma |- a, m :t [t @ty l] ->
        lv_le c (conf l) ->
        l <=c a ->
        gamma |- a, (tm_decl c m) :t [t @ty {c, (integ l)}]
where "G |- a , m ':t' s"  := (typing G a m s).

Definition empty_gamma : var -> option stype := (fun (_ : var) => None).

Check (Some ([Int @ty {High, High}]) .: empty_gamma).
Compute ((Some ([Int @ty {High, High}]) .: empty_gamma) 0%nat).

Lemma preserve_subst_value : forall (gamma : var -> option stype) (sigma : var -> tm) (a : slabel) (V : tm) (s : stype),
    value V ->
    gamma |- a, V :t s ->
    (forall (x : var) (s' : stype), gamma x = Some s' -> value (sigma x)) ->
    value V.[sigma].
Proof.
    intros.
    induction H0; simpl; eauto using value; inversion H.
    -   apply v_pair.
        apply IHtyping1. apply H4. apply H1.
        apply IHtyping2. apply H6. apply H1.
Qed.

Lemma preserve_subst_context : forall (gamma : var -> option stype) (sigma : var -> tm) (a : slabel) (D : tm) (s : stype),
    value_context D ->
    gamma |- a, D :t s ->
    (forall (x : var) (s' : stype), gamma x = Some s' -> value (sigma x)) ->
    value D.[sigma].
Proof.
    intros.
    induction H0; simpl; eauto using value, preserve_subst_value; inversion H.
    -   apply v_pair.
        apply IHtyping1. apply value_is_value_context. apply H4. apply H1.
        apply IHtyping2. apply value_is_value_context. apply H6. apply H1.
Qed.


(* Lemma 1 *)
Lemma monotonicity_of_typing : forall gamma (c c' e e' : level) (m : tm) (s : stype),
    gamma |- {c, e}, m :t s -> 
    c <=lv c' -> 
    e <=lv e' ->
    gamma |- {c', e'}, m :t s.
Proof.
    intros.
    remember {c, e} as a.
    induction H; subst; eauto using typing.
    -   apply t_true.
        unfold integ_le in *.
        simpl in *.
        eapply lv_le_trans.
        apply H.
        apply H1.
    -   apply t_false.
        unfold integ_le in *.
        simpl in *.
        eapply lv_le_trans.
        apply H.
        apply H1.
    -   apply t_int.
        unfold integ_le in *.
        simpl in *.
        eapply lv_le_trans.
        apply H.
        apply H1.
    -   apply t_op_int; auto.
        simpl in *.
        eapply lv_le_trans.
        apply H3.
        apply H1.
    -   apply t_op_bool; auto.
        simpl in *.
        eapply lv_le_trans.
        apply H3.
        apply H1.
    -   apply t_pair; auto.
        unfold integ_le in *.
        simpl in *.
        eapply lv_le_trans.
        apply H3.
        apply H1.
    -   apply t_fun.
        +   apply IHtyping.
            reflexivity.
        +   unfold integ_le in *.
            simpl in *.
            eapply lv_le_trans.
            apply H2.
            apply H1.
    -   apply t_decl; auto. 
        unfold conf_le in *.
        simpl in *.
        eapply lv_le_trans.
        apply H3.
        apply H0.
Qed.

Corollary monotonicity_of_typing_HH : forall gamma (a : slabel) (m : tm) (s : stype),
    gamma |- a, m :t s -> 
    gamma |- {High, High}, m :t s.
Proof.
    intros.
    eapply monotonicity_of_typing.
    +   rewrite (label_deconstract a) in H. apply H.
    +   unfold lv_le in *. right. reflexivity.
    +   unfold lv_le in *. right. reflexivity.
Qed.



(* Evaluation *)

Definition value_prot (l : slabel) (m : tm) : tm :=
    match m with
    | tm_true l'        => tm_true (l' |_| l)
    | tm_false l'       => tm_false (l' |_| l)
    | tm_int l' n       => tm_int (l' |_| l) n
    | tm_pair l' m1 m2  => tm_pair (l' |_| l) m1 m2
    | tm_abs l' m1 s  => tm_abs (l' |_| l) m1 s
    | _ => m
    end.
    
Definition value_dec (c : level) (m : tm) : tm :=
    match m with
    | tm_true l => tm_true {c, integ l}
    | tm_false l => tm_false {c, integ l}
    | tm_int l n => tm_int {c, integ l} n
    | tm_pair l m1 m2 => tm_pair {c, integ l} m1 m2
    | tm_abs l m1 s => tm_abs {c, integ l} m1 s
    | _ => m
    end.

Inductive e_ctx : Type :=
    | c_hole        : e_ctx
    | c_if          : e_ctx -> tm -> tm -> e_ctx
    | c_pair1       : slabel -> e_ctx -> tm -> e_ctx
    | c_pair2       : forall (l : slabel) (v : tm) (E : e_ctx), value v -> e_ctx
    | c_proj1       : e_ctx -> e_ctx
    | c_proj2       : e_ctx -> e_ctx
    | c_app1        : e_ctx -> tm -> e_ctx
    | c_app2        : forall (v : tm) (E : e_ctx), value v -> e_ctx
    | c_op_int1     : level -> op_int_type -> e_ctx -> tm -> e_ctx
    | c_op_int2     : forall (l : level) (op : op_int_type) (v : tm) (E : e_ctx), value v -> e_ctx
    | c_op_bool1    : level -> op_bool_type -> e_ctx -> tm -> e_ctx
    | c_op_bool2    : forall (l : level) (op : op_bool_type) (v : tm) (E : e_ctx), value v -> e_ctx
    | c_prot        : slabel -> e_ctx -> e_ctx
    | c_decl        : level -> e_ctx -> e_ctx.

Compute (tm_var 0%nat).[ren S].

Fixpoint e_ctx_to_tm (E : e_ctx) : tm :=
    match E with
    | c_hole                    => tm_var 0%nat
    | c_if E m2 m3              => tm_if (e_ctx_to_tm E) m2.[ren S] m3.[ren S]
    | c_pair1 l E m2            => tm_pair l (e_ctx_to_tm E) m2.[ren S]
    | c_pair2 l v E Hv          => tm_pair l v.[ren S] (e_ctx_to_tm E)
    | c_proj1 E                 => tm_proj1 (e_ctx_to_tm E)
    | c_proj2 E                 => tm_proj2 (e_ctx_to_tm E)
    | c_app1 E m2               => tm_app (e_ctx_to_tm E) m2.[ren S]
    | c_app2 v E Hv             => tm_app v.[ren S] (e_ctx_to_tm E)
    | c_op_int1 e op E m2       => tm_op_int e op (e_ctx_to_tm E) m2.[ren S]
    | c_op_int2 e op v E Hv     => tm_op_int e op v.[ren S] (e_ctx_to_tm E)
    | c_op_bool1 l op E m2      => tm_op_bool l op (e_ctx_to_tm E) m2.[ren S]
    | c_op_bool2 l op v E Hv    => tm_op_bool l op v.[ren S] (e_ctx_to_tm E)
    | c_prot l E                => tm_prot l (e_ctx_to_tm E)
    | c_decl c E                => tm_decl c (e_ctx_to_tm E)
    end.

Definition fill (E : e_ctx) (m : tm) : tm :=
    (e_ctx_to_tm E).[m .: ids].

Compute (e_ctx_to_tm (c_app1 c_hole (tm_app (tm_var 0%nat) (tm_var 1%nat)))).

Compute (fill (c_app1 c_hole (tm_app (tm_var 0%nat) (tm_var 1%nat))) (tm_true {High, High})).

Reserved Notation "m '==>' m'" (at level 40).

Inductive Eval : tm -> tm -> Prop :=
    | e_iftrue  : forall (l : slabel) (m1 m2 : tm),
        (tm_if (tm_true l) m1 m2) ==> (tm_prot l m1)
    | e_iffalse : forall (l : slabel) (m1 m2 : tm),
        (tm_if (tm_false l) m1 m2) ==> (tm_prot l m2)
    | e_op_int  : forall (l1 l2 : slabel) (op_int : op_int_type) (n n1 n2 : Z) (e : level),
        n = (op_int n1 n2) ->
        (tm_op_int e op_int (tm_int l1 n1) (tm_int l2 n2)) ==> (tm_int (l1 |_| l2 |_| {Low, e}) n)
    | e_op_true : forall (l1 l2 : slabel) (op_bool : op_bool_type) (n1 n2 : Z) (b : bool) (e : level),
        (op_bool n1 n2) = true ->
        (tm_op_bool e op_bool (tm_int l1 n1) (tm_int l2 n2)) ==> (tm_true (l1 |_| l2 |_| {Low, e}))
    | e_op_false : forall (l1 l2 : slabel) (op_bool : op_bool_type) (n1 n2 : Z) (b : bool) (e : level),
        (op_bool n1 n2) = false ->
        (tm_op_bool e op_bool (tm_int l1 n1) (tm_int l2 n2)) ==> (tm_false (l1 |_| l2 |_| {Low, e}))
    | e_proj1   : forall (l : slabel) (m1 m2 : tm),
        value m1 -> value m2 ->
        (tm_pair l m1 m2) ==> (tm_prot l m1)
    | e_proj2   : forall (l : slabel) (m1 m2 : tm),
        value m1 -> value m2 ->
        (tm_pair l m1 m2) ==> (tm_prot l m2)
    | e_app     : forall (l : slabel) (s : stype) (m1 m2 : tm),
        value m2 ->
        (tm_app (tm_abs l m1 s) m2) ==> (tm_prot l (m1.[m2 .: ids]))
    | e_prot    : forall (l : slabel) (m : tm),
        value m ->
        (tm_prot l m) ==> (value_prot l m)
    | e_decl    : forall (c : level) (m : tm),
        value m ->
        (tm_decl c m) ==> (value_dec c m)
    | e_con     : forall (E : e_ctx) (m m' : tm),
        m ==> m' ->
        (fill E m) ==> (fill E m)
where "m '==>' m'" := (Eval m m').

Reserved Notation "m '==>*' m'" (at level 40).

Inductive multi : tm -> tm -> Prop :=
    | multi_refl    : forall (m : tm),
        m ==>* m
    | multi_step    : forall (m1 m2 m3 : tm),
        m1 ==> m2 ->
        m2 ==>* m3 ->
        m1 ==>* m3
where "m '==>*' m'" := (multi m m').

Definition subst_typing (gamma gamma' : var -> option stype) (sigma : var -> tm) (a : slabel) : Prop :=
    forall (x : var) (s : stype),
    gamma x = Some s ->
    gamma' |- a, (sigma x) :t s.

Lemma subst_rename : forall (gamma gamma' : var -> option stype) (i : var -> var) (m : tm) (s : stype) (a : slabel),
    gamma |- a, m :t s ->
    (forall x s0, gamma x = Some s0 -> gamma' (i x) = Some s0) ->
    gamma' |- a, m.[ren i] :t s.
Proof.
    intros.
    generalize dependent gamma'.
    generalize dependent i.
    induction H; intros; simpl; asimpl; eauto using typing.
    -   apply t_fun.
        apply IHtyping. intros.
        destruct x; inversion H2; asimpl.
        *   reflexivity.
        *   rewrite (H1 x s0).
            rewrite <- H4.
            reflexivity.
            apply H4.
        *   apply H0.
Qed.

Lemma subst_typing_up : forall (gamma gamma' : var -> option stype) (sigma : var -> tm) (a : slabel) (s : stype),
    subst_typing gamma gamma' sigma a ->
    subst_typing (Some s .: gamma) (Some s .: gamma') (up sigma) a.
Proof.
    unfold subst_typing in *.
    intros.
    destruct x.
    -   inversion H0. 
        apply t_var. 
        simpl. reflexivity.
    -   inversion H0.
        asimpl.
        eapply subst_rename.
        apply H. apply H2.
        intros. simpl. apply H1.
Qed.

Lemma substitution_lemma : forall (gamma gamma' : var -> option stype) (a : slabel) (sigma : var -> tm) (C : tm) (s : stype),
    subst_typing gamma gamma' sigma {High, High} ->
    gamma |- a, C :t s ->
    gamma' |- {High, High}, C.[sigma] :t s.
Proof.
    intros.
    generalize dependent sigma.
    generalize dependent gamma'.
    induction H0; intros; eauto using typing, integ_le_HH.
    -   apply t_op_int.
        apply IHtyping1. apply H0.
        apply IHtyping2. apply H0.
        simpl. unfold lv_le. right. reflexivity.
    -   apply t_op_bool.
        apply IHtyping1. apply H0.
        apply IHtyping2. apply H0.
        simpl. unfold lv_le. right. reflexivity.
    -   apply t_fun.
        apply IHtyping.
        apply subst_typing_up. apply H1.
        apply integ_le_HH.
    -   apply t_decl.
        apply IHtyping. apply H2.
        apply H.
        apply conf_le_HH.
Qed.

(* Lemma 2 *)
Corollary substitution_lemma_empty_gamma : forall (gamma : var -> option stype) (a : slabel) (sigma : var -> tm) (C : tm) (s : stype),
    subst_typing gamma empty_gamma sigma {High, High} ->
    gamma |- a, C :t s ->
    empty_gamma |- {High, High}, C.[sigma] :t s.
Proof.
    intros.
    apply (substitution_lemma gamma empty_gamma a sigma C s H H0).
Qed.


(* Definitions of closures *)

Record tvr_elm_raw :=
    {
        V1      : tm;
        V2      : tm;
        Rtype   : stype;
    }.

Check 
    {| 
        V1 := tm_true {High, High};
        V2 := tm_false {High, High};
        Rtype := [Bool @ty {High, High}]    
    |}.

Definition condition_tvr (r : tvr_elm_raw) : Prop :=
    value r.(V1) /\
    value r.(V2) /\
    empty_gamma |- {High, High}, r.(V1) :t r.(Rtype) /\
    empty_gamma |- {High, High}, r.(V2) :t r.(Rtype).


(* Definition 5 *)
Record tvr_elm :=
    {
        tri         : tvr_elm_raw;
        Rcondition  : condition_tvr tri
    }.

Check tvr_elm.

Example tvr_elm_1 : tvr_elm.
Proof.
    refine 
    {|
        tri := 
            {|
            V1 := tm_true {High, High};
            V2 := tm_true {High, High};
            Rtype := [Bool @ty {High, High}]
            |};
        Rcondition := _
    |}.
    -   split; simpl. apply v_true.
        split. apply v_true.
        split. apply t_true. apply integ_le_HH.
        apply t_true. apply integ_le_HH.
Qed.

Check Rcondition tvr_elm_1.

Print tvr_elm_1.

(* Typed value relation *)
Definition TVR : Type := tvr_elm -> Prop.


Definition value_label (v : tm) : slabel :=
    match v with
    | tm_true l         => l
    | tm_false l        => l
    | tm_int l n        => l
    | tm_pair l v1 v2   => l
    | tm_abs l m s      => l
    | _ => {Low, Low}
    end.


(* Lemma 6 *)
Lemma label_relation : forall (gamma : var -> option stype) (v : tm) (a : slabel) (s : stype),
    value v ->
    gamma |- a, v :t s ->
    forall (u : utype) (l : slabel),
    s = [u @ty l] ->
    (value_label v) <=l l.
Proof.
    intros gamma v a s H H0.
    induction H0; intros; subst.
    -   inversion H1; subst.
        assert (Hm : value_label m <=l l1).
        {
            apply (IHtyping H t1 l1).
            reflexivity.   
        }
        eapply label_le_trans.
        apply Hm. apply H5.
    -   inversion H1. simpl.
        apply label_le_refl.
    -   inversion H1. simpl.
        apply label_le_refl.
    -   inversion H.
    -   inversion H1. simpl.
        apply label_le_refl.
    -   inversion H.
    -   inversion H.
    -   inversion H1. simpl.
        apply label_le_refl.
    -   inversion H.
    -   inversion H.
    -   inversion H2. simpl.
        apply label_le_refl.
    -   inversion H.
    -   inversion H.
    -   inversion H.
    -   inversion H.
Qed.

Lemma env_label_relation : forall (R : TVR) (r : tvr_elm),
    R r ->
    forall (u : utype) (l : slabel), r.(tri).(Rtype) = [u @ty l] ->
    value_label (r.(tri).(V1)) <=l l /\ (value_label (r.(tri).(V2))) <=l l.
Proof.
    intros.
    destruct r.(Rcondition) as [H1 [H2 [H3 H4]]].
    split;
    generalize dependent H0; generalize dependent l; generalize dependent u;
    eapply label_relation.
    apply H1. apply H3.
    apply H2. apply H4.
Qed.


Record quadraple_raw :=
    {
        Rx      : TVR;
        M1      : tm;
        M2      : tm;
        Xtype   : stype;
    }.

Definition condition_quad (q : quadraple_raw) :=
    empty_gamma |- {High, High}, q.(M1) :t q.(Xtype) /\
    empty_gamma |- {High, High}, q.(M2) :t q.(Xtype).


(* Definition 7 *)
Record quadraple :=
    {
        quad        : quadraple_raw;
        Xcondition  : condition_quad quad
    }.

Inductive elm : Type :=
    | elm_R     : TVR -> elm
    | elm_quad  : quadraple -> elm.

Definition ER : Type := elm -> Prop.


Definition unlabeled_value (v : tm) : (slabel -> tm) :=
    match v with
    | tm_true l         => (fun l => tm_true l)
    | tm_false l        => (fun l => tm_false l)
    | tm_int l n        => (fun l => tm_int l n)
    | tm_pair l m1 m2   => (fun l => tm_pair l m1 m2)
    | tm_abs l m s      => (fun l => tm_abs l m s)
    | _                 => (fun _ => v)
    end.

Definition value_label_le (v1 v2 : tm) : Prop :=
    value v1 /\
    value v2 /\
    unlabeled_value v1 = unlabeled_value v2 /\
    value_label v1 <=l value_label v2.

Definition type_label_le (s1 s2 : stype) : Prop :=
    forall (u1 u2 : utype) (l1 l2 : slabel),
        s1 = [u1 @ty l1] /\ 
        s2 = [u2 @ty l2] /\
        u1 = u2 /\
        l1 <=l l2.

Definition u_condition (r : tvr_elm_raw) : Prop :=
    forall (u : utype) (l : slabel),
        r.(Rtype) = [u @ty l] /\
        value_label r.(V1) <=l l /\
        value_label r.(V2) <=l l.

Definition tvr_le  (r1 r2 : tvr_elm_raw) : Prop :=
    value_label_le r1.(V1) r2.(V1) /\
    value_label_le r1.(V2) r2.(V2) /\
    type_label_le r1.(Rtype) r2.(Rtype) /\
    u_condition r2.
        
Notation "R1 '<=r' R2" := (tvr_le R1 R2) (at level 10).


(* Definition 8 *)
Definition upward_closure_raw (R : TVR) (r' : tvr_elm_raw) : Prop :=
    exists (r : tvr_elm),
        R r /\ r.(tri) <=r r'.

Lemma destruct_value : forall (v : tm),
    value v ->
    unlabeled_value v (value_label v) = v.
Proof.
    intros.
    destruct v; inversion H; simpl; reflexivity.
Qed.

Lemma shift_label : forall (gamma : var -> option stype) (v : tm) (s : stype) (a l': slabel),
    value v ->
    gamma |- a, v :t s ->
    forall (u : utype) (l : slabel), s = [u @ty l] ->
    gamma |- a, (unlabeled_value v ((value_label v) |_| l')) :t [u @ty l |_| l'].
Proof.
    intros.
    generalize dependent u; generalize dependent l.
    induction H0.
    -   intros. 
        destruct s as [us ls]. subst.
        inversion H1; subst.
        eapply t_sub.
        +   apply (IHtyping H ls us). reflexivity.
        +   apply s_label.
            apply (monotonicity_join ls l l' H5).
            apply H7.
    -   intros. simpl. inversion H1; subst. apply t_true.
        apply monotonicity_integ_join. apply H0.
    -   intros. simpl. inversion H1; subst. apply t_false.
        apply monotonicity_integ_join. apply H0.
    -   inversion H.
    -   intros. simpl. inversion H1; subst. apply t_int.
        apply monotonicity_integ_join. apply H0.
    -   inversion H.
    -   inversion H.
    -   intros. simpl. inversion H1; subst. apply t_pair.
        apply H0_. apply H0_0.
        apply monotonicity_integ_join. apply H0.
    -   inversion H.
    -   inversion H.
    -   intros. simpl. inversion H2; subst. apply t_fun.
        apply H0.
        apply monotonicity_integ_join. apply H1.
    -   inversion H.
    -   inversion H.
    -   inversion H.
    -   inversion H.
Qed.

Lemma join_le_1 : forall (l1 l2 : slabel),
    l1 <=l l2 -> l1 |_| l2 = l2.
Proof.
    intros.
    rewrite (label_deconstract l1) in *.
    rewrite (label_deconstract l2) in *.
    unfold label_le, join in *. unfold lv_le, clv_join, ilv_join in *.
    destruct (conf l1), (integ l1), (conf l2), (integ l2); 
    simpl; destruct H as [[HL | HL] [HR | HR]]; destruct HL; destruct HR; auto.
Qed. 

Lemma join_le_2 : forall (l1 l2 l: slabel),
    l1 <=l l -> l2 <=l l -> l1 |_| l2 <=l l.
Proof.
    intros.
    rewrite (label_deconstract l1) in *.
    rewrite (label_deconstract l2) in *.
    rewrite (label_deconstract l) in *.
    unfold join. unfold clv_join, ilv_join.
    destruct (conf l); destruct (integ l); destruct (conf l1); destruct (integ l1); destruct (conf l2); destruct (integ l2); simpl;
    eauto using label_le_refl, label_le_trans; unfold label_le in *; unfold lv_le in *; 
    destruct H as [[HL | HL] [HR | HR]]; destruct HL; destruct HR; destruct H0; auto.
Qed.


(* Lemma 9 *)
Lemma Rup_is_R : forall (R : TVR) (r' : tvr_elm_raw),
    upward_closure_raw R r' ->
    condition_tvr r'.
Proof.
    intros.
    unfold upward_closure_raw in H.
    unfold tvr_le in H.
    destruct H as [r [H1 [H2 [H3 H4]]]].
    destruct (r.(Rcondition)) as [H5 [H6 [H7 H8]]].
    unfold value_label_le in *.
    destruct H2 as [H21 [H22 [H23 H24]]].
    destruct H3 as [H31 [H32 [H33 H34]]].
    unfold type_label_le in H4.
    destruct (r.(tri).(Rtype)) as [u1 l1] eqn:Eq1.
    destruct (r'.(Rtype)) as [u2 l2] eqn:Eq2.
    unfold u_condition in H4.
    destruct H4 as [H4' H4''].
    destruct (H4' u1 u2 l1 l2) as [H41 [H42 [H43 H44]]].
    destruct (H4'' u2 l2) as [H45 [H46 H47]]. 
    unfold condition_tvr.
    split.
    -   apply H22.
    -   split.
        +   apply H32.
        +   split.
            *   assert (Ha : empty_gamma |- {High, High}, r'.(V1) :t [u2 @ty l1 |_| (value_label r'.(V1))]).
                {   
                    remember (value_label r'.(V1)) as lr' eqn:E.
                    rewrite <- (destruct_value r'.(V1) H22).
                    rewrite <- H43.
                    rewrite <- H23.
                    simpl.
                    rewrite <- (join_le_1 (value_label (r.(tri).(V1))) (value_label (r'.(V1)))).
                    rewrite -> E in *.
                    eapply shift_label.
                    apply H21. apply H7. reflexivity. rewrite E in H24. apply H24.
                }
                eapply t_sub.
                --  apply Ha.
                --  rewrite Eq2. apply s_label. apply join_le_2. apply H44. apply H46.
                    apply ut_subtyping_refl.
            *   assert (Ha : empty_gamma |- {High, High}, r'.(V2) :t [u2 @ty l1 |_| (value_label r'.(V2))]).
                {
                    remember (value_label r'.(V2)) as lr' eqn:E.
                    rewrite <- (destruct_value r'.(V2) H32).
                    rewrite <- H43.
                    rewrite <- H33.
                    simpl.
                    rewrite <- (join_le_1 (value_label (r.(tri).(V2))) (value_label (r'.(V2)))).
                    rewrite -> E in *.
                    eapply shift_label.
                    apply H31. apply H8. reflexivity. rewrite E in H34. apply H34.
                }
                eapply t_sub.
                --  apply Ha.
                --  rewrite Eq2. apply s_label. apply join_le_2. apply H44. apply H47.
                    apply ut_subtyping_refl.
Qed.

Definition build_upward_tvr (R : TVR) (r : tvr_elm) (r' : tvr_elm_raw) (H_R : R r) (H_le : r.(tri) <=r r') : tvr_elm :=
    {|
        tri := r';
        Rcondition := Rup_is_R R r' (ex_intro (fun r0 => R r0 /\ r0.(tri) <=r r') r (conj H_R H_le))
    |}.

Definition upward_closure (R : TVR) (r : tvr_elm) : Prop :=
    exists (r0 : tvr_elm) 
    (H : R r0) (H' : r0.(tri) <=r r.(tri)),
    r.(tri) = (build_upward_tvr R r0 r.(tri) H H').(tri).


Definition S_context_closure_raw (R : TVR) (a : slabel) (r' : tvr_elm_raw) :=
	exists (gamma : var -> option stype) (sigma sigma' : var -> tm) (D : tm) (s : stype),
		value_context D /\
		subst_typing gamma empty_gamma sigma {High, High} /\
		subst_typing gamma empty_gamma sigma' {High, High} /\
		gamma |- a, D :t s /\
		(
			forall (x : var) (v v' : tm) (s : stype),
				gamma x = Some s ->
				sigma x = v /\ sigma' x = v' /\
				value v /\ value v' /\
				upward_closure_raw R {|V1 := v; V2 := v'; Rtype := s|}
		) /\
		r' = {| V1 := D.[sigma]; V2 := D.[sigma']; Rtype := s |}.

Lemma S_context_closure_is_R : forall (R : TVR) (a : slabel) (r' : tvr_elm_raw),
    S_context_closure_raw R a r' ->
    condition_tvr r'.
Proof.
    intros.
    unfold S_context_closure_raw in H.
    destruct H as [gamma [sigma [sigma' [D [s [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]].
    unfold condition_tvr.
    split; rewrite -> H6; simpl.
    -   eapply preserve_subst_context. apply H1. apply H4.
        intros. destruct (H5 x (sigma x) (sigma' x) s') as [H51 [H52 [H53 [H54 H55]]]].
        apply H. apply H53.
    -   split.
        +   eapply preserve_subst_context. apply H1. apply H4.
            intros. destruct (H5 x (sigma x) (sigma' x) s') as [H51 [H52 [H53 [H54 H55]]]].
            apply H. apply H54.
        +   split.
            *   eapply substitution_lemma. apply H2. apply H4.
            *   eapply substitution_lemma. apply H3. apply H4.
Qed.

Definition build_context_tvr 
    (R : TVR) (a : slabel) (r' : tvr_elm_raw) (gamma : var -> option stype) (sigma sigma' : var -> tm) (D : tm) (s : stype)
    (Hc     : value_context D)
    (Hst1   : subst_typing gamma empty_gamma sigma {High, High})
    (Hst2   : subst_typing gamma empty_gamma sigma' {High, High})
    (Ht     : gamma |- a, D :t s)
    (Hr     : forall (x : var) (v v' : tm) (s : stype),
				gamma x = Some s ->
				sigma x = v /\ sigma' x = v' /\
				value v /\ value v' /\
				upward_closure_raw R {|V1 := v; V2 := v'; Rtype := s|})
    (He    : r' = {| V1 := D.[sigma]; V2 := D.[sigma']; Rtype := s |}) 
    : tvr_elm :=
    {|
        tri := r';
        Rcondition := S_context_closure_is_R R a r' 
            (ex_intro _ gamma
            (ex_intro _ sigma
            (ex_intro _ sigma'
            (ex_intro _ D
            (ex_intro _ s
            (conj Hc (conj Hst1 (conj Hst2 (conj Ht (conj Hr He)))))
            )))))
    |}.

Definition S_context_closure (R : TVR) (a : slabel) (r : tvr_elm) : Prop :=
    exists (gamma : var -> option stype) (sigma sigma' : var -> tm) (D : tm) (s : stype)
        (Hc     : value_context D)
        (Hst1   : subst_typing gamma empty_gamma sigma {High, High})
        (Hst2   : subst_typing gamma empty_gamma sigma' {High, High})
        (Ht     : gamma |- a, D :t s)
        (Hr     : forall (x : var) (v v' : tm) (s : stype),
                    gamma x = Some s ->
                    sigma x = v /\ sigma' x = v' /\
                    value v /\ value v' /\
                    upward_closure_raw R {|V1 := v; V2 := v'; Rtype := s|})
        (He    : r.(tri) = {| V1 := D.[sigma]; V2 := D.[sigma']; Rtype := s |}),
        r.(tri) = (build_context_tvr R a r.(tri) gamma sigma sigma' D s Hc Hst1 Hst2 Ht Hr He).(tri).


(* Definition 10 *)
Definition context_closure (R : TVR) (a : slabel) : tvr_elm -> Prop :=
    upward_closure (S_context_closure R a).


Definition value_label_shift (v : tm) (l : slabel) : tm :=
    (unlabeled_value v) ((value_label v) |_| l).

Lemma value_label_shift_value : forall (v : tm) (l : slabel),
    value v ->
    value (value_label_shift v l).
Proof.
    intros.
    unfold value_label_shift.
    destruct v; inversion H; simpl; eauto using value.
Qed.

Definition S_if_closure_raw_right (R : TVR) (a : slabel) (r' : tvr_elm_raw) : Prop :=
    exists (v v' w w' dw dw' : tm) (u : utype) (l lb : slabel),
    (value v /\ value v') /\
    (value w /\ value w') /\
    (upward_closure_raw R) {| V1 := v; V2 := v'; Rtype := [Bool @ty lb] |} /\
    (unlabeled_value v) <> (unlabeled_value v') /\
    not ((conf l) <=lv (conf a)) /\
    (upward_closure_raw (S_context_closure R a)) {| V1 := w; V2 := dw; Rtype := [u @ty l]|} /\
    (upward_closure_raw (S_context_closure R a)) {| V1 := dw'; V2 := w'; Rtype := [u @ty l]|} /\
    r' = {| V1 := value_label_shift w (value_label v); V2 := value_label_shift w' (value_label v'); Rtype := [u @ty (l |_| lb)]|}.

Lemma S_if_closure_raw_right_is_R : forall (R : TVR) (a : slabel) (r' : tvr_elm_raw),
    S_if_closure_raw_right R a r' ->
    condition_tvr r'.
Proof.
    intros.
    unfold S_if_closure_raw_right in H.
    destruct H as [v [v' [w [w' [dw [dw' [u [l [lb [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]]]]]]]]].
    destruct H1 as [H1L H1R].
    destruct H2 as [H2L H2R].
    rewrite H8.
    unfold condition_tvr; simpl.
    split.
    -   apply value_label_shift_value. apply H2L.
    -   split.
        +   apply value_label_shift_value. apply H2R.
        +   split.
            *   destruct (Rup_is_R R {| V1 := v; V2 := v'; Rtype := [Bool @ty lb] |} H3) as [_ [_ [H33 _]]].
                destruct (Rup_is_R (S_context_closure R a) {| V1 := w; V2 := dw; Rtype := [u @ty l] |} H6) as [_ [_ [H63 _]]].
                simpl in *.
                assert (Hvlb : (value_label v) <=l lb).
                {
                    eapply (label_relation empty_gamma v {High, High} [Bool @ty lb] H1L H33).
                    reflexivity.
                }
                unfold value_label_shift.
                assert (Hwv : empty_gamma |- {High, High}, unlabeled_value w (value_label w |_| value_label v) :t [u @ty l |_| (value_label v)]).
                {
                    eapply shift_label.
                    apply H2L. apply H63. reflexivity.
                }
                eapply t_sub.
                apply Hwv. apply s_label.
                rewrite (join_comm l (value_label v)).
                rewrite (join_comm l lb).
                apply monotonicity_join. apply Hvlb.
                apply ut_subtyping_refl.
            *   destruct (Rup_is_R R {| V1 := v; V2 := v'; Rtype := [Bool @ty lb] |} H3) as [_ [_ [_ H34]]].
                destruct (Rup_is_R (S_context_closure R a) {| V1 := dw'; V2 := w'; Rtype := [u @ty l] |} H7) as [_ [_ [_ H74]]].
                simpl in *.
                assert (Hv'lb : (value_label v') <=l lb).
                {
                    eapply (label_relation empty_gamma v' {High, High} [Bool @ty lb] H1R H34).
                    reflexivity.
                }
                unfold value_label_shift.
                assert (Hw'v' : empty_gamma |- {High, High}, unlabeled_value w' (value_label w' |_| value_label v') :t [u @ty l |_| (value_label v')]).
                {
                    eapply shift_label.
                    apply H2R. apply H74. reflexivity.
                }
                eapply t_sub.
                apply Hw'v'. apply s_label.
                rewrite (join_comm l (value_label v')).
                rewrite (join_comm l lb).
                apply monotonicity_join. apply Hv'lb.
                apply ut_subtyping_refl.
Qed.

Definition build_if_tvr 
    (R : TVR) (a : slabel) (r' : tvr_elm_raw) (v v' w w' dw dw' : tm) (u : utype) (l lb : slabel)
    (Hv     : value v /\ value v')
    (Hw     : value w /\ value w')
    (Hvr    : (upward_closure_raw R) {| V1 := v; V2 := v'; Rtype := [Bool @ty lb] |})
    (Hneq   : (unlabeled_value v) <> (unlabeled_value v'))
    (Hnle   : not ((conf l) <=lv (conf a)))
    (Hwctx  : (upward_closure_raw (S_context_closure R a)) {| V1 := w; V2 := dw; Rtype := [u @ty l]|})
    (Hw'ctx : (upward_closure_raw (S_context_closure R a)) {| V1 := dw'; V2 := w'; Rtype := [u @ty l]|})
    (He     : r' = {| V1 := value_label_shift w (value_label v); V2 := value_label_shift w' (value_label v'); Rtype := [u @ty (l |_| lb)]|})
    : tvr_elm :=
    {|
        tri := r';
        Rcondition :=
            S_if_closure_raw_right_is_R R a r'
            (ex_intro _ v (ex_intro _ v' (ex_intro _ w (ex_intro _ w' (ex_intro _ dw (ex_intro _ dw'
            (ex_intro _ u
            (ex_intro _ l (ex_intro _ lb
            (conj Hv (conj Hw (conj Hvr (conj Hneq (conj Hnle (conj Hwctx (conj Hw'ctx He))))))))
            ))))))))
    |}.

Definition S_if_closure_right (R : TVR) (a : slabel) (r : tvr_elm) : Prop :=
    exists (v v' w w' dw dw' : tm) (u : utype) (l lb : slabel)
        (Hv     : value v /\ value v')
        (Hw     : value w /\ value w')
        (Hvr    : (upward_closure_raw R) {| V1 := v; V2 := v'; Rtype := [Bool @ty lb] |})
        (Hneq   : (unlabeled_value v) <> (unlabeled_value v'))
        (Hnle   : not ((conf l) <=lv (conf a)))
        (Hwctx  : (upward_closure_raw (S_context_closure R a)) {| V1 := w; V2 := dw; Rtype := [u @ty l]|})
        (Hw'ctx : (upward_closure_raw (S_context_closure R a)) {| V1 := dw'; V2 := w'; Rtype := [u @ty l]|})
        (He     : r.(tri) = {| V1 := value_label_shift w (value_label v); V2 := value_label_shift w' (value_label v'); Rtype := [u @ty (l |_| lb)]|}),
    r.(tri) = (build_if_tvr R a r.(tri) v v' w w' dw dw' u l lb Hv Hw Hvr Hneq Hnle Hwctx Hw'ctx He).(tri).

Definition S_if_closure (R : TVR) (a : slabel) (r : tvr_elm) : Prop :=
    (R r) \/ (S_if_closure_right R a r).


(* Definition 12 *)
Definition if_closure (R : TVR) (a : slabel) : tvr_elm -> Prop :=
    context_closure (S_if_closure R a) a.


Definition X_arrow_quad (X : ER) (q : quadraple) : Prop :=
    exists (q' : quadraple_raw) (q0 : quadraple)
    (Hx     : X (elm_quad q0))
    (Ht     : q'.(Xtype) = q0.(quad).(Xtype))
    (Hty1   : empty_gamma |- {High, High}, q'.(M1) :t q'.(Xtype))
    (Hty2   : empty_gamma |- {High, High}, q'.(M2) :t q'.(Xtype))
    (Hm1    : q'.(M1) ==>* q0.(quad).(M1))
    (Hm2    : q'.(M2) ==>* q0.(quad).(M2)),
    q.(quad) =
        {|
            quad := q';
            Xcondition := conj Hty1 Hty2
        |}.(quad).

Definition X_arrow_tvr (X : ER) (q : quadraple) : Prop :=
    exists (R : TVR) (r : tvr_elm) (q' : quadraple_raw)
    (HXR    : X (elm_R R))
    (HRr    : R r)
    (HXRx   : X (elm_R q'.(Rx)))
    (Ht     : q'.(Xtype) = r.(tri).(Rtype))
    (Hty1   : empty_gamma |- {High, High}, q'.(M1) :t q'.(Xtype))
    (Hty2   : empty_gamma |- {High, High}, q'.(M2) :t q'.(Xtype))
    (Hm1    : q'.(M1) ==>* r.(tri).(V1))
    (Hm2    : q'.(M2) ==>* r.(tri).(V2)),
    q.(quad) =
        {|
            quad := q';
            Xcondition := conj Hty1 Hty2
        |}.(quad).

Definition X_arrow (X : ER) (q : quadraple) : Prop :=
    X_arrow_quad X q \/ X_arrow_tvr X q.


Definition condition_tvr_weak (r' : tvr_elm_raw) : Prop :=
    empty_gamma |- {High, High}, r'.(V1) :t r'.(Rtype) /\
    empty_gamma |- {High, High}, r'.(V2) :t r'.(Rtype).

Definition if_closure_tm (R : TVR) (a : slabel) (r' : tvr_elm_raw) : Prop :=
    exists (gamma gamma0 : var -> option stype) (sigma sigma' sigma0 sigma0' : var -> tm) (C : tm) (s: stype),
        subst_typing gamma gamma0 sigma {High, High} /\
        subst_typing gamma gamma0 sigma' {High, High} /\
        subst_typing gamma0 empty_gamma sigma0 {High, High} /\
        subst_typing gamma0 empty_gamma sigma0' {High, High} /\
        gamma |- a, C :t s /\
        (
            forall (x : var) (s : stype),
                gamma x = Some s ->
                gamma0 x = None ->
                upward_closure_raw R {|V1 := sigma x; V2 := sigma' x; Rtype := s|}
        ) /\
        (
            forall (x : var) (s : stype),
                gamma0 x = Some s ->
                exists (v v' : tm) (u : utype) (l l'' : slabel) (r r0 : tvr_elm),
                    upward_closure_raw R {|V1 := v; V2 := v'; Rtype := [Bool @ty l'']|} /\
                    unlabeled_value v <> unlabeled_value v' /\
                    ~ (conf l'') <=lv (conf a) /\
                    context_closure R a r /\
                    context_closure R a r0 /\
                    r.(tri).(Rtype) = [u @ty l] /\
                    r0.(tri).(Rtype) = [u @ty l] /\
                    {|V1 := sigma0 x; V2 := sigma0' x; Rtype := s|} 
                        <=r {|V1 := value_label_shift r.(tri).(V1) (value_label v); V2 := value_label_shift r0.(tri).(V2) (value_label v'); Rtype := [u @ty (l |_| l'')]|}
        ) /\
        r' = {|V1 := (C.[sigma]).[sigma0]; V2 := (C.[sigma']).[sigma0']; Rtype := s|}.

Lemma condition_if_closure_tm : forall (R : TVR) (a : slabel) (r' : tvr_elm_raw),
    if_closure_tm R a r' ->
    condition_tvr_weak r'.
Proof.
    intros.
    unfold if_closure_tm in H.
    destruct H as [gamma [gamma0 [sigma [sigma' [sigma0 [sigma0' [C [s H]]]]]]]].
    destruct H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
    unfold condition_tvr_weak. rewrite H8. simpl.
    split; eauto using substitution_lemma.
Qed.

Lemma type_preservation_closed_context : forall (E : e_ctx) (a : slabel) (s s0 : stype) (m : tm),
    empty_gamma |- {High, High}, m :t s0 -> 
    (Some s0 .: empty_gamma) |- a, e_ctx_to_tm E :t s ->
    empty_gamma |- {High, High}, (fill E m) :t s.
Proof.
    intros.
    apply (substitution_lemma_empty_gamma (Some s0 .: empty_gamma) a).
    -   unfold subst_typing. intros.
        destruct x.
        +   simpl in H1. inversion H1; subst. apply H.
        +   simpl in H1. unfold empty_gamma in H1. inversion H1.
    -   apply H0.   
Qed.

Definition condition_tvr_weak_ctx (s : stype) (r' : tvr_elm_raw) : Prop :=
    (Some s .: empty_gamma) |- {High, High}, r'.(V1) :t r'.(Rtype) /\
    (Some s .: empty_gamma) |- {High, High}, r'.(V2) :t r'.(Rtype).

Definition if_closure_e_ctx (R : TVR) (a : slabel) (t : stype) (r' : tvr_elm_raw) : Prop :=
    exists (gamma gamma0 : var -> option stype) (sigma sigma' sigma0 sigma0' : var -> tm) (C : tm) (s: stype) (E E' : e_ctx),
        subst_typing gamma gamma0 (up sigma) {High, High} /\
        subst_typing gamma gamma0 (up sigma') {High, High} /\
        subst_typing gamma0 (Some t .: empty_gamma) (up sigma0) {High, High} /\
        subst_typing gamma0 (Some t .: empty_gamma) (up sigma0') {High, High} /\
        gamma |- a, e_ctx_to_tm E :t s /\
        gamma |- a, e_ctx_to_tm E' :t s /\
        (
            forall (x : var) (s : stype),
                gamma x = Some s ->
                gamma0 x = None ->
                upward_closure_raw R {|V1 := (up sigma) x; V2 := (up sigma') x; Rtype := s|}
        ) /\
        (
            forall (x : var) (s : stype),
                gamma0 x = Some s ->
                exists (v v' : tm) (u : utype) (l l'' : slabel) (r r0 : tvr_elm),
                    upward_closure_raw R {|V1 := v; V2 := v'; Rtype := [Bool @ty l'']|} /\
                    unlabeled_value v <> unlabeled_value v' /\
                    ~ (conf l'') <=lv (conf a) /\
                    context_closure R a r /\
                    context_closure R a r0 /\
                    r.(tri).(Rtype) = [u @ty l] /\
                    r0.(tri).(Rtype) = [u @ty l] /\
                    {|V1 := (up sigma0) x; V2 := (up sigma0') x; Rtype := s|} 
                        <=r {|V1 := value_label_shift r.(tri).(V1) (value_label v); V2 := value_label_shift r0.(tri).(V2) (value_label v'); Rtype := [u @ty (l |_| l'')]|}
        ) /\
        r' = {|V1 := ((e_ctx_to_tm E).[up sigma]).[up sigma0]; V2 := ((e_ctx_to_tm E').[up sigma']).[up sigma0']; Rtype := s|}.

Lemma condition_if_closure_e_ctx : forall (R : TVR) (a : slabel) (t : stype) (r' : tvr_elm_raw),
    if_closure_e_ctx R a t r' ->
    condition_tvr_weak_ctx t r'.
Proof.
    intros.
    unfold if_closure_e_ctx in H.
    destruct H as [gamma [gamma0 [sigma [sigma' [sigma0 [sigma0' [C [s [E [E' H]]]]]]]]]].
    destruct H as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
    unfold condition_tvr_weak_ctx. rewrite H9. simpl.
    split.
    -   eapply substitution_lemma.
        apply H3.
        eapply substitution_lemma.
        apply H1.
        apply H5.
    -   eapply substitution_lemma.
        apply H4.
        eapply substitution_lemma.
        apply H2.
        apply H6.
Qed.

Lemma condition_x_if_E : forall (a : slabel) (R : TVR) (q : quadraple) (E E' : e_ctx) (s : stype),
    if_closure_e_ctx q.(quad).(Rx) a q.(quad).(Xtype) {|V1 := e_ctx_to_tm E; V2 := e_ctx_to_tm E'; Rtype := s|} ->
    condition_quad {|Rx := R; M1 := (fill E q.(quad).(M1)); M2 := (fill E' q.(quad).(M2)); Xtype := s|}.
Proof.
    intros.
    destruct q.(Xcondition). 
    specialize (condition_if_closure_e_ctx q.(quad).(Rx) a q.(quad).(Xtype) {| V1 := e_ctx_to_tm E; V2 := e_ctx_to_tm E'; Rtype := s |} H) as H2.
    unfold condition_tvr_weak_ctx in H2. simpl in H2. destruct H2 as [H2L H2R].
    unfold condition_quad. simpl.
    split; eauto using type_preservation_closed_context.
Qed.

Lemma condition_x_if_Ep : forall (a : slabel) (R : TVR) (r : tvr_elm) (q1 q2 : quadraple) (E E' : e_ctx) (s : stype) (u : utype) (l lb : slabel),
    q1.(quad).(Xtype) = [u @ty l] -> 
    q2.(quad).(Xtype) = [u @ty l] ->
    r.(tri).(Rtype) = [Bool @ty lb] ->
    if_closure_e_ctx q1.(quad).(Rx) a [u @ty (l |_| lb)] {|V1 := e_ctx_to_tm E; V2 := e_ctx_to_tm E'; Rtype := s|} ->
    condition_quad {|Rx := R; M1 := (fill E (tm_prot (value_label r.(tri).(V1)) (q1.(quad).(M1)))); M2 := (fill E' (tm_prot (value_label r.(tri).(V2)) (q2.(quad).(M2)))); Xtype := s|}.
Proof.
    intros.
    destruct q1.(Xcondition) as [H3 _].
    destruct q2.(Xcondition) as [_ H4].
    rewrite H in H3. rewrite H0 in H4.
    assert (H5 : empty_gamma |- {High, High}, (tm_prot (value_label (V1 (tri r))) (q1.(quad).(M1))) :t [u @ty (l |_| lb)]).
    {
        eapply t_sub.
        apply t_prot. apply H3.
        destruct r.(Rcondition) as [Ha [_ [Hb _]]].
        specialize (label_relation empty_gamma r.(tri).(V1) {High, High} r.(tri).(Rtype) Ha Hb Bool lb H1) as Hc. intros.
        apply s_label. rewrite (join_comm l (value_label r.(tri).(V1))). rewrite (join_comm l lb). apply monotonicity_join. apply Hc.
        apply ut_subtyping_refl.
    }
    assert (H6 : empty_gamma |- {High, High}, (tm_prot (value_label (V2 (tri r))) (q2.(quad).(M2))) :t [u @ty (l |_| lb)]).
    {
        eapply t_sub.
        apply t_prot. apply H4.
        destruct r.(Rcondition) as [_ [Ha [_ Hb]]].
        specialize (label_relation empty_gamma r.(tri).(V2) {High, High} r.(tri).(Rtype) Ha Hb Bool lb H1) as Hc. intros.
        apply s_label. rewrite (join_comm l (value_label r.(tri).(V2))). rewrite (join_comm l lb). apply monotonicity_join. apply Hc.
        apply ut_subtyping_refl.
    }
    specialize (condition_if_closure_e_ctx q1.(quad).(Rx) a [u @ty (l |_| lb)] {| V1 := e_ctx_to_tm E; V2 := e_ctx_to_tm E'; Rtype := s |} H2) as H7.
    unfold condition_tvr_weak_ctx in H7. simpl in H7. destruct H7 as [H7L H7R].
    unfold condition_quad. simpl.
    split; eauto using type_preservation_closed_context.
Qed.

Lemma prot_shift : forall (m : tm) (a k l' : slabel) (s : stype),
    empty_gamma |- a, (tm_prot k m) :t s ->
    forall (u : utype) (l : slabel), s = [u @ty l] ->
    empty_gamma |- a, (tm_prot (k |_| l') m) :t [u @ty (l |_| l')].
Proof.
    intros.
    remember (tm_prot k m) as mp.
    generalize dependent u.
    generalize dependent l.
    induction H; inversion Heqmp; intros.
    -   inversion H0; subst.
        eapply t_sub.
        apply IHtyping. reflexivity. reflexivity.
        inversion H6; subst. apply s_label. apply monotonicity_join. apply H3. apply H4.
    -   subst. inversion H0; subst. rewrite join_assoc.
        apply t_prot. apply H.
Qed.

Lemma condition_x_if_Ep_shift : forall (a : slabel) (R : TVR) (r : tvr_elm) (q1 q2 : quadraple) (E1 E2 : e_ctx) (s : stype) (u : utype) (l lb k1 k2 : slabel) (m1 m2 : tm),
    q1.(quad).(M1) = tm_prot k1 (m1) ->
    q2.(quad).(M2) = tm_prot k2 (m2) ->
    q1.(quad).(Xtype) = [u @ty l] ->
    q2.(quad).(Xtype) = [u @ty l] ->
    r.(tri).(Rtype) = [Bool @ty lb] ->
    if_closure_e_ctx q1.(quad).(Rx) a [u @ty (l |_| lb)] {|V1 := e_ctx_to_tm E1; V2 := e_ctx_to_tm E2; Rtype := s|} ->
    condition_quad {|Rx := R; M1 := (fill E1 (tm_prot (k1 |_| (value_label r.(tri).(V1))) m1)); M2 := (fill E2 (tm_prot (k2 |_| (value_label r.(tri).(V2))) m2)); Xtype := s|}.
Proof.
    intros.
    destruct q1.(Xcondition) as [H5 _].
    destruct q2.(Xcondition) as [_ H6].
    rewrite H in H5. rewrite H1 in H5. rewrite H0 in H6. rewrite H2 in H6.
    assert (H7 : empty_gamma |- {High, High}, (tm_prot (k1 |_| (value_label r.(tri).(V1))) m1) :t [u @ty (l |_| lb)]).
    {
        eapply t_sub.
        -   eapply prot_shift. apply H5. reflexivity.
        -   apply s_label.
            +   destruct r.(Rcondition) as [Hr1 [_ [Hr2 _]]].
                rewrite H3 in Hr2.
                specialize (label_relation empty_gamma r.(tri).(V1) {High, High} [Bool @ty lb] Hr1 Hr2) as Hr.
                rewrite (join_comm l (value_label r.(tri).(V1))). rewrite (join_comm l lb).
                apply monotonicity_join. apply (Hr Bool lb). reflexivity.
            +   apply ut_subtyping_refl.
    }
    assert (H8 : empty_gamma |- {High, High}, (tm_prot (k2 |_| (value_label r.(tri).(V2))) m2) :t [u @ty (l |_| lb)]).
    {
        eapply t_sub.
        -   eapply prot_shift. apply H6. reflexivity.
        -   apply s_label.
            +   destruct r.(Rcondition) as [_ [Hr1 [_ Hr2]]].
                rewrite H3 in Hr2.
                specialize (label_relation empty_gamma r.(tri).(V2) {High, High} [Bool @ty lb] Hr1 Hr2) as Hr.
                rewrite (join_comm l (value_label r.(tri).(V2))). rewrite (join_comm l lb).
                apply monotonicity_join. apply (Hr Bool lb). reflexivity.
            +   apply ut_subtyping_refl.
    }
    unfold condition_quad. simpl.
    specialize (condition_if_closure_e_ctx q1.(quad).(Rx) a [u @ty (l |_| lb)] {|V1 := e_ctx_to_tm E1; V2 := e_ctx_to_tm E2; Rtype := s|} H4) as H9.
    unfold condition_tvr_weak_ctx in H9. simpl in H9. destruct H9 as [H9L H9R].
    split; eauto using type_preservation_closed_context.
Qed.

(* Definition 14 *)
Inductive X_if_closure (X : ER) (a : slabel) : elm -> Prop :=
    | x_if_X     : forall (e : elm),
        X e -> X_if_closure X a e
    | x_if_R     : forall (R RS : TVR),
        X (elm_R RS) ->
        (
            forall (r : tvr_elm),
                R r -> if_closure RS a r
        ) ->
        X_if_closure X a (elm_R R)
    | x_if_M     : forall (R RS : TVR) (rm : tvr_elm_raw),
        X (elm_R RS) ->
        (
            forall (r : tvr_elm),
                R r -> if_closure RS a r
        ) ->
        forall (H : if_closure_tm RS a rm),
        X_if_closure X a 
            (elm_quad 
                {|
                    quad := {|Rx := R; M1 := rm.(V1); M2 := rm.(V2); Xtype := rm.(Rtype)|};
                    Xcondition := condition_if_closure_tm RS a rm H
                |})
    | x_if_E    : forall (R : TVR) (q : quadraple) (E E' : e_ctx) (s : stype),
        (X_arrow (X_if_closure X a)) q ->
        (
            forall (r : tvr_elm),
                R r -> if_closure q.(quad).(Rx) a r
        ) ->
        forall 
        (H : if_closure_e_ctx q.(quad).(Rx) a q.(quad).(Xtype) {|V1 := e_ctx_to_tm E; V2 := e_ctx_to_tm E'; Rtype := s|}),
        X_if_closure X a
            (elm_quad
                {|
                    quad := {|Rx := R; M1 := (fill E q.(quad).(M1)); M2 := (fill E' q.(quad).(M2)); Xtype := s|};
                    Xcondition := condition_x_if_E a R q E E' s H
                |})
    | x_if_Ep   : forall (R : TVR) (q1 q2 : quadraple) (r : tvr_elm) (E1 E2 : e_ctx) (s : stype) (u : utype) (l lb : slabel)
        (Hq1c   : (X_arrow (X_if_closure X a)) q1)
        (Hq2c   : (X_arrow (X_if_closure X a)) q2)
        (HRxe   : q1.(quad).(Rx) = q2.(quad).(Rx))
        (Hq1t   : q1.(quad).(Xtype) = [u @ty l]) 
        (Hq2t   : q2.(quad).(Xtype) = [u @ty l])
        (HRSif  :
            forall (r : tvr_elm),
                R r -> if_closure q1.(quad).(Rx) a r
        )
        (Hr     : upward_closure q1.(quad).(Rx) r)
        (Hrt    : r.(tri).(Rtype) = [Bool @ty lb])
        (Hneq   : unlabeled_value r.(tri).(V1) <> unlabeled_value r.(tri).(V2))
        (Hnle   : ~ (conf l <=lv conf a))
        (Hctx   : if_closure_e_ctx q1.(quad).(Rx) a [u @ty (l |_| lb)] {|V1 := e_ctx_to_tm E1; V2 := e_ctx_to_tm E2; Rtype := s|}),
        X_if_closure X a
            (elm_quad
                {|
                    quad := {|Rx := R; M1 := (fill E1 (tm_prot (value_label r.(tri).(V1)) (q1.(quad).(M1)))); M2 := (fill E2 (tm_prot (value_label r.(tri).(V2)) (q2.(quad).(M2)))); Xtype := s|};
                    Xcondition := condition_x_if_Ep a R r q1 q2 E1 E2 s u l lb Hq1t Hq2t Hrt Hctx
                |}
            )
    | x_if_Ep_shift : forall (R : TVR) (q1 q2 : quadraple) (r : tvr_elm) (E1 E2 : e_ctx) (s : stype) (u : utype) (l lb k1 k2: slabel) (m1 m2 : tm)
        (Hq1c   : (X_arrow (X_if_closure X a)) q1)
        (Hq2c   : (X_arrow (X_if_closure X a)) q2)
        (HRxe   : q1.(quad).(Rx) = q2.(quad).(Rx))
        (Hq1m1  : q1.(quad).(M1) = tm_prot k1 (m1))
        (Hq2m2  : q2.(quad).(M2) = tm_prot k2 (m2))
        (Hq1t   : q1.(quad).(Xtype) = [u @ty l]) 
        (Hq2t   : q2.(quad).(Xtype) = [u @ty l])
        (HRSif  :
            forall (r : tvr_elm),
                R r -> if_closure q1.(quad).(Rx) a r
        )
        (Hr     : upward_closure q1.(quad).(Rx) r)
        (Hrt    : r.(tri).(Rtype) = [Bool @ty lb])
        (Hneq   : unlabeled_value r.(tri).(V1) <> unlabeled_value r.(tri).(V2))
        (Hnle   : ~ (conf l <=lv conf a))
        (Hctx   : if_closure_e_ctx q1.(quad).(Rx) a [u @ty (l |_| lb)] {|V1 := e_ctx_to_tm E1; V2 := e_ctx_to_tm E2; Rtype := s|}),
        X_if_closure X a
            (elm_quad
                {|
                    quad := {|Rx := R; M1 := (fill E1 (tm_prot (k1 |_| (value_label r.(tri).(V1))) m1)); M2 := (fill E2 (tm_prot (k2 |_| (value_label r.(tri).(V2))) m2)); Xtype := s|};
                    Xcondition := condition_x_if_Ep_shift a R r q1 q2 E1 E2 s u l lb k1 k2 m1 m2 Hq1m1 Hq2m2 Hq1t Hq2t Hrt Hctx
                |}
            ).


Definition X_step_quad (X : ER) (q : quadraple) : Prop :=
    exists (q' : quadraple_raw) (q0 : quadraple) (m : tm)
    (Hx     : X (elm_quad q0))
    (Ht     : q'.(Xtype) = q0.(quad).(Xtype))
    (Hty1   : empty_gamma |- {High, High}, q'.(M1) :t q'.(Xtype))
    (Hty2   : empty_gamma |- {High, High}, q'.(M2) :t q'.(Xtype))
    (Hmm    : q'.(M1) ==> m)
    (Hm1    : m ==>* q0.(quad).(M1))
    (Hm2    : q'.(M2) ==>* q0.(quad).(M2)),
    q.(quad) =
        {|
            quad := q';
            Xcondition := conj Hty1 Hty2
        |}.(quad).

Definition X_step (X : ER) (q : quadraple) : Prop :=
    X_step_quad X q \/ X_arrow_tvr X q.


Definition environmental_simulation_quadraple (X : ER) (a : slabel) (e : elm) : Prop :=
    forall (q : quadraple), 
        e = elm_quad q ->
        (X_step (X_if_closure X a)) q.

Definition environmental_simulation_R_bool (R : TVR) (a : slabel) : Prop :=
    forall (r : tvr_elm),
        R r ->
    exists (l : slabel),
        r.(tri).(Rtype) = [Bool @ty l] ->
        (conf l) <=lv (conf a) /\
        unlabeled_value r.(tri).(V1) = unlabeled_value r.(tri).(V2).

Definition environmental_simulation_R_int (R : TVR) (a : slabel) : Prop :=
    forall (r1 r2 : tvr_elm),
        if_closure R a r1 ->
        if_closure R a r2 ->
    exists (l1'' l2'' : slabel),
        r1.(tri).(Rtype) = [Int @ty l1''] /\
        r2.(tri).(Rtype) = [Int @ty l2''] ->
    exists (i i' j j' : Z) (l1 l1' l2 l2' : slabel),
        r1.(tri).(V1) = tm_int l1 i /\
        r1.(tri).(V2) = tm_int l1' i' /\
        r2.(tri).(V1) = tm_int l2 j /\
        r2.(tri).(V2) = tm_int l2 j' /\
        forall (e : level) (op : Z -> Z -> Z) (r : tvr_elm),
            e <=lv (integ a) ->
            r.(tri).(V1) = tm_int (l1 |_| l2 |_| {Low, e}) (op i j) ->
            r.(tri).(V2) = tm_int (l1' |_| l2' |_| {Low, e}) (op i' j') ->
            r.(tri).(Rtype) = [Int @ty (l1'' |_| l2'' |_| {Low, e})] ->
            if_closure R a r.

Definition environmental_simulation_R_label (R : TVR) (a : slabel) : Prop :=
    forall (r : tvr_elm),
        R r ->
    exists (u : utype) (l : slabel) (r0 : tvr_elm),
        r.(tri).(Rtype) = [u @ty l] /\
        forall (c : level), 
            c <=lv (conf l) ->
            r0.(tri).(V1) = unlabeled_value r.(tri).(V1) {c, integ (value_label r.(tri).(V1))} ->
            r0.(tri).(V2) = unlabeled_value r.(tri).(V1) {c, integ (value_label r.(tri).(V2))} ->
            r0.(tri).(Rtype) = [u @ty {c, integ l}] ->
            if_closure R a r0.

Definition environmental_simulation_R_pair (R : TVR) (a : slabel) : Prop :=
    forall (r : tvr_elm),
        R r ->
    exists (s1 s2 : stype) (l'' : slabel),
        r.(tri).(Rtype) = [(s1 *s s2) @ty l''] ->
    exists (v1 v2 v1' v2' : tm) (u1 u2 : utype) (l l' l1 l2 : slabel) (r1 r2 : tvr_elm),
        r.(tri).(V1) = tm_pair l v1 v2 /\
        r.(tri).(V2) = tm_pair l' v1' v2' /\
        s1 = [u1 @ty l1] /\
        s2 = [u2 @ty l2] /\
        r1.(tri).(V1) = value_label_shift v1 l /\
        r1.(tri).(V2) = value_label_shift v2 l /\
        r1.(tri).(Rtype) = [u1 @ty (l1 |_| l'')] /\
        r2.(tri).(V1) = value_label_shift v1' l' /\
        r2.(tri).(V2) = value_label_shift v2' l' /\
        r2.(tri).(Rtype) = [u2 @ty (l2 |_| l'')] /\
        if_closure R a r1 /\
        if_closure R a r2.
        
Definition environmental_simulation_R_fun (X : ER) (R : TVR) (a : slabel) : Prop :=
    forall (r : tvr_elm),
        R r ->
    exists (s1 s2 : stype) (l'' : slabel),
        r.(tri).(Rtype) = [(s1 ->s s2) @ty l''] ->
    exists (m m' : tm) (l l' : slabel),
        r.(tri).(V1) = tm_abs l m s1 /\
        r.(tri).(V2) = tm_abs l' m' s1 /\
        forall (q : quadraple) (r0 : tvr_elm),
            if_closure R a r0 ->
            q.(quad).(M1) = tm_prot l m.[r0.(tri).(V1) .: ids] ->
            q.(quad).(M2) = tm_prot l' m'.[r0.(tri).(V2) .: ids] ->
            q.(quad).(Xtype) = s2 ->
            X_arrow (X_if_closure X a) q.

Definition environmental_simulation_R (X : ER) (a : slabel) (e : elm) : Prop :=
    forall (R : TVR),
        e = elm_R R ->
        environmental_simulation_R_bool R a /\
        environmental_simulation_R_int R a /\
        environmental_simulation_R_label R a /\
        environmental_simulation_R_pair R a /\
        environmental_simulation_R_fun X R a.

(* Definition 15 *)
Definition environmental_simulation (X : ER) (a : slabel) : Prop :=
    forall (e : elm),
        X e ->
        environmental_simulation_quadraple X a e \/
        environmental_simulation_R X a e.

Definition inversion_TVR (R : TVR) (r : tvr_elm) : Prop :=
    exists (r0 : tvr_elm),
        R r0 /\ 
        r.(tri).(V1) = r0.(tri).(V2) /\
        r.(tri).(V2) = r0.(tri).(V1) /\
        r.(tri).(Rtype) = r0.(tri).(Rtype).

Definition inversion_ER (X : ER) (e : elm) : Prop :=
    (
        forall (R : TVR),
            e = elm_R R ->
                exists (R0 : TVR),
                    X (elm_R R0) /\ R = inversion_TVR R0
    ) \/
    (
        forall (q : quadraple),
            e = elm_quad q ->
                exists (q0 : quadraple),
                    X (elm_quad q0) /\
                    q.(quad).(Rx) = q0.(quad).(Rx) /\
                    q.(quad).(M1) = q0.(quad).(M2) /\
                    q.(quad).(M2) = q0.(quad).(M1) /\
                    q.(quad).(Xtype) = q0.(quad).(Xtype)
    ).

Definition environmental_bisimulation (X : ER) (a : slabel) : Prop :=
    environmental_simulation X a /\
    environmental_simulation (inversion_ER X) a.