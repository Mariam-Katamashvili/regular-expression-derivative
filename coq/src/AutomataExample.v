From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Stdlib Require Import String Ascii PeanoNat.

From regexderiv Require Import Alphabet.
From regexderiv Require Import AutomataConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope string_scope.

Module ABC.

Inductive sym := a | b | c.

Definition sym_eq (x y : sym) : bool :=
  match x, y with
  | a, a => true
  | b, b => true
  | c, c => true
  | _, _ => false
  end.

Lemma sym_eqP : Equality.axiom sym_eq.
Proof. by do 2 case; constructor. Qed.

Canonical sym_eqMixin := Equality.Mixin sym_eqP.
Canonical sym_eqType := Equality.Pack (Equality.Class sym_eqMixin).

Definition A := sym_eqType.

Definition cmpA (x y : A) : comparison :=
  match x, y with
  | a, a | b, b | c, c => Eq
  | a, _ => Lt
  | b, a => Gt
  | b, c => Lt
  | c, _ => Gt
  end.

End ABC.

Module X <: OFINSYM.
  Definition A := ABC.A.
  Definition cmpA := ABC.cmpA.

  Lemma cmpA_refl : forall a, cmpA a a = Eq.
  Proof. by case. Qed.

  Lemma cmpA_eq_axiom : forall a b, reflect (a = b)
    (if cmpA a b is Eq then true else false).
  Proof.
    by case; case; constructor.
  Qed.

  Lemma cmpA_trans : forall a b c (x : comparison),
      cmpA a b = x -> cmpA b c = x -> cmpA a c = x.
  Proof.
    by case; case; case; case; simpl; try congruence.
  Qed.

  Lemma cmpA_neg : forall a b, cmpA b a = CompOpp (cmpA a b).
  Proof. by case; case. Qed.

  Definition leA : rel A :=
    fun a b => if cmpA a b is Gt then false else true.

  Lemma leA_refl : reflexive leA.
  Proof. by move=> a; rewrite /leA cmpA_refl. Qed.

  Lemma leA_total : total leA.
  Proof.
    move=> a b; rewrite /leA cmpA_neg; by case: (cmpA b a).
  Qed.

  Definition alphabet : seq A := [:: ABC.a; ABC.b; ABC.c].

  Lemma alphabet_uniq : uniq alphabet.
  Proof. by []. Qed.

  Lemma alphabet_nonempty : alphabet != [::].
  Proof. by []. Qed.

  Lemma alphabet_complete : forall a : A, a \in alphabet.
  Proof. by case. Qed.
End X.

Module AC := AutomataConstruction X.
Import X AC.

Definition aa : A := ABC.a.
Definition bb : A := ABC.b.
Definition cc : A := ABC.c.

(* Input regex r = ab + ac. This is the paper's initial state q0 = [r]. *)
Definition r_ab_or_ac : regex :=
  Alt (Seq (Char aa) (Char bb))
      (Seq (Char aa) (Char cc)).

(* Fuel 4 is enough for this example: q0, b+c, Empty, Eps. *)
Definition M_ab_or_ac : dfa :=
  construct_dfa 4 r_ab_or_ac.

Definition sappend := String.append.

Definition parens (s : string) : string :=
  sappend "("%string (sappend s ")"%string).

Definition digit_ascii (n : nat) : ascii :=
  match n with
  | 0 => "0"%char
  | 1 => "1"%char
  | 2 => "2"%char
  | 3 => "3"%char
  | 4 => "4"%char
  | 5 => "5"%char
  | 6 => "6"%char
  | 7 => "7"%char
  | 8 => "8"%char
  | _ => "9"%char
  end.

Fixpoint show_nat_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => "0"%string
  | fuel'.+1 =>
      if n < 10 then String (digit_ascii n) EmptyString
      else sappend (show_nat_aux fuel' (Nat.div n 10))
                   (String (digit_ascii (n - (Nat.div n 10) * 10)) EmptyString)
  end.

Definition show_nat (n : nat) : string :=
  show_nat_aux n.+1 n.

Fixpoint join_with (sep : string) (xs : seq string) : string :=
  if xs is x :: xs' then
    if xs' is [::] then x
    else sappend x (sappend sep (join_with sep xs'))
  else ""%string.

Definition show_sym (a : A) : string :=
  match a with
  | ABC.a => "a"%string
  | ABC.b => "b"%string
  | ABC.c => "c"%string
  end.

Fixpoint show_regex (r : regex) : string :=
  match r with
  | Empty => "Empty"%string
  | Eps => "Eps"%string
  | Char a => show_sym a
  | Alt r1 r2 => parens (sappend (show_regex r1) (sappend "+"%string (show_regex r2)))
  | Seq r1 r2 => parens (sappend (show_regex r1) (show_regex r2))
  | Star r1 => parens (sappend (show_regex r1) "*"%string)
  | And r1 r2 => parens (sappend (show_regex r1) (sappend "&"%string (show_regex r2)))
  | Neg r1 => parens (sappend "~"%string (show_regex r1))
  end.

(* Simple textual view of edges: (source, label, target). *)
Definition edge := (state * A * state)%type.
Definition labeled_target := (A * state)%type.
Definition state_block := (state * seq labeled_target)%type.
Definition pretty_edge := string.
Definition pretty_state_block := (string * seq string)%type.
Definition target_labels := (state * seq A)%type.

Definition transition_to_edge (t : transition) : edge :=
  (source_state t, transition_symbol t, target_state t).

Definition edges (M : dfa) : seq edge :=
  map transition_to_edge (delta M).

Definition show_arrow (q : state) (a : A) (q' : state) : string :=
  sappend (show_regex q)
    (sappend " -"%string
      (sappend (show_sym a)
        (sappend "-> "%string (show_regex q')))).

Definition pretty_edges (M : dfa) : seq pretty_edge :=
  map (fun t => show_arrow (source_state t) (transition_symbol t) (target_state t))
      (delta M).

Definition outgoing_from (q : state) (M : dfa) : seq labeled_target :=
  map (fun t => (transition_symbol t, target_state t))
      (filter (fun t => regex_eqb (source_state t) q) (delta M)).

Definition grouped_edges (M : dfa) : seq state_block :=
  map (fun q => (q, outgoing_from q M)) (Q M).

Fixpoint insert_label (q : state) (a : A) (acc : seq target_labels)
    {struct acc} : seq target_labels :=
  if acc is (q'', labels) :: acc' then
    if regex_eqb q q'' then (q'', rcons labels a) :: acc'
    else (q'', labels) :: insert_label q a acc'
  else [:: (q, [:: a])].

Fixpoint collect_by_target_acc (outs : seq labeled_target) (acc : seq target_labels)
    {struct outs} : seq target_labels :=
  if outs is (a, q') :: outs' then
    let acc' :=
      if has (fun p => regex_eqb q' p.1) acc then insert_label q' a acc
      else rcons acc (q', [:: a])
    in
    collect_by_target_acc outs' acc'
  else acc.

Definition collect_by_target (outs : seq labeled_target) : seq target_labels :=
  collect_by_target_acc outs [::].

Definition pretty_target (p : labeled_target) : string :=
  let '(a, q') := p in
  sappend (show_sym a) (sappend " -> "%string (show_regex q')).

Fixpoint show_syms (labels : seq A) : string :=
  if labels is a :: labels' then
    if labels' is [::] then show_sym a
    else sappend (show_sym a) (sappend ","%string (show_syms labels'))
  else ""%string.

Definition pretty_target_group (p : target_labels) : string :=
  let '(q', labels) := p in
  sappend (show_syms labels) (sappend " -> "%string (show_regex q')).

Definition pretty_grouped_edges (M : dfa) : seq pretty_state_block :=
  map (fun p =>
         let '(q, outs) := p in
         (show_regex q, map pretty_target outs))
      (grouped_edges M).

Definition compact_grouped_edges (M : dfa) : seq pretty_state_block :=
  map (fun p =>
         let '(q, outs) := p in
         (show_regex q, map pretty_target_group (collect_by_target outs)))
      (grouped_edges M).

Fixpoint state_index_from (q : state) (Qs : seq state) (i : nat) : nat :=
  if Qs is q' :: Qs' then
    if regex_eqb q q' then i else state_index_from q Qs' i.+1
  else i.

Definition state_index (M : dfa) (q : state) : nat :=
  state_index_from q (Q M) 0.

Definition state_name (M : dfa) (q : state) : string :=
  sappend "q"%string (show_nat (state_index M q)).

Definition named_state (M : dfa) (q : state) : string :=
  sappend (state_name M q) (sappend " = "%string (show_regex q)).

Definition named_states (M : dfa) : seq string :=
  map (named_state M) (Q M).

Definition named_finals (M : dfa) : seq string :=
  map (named_state M) (F M).

Definition start_state_line (M : dfa) : string :=
  sappend "q0 = "%string (show_regex (q0 M)).

Definition named_target_group (M : dfa) (p : target_labels) : string :=
  let '(q', labels) := p in
  sappend (show_syms labels)
    (sappend " -> "%string
      (sappend (state_name M q')
        (sappend " = "%string (show_regex q')))).

Definition named_transition_lines_from (M : dfa) (q : state) : seq string :=
  map (fun p =>
         sappend (state_name M q)
           (sappend " - "%string (named_target_group M p)))
      (collect_by_target (outgoing_from q M)).

Definition named_transition_lines (M : dfa) : seq string :=
  flatten (map (named_transition_lines_from M) (Q M)).

Definition pretty_dfa (M : dfa) : seq string :=
  [:: sappend "Q = { "%string
         (sappend (join_with "; "%string (named_states M)) " }"%string);
      sappend "Sigma = { "%string
         (sappend (join_with ","%string (map show_sym (Sigma M))) " }"%string);
      start_state_line M;
      sappend "F = { "%string
         (sappend (join_with "; "%string (named_finals M)) " }"%string);
      "delta ="%string ]
  ++ named_transition_lines M.

(* Some test words. *)
Definition w_ab : word := [:: aa; bb].
Definition w_ac : word := [:: aa; cc].
Definition w_aa : word := [:: aa; aa].
Definition w_b  : word := [:: bb].

(* q0 should be the canonical form of ab + ac. *)
Compute (q0 M_ab_or_ac).
Compute (show_regex (q0 M_ab_or_ac)).

(* Enumerated states Q and accepting states F. *)
Compute (Q M_ab_or_ac).
Compute (F M_ab_or_ac).
Compute (map show_regex (Q M_ab_or_ac)).
Compute (map show_regex (F M_ab_or_ac)).
Compute (named_states M_ab_or_ac).
Compute (named_finals M_ab_or_ac).

(* Transition table as records, and as explicit arrows (source, symbol, target). *)
Compute (delta M_ab_or_ac).
Compute (edges M_ab_or_ac).
Compute (pretty_edges M_ab_or_ac).

(* Transition table grouped by source state. *)
Compute (grouped_edges M_ab_or_ac).
Compute (outgoing_from (q0 M_ab_or_ac) M_ab_or_ac).
Compute (pretty_grouped_edges M_ab_or_ac).
Compute (compact_grouped_edges M_ab_or_ac).
Compute (named_transition_lines M_ab_or_ac).
Compute (pretty_dfa M_ab_or_ac).

(* Basic sanity checks for the example language. *)
Compute (accepts M_ab_or_ac w_ab).
Compute (accepts M_ab_or_ac w_ac).
Compute (accepts M_ab_or_ac w_aa).
Compute (accepts M_ab_or_ac w_b).
