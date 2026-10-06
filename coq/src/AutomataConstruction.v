From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

From regexderiv Require Import Alphabet.
From regexderiv Require Import RegexSemantics.
From regexderiv Require Import Nullable.
From regexderiv Require Import Derivatives.
From regexderiv Require Import Canonicalization.
From regexderiv Require Import CanonicalizationCorrectness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module AutomataConstruction (X : OFINSYM).
  Import X.

  Module Export D := Derivatives X.
  Module CC := CanonicalizationCorrectness X.

  Fixpoint to_c_regex (r : regex) : CC.C.RS.regex :=
    match r with
    | Empty      => CC.C.RS.Empty
    | Eps        => CC.C.RS.Eps
    | Char a     => CC.C.RS.Char a
    | Alt r1 r2  => CC.C.RS.Alt (to_c_regex r1) (to_c_regex r2)
    | Seq r1 r2  => CC.C.RS.Seq (to_c_regex r1) (to_c_regex r2)
    | Star r1    => CC.C.RS.Star (to_c_regex r1)
    | And r1 r2  => CC.C.RS.And (to_c_regex r1) (to_c_regex r2)
    | Neg r1     => CC.C.RS.Neg (to_c_regex r1)
    end.

  Fixpoint from_c_regex (r : CC.C.RS.regex) : regex :=
    match r with
    | CC.C.RS.Empty      => Empty
    | CC.C.RS.Eps        => Eps
    | CC.C.RS.Char a     => Char a
    | CC.C.RS.Alt r1 r2  => Alt (from_c_regex r1) (from_c_regex r2)
    | CC.C.RS.Seq r1 r2  => Seq (from_c_regex r1) (from_c_regex r2)
    | CC.C.RS.Star r1    => Star (from_c_regex r1)
    | CC.C.RS.And r1 r2  => And (from_c_regex r1) (from_c_regex r2)
    | CC.C.RS.Neg r1     => Neg (from_c_regex r1)
    end.

  Definition canonize (r : regex) : regex :=
    from_c_regex (CC.C.canonize (to_c_regex r)).

  Definition regex_eqb (r s : regex) : bool :=
    CC.C.eq_regex (to_c_regex r) (to_c_regex s).

  Definition canonical_derivative (a : A) (q : regex) : regex :=
    canonize (D_char a q).

  Definition accepting_state (q : regex) : bool :=
    has_eps q.

  Definition state := regex.

  Record transition := {
    source_state : state;
    transition_symbol : A;
    target_state : state
  }.

  Definition same_transition_key (q : state) (a : A) (t : transition) : bool :=
    regex_eqb (source_state t) q && (transition_symbol t == a).

  Fixpoint mem_state (q : state) (Q : seq state) : bool :=
    if Q is q' :: Q' then regex_eqb q q' || mem_state q Q' else false.

  Definition add_state (q : state) (Q : seq state) : seq state :=
    if mem_state q Q then Q else rcons Q q.

  Fixpoint lookup_transition (q : state) (a : A) (delta : seq transition)
    : option state :=
    if delta is t :: delta' then
      if same_transition_key q a t then Some (target_state t)
      else lookup_transition q a delta'
    else None.

  Fixpoint add_transition (q : state) (a : A) (q' : state)
           (delta : seq transition) : seq transition :=
    if delta is t :: delta' then
      if same_transition_key q a t then
        {| source_state := q;
           transition_symbol := a;
           target_state := q' |} :: delta'
      else
        t :: add_transition q a q' delta'
    else
      [:: {| source_state := q;
             transition_symbol := a;
             target_state := q' |} ].

  Fixpoint uniq_states (Q : seq state) : bool :=
    if Q is q :: Q' then ~~ mem_state q Q' && uniq_states Q' else true.

  Definition transition_respects_states (Q : seq state) (t : transition) : bool :=
    mem_state (source_state t) Q && mem_state (target_state t) Q.




  Record dfa := {
    Q : seq state;
    Sigma : seq A;
    delta : seq transition;
    q0 : state;
    F : seq state
  }.

  Definition dfa_well_formed (M : dfa) : bool :=
    [&& uniq_states (Q M),
        mem_state (q0 M) (Q M),
        all (transition_respects_states (Q M)) (delta M)
      & all (fun q => mem_state q (Q M)) (F M)].

  (*
    Paper definition of the accepting set:
      F := { q in Q | nullable(q) }.
  *)
  Definition final_states (Q : seq state) : seq state :=
    filter accepting_state Q.

  (*
    Executable transition function induced by the finite transition table.
    If a transition is absent because the fuel was too small, we fall back to
    the mathematical delta(q, a) = [ D_a(q) ] from the paper.
  *)
  Definition step (M : dfa) (q : state) (a : A) : state :=
    if lookup_transition q a (delta M) is Some q' then q'
    else canonical_derivative a q.

  Fixpoint delta_star (M : dfa) (q : state) (w : word) : state :=
    if w is a :: w' then delta_star M (step M q a) w' else q.

  Definition final_in_dfa (M : dfa) (q : state) : bool :=
    mem_state q (F M).

  Definition accepts (M : dfa) (w : word) : bool :=
    final_in_dfa M (delta_star M (q0 M) w).

  Definition accepts_semantic (M : dfa) (w : word) : bool :=
    accepting_state (delta_star M (q0 M) w).

  (*
    This is the recursive content of the paper's goto procedure.

      goto(q, a, Q, delta):
         q_a := [ D(a, q) ]
         if q_a in Q then
             delta[(q, a)] := q_a
             return (Q, delta)
         else
             Q     := union(Q, { q_a })
             delta := union(delta, (q, a) -> q_a))
             for each a' in Sigma do
                 (Q, delta) := goto(q_a, a', Q, delta)
             return (Q, delta)

    The extra parameter fuel is the structurally decreasing argument that makes
    the exploration executable in Coq.
  *)
  Fixpoint goto (fuel : nat) (q : state) (a : A)
           (Q : seq state) (delta : seq transition)
           {struct fuel} : seq state * seq transition :=
    match fuel with
    | 0 => (Q, delta)
    | fuel'.+1 =>
        let q_a := canonical_derivative a q in
        (* q_a := [ D(a, q) ] *)
        if mem_state q_a Q then
          (* if q_a in Q then delta[(q, a)] := q_a *)
          (Q, add_transition q a q_a delta)
        else
          let Q1 := add_state q_a Q in
          let delta1 := add_transition q a q_a delta in
          (* Q := union(Q, { q_a }) ; delta := union(delta, (q, a) -> q_a) *)
          let fix explore (Sigma : seq A) (Qacc : seq state)
                          (deltaacc : seq transition) {struct Sigma}
              : seq state * seq transition :=
              if Sigma is a' :: Sigma' then
                let '(Qnext, deltanext) := goto fuel' q_a a' Qacc deltaacc in
                (* for each a' in Sigma do (Q, delta) := goto(q_a, a', Q, delta) *)
                explore Sigma' Qnext deltanext
              else (Qacc, deltaacc)
          in explore alphabet Q1 delta1
    end.

  (*
      dfa(r):
         q_0 := [ r ]
         Q := { q_0 }
         delta := empty
         for each a in Sigma do
             (Q, delta) := goto(q_0, a, Q, delta)
         F := { q in Q | nullable(q) }
         return (Q, Sigma, delta, q_0, F)
  *)
  Definition construct_dfa (fuel : nat) (r : regex) : dfa :=
    let q0 := canonize r in
    let fix build_from_initial (Sigma : seq A) (Q : seq state)
                               (delta : seq transition) {struct Sigma}
        : seq state * seq transition :=
        if Sigma is a :: Sigma' then
          let '(Qnext, deltanext) := goto fuel q0 a Q delta in
          build_from_initial Sigma' Qnext deltanext
        else (Q, delta)
    in
    let '(Q, delta) := build_from_initial alphabet [:: q0] [::] in
    {| Q := Q;
       Sigma := alphabet;
       delta := delta;
       q0 := q0;
       F := final_states Q |}.


    (*TODO L(M) = L(r)*)

End AutomataConstruction.
