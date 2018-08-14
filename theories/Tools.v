Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope bool_scope.
Open Scope list_scope.

Global Set Printing Depth 10000.

Ltac print_inductive T :=
  idtac "sealed trait" T;
  let x := fresh "x" in
  let E := fresh "E" in
  assert (x: T);
  [ exfalso
  | destruct x eqn: E;
    match type of E with
    | x = ?c =>
      is_constructor c;
      idtac "case object" c "extends" T
    | x = ?c ?a1 =>
      is_constructor c;
      let T1 := type of a1 in
      idtac "case class" c "(" a1 ":" T1 ")" "extends" T
    | x = ?c ?a1 ?a2 =>
      is_constructor c;
      let T1 := type of a1 in
      let T2 := type of a2 in
      idtac "case class" c "(" a1 ":" T1 "," a2 ":" T2 ")" "extends" T
    | x = ?c ?a1 ?a2 ?a3 =>
      is_constructor c;
      let T1 := type of a1 in
      let T2 := type of a2 in
      let T3 := type of a3 in
      idtac "case class" c "(" a1 ":" T1 "," a2 ":" T2 "," a3 ":" T3 ")" "extends" T
    | x = ?c ?a1 ?a2 ?a3 ?a4 =>
      is_constructor c;
      let T1 := type of a1 in
      let T2 := type of a2 in
      let T3 := type of a3 in
      let T4 := type of a4 in
      idtac "case class" c "(" a1 ":" T1 "," a2 ":" T2 "," a3 ":" T3 "," a4 ":" T4 ")" "extends" T
    end;
    admit ].

(* output needs manual fixes, but gives the skeleton of what's needed *)
Ltac print_inductive_match_notation T :=
  idtac "Notation ""x 'match' {";
  let x := fresh "x" in
  let E := fresh "E" in
  assert (x: T);
  [ exfalso
  | destruct x eqn: E;
    match type of E with
    | x = ?c =>
      is_constructor c;
      idtac "'case' '" c "' => e ;" 
    | x = ?c ?a1 =>
      is_constructor c;
      idtac "'case' '" c "' (" a1 ") => e ;"
    | x = ?c ?a1 ?a2 =>
      is_constructor c;
      idtac "'case' '" c "' (" a1 "," a2 ") => e ;"
    | x = ?c ?a1 ?a2 ?a3 =>
      is_constructor c;
      idtac "'case' '" c "' (" a1 "," a2 "," a3 ") => e ;"
    | x = ?c ?a1 ?a2 ?a3 ?a4 =>
      is_constructor c;
      idtac "'case' '" c "' (" a1 "," a2 "," a3 "," a4 ") => e ;"
    end;
    admit ];
  idtac "}"" := (match x with";
  assert (x: T);
  [ exfalso
  | destruct x eqn: E;
    match type of E with
    | x = ?c =>
      is_constructor c;
      idtac "|" c " => e" 
    | x = ?c ?a1 =>
      is_constructor c;
      idtac "|" c a1 "=> e"
    | x = ?c ?a1 ?a2 =>
      is_constructor c;
      idtac "|" c a1 a2 "=> e"
    | x = ?c ?a1 ?a2 ?a3 =>
      is_constructor c;
      idtac "|" c a1 a2 a3 "=> e"
    | x = ?c ?a1 ?a2 ?a3 ?a4 =>
      is_constructor c;
      idtac "|" c a1 a2 a3 a4 "=> e"
    end;
    admit ];
  idtac "end) (at level 8).".
  
Ltac print_fun0 f :=
  let T := type of f in
  let rhs := eval cbv delta [f] in f in
  idtac "val" f ":" T "=" rhs.

Ltac print_fun1 f :=
  let T := type of f in
  match T with
  | (?A -> ?B) =>
    let rhs := eval cbv delta [f] in f in
    let arg := fresh "arg0" in
    assert (arg: A) by admit;
    let body := eval cbv beta in (rhs arg) in
    idtac "def" f "(" arg ":" A ")" ":" B "=" "{" body "}";
    clear arg
  end.

Ltac print_fun2 f :=
  let T := type of f in
  match T with
  | (?A -> ?B -> ?C) =>
    let rhs := eval cbv delta [f] in f in
    let arg0 := fresh "arg0" in
    let arg1 := fresh "arg1" in
    assert (arg0: A) by admit;
    assert (arg1: B) by admit;
    let body := eval cbv beta in (rhs arg0 arg1) in
    idtac "def" f "(" arg0 ":" A "," arg1 ":" B ")" ":" C "=" "{" body "}";
    clear arg0 arg1
  end.
  
Notation Long := Z.
Notation Boolean := bool.

Notation "'val' a = e1 ; e2" := (let a := e1 in e2) (at level 8, right associativity, only printing).

Notation "'if' ( c ) { e1 } 'else' { e2 }" := (if c then e1 else e2)
  (at level 200, right associativity, only printing, format "'if'  ( c )  {  '/' e1 '/'  }  'else'  {  '/' e2 '/'  }").

Notation "a ( b )" := (a b) (at level 10, format "a ( b )", only printing).  
Notation "a ( b , c )" := (a b c) (at level 10, format "a ( b ,  c )", only printing).
Notation "a ( b , c , d )" := (a b c d) (at level 10, format "a ( b ,  c ,  d )", only printing).
Notation "a ( b , c , d , e )" := (a b c d e) (at level 10, format "a ( b ,  c ,  d ,  e )", only printing).

Notation "a == b" := (Z.eqb a b) (at level 38, no associativity, only printing).
Notation "a | b" := (Z.lor a b) (at level 40, only printing).
Notation "a << b" := (Z.shiftl a b) (at level 45, only printing).

Notation "'Nil'" := (@nil _) (only printing).

Notation "x 'match' { 'case' h :: t => e1 ; 'case' 'Nil' => e2 }" :=
  (match x with
   | h :: t => e1
   | nil => e2
   end) (at level 8).

Notation "x 'match' { 'case' 'Nil' => e1 ; 'case' h :: 'Nil' => e2 ; 'case' h1 :: h2 :: t => e3 }" :=
  (match x with
   | nil => e1
   | h :: nil => e2
   | h1 :: h2 :: t => e3
   end) (at level 8).
