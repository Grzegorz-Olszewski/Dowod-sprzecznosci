% Definiujemy moduł zawierający testy.
% Należy zmienić nazwę modułu na {imie}_{nazwisko}_tests gdzie za
% {imie} i {nazwisko} należy podstawić odpowiednio swoje imię
% i nazwisko bez wielkich liter oraz znaków diakrytycznych
 :- module(grzegorz_olszewski_tests, [resolve_tests/5, prove_tests/4]).

% definiujemy operatory ~/1 oraz v/2
:- op(200, fx, ~).
:- op(500, xfy, v).

% Zbiór faktów definiujących testy dla predykatu resolve
% Należy zdefiniować swoje testy
resolve_tests(simple_test, q, p v q, ~q v r, p v r).
resolve_tests(with_literal, q, q , ~q v p, p).
resolve_tests(duplicates, p, p v p v p v ~p v r , ~p v f, r v f ).
resolve_tests(longer_one, p, p v q v r v w v s v d v f, ~p v u v h v j v q, q v r v w v s v d v f v u v h v j v q).
resolve_tests(false, p , p, ~p, []).

% Zbiór faktów definiujących testy dla predykatu prove
% Należy zdefiniować swoje testy

prove_tests(empty_clause, validity, [[]], unsat).
prove_tests(empty_set, validity, [], sat).
prove_tests(easy_false, validity, [p, ~p], unsat).
prove_tests(tautology, validity, [p v ~p], sat).
prove_tests(with_empty_clause, validity, [p v r v y v s, q v s v l v e, q v a v l, ~i v ~ u v d, [], o v p v l], unsat).
prove_tests(test1, validity,[p, p v ~q, ~q], sat).
prove_tests(duplicates, validity, [p, p v p v p v p, r v ~r v r v ~r, q v ~q], sat).
prove_tests(test2, validity, [p v r, ~p v ~r], sat).
prove_tests(test3, validity, [p v r v h, ~p, ~r, ~h], unsat).