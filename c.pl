:- use_module(rtg).
:- op(1200,xfx,[--,+++]).
term_expansion(A--B,R) :- next_term_expansion(B:-A,R).
:- begin_var_names(['^[τθ]']).

  term_expansion(A+++B,R) :- next_term_expansion(B:-A,R).

  θ=1 +++ test1(θ).

  test(θ,θ).
  :- τ1=hogehoge7,writeln(τ1).
  :- test(a,R),writeln(R).

  θ=1
  --
  test2(θ).

:- end_var_names(_).

:- writeln(θ).
:- atom_concat(α,I,α12),atom_number(I,_).
:- test2(1).
:- test1(1).
:- halt.
