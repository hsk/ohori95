% RTG : Regular Tree Grammer validator generator

:- module(rtg, [
  op(1200, xfx, [::=]),
  call2/2,
  next_term_expansion/2,
  begin_var_names/1,
  end_var_names/1,
  begin_var_names/2,
  end_var_names/2
]).

list2tpl([A],A).
list2tpl([A|B],(A,B_)) :- list2tpl(B,B_).

addm(A,M,L) :- atom(A), L =.. [A|M].
addm(A,M,L) :- A=..B,append(B,M,R), L =.. R.

split(A,L,[B,R|L]) :- var(A),addm(call2,[A,B],R).
split(A,L,[B,R|L]) :- syntax(A),addm(A,[B],R).
split(A,L,[A|L]) :- atom(A),!.
split(A,L,[B|Ps1_]) :-
  A =.. [A_|Ps],!,
  foldl([P,(L1,L2),(R,[C|L2])]>> (split(P,L1,[C|R]),!),
    Ps,(L,[]),(Ps1,Ps_)
  ),!,
  reverse(Ps1,Ps1_),!, reverse(Ps_,Ps__),!,
  B =.. [A_|Ps__].
  
split2(M,A,C) :- split(A,[],[N|B]),list2tpl([M=N|B],C).

user:term_expansion(syntax(A),ignore) :- assert(syntax(A)).
user:term_expansion(A::=B,A_ :- syntax(A_,M,B)) :- assert(syntax(A)), addm(A,[M],A_).

syntax_expansion(M,(B|Bs),((B_,!);Bs_)) :- split2(M,B,B_), syntax_expansion(M,Bs,Bs_).
syntax_expansion(M,B,B_) :- split2(M,B,B_).

user:goal_expansion(syntax(_,M,A),B_) :- syntax_expansion(M,A,B_)/*,writeln(A_:-B_)*/.

call2([],[]) :- !.
call2([F|Fs],[M|Ms]) :- !,call2(F,M),call2(Fs,Ms).
call2(X,M) :- atom(X),syntax(X),call(X,M).
call2(F,M) :- F=..[O|Fs],M=..[O|Ms], call2(Fs,Ms).

syntax(atom).
:- user:discontiguous(syntax/1).
:- user:discontiguous(ignore/0).

%--------------
:- use_module(library(lists)).
:- use_module(library(pcre)).
next_term_expansion(T,T_) :- user:term_expansion(T,T_),!.
next_term_expansion(T,T) :- !.

dynamic(var_names/2).
dynamic(ex_var_names/2).
dynamic(lvflg1/1).
begin_var_names(Vs) :- begin_var_names(Vs,[]).
begin_var_names(Vs,Es) :-
  maplist([V,V2]>>re_compile(V,V2,[]),Vs,Vs2),
  assert(var_names(Vs,Vs2)),
  maplist([EV,EV2]>>re_compile(EV,EV2,[]),Es,Es2),
  assert(ex_var_names(Es,Es2)).
end_var_names(Vs) :- end_var_names(Vs,_).
end_var_names(Vs,Es) :-
  retract(var_names(Vs,_)),
  retract(ex_var_names(Es,_)).
checkflg :- \+current_predicate(lvflg1/1),!.
checkflg :- findall(R,lvflg1(R),Ls),length(Ls,0),!.
user:term_expansion(T,T_):-
  current_predicate(var_names/2),
  checkflg,
  var_names(_,Vs),
  lists:maplist([V,V:_]>>!,Vs,Vs_),
  varcnv(Vs_,T,_,T1),
  \+checkflg,
  next_term_expansion(T1,T_),
  retractall(lvflg1(_)).
%varcnv(G,T,_,_) :- writeln(varcnv(G,T)),fail.
varcnv(G,T,G,T) :-var(T),!.
varcnv(G,T,G,T_):-string(T),!,atom_string(T_,T),assert(lvflg1(T)),!.
varcnv(G,T,G,T_):-atom(T),member(T:T_,G),assert(lvflg1(T)),!.
varcnv(G,T,[T:T2|G],T2):- atom(T),member(A:_,G),re_match(A, T),
  forall(ex_var_names(_,A2),maplist([A3]>>(\+re_match(A3,T)),A2)),assert(lvflg1(T)),!.%,writeln(rematch(A,T)).
varcnv(G,T,G_,T_):-compound(T),!,T =..[N|L],lists:foldl(rtg:varcnv1,L,(G,[]),(G_,L_)),!,reverse(L_,L2),T_ =..[N|L2],!.
varcnv(G,T,G,T):-!.
varcnv1(T,(G,L),(G_,[T_|L])) :- varcnv(G,T,G_,T_).
