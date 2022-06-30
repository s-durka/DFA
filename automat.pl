% Zadanie zaliczeniowe 3 - Prolog
% autor: Stanisław Durka
% DFA (Deterministic Finite Automaton) - deterministyczny automat skończony

% dfa(FunkcjaPrzejścia, StanPoczątkowy, ZbiórStanówAkceptujących)
% FukcjaPrzejścia to lista termów postaci: fp(S1, C, S2)

% correct(+Automat, -Reprezentacja)
% poprawne DFA:
%   kazde przejście występuje raz
correct(dfa(Transitions, InitState, AccState), rep(TransTree, InitS, AccTree)) :-
    createTransTree(Transitions, TransTree).
    % createBST(AcceptStates, AccTree).    

% accept(+Automat, ?Słowo)
% accept(Automat, Word) :-
%     correct(Automat, rep(TransTree, InitState, AcceptTree)),
%     accept2(InitState, TransTree, AcceptTree, Word).

% accept2(CurrentState, TransTree, AcceptTree, [X| Xs]) :- 


% empty(+Automat)
% equal(+Automat1, +Automat2)
% subsetEq(+Automat1, +Automat2)

edge(S1, A, S2, Trans) :- findBST(fp(S1, A, S2), Trans). % TODO



% jeśli klucz (stan) "From" jest juz w drzewie, dodajemy tranzycję (znak, stan') do jego zbioru (drzewa)
% przy dodawaniu elementu nalezy upewnić się, ze w drzewie nie ma: 
%   - przejscia po danym znaku (kluczu)
%   - przejscia do tego samego stanu (wartosci)
addTransition(StatesTree, fp(From, A, To), StatesTreeNew) :-
    findBST((From, TransitionsT), StatesTree), !, % znajdz drzewo tranzycji wychodzących ze stanu "From"
    \+ searchValTree(To, TransitionsT), % upewnij się, ze nie ma w nim przejscia do stanu "To" po jakimkolwiek znaku
    insertBST(TransitionsT, (A, To), TransitionsTNew), % dodaj nową tranzycję (uwaga -- jeśli wartość o danym kluczu juz istnieje, zwraca false)
    modifyBST(StatesTree, (From, TransitionsTNew), StatesTreeNew). % wstaw poddrzewo z nową tranzycją do BST stanów

% jeśli klucza (stanu) "From" nie ma w drzewie stanów, dodajemy go do drzewa:
addTransition(StatesTree, fp(From, A, To), StatesTreeNew) :-
    \+ findBST((From, _), StatesTree), !,
    createBST([(A, To)], TransTree), % utwórz jednoelementowe drzewo z nową tranzycją
    insertBST(StatesTree, (From, TransTree), StatesTreeNew). % dodaj parę (NowyStan, NoweDrzewo) do drzewa stanów

% createTransTree(List, Tree) - List - lista przejść fp(X, A, Y), Tree - BST przejść
createTransTree(List, Tree) :- createTransTree(List, null, Tree).
% rozw. z akumulatorem - rekursja ogonowa:
createTransTree([], T, T).
createTransTree([T| Ts], AccTree, Ret) :-
    addTransition(AccTree, T, AccTree1), % wstaw nowe przejście do akumulatora
    createTransTree(Ts, AccTree1, Ret). % dodaj kolejne elementy listy do drzewa



% ----------------------------------------------------
% Funkcje pomocnicze - operacje na Binary Search Trees:

% findBST((Key, Value), BST). -- search BST by the Key value
findBST(X, tree(X, _L, _R)).
% jeśli X jest określony, znajdz X:
findBST((Key, Val), tree((RootK, _V), _L, R)) :-
    nonvar(Key),
    RootK @=< Key, !,
    findBST((Key, Val), R).
findBST((Key, Val), tree((RootK, _V), L, _R)) :-
    nonvar(Key),
    RootK @> Key, !,
    findBST((Key, Val), L).
% jeśli X nie jest określony, generuj wszystkie wartości w drzewie
findBST((Key, Val), tree(_Root, _L, R)) :- 
    var(Key),
    findBST((Key, Val), R).
findBST((Key, Val), tree(_Root, L, _R)) :- 
    var(Key),
    findBST((Key, Val), L).

% szuka w drzewie wartości (Key, Value) wartości Value (przechodzi całe drzewo az znajdzie wartość)
searchValTree(Val, tree((_, Val), _L, _R)).
searchValTree(Val, tree(_Root, L, R)) :- 
    searchValTree(Val, R); 
    searchValTree(Val, L).

% insertBST(Tree, (Key, Value), NewTree).
% -- false jeśli w drzewie jest juz element o danym kluczu
insertBST(null, El, tree(El, null, null)).
insertBST(tree(El, L, R), El, tree(El, L, R)) :- fail. % fail przy próbie wielokrotnego wstawienia elementu 
insertBST(tree((RootK, RootV), L, R), (Key, Val), tree((RootK, RootV), NewL, R)) :- 
    Key @< RootK, !,
    insertBST(L, (Key, Val), NewL).
insertBST(tree((RootK, RootV), L, R), (Key, Val), tree((RootK, RootV), L, NewR)) :- 
    Key @> RootK, 
    insertBST(R, (Key, Val), NewR).



% modifyBST(Tree, (Key, Value), NewTree).
% jeśli wartość o podanym kluczu juz istnieje w drzewie, zmienia ją
% wpp. wstawia wartość (Key, Value) do drzewa
modifyBST(null, El, tree(El, null, null)).
modifyBST(tree((Key, _Val), L, R), (Key, NewVal), tree((Key, NewVal), L, R)) :- !. % zmiana wartosci
modifyBST(tree((RootK, RootV), L, R), (Key, Val), tree((RootK, RootV), NewL, R)) :- 
    Key @< RootK, !,
    modifyBST(L, (Key, Val), NewL).
modifyBST(tree((RootK, RootV), L, R), (Key, Val), tree((RootK, RootV), L, NewR)) :- 
    Key @> RootK, 
    modifyBST(R, (Key, Val), NewR).

% tworzy drzewo BST 
% z akumulatorem: rekursja jest ogonowa + dodaje od początku listy, 
% czyli korzeniem jest pierwszy element
createBST(L, D) :- createBST(L, null, D).
createBST([], A, A) :- !.
createBST([X|Xs], A, Ret) :- 
    insertBST(A, X, A1), 
    createBST(Xs, A1, Ret).

% insertSimpleBST(BST, Value, NewBST). (klucz to jednocześnie wartość)
% -- false jeśli w drzewie jest juz element o danym kluczu
insertSimpleBST(null, El, tree(El, null, null)).
insertSimpleBST(tree(El, L, P), El, tree(El, L, P)) :- !.   % nie wstawia wielokrotnie
insertSimpleBST(tree(Root, L, R), El, tree(Root, NewL, R)) :- 
    El @< Root, !,
    insertSimpleBST(L, El, NewL).
insertSimpleBST(tree(Root, L, R), El, tree(Root, L, NewR)) :- 
    El @> Root, 
    insertSimpleBST(R, El, NewR).

% Uzywane przy tworzeniu drzewa stanow akceptujacych
createSimpleBST(L, D) :- createSimpleBST(L, null, D).
createSimpleBST([], A, A) :- !.
createSimpleBST([X|Xs], A, Ret) :- 
    insertSimpleBST(A, X, A1), 
    createSimpleBST(Xs, A1, Ret).

% example(IdentyfikatorAutomatu, Automat)
example(a11, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)], 1, [2,1])).
example(a12, dfa([fp(x,a,y),fp(x,b,x),fp(y,a,x),fp(y,b,x)], x, [x,y])).
example(a2, dfa([fp(1,a,2),fp(2,b,1),fp(1,b,3),fp(2,a,3), fp(3,b,3),fp(3,a,3)], 1, [1])).
example(a3, dfa([fp(0,a,1),fp(1,a,0)], 0, [0])).
example(a4, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,x)], x, [x])).
example(a5, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,zz),fp(zz,a,x)], x, [x])).
example(a6, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)], 1, [])).
example(a7, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1),

fp(3,b,3),fp(3,a,3)], 1, [3])).
% bad ones
example(b1, dfa([fp(1,a,1),fp(1,a,1)], 1, [])).
example(b2, dfa([fp(1,a,1),fp(1,a,2)], 1, [])).
example(b3, dfa([fp(1,a,2)], 1, [])).
example(b4, dfa([fp(1,a,1)], 2, [])).
example(b5, dfa([fp(1,a,1)], 1, [1,2])).
example(b6, dfa([], [], [])).