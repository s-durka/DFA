% Zadanie zaliczeniowe 3 - Prolog
% autor: Stanisław Durka
% DFA (Deterministic Finite Automaton) - deterministyczny automat skończony
% ------------------------------------------------------------------------------------------------

% dfa(FunkcjaPrzejścia, StanPoczątkowy, ZbiórStanówAkceptujących)
% FukcjaPrzejścia to lista postaci: [fp(S1, C, S2)|...]

% ==================================== (1) ========================================================
% correct(+Automat, -Reprezentacja)
% Automat jest poprawną reprezentacją DFA jeśli:
%   - kazde przejście występuje dokładnie raz
%   - zbiór stanów akceptujących jest podzbiorem wszystkich stanów
%   - stan początkowy nalezy do zbioru wszystkich stanów
%   - kazdy stan ma przejscie po kazdej z liter z alfabetu, dokładnie raz
correct(dfa(Transitions, InitState, AccStates), rep(TransTree, InitState, AccTree, AlphTree)) :-
    createTransTree(Transitions, TransTree0),
    addEmptyStates(TransTree0, Transitions, TransTree),
    createSimpleBST(AccStates, AccTree),
    createAlphabet(Transitions, AlphTree),
    findBST((InitState, _), TransTree), % stan początkowy nalezy do zbioru wszystkich stanów
    containsKeys(AccTree, TransTree), % zbiór stanów akceptujących jest podzbiorem wszystkich stanów
    checkFullness(TransTree, AlphTree). % sprawdzenie pełności funkcji przejścia


% containsKeys(KeysTree, Tree) :- true wtw. zestaw kluczy KeysTree jest podzbiorem Tree
% KeysTree -- (Simple) BST zawierające tylko klucze
% Tree -- BST o elementach postaci (Klucz, Wartość)
containsKeys(null, _).
containsKeys(tree(Key, L, R), Tree) :-
    findBST((Key, _), Tree),
    containsKeys(L, Tree),
    containsKeys(R, Tree).

% checkFullness(TransTree, AlphTree).
% TransTree - drzewo, którego kluczami są stany, a wartościami drzewa tranzycji o wartościach (Znak, StanDocelowy)
% AlphTree - drzewo 
% sprawdza, ze funkcja przejscia jest pełna, czyli
%   czy alfabet automatu (AlphTree) jest podzbiorem (StateTransT) alfabetu tranzycji 
checkFullness(null, _).
checkFullness(tree((_State, StateTransT), L, R), AlphTree) :-
    containsKeys(AlphTree, StateTransT),
    checkFullness(L, AlphTree),
    checkFullness(R, AlphTree).

% createAlphabet(Transitions, AlphBST) - AlphBST - BST wszystkich liter z alfabetu
% działa jak createSimpleBST().
createAlphabet(L, AlphBST) :- createAlphabet(L, null, AlphBST).
createAlphabet([], Acc, Acc) :- !.
createAlphabet([fp(_, X, _)|Xs], Acc, Ret) :- 
    insertSimpleBST(Acc, X, Acc1), 
    createAlphabet(Xs, Acc1, Ret).

% jeśli klucz (stan) "From" jest juz w drzewie, dodajemy tranzycję (znak, stan') do jego zbioru (drzewa)
% przy dodawaniu elementu nalezy upewnić się, ze w drzewie nie ma: przejscia po danym znaku (kluczu)
addTransition(StatesTree, fp(From, A, To), StatesTreeNew) :-
    findBST((From, TransitionsT), StatesTree), !, % znajdz drzewo tranzycji wychodzących ze stanu "From"
    % \+ searchValTree(To, TransitionsT), % upewnij się, ze nie ma w nim przejscia do stanu "To" po jakimkolwiek znaku
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

% DEBUG:
debug((From, To)).
% addEmptyStates(TransTree, TransList, TransTreeNew).
% dodaje stany S2(!) x listy postaci [fp(S1, X, S2)|...] do drzewa TransTree i zapisuje w TransTreeNew.
% - Wazne dla przypadkow brzegowych, gdzie istnieją stany, od których nic nie wychodzi
%   - wtedy takie stany nie będą dodane do TransTree przez funkcję createTransTree() !
% po dodaniu takiego "pustego" stanu, funkcja checkFullness() sprawdzająca pełność funkcji przejścia zwróci false.
addEmptyStates(T, [], T).
addEmptyStates(TransTree, [fp(_, _, S)|Ss], NewTransTree) :-
    findBST((S, _), TransTree), % stan S istnieje w drzewie TransTree,
    addEmptyStates(TransTree, Ss, NewTransTree). % więc nic nie dodajemy.
addEmptyStates(TransTree, [fp(_, _, S)|Ss], TransTree2) :-
    \+ findBST((S, _), TransTree), % stanu S nie ma jako klucza w drzewie TransTree,
    insertBST(TransTree, (S, null), TransTree1), % więc dodajemy go (drzewo tranzycji wychodzących z S jest puste)
    addEmptyStates(TransTree1, Ss, TransTree2).
      
% ==================================== (2) ========================================================
% accept(+A, ?Słowo) :- true wtw. Słowo \in L(A);
%  A - Automat FDA, Słowo - lista znaków

% accept(+Automat, +Słowo)
accept(Automaton, Word) :-
    correct(Automaton, rep(TransT, InitS, AccT, AlphT)),
    nonvar(Word),
    eval(InitS, Word, rep(TransT, InitS, AccT, AlphT)).

% accept(+Automat, -Słowo).
% aby zapewnić, ze przy generacji słów nalezących do języka automat nie zapętli się,
%   przypadek, gdy Słowo nie jest ustalone jest wyodrębniony.
accept(Automaton, Word) :-
    correct(Automaton, rep(TransT, InitS, AccT, AlphT)),
    var(Word),
    generate(InitS, Word, rep(TransT, InitS, AccT, AlphT)).

% eval(CurrentState, Word, Rep).
eval(State, [], rep(TransT, InitS, AccT, AlphT)) :-
    acceptState(State, AccT).
eval(CurrState, [X| Xs], rep(TransT, InitS, AccT, AlphT)) :-
    transition(CurrState, X, NewState, TransT),
    eval(NewState, Xs, rep(TransT, InitS, AccT, AlphT)).

transition(S1, A, S2, TransTree) :- 
    findBST((S1, SubTree), TransTree), % teraz jesteśmy w poddrzewie zawierającym przejścia ze stanu S1
    findBST((A, S2), SubTree).

acceptState(State, AccTree) :-
    findSimpleBST(State, AccTree).
    
% TODO zeby generateLen informowal jakos (fail?), jak nie ma juz tranzycji?
% jesli język jest skończony czy nie będzie się petlił teraz?

% generate(CurrentState, Word, Rep).
generate(State0, Word, Rep) :- generate(State0, Word, Rep, 1).
generate(State, Word, Rep, Len) :- 
    generateLen(State, Word, Rep, Len).
generate(State, Word, Rep, Len) :- 
    Len1 is Len + 1,
    % Len1 < 10, % DEBUG
    generate(State, Word, Rep, Len1).


% generateLen(CurrentState, Word, Rep, Len) :- true wtw. length(Word) == Len oraz S \in L(A)
generateLen(CurrState, [], rep(_TransT, _InitS, AccT, _AlphT), Len) :-
    0 is Len, !,
    acceptState(CurrState, AccT).

% generateLen(CurrState, Word, Tail, Rep, CurrLen, Len).     
generateLen(CurrState, [X|Xs], rep(TransT, InitS, AccT, AlphT), Len) :-
    \+ Len is 0,
    transition(CurrState, X, NewState, TransT),
    Len1 is Len - 1,
    generateLen(NewState, Xs, rep(TransT, InitS, AccT, AlphT), Len1).


% ==================================== (3) =======================================================
% empty(+Automat) :- true wtw. gdy język generowany przez automat jest pusty

% empty(dfa(Transitions, InitState, AccStates)) :-
%     \+ member(_,AccStates) ,!. % jeśli lista stanów akceptujących jest pusta, L(A) jest pusty
% jeśli Automat nie jest poprawną reprezentacją DFA, zwraca false
empty(Automaton) :-
    correct(Automaton, rep(TransT, InitS, AccT, AlphT)),
    \+ findAPath(InitS, tree(InitS, null, null), AccT, TransT). % drzewo jednoelementowe ze stanem początkowym jest początkową wartością zbioru stanów odwiedzonych

% findAPath(State, Visited, Accepting, Transitions) :- true wtw. gdy 
% w grafie istnieje ściezka od stanu State do dowolnego stanu akceptującego
% false wpp.            (DFS)
findAPath(State, _, Accepting, _) :-
    acceptState(State, Accepting), !.
findAPath(State, Visited, Accepting, Transitions) :-
    transition(State, _, NewState, Transitions),
    \+ findSimpleBST(NewState, Visited), % szukamy stanu, który nie był jeszcze odwiedzony
    insertSimpleBST(Visited, NewState, Visited1), % oznaczamy stan jako odwiedzony dla następnych iteracji
    findAPath(NewState, Visited1, Accepting, Transitions).

% ==================================== (4) =======================================================
% equal(+Automat1, +Automat2).
% Odnosi sukces wtw, gdy L(Automat1) = L(Automat2) oraz alfabety obu automatów są równe.
equal(Automat1, Automat2) :- 
    subsetEq(Automat1, Automat2),
    subsetEq(Automat1, Automat2).

% ==================================== (5) =======================================================
% subsetEq(+A, +B). - A, B - automaty DFA
% Odnosi sukces wtw, gdy L(A) \in L(B) oraz alfabety obu automatów są równe
% 1. stworz B2 t. ze L(BC) jest dopełnieniem L(B)
% 2. stworz automat L(C) taki, ze L(C) jest przecięciem L(A) i L(B2)
% 3. jeśli L(C) jest pusty, L(A) jest podzbiorem L(B)
subsetEq(A, B) :-
    correct(A, RepA),
    correct(B, RepB),
    complement(RepB, RepB2),
    intersect(A, B, RepA, RepB2, RepC),
    empty(RepC).

% intersect(A, B, RepA, RepB, RepC) :- suckes jeśli RepC jest reprezentacją przecięcia automatów A i B.
% sprawdza tez, czy alfabety A i B są równe
intersect(dfa(TransListA, InitA, AccListA), dfa(TransListB, InitB, AccListB), 
          rep(TransTreeA, InitA, AccTreeA, AlphTreeA), rep(TransTreeB, InitB, AccTreeB, AlphTreeB), 
          rep(TransTreeC, (InitA, InitB), AccTreeC, AlphTreeC)) :-
    % subsetOf(AlphTreeA, AlphTreeB),
    % subsetOf(AlphTreeB, AlphTreeA), % alfabety automatów A i B są sobie równe
    intersectTrans(TransListA, TransTreeB, TransListC), % stwórz listę tranzycji przeciecia A i B,
    % print(TransListC),
    createTransTree(TransListC, TransTreeC), % stwórz drzewo tranzycji przecięcia z listy tranzycji.
    print(TransTreeC).    
    % listProduct(AccListA, AccListB, AccListC), % zbiór accept(C) to iloczyn kartezjański accept(A) x accept(B)
    % createSimpleBST(AccListC, AccTreeC).

% intrs(dfa(TransA, InitA, AccA), dfa(TransB, InitB, AccB), dfa(TransC, InitC, AccC)) :-

% intersectTrans(TransListA, TransTreeB, TransListAB).
% - A, B - automaty DFA
% TransListAB - lista tranzycji przecięcia A i B
% intersectTrans([fp(XA, Z, YA) | TailA], TransTreeB, [fp((XA, XB), Z, (YA, YB))| Ts]) :-
%     transition(XB, Z, YB, TransTreeB), !, % jeśli jest tez przejście po Z w B,
%     intersectTrans(TailA, TransTreeB, Ts).
% intersectTrans([fp(XA, Z, YA) | TailA], TransTreeB, Ts) :-
%     intersectTrans(TailA, TransTreeB, Ts). % jeśli nie ma tranzycji, to idziemy do kolejnego el. listy
intersectTrans([], _, []).
intersectTrans([fp(XA, Z, YA) | TailA], TransTreeB, IntersectList) :-
    findall(fp((XA, XB), Z, (YA, YB)), transition(XB, Z, YB, TransTreeB), L), % znajdz wszystkie przejscia po Z w B
    intersectTrans(TailA, TransTreeB, L1),
    append(L, L1, IntersectList).
% intersectTrans([_| TailA], TransTreeB, Ts) :-
%     intersectTrans(TailA, TransTreeB, Ts). % jeśli nie ma tranzycji, to idziemy do kolejnego el. listy

listProduct(L1,L2,L3) :- findall((X,Y),(member(X,L1),member(Y,L2)),L3).

% addInterceptAcceptState(AccTreeAB, XA, XB, AccTreeA, AccTreeB, AccTreeABNew) :-
%     acceptState(XA, AccTreeA),
%     acceptState(XB, AccTreeB),
%     insertSimpleBST(AccTreeAB, (XA, XB), AccTreeABNew).

% addInterceptAcceptState(AccTreeAB, XA, XB, AccTreeA, AccTreeB, AccTreeAB) :- 
%     \+ acceptState(XA, AccTreeA).
% addInterceptAcceptState(AccTreeAB, XA, XB, AccTreeA, AccTreeB, AccTreeAB) :- 
%     \+ acceptState(XB, AccTreeB).



    % fp(S1, C, S2)
% subsetOf(Tree1, Tree2) :- true wtw. zbiór kluczy w Tree1 jest podzbiorem kluczy w Tree2
subsetOf(null, _).
subsetOf(tree(X, L, R), Tree) :-
    findBST(X, Tree),
    subsetOf(L, Tree),
    subsetOf(R, Tree).

% complement(+AutRep, -AutComp) :- true wtw, gdy AutComp jest reprezentacją automatu 
%   będącego dopełnieniem automatu o reprezentacji AutRep nad tym samym alfabetem
complement(rep(TransT, InitS, Acc, Alph), rep(TransT, InitS, Acc1, Alph)) :-
    reverse(Acc, Acc1, TransT). % nowe stany akceptujące to dopełnienie oryginalnego zbioru st. akc.

% wykonuje complementList i zamienia ją na drzewo BST
reverse(SubsetT, CompT, TransT) :- 
    complementList(SubsetT, [], CompList, TransT),
    createSimpleBST(CompList, CompT).

% complementList(Subset, Acc, ComplimentList, Tree). - odnosi suckes,
% Subset jest drzewem BST o elementach będących podzbiorem kluczy Tree, 
% a ComplimentList jest listą wszystkich elementów nalezących do ( Tree \ Subset );
complementList(_, Acc, Acc, null). % Acc - akumulator; 
complementList(Subset, Acc, CompList, tree((State, _), L, R)) :-
    \+ findSimpleBST(State, Subset), !,              % jeśli nieprawda, ze State \in Subset,
    complementList(Subset, [State| Acc], CL1, L),    % CL1 == (States(L) \ Subset) ++ [State| Acc]
    complementList(Subset, CL1, CompList, R).        % CompList == (States(R) \ Subset) ++ CL1
    % CompList jest listą wszystkich stanów z dopełnienia Subset, 
    % które występują jako klucze w poddrzewie o korzeniu (State, _).
complementList(Subset, Acc, CompList, tree((State, _), L, R)) :-
    findSimpleBST(State, Subset),              % State \in Subset, więc nie dodajemy go do dopełnienia
    complementList(Subset, Acc, CL1, L),       % CL1 == (States(L) \ Subset) ++ [State| Acc]
    complementList(Subset, CL1, CompList, R).  % CompList == (States(R) \ Subset) ++ CL1



% -----------------------------------------------------
% Funkcje pomocnicze - operacje na Binary Search Trees:
% -----------------------------------------------------

% findBST((Key, Value), BST). -- przeszukaj drzewo BST uporządkowane przez wartość klucza Key
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
% jeśli X nie jest określony, generuj wszystkie wartości w drzewie:
findBST((Key, Val), tree(_Root, _L, R)) :- 
    var(Key),
    findBST((Key, Val), R).
findBST((Key, Val), tree(_Root, L, _R)) :- 
    var(Key),
    findBST((Key, Val), L).

findSimpleBST(X, tree(X, _L, _R)).
% jeśli X jest określony, znajdz Key:
findSimpleBST(X, tree(Root, _L, R)) :-
    nonvar(X),
    Root @=< X, !,
    findSimpleBST(X, R).
findSimpleBST(X, tree(Root, L, _R)) :-
    nonvar(X),
    Root @> X, !,
    findSimpleBST(X, L).
% jeśli X nie jest określony, generuj wszystkie wartości w drzewie:
findSimpleBST(X, tree(_Root, _L, R)) :- 
    var(X),
    findSimpleBST(X, R).
findSimpleBST(X, tree(_Root, L, _R)) :- 
    var(X),
    findSimpleBST(X, L).

% szuka w drzewie wartości (Key, Value) wartości Value (przechodzi całe drzewo az znajdzie wartość)
% searchValTree(Val, tree((_, Val), _L, _R)).
% searchValTree(Val, tree(_Root, L, R)) :- 
%     searchValTree(Val, R); 
%     searchValTree(Val, L).

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

% tworzy drzewo BST 
% z akumulatorem: rekursja jest ogonowa + dodaje od początku listy, 
% czyli korzeniem jest pierwszy element
createBST(L, D) :- createBST(L, null, D).
createBST([], A, A) :- !.
createBST([X|Xs], A, Ret) :- 
    insertBST(A, X, A1), 
    createBST(Xs, A1, Ret).

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

% generuje wszystkie elementy drzewa
% TODO nieuzywane
traverseTree(X, tree(X, _, _)).
traverseTree(X, tree(_, L, R)) :-
    traverseTree(X, L);
    traverseTree(X, R).

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