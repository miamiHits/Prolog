:- use_module(naive_sat).


/* solve again */

evaluate([],Value, Value).

evaluate([X|List], Value):-
        evaluate(List, Value, X).

evaluate(['+'|Rest], Value, Acc):-
    write('in + method'),
    evaluate(Rest, SubValue),
    Value is Acc+SubValue.

evaluate(['*'|Rest], Value, Acc):-
    write('in * method'),
    evaluate(Rest, SubValue),
    Value is Acc*SubValue.
    
/* hamming of pairs */
checkHamming([_]).

checkHamming([W1,W2|List]):-
    hamming(W1, W2), !, 
    checkHamming([W1|List]),
    checkHamming([W2|List]).

hamming(W1, W2):- writeln((W1,W2)).
/*
transpose(_,)


transpose(Rows, [FirstCol|Cols]):-
    makeRows(Rows, FirstCol, RestRows),
    transpose(Rows, Cols).

makeRows([], [], []).
makeRows([[Ele|Row]|Rows], [Ele|FirstCol], [Row|RestRows]):-
    makeRows(Rows, FirstCol, RestRows).
*/

%transpose(Rows,[]) :-
        %nullrows(Rows).

transpose(Rows,[FirstCol|Cols]) :-
    makerow(Rows,FirstCol,RestRows),
    transpose(RestRows,Cols).

makerow([],[],[]).

makerow([[X|RestRow]|Rows],[X|Col],[RestRow|RestRows]) :-
        makerow(Rows,Col,RestRows).
        
nullrows([]).

nullrows([[]|Ns]) :-
    nullrows(Ns).


is_nonogram(nonogram(N, M, ColData, RowData), Solution):-
    checkRows(M, RowData, Solution).

checkRows(0,[],[]).
checkRows(N, [Row|Rows], [S|Sol]):-
    N > 0,
    N1 is N-1,
    checkRow(Row, S),
    checkRows(N1, Rows, Sol).

checkRow([R|Row], [1|Sol]):-
    R1 is R-1,
    checkRow([R1|Row], Sol).

checkRow([0|Row], Sol):-
    checkRow(Row, Sol).

checkRow(Row, [0|Sol]):-
    checkRow(Row, Sol).


checkRow([],[]).

checkRow([0],[]).

/* QUIZ START HERE */
/* 1A */
nonogram_verify([0], 0, []).

nonogram_verify([0], 1,[0]).

nonogram_verify([0|Ns], N,[0|Xs]):- 
    N1 is N-1,
    nonogram_verify(Ns, N1, Xs).

nonogram_verify([Row|Ns],N,[1|Xs]):-
    N > 0,
    Row1 is Row-1,
    N1 is N-1, 
    nonogram_verify([Row1|Ns], N1, Xs).

nonogram_verify([Row|Ns], N,[0|Xs]):- 
    N > 0,
    N1 is N-1,
    nonogram_verify([Row|Ns], N1, Xs).

/* 1B */

nonogram(Ns,N,Xs):-
    length(Xs, N),   
    placeBlocks(Ns, Xs).

placeBlocks(Rows,[0|Xs]):-
    placeBlocks(Rows, Xs).

placeBlocks([Row],Xs):-    
    length(Block, Row),
    ones(Block),
    append(Block, Rest, Xs),
    zeros(Rest).

placeBlocks([Row|Rows],Xs):-    
    length(Block, Row),
    ones(Block),
    append(Block, [0|Rest], Xs),
    placeBlocks(Rows, Rest).

ones([]).
ones([1|Rest]):-
    ones(Rest).

zeros([]).
zeros([0|Rest]):-
    zeros(Rest).
/* 2A */  
 /* Direct Encode */
%(+,-,+)
%    Cnf1 = [[B, X],[B, Y],[-B, -X, -Y]],
 
 direct(Xs,N,CNF):-   
    length(Xs, N),
    onlyOneBit(Xs, CNF1),
   append([Xs], CNF1, CNF).

onlyOneBit([_], []).

onlyOneBit([X, Y |Xs], CNF):-
    onlyOneBit([X | Xs], CNF1),
    onlyOneBit([Y | Xs], CNF2),
    append([[[-X, -Y]], CNF1, CNF2], CNF).


/* 2B */ 
diff(Xs,Ys,[[B]|Cnf]):-
    diff(B, Xs, Ys, Cnf).

diff(B, [X], [Y], CNF):-
        CNF = [[-B, -X, -Y], [-B, X, Y], [B, -X, Y], [B, X, -Y]].

diff(B, [X|Xs], [Y|Ys], CNF):-
    CNF1 = [[-B, -X, -Y, B1], [-B, X, Y, B1], [B, -X, Y], [B, X, -Y], [B, -B1]],
    diff(B1, Xs, Ys, CNF2),
    append(CNF1, CNF2, CNF).


diff(_, [], [], []).

/* 2C */

allDiff([], _, []). 
allDiff([X],N,CNF):- direct(X, N, CNF).

allDiff([X, Y|XXs],N,CNF):-
    direct(X, N, CNF1),
    direct(Y, N, CNF2),
    diff(X, Y, CNF3),
    allDiff([X|XXs], N, CNF4),
    allDiff([Y|XXs], N, CNF5),   
    append([CNF1, CNF2, CNF3, CNF4, CNF5], CNF).

gen_diff(A, B) :-
    length(A, 3), 
    length(B, 3), 
    diff(A, B, CNF),
    sat(CNF).


/* 3A */
lexLT(Xs,Ys,Cnf):-
        lexLT2(Xs,Ys,Cnf1),
        diff(Xs,Ys,CNF2),
        append(Cnf1,CNF2,Cnf).   

lexLT2([], [], []).
lexLT2([X|Xs], [Y|Ys], Cnf):-
     lexLT(Xs, Ys, Cnf1),
     append([[[-X, Y]], Cnf1], Cnf).
         
gen_diff2(A, B) :-
        length(A, 3), 
        length(B, 3), 
        lexLT(A, B, CNF),
        sat(CNF).

/* Task 3B */

matrixLexLt([_], []).

matrixLexLt([Row1, Row2 | Matrix],Cnf):-
        lexLT(Row1, Row2, Cnf1),
        matrixLexLt([Row2|Matrix], Cnf2),
        append([Cnf1, Cnf2], Cnf).
        
/* Task 4a */
bit_vector(N, Vector):-
    length(Vector, N),
    generateVec(Vector, N).

generateVec([], 0).

generateVec([0|V], N):-
    N > 0,
    N1 is N-1,
    generateVec(V, N1).

generateVec([1|V], N):-
    N > 0,
    N1 is N-1,
    generateVec(V, N1).

/* Task 4b */

comparator(X1, X2, X2, X1):-
     X1 =< X2.

comparator(X1, X2, T1, T2):-
    X1>X2,
    T1 is X1,
    T2 is X2.
    
cs([comparator(X1, X3, T1, T3), comparator(X2, X4, T2, T4),
comparator(T1, T2, Y1, Y2), comparator(T3, T4, Y3, Y4),
comparator(Y2, Y3, Z1, Z2)]).

apply_network(Cs, _, _):-
    apply_network(Cs).

apply_network([]).

apply_network([comparator(X1, X2, X1, X2)| Rest]):-
    X1 >= X2,
    apply_network(Rest).

apply_network([comparator(X1, X2, X2, X1)| Rest]):-
    X1 < X2,
    apply_network(Rest).

/* Task 3c */
%is_a_sorting network(Cs, In, Out)



% apply_network([comparator(X1, X2, T1, T2) | Rest], In, Out) :-
%     length(In, N),
%     length(Out1, N),
%     nth1(X1i, In, X1),
%     nth1(X2i, In, X2),
%     nth1(X1i, Out1, T1),
%     nth1(X2i, Out1, T2),
%     apply_network(Rest, Out1, Out).
    
%     apply_network([], Out, Out).