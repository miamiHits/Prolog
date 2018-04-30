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


% one dimentional nonogram
% nonogram(Ns,Xs) :- Ns is the list of "blocks" to be
% placed in list of variables Xs   
    
nonogram(Ns,N,Xs) :-
    length(Xs, N),
    placeBlocks(Ns, Xs).

placeBlocks([[N1],N2|Ns], Xs):-
    length(Block, N1),
    ones(Block),
    append(Block,[0|Rest], Xs),
    placeBlocks([N2|Ns], Rest).

placeBlocks([[N]], Xs):-
        length(Block, N),
        ones(Block),
        append(Block, Rest, Xs),
        zeros(Rest).

placeBlocks(Ns, [0|Xs]):-
    placeBlocks(Ns, Xs).



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
         