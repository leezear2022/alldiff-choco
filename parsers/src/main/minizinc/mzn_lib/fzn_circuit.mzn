%-----------------------------------------------------------------------------%
% Constrains the elements of 'x' to define a circuit where 'x[i] = j' means
% that 'j' is the successor of 'i'.
%-----------------------------------------------------------------------------%

predicate fzn_circuit(array[int] of var int: x) =
    circuitChoco(x);

%-----------------------------------------------------------------------------%

predicate fzn_circuit_reif(array[int] of var int: x, var bool: b) =
    abort("Reified circuit/1 is not supported.");