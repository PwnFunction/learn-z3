# learn-z3

Some simple example challenges to get started with z3.

## Simple Equation

Solve for `x` & `y` where `x + 2y = 7`, `x > 2` and `y < 10`

_[Solution](./1-simple-equation.py)_

## Logical Reasoning

John, Aries, and Joseph are brothers with different ages.

1. Aries is the oldest.
2. John is not the youngest.

Who is the youngest brother?

_[Solution](./2-logical-reasoning.py)_

## Calculate Distribution

Spend exactly 100 dollars and buy exactly 100 animals. 

- Dogs cost 15 dollars
- Cats cost 1 dollar
- Mice cost 25 cents each. 

You have to buy at least one of each. How many of each should you buy?

_[Solution](./3-calculate-distribution.py)_

## Match Assignment

There is an assignment of unique digits to letters such that the equation `send + more = money` holds. 
Find an assignment of the digits to make this true.

_[Solution](./4-match-assignments.py)_

## Magic Square

A square array of numbers, usually positive integers, is called a magic square
if the sums of the numbers in each row, each column, and both main diagonals are the same.

Magic square of 15 looks like:
8 1 6
3 5 7
4 9 2

Generate a magic square of 15 with z3.

_[Solution](./5-magic-square.py)_

## Simple Weak Hash

Following is a simple hash, find the string `s` such that it satifies the statement `n == n2`.

```java
private static boolean hash(final String s) {
    int n = 7;
    final int n2 = 593779930;
    for(int i = 0; i < 6; ++i) {
        n = n * 31 + s.charAt(i);
    }
    return n == n2;
}
```

_[Solution](./6-simple-weak-hash.py)_

## Sudoku

Solve the following sudoku with z3.

```py
0 0 0 0 9 4 0 3 0
0 0 0 5 1 0 0 0 7
0 8 9 0 0 0 0 4 0
0 0 0 0 0 0 2 0 8
0 6 0 2 0 1 0 5 0
1 0 2 0 0 0 0 0 0
0 7 0 0 0 0 5 2 0
9 0 0 0 6 5 0 0 0
0 4 0 9 7 0 0 0 0
```

_[Solution](./7-sudoku-solver.py)_