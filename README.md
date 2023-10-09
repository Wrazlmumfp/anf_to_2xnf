# anf_to_2xnf

> Tool for conversion of ANF to 2-XOR-OR-AND normal form (2-XNF) implemented in Python 3.

### Usage

> `python3 anf_to_2xnf.py input.anf -xp output.xnf`

`input.anf` is a text file with the following structure:

- The first line contains all indeterminates separated with a comma and AT LEAST ONE SPACE BAR (important for reading in indeterminates of the form `x[1,1]`).
- All other lines contain each exactly one polynomial.
- Polynomials sums (`+`) of terms and a term is a product (`*`) of indeterminates or simply `1`.
- Except for the first line, spaces and tabs are ignored and no indeterminate can be called `1`.
- Lines marked with `#` at the start are treated as comment lines.


`output.xnf` is a text file containing a DIMACS-like description of a 2-XNF representation of the system in `input.anf`:

- Lines starting with `c` are ignored as comment lines,
- the header is of the form `p xnf n_vars n_cls`,
- linerals are represented as sums of literals (e.g. `-1+2+-3` for the lineral $(\neg X_1 \oplus X_2 \oplus \neg X_3)$,
- XNF literals are lists of linerals, separated using spaces and terminated with `0` (e.g. `-1+2 3 0` represents $(\neg X_1 \oplus X_2) \lor X_3$)

For example, the XNF $((X_1 \oplus X_2) \lor X_3) \land (X_1 \lor \neg(X_1 \oplus X_3)) \land (X_2 \oplus X_1) \land X_2$ is encoded as

```
p xnf 3 4
1+2 3 0
1 -1+3 0
2+1 0
2 0
```


Run `python3 anf_to_2xnf.py -h` to get detailed informations about all options.

### Requirements

- Python 3.10.12 or newer
- Python package `galois` (see <https://github.com/mhostetter/galois>)
- Python package `numpy` (see <https://numpy.org/>)

Optional:

- Python package `pysat` (for option `--maxsat`) (see <https://github.com/mhostetter/galois>)
