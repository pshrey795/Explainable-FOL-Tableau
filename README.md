This project implements an automatic theorem prover for a logical consequence theorem constructed out of statements in first order logic (defined in the file `fol.sml`). If the theorem holds, the program constructs an explainable tableau, with black arrows denoting the tableau path, blue dashed arrows providing the justification for each step of the tableau unless it is derived from its parent in the path, and red arrows showing the reasoning for the closure of branches. If the theorem doesn't hold, the program runs forever. Check the file `FOL_Tableau.pdf` for details. 

Dependencies:

- SML/NJ (Standard ML of New Jersey) compiler
- dot2tex (for visualizing the tableau)

To run the program, follow these steps:

- Clone the repository and navigate to the project directory.
- Open the SML/NJ REPL by running `sml` in your terminal.
- Load the necessary files: `fol.sml` and the argument file (e.g. `arg.sml`) using the `use` command in the REPL.
- Invoke the checkTableau function on the loaded argument.

The above steps will create a dot file representing the tableau if the theorem holds. For visualization: 

- `dot2tex tableau.dot > tableau.tex`
- `pdflatex tableau.tex`